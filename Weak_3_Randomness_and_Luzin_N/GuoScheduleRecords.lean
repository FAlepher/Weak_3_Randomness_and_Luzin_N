import Std

namespace Guo

abbrev WitnessRelation := Nat → Nat → Bool

/-- Verify the first `len` obligations using witnesses up to `time`. -/
def validLength (R : WitnessRelation) (time len : Nat) : Bool :=
  (List.range len).all (fun n => (List.range (time + 1)).any (R n))

theorem validLength_iff (R : WitnessRelation) (time len : Nat) :
    validLength R time len = true ↔ ∀ n < len, ∃ witness ≤ time, R n witness = true := by
  simp [validLength, List.all_eq_true, List.any_eq_true, Nat.lt_succ_iff]

/-- The greatest verified length at most the search cap. -/
def greatestVerified (R : WitnessRelation) (time : Nat) : Nat → Nat
  | 0 => 0
  | cap + 1 =>
    if validLength R time (cap + 1) then cap + 1 else greatestVerified R time cap

theorem greatestVerified_le (R : WitnessRelation) (time cap : Nat) :
    greatestVerified R time cap ≤ cap := by
  induction cap with
  | zero => exact Nat.le_refl _
  | succ cap ih =>
    simp only [greatestVerified]
    split <;> omega

theorem greatestVerified_valid (R : WitnessRelation) (time cap : Nat) :
    validLength R time (greatestVerified R time cap) = true := by
  induction cap with
  | zero => rfl
  | succ cap ih =>
    simp only [greatestVerified]
    split <;> assumption

theorem le_greatestVerified (R : WitnessRelation) (time cap len : Nat) (hle : len ≤ cap)
    (valid : validLength R time len = true) : len ≤ greatestVerified R time cap := by
  induction cap with
  | zero => exact hle
  | succ cap ih =>
    simp only [greatestVerified]
    split
    · exact hle
    · rename_i failed
      by_cases h : len ≤ cap
      · exact ih h
      · have eq : len = cap + 1 := by omega
        exact (failed (eq ▸ valid)).elim

def score (R : WitnessRelation) (time : Nat) : Nat := greatestVerified R time time

theorem score_monotone (R : WitnessRelation) (st : s ≤ t) : score R s ≤ score R t := by
  apply le_greatestVerified
  · exact Nat.le_trans (greatestVerified_le R s s) st
  · apply (validLength_iff R t (score R s)).mpr
    intro n hn
    obtain ⟨w, hw, certificate⟩ :=
      (validLength_iff R s (score R s)).mp (greatestVerified_valid R s s) n hn
    exact ⟨w, Nat.le_trans hw st, certificate⟩

private theorem bounded_witnesses (R : WitnessRelation)
    (total : ∀ n, ∃ w, R n w = true) (len : Nat) :
    ∃ t, len ≤ t ∧ ∀ n < len, ∃ w ≤ t, R n w = true := by
  induction len with
  | zero => exact ⟨0, Nat.le_refl _, fun n hn => (Nat.not_lt_zero n hn).elim⟩
  | succ len ih =>
    obtain ⟨t, ht, old⟩ := ih
    obtain ⟨w, witness⟩ := total len
    refine ⟨max (max t w) (len + 1), Nat.le_max_right _ _, fun n hn => ?_⟩
    by_cases hnOld : n < len
    · obtain ⟨w', bound, certificate⟩ := old n hnOld
      exact ⟨w', by omega, certificate⟩
    · obtain rfl : n = len := by omega
      exact ⟨w, by omega, witness⟩

theorem unbounded_score_on_visits_iff (R : WitnessRelation) (visit : Nat → Nat)
    (unboundedVisits : ∀ t, ∃ v, t ≤ visit v) :
    (∀ len, ∃ v, len ≤ score R (visit v)) ↔ ∀ n, ∃ w, R n w = true := by
  constructor
  · intro unbounded n
    obtain ⟨v, hv⟩ := unbounded (n + 1)
    obtain ⟨w, _, hw⟩ :=
      (validLength_iff R (visit v) (score R (visit v))).mp
        (greatestVerified_valid R _ _) n (by omega)
    exact ⟨w, hw⟩
  · intro total len
    obtain ⟨t, ht, verified⟩ := bounded_witnesses R total len
    obtain ⟨v, htv⟩ := unboundedVisits t
    refine ⟨v, Nat.le_trans (le_greatestVerified R t t len ht ?_) (score_monotone R htv)⟩
    exact (validLength_iff R t len).mpr verified

private theorem eventually_constant_of_bounded (a : Nat → Nat)
    (mono : ∀ ⦃m n⦄, m ≤ n → a m ≤ a n) (B : Nat) (bounded : ∀ n, a n ≤ B) :
    ∃ start, ∀ n, start ≤ n → a n = a start := by
  classical
  induction B with
  | zero => exact ⟨0, fun n _ => by have := bounded n; have := bounded 0; omega⟩
  | succ B ih =>
    by_cases attains : ∃ n, a n = B + 1
    · obtain ⟨start, top⟩ := attains
      refine ⟨start, fun n hn => ?_⟩
      have h₁ := mono hn
      have h₂ := bounded n
      omega
    · exact ih (fun n => by
        have h₁ := bounded n
        have h₂ : a n ≠ B + 1 := fun he => attains ⟨n, he⟩
        omega)

theorem recurrent_increases_iff_unbounded (a : Nat → Nat)
    (mono : ∀ ⦃m n⦄, m ≤ n → a m ≤ a n) :
    (∀ start, ∃ n, start ≤ n ∧ a n < a (n + 1)) ↔ (∀ B, ∃ n, B ≤ a n) := by
  classical
  constructor
  · intro recurs B
    apply Classical.byContradiction
    intro fails
    have bounded (n : Nat) : a n ≤ B := by
      have h : ¬B ≤ a n := fun h => fails ⟨n, h⟩
      omega
    obtain ⟨start, constant⟩ := eventually_constant_of_bounded a mono B bounded
    obtain ⟨n, hn, increases⟩ := recurs start
    rw [constant n hn, constant (n + 1) (by omega)] at increases
    exact (Nat.lt_irrefl _ increases)
  · intro unbounded start
    apply Classical.byContradiction
    intro stops
    have constant (n : Nat) (hn : start ≤ n) : a n = a start := by
      induction n with
      | zero =>
        obtain rfl : start = 0 := by omega
        rfl
      | succ n ih =>
        change a (n + 1) = a start
        by_cases h : start ≤ n
        · have nlt : ¬a n < a (n + 1) := fun hlt => stops ⟨n, h, hlt⟩
          have step : a n ≤ a (n + 1) := mono (Nat.le_succ n)
          have eq := ih h
          omega
        · obtain rfl : start = n + 1 := by omega
          rfl
    obtain ⟨n, hn⟩ := unbounded (a start + 1)
    by_cases h : start ≤ n
    · have := constant n h
      omega
    · have := mono (show n ≤ start by omega)
      omega

/-- On each unbounded increasing sequence of visits, records recur exactly for true candidates. -/
theorem records_iff_all_witnesses (R : WitnessRelation) (visit : Nat → Nat)
    (monotoneVisits : ∀ ⦃m n⦄, m ≤ n → visit m ≤ visit n)
    (unboundedVisits : ∀ t, ∃ v, t ≤ visit v) :
    (∀ start, ∃ n, start ≤ n ∧ score R (visit n) < score R (visit (n + 1))) ↔
      ∀ n, ∃ w, R n w = true :=
  (recurrent_increases_iff_unbounded (fun n => score R (visit n))
    (fun {_ _} h => score_monotone R (monotoneVisits h))).trans
    (unbounded_score_on_visits_iff R visit unboundedVisits)

end Guo

#print axioms Guo.records_iff_all_witnesses
