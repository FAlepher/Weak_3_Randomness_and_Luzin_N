import Weak_3_Randomness_and_Luzin_N.GuoLocalFinite
import Weak_3_Randomness_and_Luzin_N.GuoScheduleRecords

namespace Guo

/-- A reservation system describes the stage of each visit and how to recognize it. -/
structure Reservation where
  visit : Nat → Nat → Nat
  slot : Nat → Option (Nat × Nat)
  slot_visit : ∀ i m, slot (visit i m) = some (i, m)
  visit_slot : ∀ {t i m}, slot t = some (i, m) → visit i m = t
  fits : ∀ {t i m}, slot t = some (i, m) → i ≤ t + 1
  strict : ∀ i, ∀ {m n}, m < n → visit i m < visit i n
  unbounded : ∀ i t, ∃ m, t ≤ visit i m

structure CandidateWords where
  width : Nat → Nat
  word : (i : Nat) → Bits (width i)
  fits : ∀ i, width i ≤ i
  witness : Nat → WitnessRelation

private def StageAction.reindex (a : StageAction s) (eq : s = t) : StageAction t := eq ▸ a

@[simp] private theorem StageAction.index_reindex (a : StageAction s) (eq : s = t) :
    (a.reindex eq).index = a.index := by cases eq; rfl

@[simp] private theorem StageAction.hitsAt_reindex (a : StageAction s) (eq : s = t) (i) (x) :
    (a.reindex eq).hitsAt i x = a.hitsAt i x := by cases eq; rfl

def recordTest (V : Reservation) (C : CandidateWords) (i m : Nat) : Bool :=
  let current := score (C.witness i) (V.visit i m + 1)
  let previous := match m with
    | 0 => 0
    | n + 1 => score (C.witness i) (V.visit i n + 1)
  decide (previous < current)

/-- Construct the schedule by the finite record test at each reserved stage. -/
def candidateSchedule (V : Reservation) (C : CandidateWords) : Schedule := fun t =>
  match V.slot t with
  | none => .idle (t + 1)
  | some (i, m) =>
    if hi : i ≤ t + 1 ∧ recordTest V C i m = true then
      let a := StageAction.selected i (t + 1 - i) (C.word i) (C.fits i)
      a.reindex (by have := hi.1; omega)
    else .idle (t + 1)

theorem candidateSchedule_index_iff (V : Reservation) (C : CandidateWords) (t i : Nat) :
    (candidateSchedule V C t).index = some i ↔ ∃ m, V.slot t = some (i, m) ∧ recordTest V C i m = true := by
  cases heq : V.slot t with
  | none => simp [candidateSchedule, heq, StageAction.index]
  | some im =>
    rcases im with ⟨j, m⟩
    have fit := V.fits heq
    by_cases record : recordTest V C j m = true
    · have branch : j ≤ t + 1 ∧ recordTest V C j m = true := ⟨fit, record⟩
      simp only [candidateSchedule, heq, dif_pos branch, StageAction.index_reindex]
      simp only [StageAction.index, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro rfl
        exact ⟨m, ⟨rfl, rfl⟩, record⟩
      · rintro ⟨_, ⟨h, _⟩, _⟩
        exact h
    · simp [candidateSchedule, heq, StageAction.index, record]
      rintro rfl
      simpa using record

theorem candidateSchedule_hitsAt (V : Reservation) (C : CandidateWords) (t i : Nat)
    (chosen : (candidateSchedule V C t).index = some i) (x : Cantor) :
    (candidateSchedule V C t).hitsAt i x ↔ cylinder (C.word i) x := by
  obtain ⟨m, slot, record⟩ := (candidateSchedule_index_iff V C t i).mp chosen
  have branch : i ≤ t + 1 ∧ recordTest V C i m = true := ⟨V.fits slot, record⟩
  simp only [candidateSchedule, slot, dif_pos branch, StageAction.hitsAt_reindex]
  simp [StageAction.hitsAt]

private theorem visit_mono (V : Reservation) (i) {m n : Nat} (le : m ≤ n) :
    V.visit i m ≤ V.visit i n := by
  cases Nat.lt_or_eq_of_le le with
  | inl h => exact Nat.le_of_lt (V.strict i h)
  | inr h => cases h; exact Nat.le_refl _

theorem candidate_recurrence_iff (V : Reservation) (C : CandidateWords) (i : Nat) :
    InfinitelySelected (candidateSchedule V C) i ↔ ∀ n, ∃ witness, C.witness i n witness = true := by
  have recordAt (m : Nat) :
      recordTest V C i (m + 1) = true ↔
        score (C.witness i) (V.visit i m + 1) < score (C.witness i) (V.visit i (m + 1) + 1) := by
    simp [recordTest]
  have math := records_iff_all_witnesses (C.witness i) (fun m => V.visit i m + 1)
    (fun {_ _} h => Nat.succ_le_succ (visit_mono V i h))
    (fun t => by obtain ⟨m, hm⟩ := V.unbounded i t; exact ⟨m, by omega⟩)
  rw [← math]
  constructor
  · intro inf start
    obtain ⟨t, ht, chosen⟩ := inf (V.visit i (start + 1))
    obtain ⟨m, slot, record⟩ := (candidateSchedule_index_iff V C t i).mp chosen
    have stage := V.visit_slot slot
    have large : start + 1 ≤ m := by
      by_cases h : m < start + 1
      · have lt := V.strict i h
        omega
      · omega
    cases m with
    | zero => omega
    | succ m =>
      exact ⟨m, by omega, (recordAt m).mp record⟩
  · intro inf start
    obtain ⟨m, startBefore⟩ := V.unbounded i start
    obtain ⟨n, hn, increased⟩ := inf m
    refine ⟨V.visit i (n + 1), Nat.le_trans startBefore (visit_mono V i (by omega)), ?_⟩
    exact (candidateSchedule_index_iff V C _ i).mpr
      ⟨n + 1, V.slot_visit i (n + 1), (recordAt n).mpr increased⟩

end Guo

#print axioms Guo.candidate_recurrence_iff
#print axioms Guo.candidateSchedule
