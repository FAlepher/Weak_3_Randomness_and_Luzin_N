import Weak_3_Randomness_and_Luzin_N.GuoCantorCoding

namespace Guo

def StageAction.index (a : StageAction s) : Option Nat :=
  match a with
  | .idle _ => none
  | .selected i _ _ _ => some i

def StageAction.hitsAt (a : StageAction s) (i : Nat) (x : Cantor) : Prop :=
  match a with
  | .idle _ => False
  | .selected j _ σ _ => j = i ∧ cylinder σ x

def InfinitelySelected (schedule : Schedule) (i : Nat) : Prop :=
  ∀ t, ∃ u, t ≤ u ∧ (schedule u).index = some i

theorem StageAction.index_of_hit (a : StageAction s) (hit : a.hitsAt i x) :
    a.index = some i := by
  cases a with
  | idle _ => exact False.elim hit
  | selected _ _ _ _ => exact congrArg some hit.1

theorem StageAction.hitsBelow_iff (a : StageAction s) (x : Cantor) :
    a.hitsBelow j x ↔ ∃ i, i < j ∧ a.index = some i ∧ a.hitsAt i x := by
  cases a with
  | idle _ => simp [StageAction.hitsBelow, StageAction.index]
  | selected i _ σ _ =>
    simp only [StageAction.hitsBelow, StageAction.index, StageAction.hitsAt, Option.some.injEq]
    constructor
    · rintro ⟨hi, hit⟩
      exact ⟨i, hi, rfl, rfl, hit⟩
    · rintro ⟨_, hi, rfl, hit⟩
      exact ⟨hi, hit.2⟩

theorem StageAction.hit_width (a : StageAction s) (h : Nat) (hit : a.hitsAt i x) :
    h + s - i ≤ a.nextWidth h := by
  cases a with
  | idle _ => exact False.elim hit
  | selected j k σ hl =>
    obtain ⟨rfl, _⟩ := hit
    simp only [StageAction.nextWidth]
    omega

/-- On a hit the first `h + s - i` output bits depend only on the old input. -/
theorem StageAction.read_hitsAt (a : StageAction s) (code : StageCode h s) (x y : Cantor)
    (hitX : a.hitsAt i x) (hitY : a.hitsAt i y)
    (sameOldInput : readBits x (h + s) = readBits y (h + s)) :
    takePrefix ((a.run code).read x).1 (h + s - i) (a.hit_width h hitX) =
      takePrefix ((a.run code).read y).1 (h + s - i) (a.hit_width h hitY) := by
  cases a with
  | idle _ => exact False.elim hitX
  | selected j k σ hl =>
    obtain ⟨rfl, memX⟩ := hitX
    obtain ⟨_, memY⟩ := hitY
    have testY := (hits_stream_iff σ hl y (show j ≤ h + (j + k) by omega)).mpr memY
    simp only [StageAction.run, StageAction.nextWidth]
    rw [code.read_selected σ hl x, code.read_selected σ hl y]
    simp only [forward, if_pos testY, StageCode.focus, sameOldInput]
    rw [takePrefix_push _ _ (show h + (j + k) - j ≤ h + k by omega),
      takePrefix_push _ _ (show h + (j + k) - j ≤ h + k by omega)]

theorem StageAction.hit_of_same_input (a : StageAction s) (h : Nat) (x y : Cantor)
    (hit : a.hitsAt i x) (eq : readBits x (h + s) = readBits y (h + s)) :
    a.hitsAt i y := by
  cases a with
  | idle _ => exact False.elim hit
  | @selected j k l σ hl =>
    obtain ⟨rfl, memX⟩ := hit
    refine ⟨rfl, ?_⟩
    have hLength : l ≤ h + (j + k) := by omega
    have prefixEq : readBits x l = readBits y l := by
      simpa only [takePrefix_readBits] using congrArg (fun w => takePrefix w l hLength) eq
    exact prefixEq.symm.trans memX

/-- The one-input-cylinder inclusion used in Lemma 4.1. -/
theorem image_of_hit_cylinder (schedule : Schedule) (t i : Nat) (x : Cantor)
    (hit : (schedule t).hitsAt i x) (y : Cantor)
    (same : cylinder (readBits x (outputWidth schedule t + (t + 1))) y) :
    cylinder (readBits (cantorOutput schedule x) (outputWidth schedule t + (t + 1) - i))
      (cantorOutput schedule y) := by
  have hitY := (schedule t).hit_of_same_input (outputWidth schedule t) x y hit same.symm
  have readEq := (schedule t).read_hitsAt (stagedCode schedule t) x y hit hitY same.symm
  have leNext : outputWidth schedule t + (t + 1) - i ≤ outputWidth schedule (t + 1) :=
    (schedule t).hit_width _ hit
  change readBits (cantorOutput schedule y) _ = readBits (cantorOutput schedule x) _
  rw [← takePrefix_readBits (cantorOutput schedule y) leNext,
    ← takePrefix_readBits (cantorOutput schedule x) leNext, cantorOutput_reads, cantorOutput_reads]
  exact readEq.symm

theorem finitely_selected_cutoff (schedule : Schedule) (i : Nat)
    (notInf : ¬InfinitelySelected schedule i) :
    ∃ t, ∀ u, t ≤ u → (schedule u).index ≠ some i := by
  classical
  simp only [InfinitelySelected, Classical.not_forall, not_exists, not_and] at notInf
  exact notInf

theorem small_selections_eventually_recur (schedule : Schedule) (j : Nat) :
    ∃ t, ∀ u, t ≤ u → ∀ i, i < j → (schedule u).index = some i →
      InfinitelySelected schedule i := by
  induction j with
  | zero => exact ⟨0, fun _ _ _ h => (Nat.not_lt_zero _ h).elim⟩
  | succ j ih =>
    obtain ⟨t, earlier⟩ := ih
    by_cases recurs : InfinitelySelected schedule j
    · refine ⟨t, fun u hu i hij chosen => ?_⟩
      by_cases h : i < j
      · exact earlier u hu i h chosen
      · obtain rfl : i = j := by omega
        exact recurs
    · obtain ⟨t', stops⟩ := finitely_selected_cutoff schedule j recurs
      refine ⟨max t t', fun u hu i hij chosen => ?_⟩
      by_cases h : i < j
      · exact earlier u (Nat.le_trans (Nat.le_max_left _ _) hu) i h chosen
      · obtain rfl : i = j := by omega
        exact (stops u (Nat.le_trans (Nat.le_max_right _ _) hu) chosen).elim

private theorem same_stored (schedule : Schedule) (x : Cantor) (eq : u = t)
    (hu : j ≤ u + 1) (ht : j ≤ t + 1) :
    takePrefix (stageRead schedule u x).2 j hu = takePrefix (stageRead schedule t x).2 j ht := by
  subst u
  rfl

/--
The uniform stabilization used in Lemma 4.2. The premise says that at a
recurrent index a selected cylinder misses all points of `A`.
-/
theorem stored_prefix_stabilizes (schedule : Schedule) (A : Cantor → Prop)
    (misses : ∀ t i x, A x → InfinitelySelected schedule i → ¬(schedule t).hitsAt i x)
    (j : Nat) :
    ∃ t, ∃ hj : j ≤ t + 1, ∀ u, ∀ htu : t ≤ u, ∀ x, A x →
      takePrefix (stageRead schedule u x).2 j (by omega) =
        takePrefix (stageRead schedule t x).2 j hj := by
  obtain ⟨cut, small⟩ := small_selections_eventually_recur schedule j
  let t := max cut j
  have ht : j ≤ t + 1 := by have := Nat.le_max_right cut j; omega
  refine ⟨t, ht, fun u htu x hx => ?_⟩
  induction u with
  | zero =>
    exact same_stored schedule x (show 0 = t by omega) _ _
  | succ u ih =>
    by_cases h : t ≤ u
    · have safe : ¬(schedule u).hitsBelow j x := by
        intro low
        obtain ⟨i, hi, chosen, hit⟩ := ((schedule u).hitsBelow_iff x).mp low
        have recurrent := small u (Nat.le_trans (Nat.le_max_left cut j) h) i hi chosen
        exact misses u i x hx recurrent hit
      exact ((schedule u).read_stored_prefix (stagedCode schedule u) x (by omega) safe).trans (ih h)
    · exact same_stored schedule x (show u + 1 = t by omega) _ _

end Guo

#print axioms Guo.image_of_hit_cylinder
#print axioms Guo.stored_prefix_stabilizes
