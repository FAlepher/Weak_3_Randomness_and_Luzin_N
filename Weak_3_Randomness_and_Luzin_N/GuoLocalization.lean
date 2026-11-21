import Weak_3_Randomness_and_Luzin_N.GuoCover
import Weak_3_Randomness_and_Luzin_N.GuoWitness
import Weak_3_Randomness_and_Luzin_N.GuoCandidateSchedule
import Mathlib.Data.Nat.Pairing

open Set MeasureTheory
open scoped ENNReal

namespace Guo

/-- A computable reservation using the natural-number pairing bijection. -/
def pairedReservation : Reservation where
  visit := Nat.pair
  slot t := some (Nat.unpair t)
  slot_visit i m := congrArg some (Nat.unpair_pair i m)
  visit_slot eq := Nat.pair_eq_of_unpair_eq (Option.some.inj eq)
  fits := by
    intro t i m eq
    have same := Nat.pair_eq_of_unpair_eq (Option.some.inj eq)
    have bound := Nat.left_le_pair i m
    rw [same] at bound
    exact bound.trans (Nat.le_succ _)
  strict := Nat.pair_lt_pair_right
  unbounded i t := ⟨t, Nat.right_le_pair i t⟩

/-- Equation (1), for a complement already presented by its total-witness candidates. -/
theorem candidate_coverage (V : Reservation) (C : CandidateWords) :
    {x : Cantor | ∃ i, cylinder (C.word i) x ∧ ∀ n, ∃ b, C.witness i n b = true} =
      ⋃ i : {i // InfinitelySelected (candidateSchedule V C) i}, cylinderSet (C.word i.val) := by
  ext x
  simp only [mem_setOf_eq, mem_iUnion]
  constructor
  · rintro ⟨i, hx, all⟩
    exact ⟨⟨i, (candidate_recurrence_iff V C i).mpr all⟩, hx⟩
  · rintro ⟨i, hx⟩
    exact ⟨i.val, hx, (candidate_recurrence_iff V C i.val).mp i.property⟩

/--
The noneffective conclusions of Cantor-space localization, given the two
mathematical laws relating the selected actions to the enumerated cylinders.
-/
theorem cantor_localization_of_schedule (schedule : Schedule) (A : Set Cantor)
    (hA : IsCompact A) (width : Nat → Nat) (word : (i : Nat) → Bits (width i))
    (uses : ∀ i, UsesCylinder schedule i (word i))
    (coverage : Aᶜ = ⋃ i : {i // InfinitelySelected schedule i}, cylinderSet (word i.val)) :
    Continuous (cantorOutput schedule) ∧
    MeasurePreserving (cantorOutput schedule) fairCoin fairCoin ∧
    (∀ x ∉ A, ∃ (I : Set Cantor) (i : Nat),
      x ∈ I ∧ I ⊆ Aᶜ ∧
      ∀ U, IsOpen U →
        ∃ V, IsOpen V ∧ cantorOutput schedule '' (U ∩ I) ⊆ V ∧
          fairCoin V ≤ (2 : ℝ≥0∞)^i * fairCoin (U ∩ I)) ∧
    (∃ D : Set Cantor, D ⊆ A ∧ IsCompact D ∧ fairCoin D = 0 ∧
      fairCoin A ≤ fairCoin (cantorOutput schedule '' D)) := by
  refine ⟨cantorOutput_continuous schedule, cantorOutput_measurePreserving schedule, ?_, ?_⟩
  · intro x hx
    have outside : x ∈ Aᶜ := hx
    rw [coverage] at outside
    obtain ⟨i, hxI⟩ := mem_iUnion.mp outside
    refine ⟨cylinderSet (word i.val), i.val, hxI, ?_, ?_⟩
    · intro y hy
      rw [coverage]
      exact mem_iUnion.mpr ⟨i, hy⟩
    · exact cover_open_at_recurrent_index schedule i.val (word i.val) i.property (uses i.val)
  · apply compact_null_witness schedule A hA
    intro t i x hx recurs hit
    have belongs := (uses i t ((schedule t).index_of_hit hit) x).mp hit
    have outside : x ∈ Aᶜ := by
      rw [coverage]
      exact mem_iUnion.mpr ⟨⟨i, recurs⟩, belongs⟩
    exact outside hx

/-- Instantiate the Cantor-space localization with executable record scheduling. -/
theorem cantor_localization_from_normal_form (C : CandidateWords) (A : Set Cantor) (hA : IsCompact A)
    (form : Aᶜ = {x : Cantor | ∃ i, cylinder (C.word i) x ∧ ∀ n, ∃ b, C.witness i n b = true}) :
    let schedule := candidateSchedule pairedReservation C
    Continuous (cantorOutput schedule) ∧
    MeasurePreserving (cantorOutput schedule) fairCoin fairCoin ∧
    (∀ x ∉ A, ∃ (I : Set Cantor) (i : Nat),
      x ∈ I ∧ I ⊆ Aᶜ ∧
      ∀ U, IsOpen U →
        ∃ V, IsOpen V ∧ cantorOutput schedule '' (U ∩ I) ⊆ V ∧
          fairCoin V ≤ (2 : ℝ≥0∞)^i * fairCoin (U ∩ I)) ∧
    (∃ D : Set Cantor, D ⊆ A ∧ IsCompact D ∧ fairCoin D = 0 ∧
      fairCoin A ≤ fairCoin (cantorOutput schedule '' D)) := by
  exact cantor_localization_of_schedule (candidateSchedule pairedReservation C) A hA C.width C.word
    (fun i t chosen x => candidateSchedule_hitsAt pairedReservation C t i chosen x)
    (form.trans (candidate_coverage pairedReservation C))

theorem null_image_on_complement (schedule : Schedule) (A : Set Cantor)
    (width : Nat → Nat) (word : (i : Nat) → Bits (width i))
    (uses : ∀ i, UsesCylinder schedule i (word i))
    (coverage : Aᶜ = ⋃ i : {i // InfinitelySelected schedule i}, cylinderSet (word i.val))
    (E : Set Cantor) (inside : E ⊆ Aᶜ) (null : fairCoin E = 0) :
    fairCoin (cantorOutput schedule '' E) = 0 := by
  let I := {i // InfinitelySelected schedule i}
  let Epart (i : I) := E ∩ cylinderSet (word i.val)
  have unionE : E = ⋃ i, Epart i := by
    ext x
    rw [mem_iUnion]
    constructor
    · intro hx
      have out := inside hx
      rw [coverage] at out
      obtain ⟨i, hi⟩ := mem_iUnion.mp out
      exact ⟨i, hx, hi⟩
    · rintro ⟨i, h⟩
      exact h.1
  have zeroImage (i : I) : fairCoin (cantorOutput schedule '' Epart i) = 0 := by
    have partNull : fairCoin (Epart i) = 0 := by
      apply le_antisymm _ bot_le
      exact (measure_mono inter_subset_left).trans_eq null
    have bound := outer_measure_image_at_recurrent_index schedule i.val (word i.val)
      i.property (uses i.val) (Epart i) inter_subset_right
    rw [partNull, mul_zero] at bound
    exact le_antisymm bound bot_le
  rw [unionE, image_iUnion]
  exact measure_iUnion_null zeroImage

end Guo

#print axioms Guo.cantor_localization_of_schedule
#print axioms Guo.candidate_coverage
#print axioms Guo.cantor_localization_from_normal_form
#print axioms Guo.null_image_on_complement
