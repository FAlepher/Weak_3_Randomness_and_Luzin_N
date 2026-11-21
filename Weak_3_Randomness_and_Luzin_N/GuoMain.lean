import Weak_3_Randomness_and_Luzin_N.GuoConcreteReflection
import Weak_3_Randomness_and_Luzin_N.GuoOutsideCandidate
import Weak_3_Randomness_and_Luzin_N.GuoRealRationalBasis
import Weak_3_Randomness_and_Luzin_N.GuoTypeTwo

open Set MeasureTheory
open scoped ENNReal

namespace Guo

def WeakThreeRandomReal (x : ℝ) : Prop := ¬ RationalFailsWeak firstJump x

def SecondJumpMartinLofRandomReal (x : ℝ) : Prop := ¬ RationalFailsMartinLof secondJump x

/-- Theorem 1.1. A single Type-2 computable continuous map reflects both real
randomness notions and maps a compact null set to a set of measure at least `1 - ε`. -/
theorem weakThreeRandomness_and_realNullImage (ε : ℝ≥0∞) (positive : 0 < ε) (_small : ε < 1) :
    ∃ (g : ℝ → ℝ) (B : Set ℝ),
      TypeTwoComputable g ∧ Continuous g ∧ (∀ x, g x ∈ Icc 0 1) ∧
      B ⊆ Icc 0 1 ∧ IsCompact B ∧ volume B = 0 ∧ 1 - ε ≤ volume (g '' B) ∧
      (∀ x, WeakThreeRandomReal (g x) → WeakThreeRandomReal x) ∧
      (∀ x, SecondJumpMartinLofRandomReal (g x) → SecondJumpMartinLofRandomReal x) := by
  obtain ⟨C, witness, words, weak, ml, cont, values, B, inside, compact, null, image⟩ :=
    real_reflection_on_fatCantor ε positive
  let g := realAffineExtension (cantorOutput (candidateSchedule pairedReservation C))
  refine ⟨g, B, candidate_realAffineExtension_typeTwoComputable C witness words,
    cont, values, inside, compact, null, image, ?_, ?_⟩
  · intro x random fails
    apply random
    apply rationalFailsWeak_iff_real.mpr
    have test := rationalFailsWeak_iff_real.mp fails
    by_cases inSet : x ∈ fatCantorSet
    · exact weak x inSet test
    · exact (candidate_realAffineExtension_reflects_outside C witness words firstJump inSet).1 test
  · intro x random fails
    apply random
    apply rationalFailsMartinLof_iff_real.mpr
    have test := rationalFailsMartinLof_iff_real.mp fails
    by_cases inSet : x ∈ fatCantorSet
    · exact ml x inSet test
    · exact (candidate_realAffineExtension_reflects_outside C witness words secondJump inSet).2 test

/-- The Luzin N property for Lebesgue outer measure on the real line. -/
def LuzinN (g : ℝ → ℝ) : Prop :=
  ∀ B : Set ℝ, volume B = 0 → volume (g '' B) = 0

theorem exists_reflecting_not_luzinN :
    ∃ g : ℝ → ℝ, TypeTwoComputable g ∧ Continuous g ∧ ¬ LuzinN g ∧
      (∀ x, WeakThreeRandomReal (g x) → WeakThreeRandomReal x) ∧
      (∀ x, SecondJumpMartinLofRandomReal (g x) → SecondJumpMartinLofRandomReal x) := by
  have positive : 0 < (2 : ℝ≥0∞)⁻¹ := by norm_num
  have small : (2 : ℝ≥0∞)⁻¹ < 1 := by norm_num
  obtain ⟨g, B, computed, cont, _, _, _, null, lower, weak, ml⟩ :=
    weakThreeRandomness_and_realNullImage _ positive small
  refine ⟨g, computed, cont, ?_, weak, ml⟩
  intro transfers
  exact (ne_of_gt ((tsub_pos_of_lt small).trans_le lower)) (transfers B null)

end Guo

#print axioms Guo.weakThreeRandomness_and_realNullImage
#print axioms Guo.exists_reflecting_not_luzinN
