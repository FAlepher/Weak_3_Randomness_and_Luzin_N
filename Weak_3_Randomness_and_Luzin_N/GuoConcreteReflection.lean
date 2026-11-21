import Weak_3_Randomness_and_Luzin_N.GuoCombined
import Weak_3_Randomness_and_Luzin_N.GuoJumpArithmetic
import Weak_3_Randomness_and_Luzin_N.GuoOracleUniversal
import Weak_3_Randomness_and_Luzin_N.GuoOracleCompiler

open Set MeasureTheory
open scoped ENNReal

namespace Guo

private noncomputable def replayCompiler : EffectiveReplayCompiler where
  code := OracleCode.replayIndex
  primitive := OracleCode.replayIndex_primrec
  correct := OracleCode.replayIndex_correct

/-- The exact indexed cylinder normal form used in §3.1 for the concrete second jump. -/
theorem secondJump_openLayer_normalForm {U : ℕ → Set Cantor}
    (effective : OracleUniformOpen secondJump U) (n : ℕ) :
    ∃ R : CylinderWitness, Primrec R ∧ U n = quantifiedCylinderUnion R :=
  oracleUniformOpen_quantifiedCylinder_of_binarySigmaTwo
    (secondJump_binarySigmaTwo replayCompiler) effective n

/-- The localized witness and reflection on the fat Cantor set, with the effective
inputs needed by the rational approximation of its real extension. -/
theorem real_reflection_on_fatCantor (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ C : CandidateWords,
      Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2) ∧
      Primrec (fun i => (C.word i).toList) ∧
      let schedule := candidateSchedule pairedReservation C
      let g := realAffineExtension (cantorOutput schedule)
      (∀ x ∈ fatCantorSet, RealFailsWeak firstJump x → RealFailsWeak firstJump (g x)) ∧
      (∀ x ∈ fatCantorSet, RealFailsMartinLof secondJump x → RealFailsMartinLof secondJump (g x)) ∧
      Continuous g ∧ (∀ x, g x ∈ Icc 0 1) ∧
      ∃ B : Set ℝ, B ⊆ Icc 0 1 ∧ IsCompact B ∧ volume B = 0 ∧ 1 - ε ≤ volume (g '' B) := by
  obtain ⟨G, universal⟩ := exists_universalMartinLofTest_secondJump
  have forms (layer : ℕ) :
      ∃ R : CylinderWitness, Primrec R ∧ G layer = quantifiedCylinderUnion R :=
    secondJump_openLayer_normalForm universal.1.1 layer
  choose R rec form using forms
  obtain ⟨n, witness⟩ := quantifiedCylinder_witness_and_real_reflection_on_fatCantor
    G universal R rec form ε hε
  exact ⟨indexedCandidateWords (R n), indexedCandidateWords_witness_primrec _ (rec n),
    indexedCandidateWords_word_primrec _, witness⟩

end Guo

#print axioms Guo.secondJump_openLayer_normalForm
#print axioms Guo.real_reflection_on_fatCantor
