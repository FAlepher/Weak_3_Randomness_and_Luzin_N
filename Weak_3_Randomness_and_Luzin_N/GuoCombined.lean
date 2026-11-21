import Weak_3_Randomness_and_Luzin_N.GuoOracleRates
import Weak_3_Randomness_and_Luzin_N.GuoAffineExtension
import Weak_3_Randomness_and_Luzin_N.GuoRealOraclePullback
import Weak_3_Randomness_and_Luzin_N.GuoCandidateNormalForm
import Weak_3_Randomness_and_Luzin_N.GuoKernelComputable

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace Guo

/--
For supplied normal forms of the universal-test layers and computed covering kernels, the same
selected map reflects both Cantor-space tests and its real extension has a large null image.
-/
theorem candidate_witness_and_cantor_reflection
    (G : ℕ → Set Cantor) (hG : UniversalMartinLofTest oracleOpenTestFramework secondJump G)
    (candidates : ℕ → CandidateWords)
    (normalForm : ∀ n,
      G n = {x : Cantor | ∃ i, cylinder ((candidates n).word i) x ∧
        ∀ k, ∃ b, (candidates n).witness i k b = true})
    (kernels : ∀ n i, InfinitelySelected (candidateSchedule pairedReservation (candidates n)) i →
      Computable (oracleCoverKernel (candidateSchedule pairedReservation (candidates n)) i
        (encodeOracleWord ⟨(candidates n).width i, (candidates n).word i⟩)))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ n : ℕ,
      let F := cantorOutput (candidateSchedule pairedReservation (candidates n))
      let g := realAffineExtension F
      (∀ x, FailsWeak oracleOpenTestFramework firstJump x →
        FailsWeak oracleOpenTestFramework firstJump (F x)) ∧
      (∀ x, FailsMartinLof oracleOpenTestFramework secondJump x →
        FailsMartinLof oracleOpenTestFramework secondJump (F x)) ∧
      Continuous g ∧ (∀ x, g x ∈ Icc 0 1) ∧
      ∃ B : Set ℝ, B ⊆ Icc 0 1 ∧ IsCompact B ∧ volume B = 0 ∧ 1 - ε ≤ volume (g '' B) := by
  have lim := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (show ((2 : ℝ≥0∞)⁻¹) < 1 by norm_num)
  obtain ⟨n, hn⟩ := ((tendsto_order.1 lim).2 ε hε).exists
  let A := (G n)ᶜ
  let C := candidates n
  let F := cantorOutput (candidateSchedule pairedReservation C)
  have openG : IsOpen (G n) := oracleOpenTestFramework.openLayers hG.1.1 n
  have compactA : IsCompact A := openG.isClosed_compl.isCompact
  have sizeA : 1 - ε ≤ fairCoin A := by
    change 1 - ε ≤ fairCoin (G n)ᶜ
    rw [measure_compl openG.measurableSet (measure_ne_top _ _), measure_univ]
    exact tsub_le_tsub_left ((hG.1.2 n).trans hn.le) _
  have form : Aᶜ = {x : Cantor | ∃ i, cylinder (C.word i) x ∧
      ∀ k, ∃ b, C.witness i k b = true} := by
    change (G n)ᶜᶜ = _
    rw [compl_compl]
    exact normalForm n
  have cover : EffectiveLocalCover oracleOpenTestFramework F A :=
    effectiveLocalCover_from_candidate_kernels C A form (kernels n)
  have weak (x : Cantor) (fail : FailsWeak oracleOpenTestFramework firstJump x) :
      FailsWeak oracleOpenTestFramework firstJump (F x) :=
    local_cover_transfers_weak_failure _ _ _ _ cover
      (not_not_intro (hG.2 x (weakFailure_implies_secondJumpFailure x fail) n)) fail
  have ml (x : Cantor) (fail : FailsMartinLof oracleOpenTestFramework secondJump x) :
      FailsMartinLof oracleOpenTestFramework secondJump (F x) :=
    local_cover_transfers_martinLof_failure _ _ _ _ cover
      (not_not_intro (hG.2 x fail n)) fail
  obtain ⟨continuous, into, B, hB, compact, null, lower⟩ := real_candidate_witness C A compactA form
  exact ⟨n, weak, ml, continuous, into, B, hB, compact, null, sizeA.trans lower⟩

/-- The same conditional construction reflects both real test notions at every point
of the fat Cantor set, including points whose output has two binary expansions. -/
theorem candidate_witness_and_real_reflection_on_fatCantor
    (G : ℕ → Set Cantor) (hG : UniversalMartinLofTest oracleOpenTestFramework secondJump G)
    (candidates : ℕ → CandidateWords)
    (normalForm : ∀ n,
      G n = {x : Cantor | ∃ i, cylinder ((candidates n).word i) x ∧
        ∀ k, ∃ b, (candidates n).witness i k b = true})
    (kernels : ∀ n i, InfinitelySelected (candidateSchedule pairedReservation (candidates n)) i →
      Computable (oracleCoverKernel (candidateSchedule pairedReservation (candidates n)) i
        (encodeOracleWord ⟨(candidates n).width i, (candidates n).word i⟩)))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ n : ℕ,
      let F := cantorOutput (candidateSchedule pairedReservation (candidates n))
      let g := realAffineExtension F
      (∀ x ∈ fatCantorSet, RealFailsWeak firstJump x → RealFailsWeak firstJump (g x)) ∧
      (∀ x ∈ fatCantorSet, RealFailsMartinLof secondJump x → RealFailsMartinLof secondJump (g x)) ∧
      Continuous g ∧ (∀ x, g x ∈ Icc 0 1) ∧
      ∃ B : Set ℝ, B ⊆ Icc 0 1 ∧ IsCompact B ∧ volume B = 0 ∧ 1 - ε ≤ volume (g '' B) := by
  obtain ⟨n, weak, ml, continuous, into, witness⟩ :=
    candidate_witness_and_cantor_reflection G hG candidates normalForm kernels ε hε
  refine ⟨n, ?_, ?_, continuous, into, witness⟩
  · rintro _ ⟨x, rfl⟩ fail
    rw [realAffineExtension_fatAddress]
    exact binaryEvaluation_transfers_weakFailure (weak x (fatAddress_pulls_back_weakFailure fail))
  · rintro _ ⟨x, rfl⟩ fail
    rw [realAffineExtension_fatAddress]
    exact binaryEvaluation_transfers_martinLofFailure (ml x (fatAddress_pulls_back_martinLofFailure fail))

/-- A normalized universal test provides the candidate schedules and their covering programs. -/
theorem quantifiedCylinder_witness_and_real_reflection_on_fatCantor
    (G : ℕ → Set Cantor) (universal : UniversalMartinLofTest oracleOpenTestFramework secondJump G)
    (R : ℕ → CylinderWitness) (effective : ∀ n, Primrec (R n))
    (normalForm : ∀ n, G n = quantifiedCylinderUnion (R n))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ n : ℕ,
      let F := cantorOutput (candidateSchedule pairedReservation (indexedCandidateWords (R n)))
      let g := realAffineExtension F
      (∀ x ∈ fatCantorSet, RealFailsWeak firstJump x → RealFailsWeak firstJump (g x)) ∧
      (∀ x ∈ fatCantorSet, RealFailsMartinLof secondJump x → RealFailsMartinLof secondJump (g x)) ∧
      Continuous g ∧ (∀ x, g x ∈ Icc 0 1) ∧
      ∃ B : Set ℝ, B ⊆ Icc 0 1 ∧ IsCompact B ∧ volume B = 0 ∧ 1 - ε ≤ volume (g '' B) :=
  candidate_witness_and_real_reflection_on_fatCantor G universal
    (fun n => indexedCandidateWords (R n))
    (fun n => (normalForm n).trans (indexedCandidateWords_normalForm (R n)).symm)
    (fun n i _ => (candidate_oracleCoverKernel_primrec (indexedCandidateWords (R n)) i _
      (indexedCandidateWords_witness_primrec _ (effective n))
      (indexedCandidateWords_word_primrec _)).to_comp) ε hε

end Guo

#print axioms Guo.candidate_witness_and_cantor_reflection
#print axioms Guo.candidate_witness_and_real_reflection_on_fatCantor
#print axioms Guo.quantifiedCylinder_witness_and_real_reflection_on_fatCantor
