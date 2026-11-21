import Weak_3_Randomness_and_Luzin_N.GuoConcreteReflection
import Weak_3_Randomness_and_Luzin_N.GuoCoverIndex
import Weak_3_Randomness_and_Luzin_N.GuoEndpointComputable

open Set MeasureTheory Encodable
open scoped ENNReal

namespace Guo

theorem exists_oracleStreamCode_iff {Z : Oracle} {stream : OracleStream} :
    (∃ code : OracleCode, OracleStreamCode Z code stream) ↔ ComputableIn {Z} stream := by
  constructor
  · rintro ⟨code, evaluates⟩
    unfold ComputableIn RecursiveIn
    refine (code.eval_recursiveIn Z).of_eq ?_
    intro n
    have atInput := evaluates n.unpair.1 n.unpair.2
    have inputCode : encode (Nat.unpair n) = n := Nat.pair_unpair n
    rw [inputCode] at atInput
    simpa [decode_prod_val] using atInput
  · intro computed
    obtain ⟨code, executes⟩ := OracleCode.exists_eval computed
    refine ⟨code, fun n t => ?_⟩
    rw [executes]
    simp

def CantorPrefixComputable (F : Cantor → Cantor) : Prop :=
  ∃ (required : ℕ → ℕ) (run : OracleWord × ℕ → OracleWord),
    Primrec required ∧ Primrec run ∧
    ∀ x n, run ((readBits x (required n)).toList, n) = (readBits (F x) n).toList

theorem candidate_cantorPrefixComputable (C : CandidateWords)
    (witness : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2))
    (words : Primrec (fun i => (C.word i).toList)) :
    CantorPrefixComputable (cantorOutput (candidateSchedule pairedReservation C)) := by
  let schedule := candidateSchedule pairedReservation C
  let m (n : ℕ) := outputWidth schedule n + (n + 1)
  let run (p : OracleWord × ℕ) :=
    (readBits (cantorOutput schedule (extendWord (decodeOracleWord p.1).2)) p.2).toList
  have depth : Primrec m := Primrec.nat_add.comp
    (candidateSchedule_outputWidth_primrec C witness) Primrec.succ
  refine ⟨m, run, depth, candidate_cantorOutput_listPrefix_primrec C witness words, fun x n => ?_⟩
  unfold run
  rw [extendWord_decodeOracleWord_toList]
  apply congrArg Vector.toList
  exact cantorOutput_finite_precision schedule n _ _ (readBits_extendWord _)

def IndexCoverOnCylinder (F : Cantor → Cantor) (i : ℕ) (w : OracleWord) (transform : ℕ → ℕ) : Prop :=
  Primrec transform ∧ ∀ (Z : Oracle) (stream : OracleStream) (code : OracleCode),
      OracleStreamCode Z code stream →
      ∃ (output : OracleStream) (index : OracleCode), encode index = transform (encode code) ∧
        OracleStreamCode Z index output ∧ ∀ n,
          F '' (oracleLayer stream n ∩ wordCylinder (decodeOracleWord w)) ⊆ oracleLayer output n ∧
          fairCoin (oracleLayer output n) ≤
            (2 : ℝ≥0∞)^i * fairCoin (oracleLayer stream n ∩ wordCylinder (decodeOracleWord w))

/-- Each point outside the class has a cylinder and a fixed primitive-recursive
index transformation that works relative to every oracle. -/
def IndexLocalCylinderCover (F : Cantor → Cantor) (A : Set Cantor) : Prop :=
  ∀ x ∉ A, ∃ (i : ℕ) (w : OracleWord) (transform : ℕ → ℕ),
    x ∈ wordCylinder (decodeOracleWord w) ∧ wordCylinder (decodeOracleWord w) ⊆ Aᶜ ∧
    IndexCoverOnCylinder F i w transform

/-- Lemma 4.1 on an arbitrary recurrent candidate, with a uniform program-index transformation. -/
theorem candidate_recurrent_index_cover (C : CandidateWords) (i : ℕ)
    (recurs : InfinitelySelected (candidateSchedule pairedReservation C) i)
    (witness : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2))
    (words : Primrec (fun i => (C.word i).toList)) :
    ∃ transform, IndexCoverOnCylinder (cantorOutput (candidateSchedule pairedReservation C)) i
      (encodeOracleWord ⟨C.width i, C.word i⟩) transform := by
  let schedule := candidateSchedule pairedReservation C
  let w := encodeOracleWord ⟨C.width i, C.word i⟩
  have decoded : decodeOracleWord w = ⟨C.width i, C.word i⟩ := decode_encodeOracleWord _
  have uses : UsesCylinder schedule i (decodeOracleWord w).2 := by
    rw [decoded]
    exact fun t chosen y => candidateSchedule_hitsAt pairedReservation C t i chosen y
  obtain ⟨transform, computed, preserves⟩ := oracleCoverStream_uniform_index schedule i w
    (candidate_oracleCoverKernel_primrec C i w witness words)
  refine ⟨transform, computed, fun Z stream code program => ?_⟩
  obtain ⟨new, number, computes⟩ := preserves Z stream code program
  refine ⟨oracleCoverStream schedule i w stream, new, number, computes, fun n => ?_⟩
  rw [oracleLayer_oracleCoverStream]
  exact (enumerated_local_cover_stream schedule i _ recurs uses
    (fun t => (stream (n, t)).map decodeOracleWord)).2

theorem IndexLocalCylinderCover.toEffectiveLocalCover {F : Cantor → Cantor} {A : Set Cantor}
    (covers : IndexLocalCylinderCover F A) : EffectiveLocalCover oracleOpenTestFramework F A := by
  intro x hx
  obtain ⟨i, w, _, hxw, _, _, lift⟩ := covers x hx
  refine ⟨wordCylinder (decodeOracleWord w), i, hxw, fun Z U uniform => ?_⟩
  obtain ⟨stream, effective, layers⟩ := uniform
  obtain ⟨code, evaluates⟩ := exists_oracleStreamCode_iff.mpr effective
  obtain ⟨output, index, _, outputEval, bounds⟩ := lift Z stream code evaluates
  have computed := exists_oracleStreamCode_iff.mp ⟨index, outputEval⟩
  exact ⟨oracleLayer output, ⟨output, computed, fun _ => rfl⟩,
    fun n => by simpa only [layers] using bounds n⟩

theorem candidate_indexLocalCylinderCover (C : CandidateWords) (A : Set Cantor)
    (form : Aᶜ = {x : Cantor | ∃ i, cylinder (C.word i) x ∧ ∀ n, ∃ b, C.witness i n b = true})
    (witness : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2))
    (words : Primrec (fun i => (C.word i).toList)) :
    IndexLocalCylinderCover (cantorOutput (candidateSchedule pairedReservation C)) A := by
  have region := form.trans (candidate_coverage pairedReservation C)
  intro x outside
  have belongs : x ∈ Aᶜ := outside
  rw [region] at belongs
  obtain ⟨i, here⟩ := mem_iUnion.mp belongs
  let w := encodeOracleWord ⟨C.width i.val, C.word i.val⟩
  have decoded : decodeOracleWord w = ⟨C.width i.val, C.word i.val⟩ := decode_encodeOracleWord _
  obtain ⟨transform, covers⟩ := candidate_recurrent_index_cover C i.val i.property witness words
  refine ⟨i.val, w, transform, ?_, ?_, covers⟩
  · rw [decoded]
    exact here
  · intro y hy
    rw [region]
    rw [decoded] at hy
    exact mem_iUnion.mpr ⟨i, hy⟩

/-- The complement has a uniform second-jump cylinder enumeration. -/
def SecondJumpEffectivelyClosed (A : Set Cantor) : Prop :=
  OracleUniformOpen secondJump (fun _ => Aᶜ)

/-- Theorem 2.1 with the explicit transformation on relative program indices. -/
theorem cantor_localization (A : Set Cantor) (effective : SecondJumpEffectivelyClosed A) :
    ∃ F : Cantor → Cantor, CantorPrefixComputable F ∧ Continuous F ∧
      MeasurePreserving F fairCoin fairCoin ∧ IndexLocalCylinderCover F A ∧
      ∃ D : Set Cantor, D ⊆ A ∧ IsCompact D ∧ fairCoin D = 0 ∧ fairCoin A ≤ fairCoin (F '' D) := by
  obtain ⟨R, primitive, normal⟩ := secondJump_openLayer_normalForm effective 0
  let C := indexedCandidateWords R
  have form := normal.trans (indexedCandidateWords_normalForm R).symm
  have hw := indexedCandidateWords_witness_primrec R primitive
  have enc := indexedCandidateWords_word_primrec R
  have compact : IsCompact A := by
    have open_complement : IsOpen Aᶜ := oracleOpenTestFramework.openLayers effective 0
    simpa only [compl_compl] using open_complement.isClosed_compl.isCompact
  obtain ⟨cont, preserves, _, witness⟩ := cantor_localization_from_normal_form C A compact form
  exact ⟨cantorOutput (candidateSchedule pairedReservation C), candidate_cantorPrefixComputable C hw enc,
    cont, preserves, candidate_indexLocalCylinderCover C A form hw enc, witness⟩

private theorem oracleUniformOpen_constantLayer {Z : Oracle} {U : ℕ → Set Cantor}
    (h : OracleUniformOpen Z U) (n : ℕ) : OracleUniformOpen Z (fun _ => U n) := by
  obtain ⟨stream, computed, same⟩ := h
  exact ⟨_, oracleUniformOpen_reindex computed (ComputableIn.const n), fun _ => same n⟩

/-- Lemma 2.2 for the actual first and second jumps. -/
theorem cantor_reflection_large_class (ε : ℝ≥0∞) (positive : 0 < ε) (_small : ε < 1) :
    ∃ (A : Set Cantor) (F : Cantor → Cantor),
      SecondJumpEffectivelyClosed A ∧ IsClosed A ∧ 1 - ε ≤ fairCoin A ∧
      CantorPrefixComputable F ∧ Continuous F ∧ MeasurePreserving F fairCoin fairCoin ∧
      IndexLocalCylinderCover F A ∧
      (∀ x ∈ A, ¬ FailsWeak oracleOpenTestFramework firstJump x ∧
        ¬ FailsMartinLof oracleOpenTestFramework secondJump x) ∧
      (∀ x, FailsWeak oracleOpenTestFramework firstJump x → FailsWeak oracleOpenTestFramework firstJump (F x)) ∧
      (∀ x, FailsMartinLof oracleOpenTestFramework secondJump x →
        FailsMartinLof oracleOpenTestFramework secondJump (F x)) ∧
      (∃ D : Set Cantor, D ⊆ A ∧ IsCompact D ∧ fairCoin D = 0 ∧ fairCoin A ≤ fairCoin (F '' D)) := by
  obtain ⟨G, universal⟩ := exists_universalMartinLofTest_secondJump
  have limit := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (show ((2 : ℝ≥0∞)⁻¹) < 1 by norm_num)
  obtain ⟨n, cost⟩ := ((tendsto_order.1 limit).2 ε positive).exists
  have openG : IsOpen (G n) := oracleOpenTestFramework.openLayers universal.1.1 n
  let A := (G n)ᶜ
  have closed : SecondJumpEffectivelyClosed A := by
    unfold SecondJumpEffectivelyClosed
    simpa only [A, compl_compl] using oracleUniformOpen_constantLayer universal.1.1 n
  have large : 1 - ε ≤ fairCoin A := by
    rw [show A = (G n)ᶜ from rfl, measure_compl openG.measurableSet (measure_ne_top _ _),
      measure_univ]
    exact tsub_le_tsub_left ((universal.1.2 n).trans cost.le) _
  obtain ⟨F, computed, continuous, preserving, byIndex, witness⟩ := cantor_localization A closed
  have cover := byIndex.toEffectiveLocalCover
  have avoid (x : Cantor) (failure : FailsMartinLof oracleOpenTestFramework secondJump x) : x ∉ A :=
    not_not_intro (universal.2 x failure n)
  refine ⟨A, F, closed, openG.isClosed_compl, large, computed, continuous, preserving, byIndex,
    ?_, ?_, ?_, witness⟩
  · intro x hx
    exact ⟨fun fail => avoid x (weakFailure_implies_secondJumpFailure x fail) hx, fun fail => avoid x fail hx⟩
  · intro x fail
    exact local_cover_transfers_weak_failure _ _ _ _ cover
      (avoid x (weakFailure_implies_secondJumpFailure x fail)) fail
  · intro x fail
    exact local_cover_transfers_martinLof_failure _ _ _ _ cover (avoid x fail) fail

end Guo

#print axioms Guo.cantor_localization
#print axioms Guo.cantor_reflection_large_class
#print axioms Guo.candidate_recurrent_index_cover
