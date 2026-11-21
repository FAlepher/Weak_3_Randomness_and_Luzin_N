import Weak_3_Randomness_and_Luzin_N.GuoCandidateComputable
import Weak_3_Randomness_and_Luzin_N.GuoStageComputable
import Weak_3_Randomness_and_Luzin_N.GuoRefinementComputable

namespace Guo

abbrev CoverReplies := List (Option OracleWord)

private def clippedReplies (σ : OracleWord) (replies : CoverReplies) : ℕ → Option FiniteWord :=
  clipEnumeration (fun k => (replies[k]?.getD none).map decodeOracleWord) (decodeOracleWord σ)

private def encodedCoverPieces (schedule : Schedule) (i t : ℕ) (p : OracleWord) : List OracleWord :=
  if firstSuitableStage schedule i p.length t then
    (coverWordsAt schedule t i (decodeOracleWord p)).map encodeOracleWord
  else []

private theorem encodedCoverPieces_primrec (schedule : Schedule) (i : ℕ)
    (indices : Primrec (fun t => (schedule t).index))
    (covers : Primrec (fun p : ℕ × OracleWord =>
      (coverWordsAt schedule p.1 i (decodeOracleWord p.2)).map encodeOracleWord)) :
    Primrec (fun p : ℕ × OracleWord => encodedCoverPieces schedule i p.1 p.2) := by
  have ready : PrimrecPred (fun p : ℕ × OracleWord =>
      firstSuitableStage schedule i p.2.length p.1 = true) :=
    Primrec.eq.comp ((firstSuitableStage_primrec_of_index schedule i indices).comp
      (Primrec.list_length.comp Primrec.snd) Primrec.fst) (Primrec.const true)
  exact Primrec.ite ready covers (Primrec.const [])

private theorem encodedCoverPieces_encode (schedule : Schedule) (i t : ℕ) (p : FiniteWord) :
    encodedCoverPieces schedule i t (encodeOracleWord p) =
      (if firstSuitableStage schedule i p.1 t then coverWordsAt schedule t i p else []).map encodeOracleWord := by
  have length : (encodeOracleWord p).length = p.1 := by simp [encodeOracleWord]
  cases yes : firstSuitableStage schedule i p.1 t <;> simp [encodedCoverPieces, length, yes]

/-- Certification of the program used by the relative covering theorem.
The component hypotheses describe the actual finite lists in the covering algorithm. -/
theorem oracleCoverKernel_primrec_of_components (schedule : Schedule) (i : ℕ) (σ : OracleWord)
    (indices : Primrec (fun t => (schedule t).index))
    (covers : Primrec (fun p : ℕ × OracleWord =>
      (coverWordsAt schedule p.1 i (decodeOracleWord p.2)).map encodeOracleWord))
    (refineWords : ℕ × CoverReplies → List OracleWord)
    (hr : Primrec refineWords)
    (hEq : ∀ p, refineWords p = (refinedEnumeration (clippedReplies σ p.2) p.1).map encodeOracleWord) :
    Primrec (oracleCoverKernel schedule i σ) := by
  let source (p : ℕ × CoverReplies) := p.1.unpair.1.unpair.1
  let stage (p : ℕ × CoverReplies) := p.1.unpair.1.unpair.2
  let position (p : ℕ × CoverReplies) := p.1.unpair.2
  have split : Primrec (fun p : ℕ × CoverReplies => p.1.unpair) := Primrec.unpair.comp Primrec.fst
  have times : Primrec (fun p : ℕ × CoverReplies => p.1.unpair.1.unpair) :=
    Primrec.unpair.comp (Primrec.fst.comp split)
  have sourceRec : Primrec source := Primrec.fst.comp times
  have stageRec : Primrec stage := Primrec.snd.comp times
  have positionRec : Primrec position := Primrec.snd.comp split
  let atSource (p : ℕ × CoverReplies) := refineWords (source p, p.2)
  have atSourceRec : Primrec atSource := hr.comp (sourceRec.pair Primrec.snd)
  have pieces : Primrec₂ (fun p w => encodedCoverPieces schedule i (stage p) w) :=
    ((encodedCoverPieces_primrec schedule i indices covers).comp
      ((stageRec.comp Primrec.fst).pair Primrec.snd)).to₂
  have batch : Primrec (fun p => (atSource p).flatMap (encodedCoverPieces schedule i (stage p))) :=
    Primrec.list_flatMap atSourceRec pieces
  refine (Primrec.list_getElem?.comp batch positionRec).of_eq ?_
  intro p
  change ((refineWords (source p, p.2)).flatMap (encodedCoverPieces schedule i (stage p)))[position p]? =
    (coverEnumeration schedule i (clippedReplies σ p.2) p.1).map encodeOracleWord
  rw [hEq, List.flatMap_map]
  simp only [coverEnumeration, coverBatch, ← List.getElem?_map, List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro w _
  apply encodedCoverPieces_encode

/-- The paper's finite covering program is primitive recursive given the finite word
enumeration and witness relation in its candidate presentation. -/
theorem candidate_oracleCoverKernel_primrec (C : CandidateWords) (i : ℕ) (σ : OracleWord)
    (witness : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2))
    (words : Primrec (fun j => (C.word j).toList)) :
    Primrec (oracleCoverKernel (candidateSchedule pairedReservation C) i σ) := by
  let schedule := candidateSchedule pairedReservation C
  have swapped : Primrec (fun p : ℕ × OracleWord => (p.2, p.1)) := Primrec.snd.pair Primrec.fst
  have reading := (candidate_cantorOutput_listPrefix_primrec C witness words).comp swapped
  have covers := coverWordsAt_primrec schedule i (candidateSchedule_outputWidth_primrec C witness) reading
  exact oracleCoverKernel_primrec_of_components schedule i σ
    (candidateSchedule_index_primrec C witness) covers (refinedOracleWords σ)
    (refinedOracleWords_primrec σ) (refinedOracleWords_encode σ)

theorem effectiveLocalCover_from_primitive_candidates (C : CandidateWords) (A : Set Cantor)
    (form : Aᶜ = {x : Cantor | ∃ i, cylinder (C.word i) x ∧ ∀ n, ∃ b, C.witness i n b = true})
    (witness : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2))
    (words : Primrec (fun j => (C.word j).toList)) :
    EffectiveLocalCover oracleOpenTestFramework (cantorOutput (candidateSchedule pairedReservation C)) A :=
  effectiveLocalCover_from_candidate_kernels C A form
    (fun i _ => (candidate_oracleCoverKernel_primrec C i _ witness words).to_comp)

end Guo

#print axioms Guo.oracleCoverKernel_primrec_of_components
#print axioms Guo.candidate_oracleCoverKernel_primrec
#print axioms Guo.effectiveLocalCover_from_primitive_candidates
