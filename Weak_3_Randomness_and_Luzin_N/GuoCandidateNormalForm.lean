import Weak_3_Randomness_and_Luzin_N.GuoCandidateComputable
import Weak_3_Randomness_and_Luzin_N.GuoOracleCover

open Encodable
open Set

namespace Guo

abbrev CylinderWitness := OracleWord × ℕ × ℕ × ℕ → Bool

/-- A union of cylinders whose indices carry a universally quantified witness condition. -/
def quantifiedCylinderUnion (R : CylinderWitness) : Set Cantor :=
  {x | ∃ w : OracleWord, ∃ e : ℕ, x ∈ wordCylinder (decodeOracleWord w) ∧
    ∀ n, ∃ b, R (w, e, n, b) = true}

/-- A distinct positive index for each word and certificate pair, at least the word length. -/
def candidateIndex (w : OracleWord) (e : ℕ) : ℕ :=
  Nat.pair (Nat.pair (encode w) e) w.length + 1

private def candidateAddress (i : ℕ) : ℕ × ℕ := (i - 1).unpair

private def candidateCertificate (i : ℕ) : ℕ := (candidateAddress i).1.unpair.2

theorem candidateIndex_primrec : Primrec₂ candidateIndex :=
  (Primrec.succ.comp (Primrec₂.natPair.comp
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) Primrec.snd)
    (Primrec.list_length.comp Primrec.fst))).to₂

theorem candidateIndex_injective : Function.Injective (fun p : OracleWord × ℕ => candidateIndex p.1 p.2) := by
  rintro ⟨w, e⟩ ⟨v, f⟩ eq
  have args := congrArg (fun n : ℕ => (candidateAddress n).1.unpair) eq
  simpa [candidateAddress, candidateIndex] using args

private theorem candidateAddress_primrec : Primrec candidateAddress :=
  Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))

private theorem candidateCertificate_primrec : Primrec candidateCertificate :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp candidateAddress_primrec))

private def candidateSeed (i : ℕ) : Option OracleWord :=
  (decode (α := OracleWord) (candidateAddress i).1.unpair.1).bind fun w =>
    if candidateIndex w (candidateCertificate i) = i then some w else none

private theorem candidateSeed_primrec : Primrec candidateSeed := by
  have code : Primrec (fun i : ℕ => (candidateAddress i).1.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp candidateAddress_primrec))
  have accept : Primrec (fun p : ℕ × OracleWord =>
      if candidateIndex p.2 (candidateCertificate p.1) = p.1 then some p.2 else none) :=
    Primrec.ite (Primrec.eq.comp (candidateIndex_primrec.comp Primrec.snd
      (candidateCertificate_primrec.comp Primrec.fst)) Primrec.fst)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  exact Primrec.option_bind (Primrec.decode.comp code) accept.to₂

private theorem candidateSeed_length {i : ℕ} {w : OracleWord} (h : candidateSeed i = some w) :
    w.length ≤ i := by
  unfold candidateSeed at h
  obtain ⟨v, _, hit⟩ := Option.bind_eq_some_iff.mp h
  split at hit
  next good =>
    cases hit
    rw [← good]
    exact (Nat.right_le_pair _ _).trans (Nat.le_succ _)
  · simp at hit

private def indexedCandidateWord (i : ℕ) : OracleWord := (candidateSeed i).getD []

private def indexedCandidateWitness (R : CylinderWitness) (i n b : ℕ) : Bool :=
  (candidateSeed i).elim false (fun w => R (w, candidateCertificate i, n, b))

/-- Enumerate cylinder and certificate pairs with enough room in the index for the cylinder width. -/
def indexedCandidateWords (R : CylinderWitness) : CandidateWords where
  width i := (indexedCandidateWord i).length
  word i := (decodeOracleWord (indexedCandidateWord i)).2
  fits i := by
    unfold indexedCandidateWord
    cases h : candidateSeed i with
    | none => exact Nat.zero_le _
    | some w => exact candidateSeed_length h
  witness := indexedCandidateWitness R

theorem indexedCandidateWords_word_primrec (R : CylinderWitness) :
    Primrec (fun i => ((indexedCandidateWords R).word i).toList) := by
  refine (Primrec.option_getD.comp candidateSeed_primrec (Primrec.const [])).of_eq ?_
  intro i
  change indexedCandidateWord i = (encodeOracleWord (decodeOracleWord (indexedCandidateWord i)))
  rw [encode_decodeOracleWord]

theorem indexedCandidateWords_witness_primrec (R : CylinderWitness) (recR : Primrec R) :
    Primrec (fun p : ℕ × ℕ × ℕ => (indexedCandidateWords R).witness p.1 p.2.1 p.2.2) := by
  have args : Primrec (fun p : (ℕ × ℕ × ℕ) × OracleWord =>
      (p.2, candidateCertificate p.1.1, p.1.2)) :=
    Primrec.snd.pair ((candidateCertificate_primrec.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.fst))
  have run := Primrec.option_casesOn (candidateSeed_primrec.comp Primrec.fst) (Primrec.const false)
    (recR.comp args).to₂
  refine run.of_eq ?_
  intro p
  change _ = indexedCandidateWitness R p.1 p.2.1 p.2.2
  cases h : candidateSeed p.1 <;> simp [indexedCandidateWitness, h]

/-- The candidate union is exactly the supplied quantified cylinder normal form. -/
theorem indexedCandidateWords_normalForm (R : CylinderWitness) :
    {x : Cantor | ∃ i, cylinder ((indexedCandidateWords R).word i) x ∧
        ∀ n, ∃ b, (indexedCandidateWords R).witness i n b = true} =
      quantifiedCylinderUnion R := by
  ext x
  constructor
  · rintro ⟨i, inside, hasWitness⟩
    cases h : candidateSeed i with
    | none =>
      obtain ⟨b, hb⟩ := hasWitness 0
      simp [indexedCandidateWords, indexedCandidateWitness, h] at hb
    | some w =>
      refine ⟨w, candidateCertificate i, ?_, ?_⟩
      · change x ∈ wordCylinder (decodeOracleWord (indexedCandidateWord i)) at inside
        have equal : indexedCandidateWord i = w := by simp [indexedCandidateWord, h]
        simpa only [equal] using inside
      · simpa [indexedCandidateWords, indexedCandidateWitness, h] using hasWitness
  · rintro ⟨w, e, inside, hasWitness⟩
    let i := candidateIndex w e
    have certificate : candidateCertificate i = e := by simp [i, candidateCertificate, candidateAddress, candidateIndex]
    have seed : candidateSeed i = some w := by
      rw [candidateSeed, certificate]
      simp [i, candidateAddress, candidateIndex]
    refine ⟨i, ?_, ?_⟩
    · change x ∈ wordCylinder (decodeOracleWord (indexedCandidateWord i))
      rw [show indexedCandidateWord i = w by simp [indexedCandidateWord, seed]]
      exact inside
    · simpa [indexedCandidateWords, indexedCandidateWitness, certificate, seed] using hasWitness

end Guo

#print axioms Guo.indexedCandidateWords_word_primrec
#print axioms Guo.indexedCandidateWords_witness_primrec
#print axioms Guo.indexedCandidateWords_normalForm
