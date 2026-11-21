import Weak_3_Randomness_and_Luzin_N.GuoAffineExtension
import Weak_3_Randomness_and_Luzin_N.GuoCoverWordsComputable
import Weak_3_Randomness_and_Luzin_N.GuoRealOracleTests
import Weak_3_Randomness_and_Luzin_N.GuoStageComputable

namespace Guo

private def endpointInputPrefix (p : OracleWord × Bool × ℕ) : OracleWord :=
  (List.range p.2.2).map (fun j => p.1[j]?.getD p.2.1)

private theorem endpointInputPrefix_primrec : Primrec endpointInputPrefix := by
  let Input := OracleWord × Bool × ℕ
  have lookup : Primrec₂ (fun (p : Input) (j : ℕ) => p.1[j]?.getD p.2.1) :=
    (Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).to₂
  exact Primrec.list_map (Primrec.list_range.comp (Primrec.snd.comp Primrec.snd)) lookup

private theorem endpointBit_eq_extendRetained (w : OracleWord) (right : Bool) (j : ℕ) :
    w[j]?.getD right = extendRetained (decodeOracleWord w).2 right j := by
  by_cases inside : j < w.length <;> simp [extendRetained, decodeOracleWord, inside]

private theorem endpointInputPrefix_eq_readBits (p : OracleWord × Bool × ℕ) :
    endpointInputPrefix p =
      (readBits (extendRetained (decodeOracleWord p.1).2 p.2.1) p.2.2).toList := by
  refine List.ext_getElem (by simp [endpointInputPrefix]) fun j hj hj' => ?_
  simp [endpointInputPrefix, endpointBit_eq_extendRetained]

/-- The numerator and denominator exponent of the endpoint approximation at precision `p.2.2`. -/
def rationalEndpointCode (schedule : Schedule) (p : OracleWord × Bool × ℕ) : ℕ × ℕ :=
  (binaryPrefixIndex (cantorOutput schedule (extendRetained (decodeOracleWord p.1).2 p.2.1))
    p.2.2, p.2.2)

def rationalEndpointCodeValue (code : ℕ × ℕ) : ℚ :=
  (code.1 : ℚ) / (2 : ℚ)^code.2

theorem rationalEndpointCode_value (schedule : Schedule) (p : OracleWord × Bool × ℕ) :
    rationalEndpointCodeValue (rationalEndpointCode schedule p) =
      rationalEndpointValue schedule (decodeOracleWord p.1).2 p.2.1 p.2.2 := rfl

theorem rationalEndpointCode_error (schedule : Schedule) (p : OracleWord × Bool × ℕ) :
    |realAffineExtension (cantorOutput schedule)
      ((if p.2.1 then (retainedEndpoints (decodeOracleWord p.1).2).2
        else (retainedEndpoints (decodeOracleWord p.1).2).1 : ℚ) : ℝ) -
      (rationalEndpointCodeValue (rationalEndpointCode schedule p) : ℝ)| ≤ ((2 : ℝ)^p.2.2)⁻¹ := by
  rw [rationalEndpointCode_value]
  exact rationalEndpointValue_error schedule (decodeOracleWord p.1).2 p.2.1 p.2.2

/-- Endpoint approximations require a finite input prefix and a finite output prefix. -/
theorem rationalEndpointCode_primrec (schedule : Schedule)
    (hWidth : Primrec (outputWidth schedule))
    (hPrefix : Primrec (fun p : OracleWord × ℕ =>
      (readBits (cantorOutput schedule (extendWord (decodeOracleWord p.1).2)) p.2).toList)) :
    Primrec (rationalEndpointCode schedule) := by
  let Input := OracleWord × Bool × ℕ
  let needed (p : Input) := outputWidth schedule p.2.2 + (p.2.2 + 1)
  let initial (p : Input) := endpointInputPrefix (p.1, p.2.1, needed p)
  have precision : Primrec (fun p : Input => p.2.2) := Primrec.snd.comp Primrec.snd
  have required : Primrec needed := Primrec.nat_add.comp (hWidth.comp precision)
    (Primrec.succ.comp precision)
  have inputPrefix : Primrec initial :=
    endpointInputPrefix_primrec.comp
      (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair required))
  have digits := hPrefix.comp (inputPrefix.pair precision)
  refine ((wordGridIndex_primrec.comp digits).pair precision).of_eq ?_
  intro p
  let x := extendRetained (decodeOracleWord p.1).2 p.2.1
  let y := extendWord (decodeOracleWord (initial p)).2
  have sameInput : readBits y (needed p) = readBits x (needed p) := by
    change readBits (extendWord (decodeOracleWord (initial p)).2) (needed p) = _
    have eq : initial p = (readBits x (needed p)).toList :=
      endpointInputPrefix_eq_readBits (p.1, p.2.1, needed p)
    rw [eq, extendWord_decodeOracleWord_toList, readBits_extendWord]
  change (wordGridIndex (readBits (cantorOutput schedule y) p.2.2).toList,
    p.2.2) = (binaryPrefixIndex (cantorOutput schedule x) p.2.2, p.2.2)
  rw [cantorOutput_finite_precision schedule p.2.2 y x sameInput, wordGridIndex_readBits]

/-- Uniform primitive recursiveness for the paper's candidate schedule and all its endpoints. -/
theorem candidate_rationalEndpointCode_primrec (C : CandidateWords)
    (hWitness : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2))
    (hWord : Primrec (fun i => (C.word i).toList)) :
    Primrec (rationalEndpointCode (candidateSchedule pairedReservation C)) :=
  rationalEndpointCode_primrec _ (candidateSchedule_outputWidth_primrec C hWitness)
    (candidate_cantorOutput_listPrefix_primrec C hWitness hWord)

end Guo

#print axioms Guo.rationalEndpointCode_error
#print axioms Guo.rationalEndpointCode_primrec
#print axioms Guo.candidate_rationalEndpointCode_primrec
