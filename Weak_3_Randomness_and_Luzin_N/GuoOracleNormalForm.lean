import Weak_3_Randomness_and_Luzin_N.GuoOracleReplay
import Weak_3_Randomness_and_Luzin_N.GuoCandidateNormalForm

open Encodable

namespace Guo

/-- A total binary oracle whose zero-valued queries have a primitive recursive
existential–universal presentation. -/
structure BinarySigmaTwoOracle (Z : Oracle) where
  bit : ℕ → Bool
  matrix : ℕ × ℕ × ℕ → Bool
  matrix_primrec : Primrec matrix
  graph : ∀ i, Z i = Part.some (if bit i then 0 else 1)
  answer : ∀ i, bit i = true ↔ ∃ a, ∀ b, matrix (i, a, b) = true

private def bitValue (b : Bool) : ℕ := bif b then 0 else 1

private theorem bitValue_primrec : Primrec bitValue :=
  Primrec.cond Primrec.id (Primrec.const 0) (Primrec.const 1)

private abbrev TableChallenge := List Bool × List ℕ × ℕ × List ℕ

private def answerCheck (R : ℕ × ℕ × ℕ → Bool) (q : ℕ × TableChallenge) : Bool :=
  let (j, table, positive, challenge, negative) := q
  bif table[j]?.getD false then R (j, positive[j]?.getD 0, challenge)
  else !R (j, challenge, negative[j]?.getD 0)

private theorem answerCheck_primrec (R : ℕ × ℕ × ℕ → Bool) (hR : Primrec R) :
    Primrec (answerCheck R) := by
  let Input := ℕ × TableChallenge
  have j : Primrec (Prod.fst : Input → ℕ) := Primrec.fst
  have rest : Primrec (Prod.snd : Input → TableChallenge) := Primrec.snd
  have key := Primrec.snd.comp rest
  have tail := Primrec.snd.comp key
  have bit := Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.fst.comp rest) j)
    (Primrec.const false)
  have yes := Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.fst.comp key) j)
    (Primrec.const 0)
  have no := Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.snd.comp tail) j)
    (Primrec.const 0)
  have n := Primrec.fst.comp tail
  exact Primrec.cond bit (hR.comp (j.pair (yes.pair n)))
    (Primrec.not.comp (hR.comp (j.pair (n.pair no))))

private def tableCheck (R : ℕ × ℕ × ℕ → Bool) (q : TableChallenge) : Bool :=
  (List.range q.1.length).all (fun j => answerCheck R (j, q))

private theorem tableCheck_primrec (R : ℕ × ℕ × ℕ → Bool) (hR : Primrec R) :
    Primrec (tableCheck R) := by
  have perIndex : PrimrecRel (fun j (q : TableChallenge) => answerCheck R (j, q) = true) :=
    Primrec.eq.comp (answerCheck_primrec R hR) (Primrec.const true)
  have bounded := perIndex.forall_mem_list.comp
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)) Primrec.id
  refine bounded.decide.of_eq ?_
  intro q
  apply Bool.eq_iff_iff.mpr
  simp [tableCheck, List.all_eq_true]

private theorem answerTable_iff {Z : Oracle} (oracle : BinarySigmaTwoOracle Z) (table : List Bool) :
    table = (List.range table.length).map oracle.bit ↔
      ∃ positive : List ℕ, ∀ n, ∃ negative : List ℕ,
        tableCheck oracle.matrix (table, positive, n, negative) = true := by
  classical
  have getTable {xs : List Bool} (h : xs = (List.range xs.length).map oracle.bit)
      {j : ℕ} (hj : j < xs.length) : xs[j]?.getD false = oracle.bit j := by
    have atJ := congrArg (fun ys : List Bool => ys[j]?) h
    simp [hj] at atJ
    simpa only [List.getElem?_eq_getElem hj, Option.getD_some] using atJ
  have yes (j : ℕ) : ∃ a : ℕ, oracle.bit j = true → ∀ n, oracle.matrix (j, a, n) = true := by
    by_cases h : oracle.bit j = true
    · obtain ⟨a, ha⟩ := (oracle.answer j).mp h
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun hb => (h hb).elim⟩
  choose positive atPositive using yes
  have no (n j : ℕ) :
      ∃ b : ℕ, oracle.bit j = false → oracle.matrix (j, n, b) = false := by
    by_cases h : oracle.bit j = false
    · have absent : ¬ ∀ b, oracle.matrix (j, n, b) = true := by
        intro all
        have := (oracle.answer j).mpr ⟨n, all⟩
        simp [h] at this
      obtain ⟨b, hb⟩ := not_forall.mp absent
      exact ⟨b, fun _ => Bool.eq_false_iff.mpr hb⟩
    · exact ⟨0, fun hb => (h hb).elim⟩
  choose negative atNegative using no
  constructor
  · intro correct
    refine ⟨(List.range table.length).map positive, fun n => ?_⟩
    refine ⟨(List.range table.length).map (negative n), ?_⟩
    rw [tableCheck, List.all_eq_true]
    intro j hj
    have lt : j < table.length := List.mem_range.mp hj
    have value := getTable correct lt
    have getCode (f : ℕ → ℕ) : ((List.range table.length).map f)[j]?.getD 0 = f j := by
      simp [lt]
    cases h : oracle.bit j
    · have reject := atNegative n j h
      simp only [answerCheck, value, h, Bool.cond_false, getCode, reject, Bool.not_false]
    · have confirmed := atPositive j h n
      simp only [answerCheck, value, h, Bool.cond_true, getCode, confirmed]
  · rintro ⟨pos, verified⟩
    have agrees (j : ℕ) (hj : j < table.length) : table[j]?.getD false = oracle.bit j := by
      cases b : table[j]?.getD false
      · have falseAnswer : oracle.bit j ≠ true := by
          intro success
          obtain ⟨n, hn⟩ := (oracle.answer j).mp success
          obtain ⟨neg, proof⟩ := verified n
          have localCheck := List.all_eq_true.mp proof j (List.mem_range.mpr hj)
          have contrad := hn (neg[j]?.getD 0)
          simp [answerCheck, b, contrad] at localCheck
        exact (Bool.eq_false_iff.mpr falseAnswer).symm
      · symm
        apply (oracle.answer j).mpr
        refine ⟨pos[j]?.getD 0, fun n => ?_⟩
        obtain ⟨neg, proof⟩ := verified n
        have localCheck := List.all_eq_true.mp proof j (List.mem_range.mpr hj)
        simpa [answerCheck, b] using localCheck
    apply List.ext_get (by simp)
    intro j hj hj'
    have e := agrees j hj
    simpa [List.getElem?_eq_getElem hj, List.get_eq_getElem] using e

private abbrev ReplayCertificate := (ℕ × ℕ) × List Bool × List ℕ
private abbrev ReplayMatrixInput := (OracleWord × ℕ × ℕ) × ReplayCertificate

private def replayMatrix (R : ℕ × ℕ × ℕ → Bool) (code : Nat.Partrec.Code) (layer : ℕ)
    (q : ReplayMatrixInput) : Bool :=
  let ((w, n, b), (fuel, tick), table, positive) := q
  let data := encode (table.map bitValue, encode (layer, tick))
  decide (code.evaln fuel data = some (encode (some w : Option OracleWord))) &&
    tableCheck R (table, positive, n, (decode b).getD [])

private theorem replayMatrix_primrec (R : ℕ × ℕ × ℕ → Bool) (hR : Primrec R)
    (code : Nat.Partrec.Code) (layer : ℕ) : Primrec (replayMatrix R code layer) := by
  have cert : Primrec (Prod.snd : ReplayMatrixInput → ReplayCertificate) := Primrec.snd
  have claim := Primrec.fst.comp cert
  have parameters : Primrec (Prod.fst : ReplayMatrixInput → (OracleWord × ℕ × ℕ)) := Primrec.fst
  have table := Primrec.fst.comp (Primrec.snd.comp cert)
  have naturalTable := Primrec.list_map table (bitValue_primrec.comp Primrec.snd).to₂
  have address := Primrec.encode.comp ((Primrec.const layer).pair (Primrec.snd.comp claim))
  have data := Primrec.encode.comp (naturalTable.pair address)
  have run := Nat.Partrec.Code.primrec_evaln.comp
    (((Primrec.fst.comp claim).pair (Primrec.const code)).pair data)
  have output := Primrec.option_some.comp
    (Primrec.encode.comp (Primrec.option_some.comp (Primrec.fst.comp parameters)))
  have equal := (Primrec.eq.comp run output).decide
  have codes := Primrec.snd.comp parameters
  have getNegative := Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp codes))
    (Primrec.const ([] : List ℕ))
  have fields := table.pair ((Primrec.snd.comp (Primrec.snd.comp cert)).pair
    ((Primrec.fst.comp codes).pair getNegative))
  exact Primrec.and.comp equal ((tableCheck_primrec R hR).comp fields)

private def layerWitness (R : ℕ × ℕ × ℕ → Bool) (code : Nat.Partrec.Code) (layer : ℕ) :
    CylinderWitness := fun (w, e, n, b) => (decode (α := ReplayCertificate) e).elim false
      (fun info => replayMatrix R code layer ((w, n, b), info))

private theorem layerWitness_primrec (R : ℕ × ℕ × ℕ → Bool) (hR : Primrec R)
    (code : Nat.Partrec.Code) (layer : ℕ) : Primrec (layerWitness R code layer) := by
  have arg : Primrec (fun q : (OracleWord × ℕ × ℕ × ℕ) × ReplayCertificate =>
      ((q.1.1, q.1.2.2), q.2)) :=
    ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
      Primrec.snd
  have raw : Primrec (fun q : OracleWord × ℕ × ℕ × ℕ => decode (α := ReplayCertificate) q.2.1) :=
    Primrec.decode.comp (Primrec.fst.comp Primrec.snd)
  exact (Primrec.option_casesOn raw (Primrec.const false)
    ((replayMatrix_primrec R hR code layer).comp arg).to₂).of_eq fun q => by
      rcases q with ⟨w, e, n, b⟩
      cases h : decode (α := ReplayCertificate) e <;> simp [layerWitness, h]

/-- An effective open layer relative to a binary Sigma-two oracle has the quantified
cylinder presentation used by the record schedule. -/
theorem oracleUniformOpen_quantifiedCylinder_of_binarySigmaTwo {Z : Oracle}
    (oracle : BinarySigmaTwoOracle Z) {U : ℕ → Set Cantor} (hu : OracleUniformOpen Z U)
    (layer : ℕ) : ∃ R : CylinderWitness, Primrec R ∧ U layer = quantifiedCylinderUnion R := by
  obtain ⟨stream, compiled, layers⟩ := hu
  obtain ⟨relative, relativeEval⟩ := OracleCode.exists_eval compiled
  obtain ⟨code, ordinaryEval⟩ := relative.exists_finiteReplayCode
  let pred := layerWitness oracle.matrix code layer
  refine ⟨pred, layerWitness_primrec _ oracle.matrix_primrec _ _, ?_⟩
  have oracleEq : Z = (fun i => Part.some (bitValue (oracle.bit i))) := by
    funext i
    rw [oracle.graph i]
    cases oracle.bit i <;> rfl
  have streamEval (tick : ℕ) :
      relative.eval Z (encode (layer, tick)) = Part.some (encode (stream (layer, tick))) := by
    rw [relativeEval]
    simp
  have finiteReplay (tick v : ℕ) :
      v ∈ relative.eval Z (encode (layer, tick)) ↔
        ∃ len, v ∈ code.eval (encode (((List.range len).map oracle.bit).map bitValue, encode (layer, tick))) := by
    rw [congrArg (fun Y => relative.eval Y (encode (layer, tick))) oracleEq,
      relative.eval_finiteTable_iff]
    simp only [ordinaryEval, List.map_map]
    rfl
  rw [← layers layer]
  ext x
  rw [mem_oracleLayer]
  change _ ↔ ∃ w : OracleWord, ∃ e : ℕ, x ∈ wordCylinder (decodeOracleWord w) ∧
    ∀ n, ∃ b, pred (w, e, n, b) = true
  constructor
  · rintro ⟨tick, w, occurs, inside⟩
    have value : encode (some w : Option OracleWord) ∈ relative.eval Z (encode (layer, tick)) := by
      rw [streamEval, occurs]
      exact Part.mem_some _
    obtain ⟨len, eval⟩ := (finiteReplay tick _).mp value
    obtain ⟨fuel, check⟩ := Nat.Partrec.Code.evaln_complete.mp eval
    let table := (List.range len).map oracle.bit
    have rightTable : table = (List.range table.length).map oracle.bit := by simp [table]
    obtain ⟨pos, verifies⟩ := (answerTable_iff oracle table).mp rightTable
    let e : ReplayCertificate := ((fuel, tick), table, pos)
    refine ⟨w, encode e, inside, fun n => ?_⟩
    obtain ⟨neg, verified⟩ := verifies n
    refine ⟨encode neg, ?_⟩
    change layerWitness _ _ _ (w, encode e, n, encode neg) = true
    have finished : code.evaln fuel (encode (table.map bitValue, encode (layer, tick))) =
      some (encode (some w : Option OracleWord)) := Option.mem_def.mp check
    simp only [layerWitness, replayMatrix, encodek, Option.elim_some, Option.getD_some,
      e, finished, decide_true, Bool.true_and, verified]
  · rintro ⟨w, e, inside, body⟩
    have atZero := body 0
    cases decoded : decode (α := ReplayCertificate) e with
    | none => simp [pred, layerWitness, decoded] at atZero
    | some info =>
      rcases info with ⟨⟨fuel, tick⟩, table, pos⟩
      have both : ∀ n, ∃ neg : List ℕ,
          code.evaln fuel (encode (table.map bitValue, encode (layer, tick))) =
              some (encode (some w : Option OracleWord)) ∧
          tableCheck oracle.matrix (table, pos, n, neg) = true := by
        intro n
        obtain ⟨b, pass⟩ := body n
        refine ⟨(decode b).getD [], ?_⟩
        simpa [pred, layerWitness, replayMatrix, decoded] using pass
      have valid := (answerTable_iff oracle table).mpr
        ⟨pos, fun n => by obtain ⟨neg, _, ok⟩ := both n; exact ⟨neg, ok⟩⟩
      obtain ⟨_, finished, _⟩ := both 0
      have value := Nat.Partrec.Code.evaln_sound finished
      rw [valid] at value
      have occurs := (finiteReplay tick _).mpr ⟨table.length, value⟩
      rw [streamEval] at occurs
      exact ⟨tick, w, (encode_injective (Part.mem_some_iff.mp occurs)).symm, inside⟩

end Guo

#print axioms Guo.oracleUniformOpen_quantifiedCylinder_of_binarySigmaTwo
