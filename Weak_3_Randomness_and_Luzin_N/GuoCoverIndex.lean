import Weak_3_Randomness_and_Luzin_N.GuoKernelComputable
import Weak_3_Randomness_and_Luzin_N.GuoOraclePlug

open Encodable

namespace Guo

/-- A program presents a total cylinder stream with natural-number input and reply codes. -/
def OracleStreamCode (Z : Oracle) (code : OracleCode) (stream : OracleStream) : Prop :=
  ∀ n t, code.eval Z (encode (n, t)) = Part.some (encode (stream (n, t)))

private theorem exists_oracleIndependentCode {f : ℕ → ℕ} (hf : Primrec f) :
    ∃ c : OracleCode, ∀ Z : Oracle, ∀ n, c.eval Z n = Part.some (f n) := by
  let empty : Oracle := fun _ => Part.some 0
  have computed : Nat.RecursiveIn {empty} (fun n => Part.some (f n)) :=
    (Primrec.nat_iff.mp hf).recursiveIn
  obtain ⟨c, hc⟩ := OracleCode.exists_eval computed
  refine ⟨c.plug .zero, fun Z n => ?_⟩
  rw [OracleCode.eval_plug, show OracleCode.eval Z .zero = empty from rfl, hc]

private def queryInput (p : ℕ) : ℕ := Nat.pair p.unpair.1.unpair.1 p.unpair.2.unpair.1

private theorem queryInput_primrec : Primrec queryInput := by
  have fstPair := Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)
  have sndPair := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  exact Primrec₂.natPair.comp (Primrec.fst.comp fstPair) (Primrec.fst.comp sndPair)

private def appendReply (p : ℕ) : ℕ :=
  encode (((decode (α := CoverReplies) p.unpair.1).getD []) ++
    [(decode (α := Option OracleWord) p.unpair.2).getD none])

private theorem appendReply_primrec : Primrec appendReply := by
  have seen : Primrec (fun p : ℕ => (decode (α := CoverReplies) p.unpair.1).getD []) :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const [])
  have new : Primrec (fun p : ℕ => (decode (α := Option OracleWord) p.unpair.2).getD none) :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair)) (Primrec.const none)
  exact Primrec.encode.comp (Primrec.list_concat.comp seen new)

private def runKernel (schedule : Schedule) (i : ℕ) (σ : OracleWord) (p : ℕ) : ℕ :=
  encode (oracleCoverKernel schedule i σ (p.unpair.1, (decode p.unpair.2).getD []))

private theorem runKernel_primrec (schedule : Schedule) (i : ℕ) (σ : OracleWord)
    (hk : Primrec (oracleCoverKernel schedule i σ)) : Primrec (runKernel schedule i σ) := by
  have replies : Primrec (fun p : ℕ => (decode (α := CoverReplies) p.unpair.2).getD []) :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair)) (Primrec.const [])
  exact Primrec.encode.comp (hk.comp ((Primrec.fst.comp Primrec.unpair).pair replies))

private theorem exists_coverTemplate (schedule : Schedule) (i : ℕ) (σ : OracleWord)
    (hk : Primrec (oracleCoverKernel schedule i σ)) :
    ∃ template : OracleCode, ∀ (Z : Oracle) (stream : OracleStream),
      (∀ n t, Z (encode (n, t)) = Part.some (encode (stream (n, t)))) →
        OracleStreamCode Z template (oracleCoverStream schedule i σ stream) := by
  obtain ⟨query, queryEval⟩ := exists_oracleIndependentCode queryInput_primrec
  obtain ⟨append, appendEval⟩ := exists_oracleIndependentCode appendReply_primrec
  obtain ⟨base, baseEval⟩ := exists_oracleIndependentCode (Primrec.const (encode ([] : CoverReplies)) :
    Primrec (fun _ : ℕ => encode ([] : CoverReplies)))
  obtain ⟨count, countEval⟩ := exists_oracleIndependentCode coverInputCount_primrec
  obtain ⟨kernel, kernelEval⟩ := exists_oracleIndependentCode (runKernel_primrec schedule i σ hk)
  let step := OracleCode.comp append (.pair (.comp .right .right) (.comp .call query))
  let gather := OracleCode.prec base step
  let collect := OracleCode.comp gather (.pair (.pair .left .right) (.comp count .right))
  let template := OracleCode.comp kernel (.pair .right collect)
  refine ⟨template, fun Z stream queries => ?_⟩
  have stepEval (n t k : ℕ) (past : CoverReplies) :
      step.eval Z (Nat.pair (encode (n, t)) (Nat.pair k (encode past))) =
        Part.some (encode (past ++ [stream (n, k)])) := by
    have reply : Z (Nat.pair n k) = Part.some (encode (stream (n, k))) := queries n k
    simp [step, OracleCode.eval, seq_eq_bind_map, Part.bind_eq_bind, Part.map_eq_map,
      queryEval, queryInput, appendEval, appendReply, reply, encode_prod_val]
  have gatherEval (n t k : ℕ) :
      gather.eval Z (Nat.pair (encode (n, t)) k) =
        Part.some (encode (readOraclePrefix stream n k)) := by
    let run : ℕ → Part ℕ := fun k =>
      k.rec (motive := fun _ => Part ℕ) (base.eval Z (encode (n, t)))
        (fun j prev => prev.bind fun value => step.eval Z (Nat.pair (encode (n, t)) (Nat.pair j value)))
    have runEq : ∀ j, run j = Part.some (encode (readOraclePrefix stream n j)) := by
      intro j
      induction j with
      | zero => exact baseEval _ _
      | succ j ih =>
        change (run j).bind (fun value => step.eval Z (Nat.pair (encode (n, t)) (Nat.pair j value))) = _
        rw [ih, Part.bind_some, stepEval]
        rfl
    simpa only [gather, OracleCode.eval, Nat.unpair_pair, Part.bind_eq_bind, run] using runEq k
  intro n t
  have countPair :
      (OracleCode.pair (.pair .left .right) (.comp count .right)).eval Z (encode (n, t)) =
        Part.some (Nat.pair (encode (n, t)) (coverInputCount t)) := by
    simp [OracleCode.eval, seq_eq_bind_map, Part.bind_eq_bind, Part.map_eq_map,
      countEval, encode_prod_val]
  have collectEval :
      collect.eval Z (encode (n, t)) = Part.some (encode (readOraclePrefix stream n (coverInputCount t))) := by
    change ((OracleCode.pair (.pair .left .right) (.comp count .right)).eval Z (encode (n, t))).bind
      (gather.eval Z) = _
    rw [countPair, Part.bind_some, gatherEval]
  have values :
      (OracleCode.pair .right collect).eval Z (encode (n, t)) =
        Part.some (Nat.pair t (encode (readOraclePrefix stream n (coverInputCount t)))) := by
    change (Nat.pair <$> (Part.some (encode (n, t)).unpair.2) <*> collect.eval Z (encode (n, t))) = _
    rw [collectEval]
    simp [seq_eq_bind_map, Part.bind_eq_bind, Part.map_eq_map, encode_prod_val]
  change ((OracleCode.pair .right collect).eval Z (encode (n, t))).bind (kernel.eval Z) = _
  rw [values, Part.bind_some, kernelEval]
  simp [runKernel, oracleCoverStream]

/-- This transformation on a given open-set program index is independent of its oracle.
It returns the index of the program for the actual covering stream. -/
theorem oracleCoverStream_uniform_index (schedule : Schedule) (i : ℕ) (σ : OracleWord)
    (hk : Primrec (oracleCoverKernel schedule i σ)) :
    ∃ transform : ℕ → ℕ, Primrec transform ∧
      ∀ (Z : Oracle) (stream : OracleStream) (code : OracleCode),
        OracleStreamCode Z code stream →
        ∃ output : OracleCode, encode output = transform (encode code) ∧
          OracleStreamCode Z output (oracleCoverStream schedule i σ stream) := by
  obtain ⟨template, runs⟩ := exists_coverTemplate schedule i σ hk
  refine ⟨template.plugIndex, template.plugIndex_primrec, fun Z stream code computes => ?_⟩
  refine ⟨template.plug code, ?_, ?_⟩
  · exact (template.plugIndex_encode code).symm
  · have run := runs (code.eval Z) stream computes
    intro n t
    rw [OracleCode.eval_plug]
    exact run n t

end Guo

#print axioms Guo.oracleCoverStream_uniform_index
