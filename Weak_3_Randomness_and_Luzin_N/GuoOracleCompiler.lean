import Weak_3_Randomness_and_Luzin_N.GuoOracleReplay

open Encodable

namespace Guo
namespace OracleCode

private abbrev PlainCode := Nat.Partrec.Code

private def predCode : PlainCode :=
  .comp (.prec .zero (.comp .left .right)) (.pair .zero Nat.Partrec.Code.id)

private theorem eval_predAux (n : ℕ) :
    (Nat.Partrec.Code.prec .zero (.comp .left .right)).eval (Nat.pair 0 n) =
      Part.some n.pred := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.Partrec.Code.eval_prec_succ, ih]
    simp [Nat.Partrec.Code.eval]

private theorem eval_predCode (n : ℕ) : predCode.eval n = Part.some n.pred := by
  simp [predCode, Nat.Partrec.Code.eval.eq_1, Nat.Partrec.Code.eval.eq_5, Nat.Partrec.Code.eval.eq_6, Seq.seq, pure,
    PFun.pure, eval_predAux]

private def zeroIndicator : PlainCode :=
  .comp (.prec (Nat.Partrec.Code.const 1) .zero) (.pair .zero Nat.Partrec.Code.id)

private theorem eval_zeroAux (n : ℕ) :
    (Nat.Partrec.Code.prec (Nat.Partrec.Code.const 1) .zero).eval (Nat.pair 0 n) =
      Part.some (if n = 0 then 1 else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.Partrec.Code.eval_prec_succ, ih]
    simp [Nat.Partrec.Code.eval.eq_1, pure, PFun.pure]

private theorem eval_zeroIndicator (n : ℕ) :
    zeroIndicator.eval n = Part.some (if n = 0 then 1 else 0) := by
  simp [zeroIndicator, Nat.Partrec.Code.eval.eq_1, Nat.Partrec.Code.eval.eq_5, Nat.Partrec.Code.eval.eq_6, Seq.seq, pure,
    PFun.pure, eval_zeroAux]

private def requirePositive : PlainCode :=
  .comp (.rfind' (.comp zeroIndicator .left)) (.pair Nat.Partrec.Code.id .zero)

private theorem rfind_false : Nat.rfind (fun _ => Part.some false) = Part.none :=
  Part.eq_none_iff'.mpr (by simp [Nat.rfind_dom])

private theorem rfind_true : Nat.rfind (fun _ => Part.some true) = Part.some 0 :=
  Part.eq_some_iff.mpr (Nat.mem_rfind.mpr ⟨Part.mem_some _, fun h => (Nat.not_lt_zero _ h).elim⟩)

private theorem eval_requirePositive (n : ℕ) :
    requirePositive.eval n = if n = 0 then Part.none else Part.some 0 := by
  have start :
      (Nat.Partrec.Code.pair Nat.Partrec.Code.id .zero).eval n = Part.some (Nat.pair n 0) := by
    simp [Nat.Partrec.Code.eval.eq_1, Nat.Partrec.Code.eval.eq_5, Seq.seq, pure, PFun.pure]
  change ((Nat.Partrec.Code.pair Nat.Partrec.Code.id .zero).eval n).bind
    (Nat.Partrec.Code.rfind' (.comp zeroIndicator .left)).eval = _
  rw [start, Part.bind_some]
  simp only [Nat.Partrec.Code.eval.eq_8, Nat.unpaired, Nat.unpair_pair, Nat.add_zero,
    Nat.Partrec.Code.eval.eq_6, Nat.Partrec.Code.eval.eq_3, PFun.coe_val,
    Part.bind_eq_bind, Part.bind_some, eval_zeroIndicator]
  rw [Part.map_id' (fun _ => rfl)]
  by_cases h : n = 0
  · simpa [h] using rfind_false
  · simpa [h] using rfind_true

private def codePartialPred : PlainCode := .comp .right (.pair requirePositive predCode)

private theorem eval_partialPred (n : ℕ) : codePartialPred.eval n = Part.ofOption (Nat.ppred n) := by
  cases n <;> simp [codePartialPred, Nat.Partrec.Code.eval.eq_4, Nat.Partrec.Code.eval.eq_5,
    Nat.Partrec.Code.eval.eq_6, seq_eq_bind_map, eval_requirePositive, eval_predCode]

private def tableTail : PlainCode := .comp .right codePartialPred
private def tableHead : PlainCode := .comp .left codePartialPred

private theorem eval_tableTail (table : List ℕ) :
    tableTail.eval (encode table) =
      match table with
      | [] => Part.none
      | _ :: tail => Part.some (encode tail) := by
  cases table <;>
    simp [tableTail, Nat.Partrec.Code.eval.eq_4, Nat.Partrec.Code.eval.eq_6,
      eval_partialPred, Part.ofOption]

private theorem eval_tableHead (table : List ℕ) :
    tableHead.eval (encode table) = Part.ofOption table[0]? := by
  cases table <;>
    simp [tableHead, Nat.Partrec.Code.eval.eq_3, Nat.Partrec.Code.eval.eq_6,
      eval_partialPred, Part.ofOption]

private def dropStep : PlainCode := .comp tableTail (.comp .right .right)
private def dropEncodedTable : PlainCode := .prec Nat.Partrec.Code.id dropStep

private theorem eval_dropStep (a n v : ℕ) :
    dropStep.eval (Nat.pair a (Nat.pair n v)) = tableTail.eval v := by
  simp [dropStep, Nat.Partrec.Code.eval.eq_4, Nat.Partrec.Code.eval.eq_6]

private theorem eval_dropTable (table : List ℕ) (n : ℕ) :
    dropEncodedTable.eval (Nat.pair (encode table) n) =
      if n ≤ table.length then Part.some (encode (table.drop n)) else Part.none := by
  induction n with
  | zero => simp [dropEncodedTable]
  | succ n ih =>
    have unwind :
        dropEncodedTable.eval (Nat.pair (encode table) (n + 1)) =
          (dropEncodedTable.eval (Nat.pair (encode table) n)).bind tableTail.eval := by
      unfold dropEncodedTable
      rw [Nat.Partrec.Code.eval_prec_succ]
      simp [eval_dropStep]
    rw [unwind, ih]
    by_cases enough : n < table.length
    · have left : n ≤ table.length := enough.le
      have right : n + 1 ≤ table.length := enough
      simp only [if_pos left, if_pos right, Part.bind_some]
      rw [eval_tableTail, ← (List.drop_drop (i := 1) (j := n))]
      cases h : table.drop n with
      | nil =>
        have hn := congrArg List.length h
        simp at hn
        omega
      | cons a rest => rfl
    · have noNext : ¬ n + 1 ≤ table.length := by omega
      rw [if_neg noNext]
      by_cases current : n ≤ table.length
      · have eq : (table.drop n) = [] :=
          List.drop_eq_nil_iff.mpr (by omega)
        rw [if_pos current, Part.bind_some, eq, eval_tableTail]
      · simp [current]

/-- Oracle lookup on a coded pair of a finite table and an index. -/
def explicitReplayCall : PlainCode := .comp tableHead dropEncodedTable

theorem eval_explicitReplayCall (table : List ℕ) (n : ℕ) :
    explicitReplayCall.eval (encode (table, n)) = finiteOracleTable table n := by
  change (dropEncodedTable.eval (Nat.pair (encode table) n)).bind tableHead.eval = _
  rw [eval_dropTable]
  by_cases h : n ≤ table.length
  · simp only [if_pos h, Part.bind_some, eval_tableHead, finiteOracleTable]
    rw [List.getElem?_drop]
    simp
  · have noEntry : table[n]? = none := List.getElem?_eq_none (by omega)
    simp [h, finiteOracleTable, noEntry]

private def replayRecInput : PlainCode :=
  .pair (.pair .left (.comp .left .right)) (.comp .right .right)

private def replayNestedInput : PlainCode :=
  .pair (.comp .left .left) (.pair (.comp .right .left) .right)

private def replayCompose (f g : PlainCode) : PlainCode := .comp f (.pair .left g)

private def replayRecurse (f g : PlainCode) : PlainCode :=
  .comp (.prec f (.comp g replayNestedInput)) replayRecInput

private def replaySearch (p : PlainCode) : PlainCode :=
  .comp (.rfind' (.comp p replayNestedInput)) (.pair Nat.Partrec.Code.id .zero)

/-- Compile an oracle program into an ordinary program taking a coded pair
of a finite oracle table and the original input. -/
def replayCode : OracleCode → PlainCode
  | .zero => .zero
  | .succ => .comp .succ .right
  | .left => .comp .left .right
  | .right => .comp .right .right
  | .call => explicitReplayCall
  | .pair f g => .pair f.replayCode g.replayCode
  | .comp f g => replayCompose f.replayCode g.replayCode
  | .prec f g => replayRecurse f.replayCode g.replayCode
  | .search p => replaySearch p.replayCode

private theorem eval_recInput (t a n : ℕ) :
    replayRecInput.eval (Nat.pair t (Nat.pair a n)) =
      Part.some (Nat.pair (Nat.pair t a) n) := by
  simp [replayRecInput, Nat.Partrec.Code.eval, Seq.seq]

private theorem eval_nestedInput (t a extra : ℕ) :
    replayNestedInput.eval (Nat.pair (Nat.pair t a) extra) =
      Part.some (Nat.pair t (Nat.pair a extra)) := by
  simp [replayNestedInput, Nat.Partrec.Code.eval, Seq.seq]

private theorem eval_prec_at (f g : PlainCode) (t a n : ℕ) :
    (Nat.Partrec.Code.prec f (.comp g replayNestedInput)).eval (Nat.pair (Nat.pair t a) n) =
      n.rec (f.eval (Nat.pair t a)) (fun k old => old.bind fun v =>
        g.eval (Nat.pair t (Nat.pair a (Nat.pair k v)))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.Partrec.Code.eval_prec_succ, ih]
    simp [Nat.Partrec.Code.eval, Part.bind_eq_bind, eval_nestedInput]

private theorem eval_replayCompose (f g : PlainCode) (t a : ℕ) :
    (replayCompose f g).eval (Nat.pair t a) =
      (g.eval (Nat.pair t a)).bind fun v => f.eval (Nat.pair t v) := by
  simp [replayCompose, Nat.Partrec.Code.eval, seq_eq_bind_map, Part.bind_map]

private theorem eval_replayRecurse (f g : PlainCode) (t a n : ℕ) :
    (replayRecurse f g).eval (Nat.pair t (Nat.pair a n)) =
      n.rec (f.eval (Nat.pair t a)) (fun k old => old.bind fun v =>
        g.eval (Nat.pair t (Nat.pair a (Nat.pair k v)))) := by
  change (replayRecInput.eval _).bind (Nat.Partrec.Code.prec f (.comp g replayNestedInput)).eval = _
  rw [eval_recInput, Part.bind_some, eval_prec_at]

private theorem eval_replaySearch (p : PlainCode) (t a : ℕ) :
    (replaySearch p).eval (Nat.pair t a) =
      Nat.rfind (fun n => (fun m => m = 0) <$> p.eval (Nat.pair t (Nat.pair a n))) := by
  have start :
      (Nat.Partrec.Code.pair Nat.Partrec.Code.id .zero).eval (Nat.pair t a) =
        Part.some (Nat.pair (Nat.pair t a) 0) := by
    simp [Nat.Partrec.Code.eval, Nat.Partrec.Code.id, Seq.seq, pure, PFun.pure]
  change
    ((Nat.Partrec.Code.pair Nat.Partrec.Code.id .zero).eval _).bind
      (Nat.Partrec.Code.rfind' (.comp p replayNestedInput)).eval = _
  rw [start, Part.bind_some]
  simp [Nat.Partrec.Code.eval, Nat.unpaired, eval_nestedInput, Part.map_id']

theorem eval_replayCode (c : OracleCode) (table : List ℕ) (a : ℕ) :
    c.replayCode.eval (encode (table, a)) = c.eval (finiteOracleTable table) a := by
  induction c generalizing a with
  | zero => rfl
  | succ => simp [replayCode, OracleCode.eval, Nat.Partrec.Code.eval]
  | left => simp [replayCode, OracleCode.eval, Nat.Partrec.Code.eval]
  | right => simp [replayCode, OracleCode.eval, Nat.Partrec.Code.eval]
  | call => exact eval_explicitReplayCall table a
  | pair f g hf hg => simp only [replayCode, OracleCode.eval, Nat.Partrec.Code.eval, hf, hg]
  | comp f g hf hg =>
    change (replayCompose f.replayCode g.replayCode).eval (Nat.pair (encode table) a) = _
    rw [eval_replayCompose]
    change (g.replayCode.eval (encode (table, a))).bind
      (fun v => f.replayCode.eval (encode (table, v))) = _
    simp only [OracleCode.eval, Part.bind_eq_bind, hf, hg]
  | prec f g hf hg =>
    obtain ⟨⟨x, n⟩, rfl⟩ := Nat.pairEquiv.surjective a
    change (replayRecurse f.replayCode g.replayCode).eval (Nat.pair (encode table) (Nat.pair x n)) =
      (f.prec g).eval (finiteOracleTable table) (Nat.pair x n)
    rw [eval_replayRecurse]
    change n.rec (motive := fun _ => Part ℕ) (f.replayCode.eval (encode (table, x))) (fun k old => old.bind fun v =>
      g.replayCode.eval (encode (table, Nat.pair x (Nat.pair k v)))) = _
    simp only [OracleCode.eval, Nat.unpair_pair, hf, hg, Part.bind_eq_bind]
  | search p hp =>
    change (replaySearch p.replayCode).eval (Nat.pair (encode table) a) = _
    rw [eval_replaySearch]
    change Nat.rfind (fun n => (fun m => m = 0) <$> p.replayCode.eval
      (encode (table, Nat.pair a n))) = _
    simp only [OracleCode.eval, hp]

private theorem replayCompose_primrec : Primrec₂ replayCompose :=
  Nat.Partrec.Code.primrec₂_comp.comp Primrec.fst
    (Nat.Partrec.Code.primrec₂_pair.comp (Primrec.const Nat.Partrec.Code.left) Primrec.snd)

private theorem replayRecurse_primrec : Primrec₂ replayRecurse :=
  Nat.Partrec.Code.primrec₂_comp.comp
    (Nat.Partrec.Code.primrec₂_prec.comp Primrec.fst
      (Nat.Partrec.Code.primrec₂_comp.comp Primrec.snd (Primrec.const replayNestedInput)))
    (Primrec.const replayRecInput)

private theorem replaySearch_primrec : Primrec replaySearch :=
  Nat.Partrec.Code.primrec₂_comp.comp
    (Nat.Partrec.Code.primrec_rfind'.comp
      (Nat.Partrec.Code.primrec₂_comp.comp Primrec.id (Primrec.const replayNestedInput)))
    (Primrec.const (Nat.Partrec.Code.pair Nat.Partrec.Code.id .zero))

/-- Compilation on natural program indices uses the same decoder as the jump. -/
def replayIndex (i : ℕ) : Option PlainCode := (decodeIndex i).map replayCode

private def replayLeafAtTag (tag : ℕ) : PlainCode :=
  if tag = 0 then .zero
  else if tag = 1 then .comp .succ .right
  else if tag = 2 then .comp .left .right
  else if tag = 3 then .comp .right .right
  else explicitReplayCall

private theorem replayLeafAtTag_eq (tag : ℕ) :
    replayLeafAtTag tag = (leafAtTag tag).replayCode := by
  match tag with
  | 0 | 1 | 2 | 3 | _ + 4 => rfl

private theorem replayLeafAtTag_primrec : Primrec replayLeafAtTag := by
  have check (k : ℕ) : PrimrecPred (fun tag : ℕ => tag = k) :=
    Primrec.eq.comp Primrec.id (Primrec.const k)
  exact Primrec.ite (check 0) (Primrec.const Nat.Partrec.Code.zero)
    (Primrec.ite (check 1) (Primrec.const (Nat.Partrec.Code.comp .succ .right))
      (Primrec.ite (check 2) (Primrec.const (Nat.Partrec.Code.comp .left .right))
        (Primrec.ite (check 3) (Primrec.const (Nat.Partrec.Code.comp .right .right))
          (Primrec.const explicitReplayCall))))

private def replayBinaryAtTag (tag : ℕ) (f g : PlainCode) : PlainCode :=
  if tag = 5 then .pair f g else if tag = 6 then replayCompose f g else replayRecurse f g

private theorem replayBinaryAtTag_eq (tag : ℕ) (f g : OracleCode) :
    replayBinaryAtTag tag f.replayCode g.replayCode = (binaryAtTag tag f g).replayCode := by
  unfold replayBinaryAtTag binaryAtTag
  split <;> (try split) <;> rfl

private theorem replayBinaryAtTag_primrec :
    Primrec (fun p : ℕ × PlainCode × PlainCode => replayBinaryAtTag p.1 p.2.1 p.2.2) := by
  have first : Primrec (fun p : ℕ × PlainCode × PlainCode => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have second : Primrec (fun p : ℕ × PlainCode × PlainCode => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 5))
    (Nat.Partrec.Code.primrec₂_pair.comp first second)
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 6))
      (replayCompose_primrec.comp first second) (replayRecurse_primrec.comp first second))

private abbrev ReplayHistory := List (Option PlainCode)

private def historyAt (xs : ReplayHistory) (i : ℕ) : Option PlainCode := xs[i]?.getD none

private theorem historyAt_primrec : Primrec₂ historyAt :=
  (Primrec.option_getD.comp Primrec.list_getElem? (Primrec.const none)).to₂

private abbrev ReplayStepInput := ℕ × ReplayHistory
private abbrev ProgramShape := ℕ × ℕ × ℕ

private def replayParsedStep (p : ReplayStepInput) (shape : ProgramShape) :
    Option PlainCode :=
  let (i, known) := p
  let (tag, a, b) := shape
  if tag ≤ 4 then some (replayLeafAtTag tag)
  else if a < i then
    if tag = 8 then (historyAt known a).map replaySearch
    else if b < i then (historyAt known a).bind fun f =>
      (historyAt known b).map (replayBinaryAtTag tag f)
    else none
  else none

private theorem replayParsedStep_primrec : Primrec₂ replayParsedStep := by
  let Input := ReplayStepInput × ProgramShape
  have index : Primrec (fun p : Input => p.1.1) := Primrec.fst.comp Primrec.fst
  have known : Primrec (fun p : Input => p.1.2) := Primrec.snd.comp Primrec.fst
  have tag : Primrec (fun p : Input => p.2.1) := Primrec.fst.comp Primrec.snd
  have child1 : Primrec (fun p : Input => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have child2 : Primrec (fun p : Input => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have previous1 := historyAt_primrec.comp known child1
  have previous2 := historyAt_primrec.comp known child2
  have unary := Primrec.option_map previous1 (replaySearch_primrec.comp Primrec.snd).to₂
  have binaryAction : Primrec (fun p : (Input × PlainCode) × PlainCode =>
      replayBinaryAtTag p.1.1.2.1 p.1.2 p.2) :=
    replayBinaryAtTag_primrec.comp ((tag.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have binary := Primrec.option_bind previous1
    (Primrec.option_map (previous2.comp Primrec.fst) binaryAction.to₂).to₂
  exact (Primrec.ite (Primrec.nat_le.comp tag (Primrec.const 4))
    (Primrec.option_some.comp (replayLeafAtTag_primrec.comp tag))
    (Primrec.ite (Primrec.nat_lt.comp child1 index)
      (Primrec.ite (Primrec.eq.comp tag (Primrec.const 8)) unary
        (Primrec.ite (Primrec.nat_lt.comp child2 index) binary (Primrec.const none)))
      (Primrec.const none))).to₂

private def replayIndexStep (p : ReplayStepInput) : Option PlainCode :=
  (indexedShape p.1).bind (replayParsedStep p)

private theorem replayIndexStep_primrec : Primrec replayIndexStep :=
  Primrec.option_bind (indexedShape_primrec.comp Primrec.fst) replayParsedStep_primrec

private theorem historyAt_map_range {i n : ℕ} (h : i < n) :
    historyAt ((List.range n).map replayIndex) i = replayIndex i := by
  simp [historyAt, h]

private theorem replayIndexStep_eq (n : ℕ) :
    replayIndexStep (n, (List.range n).map replayIndex) = replayIndex n := by
  unfold replayIndexStep
  change _ = (decodeIndex n).map replayCode
  rw [decodeIndex]
  cases h : indexedShape n with
  | none => rfl
  | some p =>
    rcases p with ⟨tag, a, b⟩
    change replayParsedStep (n, (List.range n).map replayIndex) (tag, a, b) = _
    simp only [replayParsedStep]
    split_ifs with hleaf ha hu hb
    · simp [← replayLeafAtTag_eq]
    · rw [historyAt_map_range ha]
      unfold replayIndex
      cases decodeIndex a <;> rfl
    · rw [historyAt_map_range ha, historyAt_map_range hb]
      unfold replayIndex
      cases decodeIndex a <;> cases decodeIndex b <;> simp [replayBinaryAtTag_eq]
    · rfl
    · rfl

theorem replayIndex_primrec : Primrec replayIndex := by
  have step : Primrec₂ (fun (_ : ℕ) (hs : ReplayHistory) =>
      some (replayIndexStep (hs.length, hs))) :=
    (Primrec.option_some.comp (replayIndexStep_primrec.comp
      ((Primrec.list_length.comp Primrec.snd).pair Primrec.snd))).to₂
  have run : Primrec₂ (fun (_ : ℕ) n => replayIndex n) :=
    Primrec.nat_strong_rec _ step (fun _ n => by
      simp only [List.length_map, List.length_range, replayIndexStep_eq])
  exact run.comp (Primrec.const 0) Primrec.id

theorem replayIndex_correct (index : ℕ) (table : List ℕ) (arg : ℕ) :
    (replayIndex index).elim Part.none (fun p => p.eval (encode (table, arg))) =
      (decode (α := OracleCode) index).elim Part.none (fun p => p.eval (finiteOracleTable table) arg) := by
  change ((decodeIndex index).map replayCode).elim Part.none
    (fun p => p.eval (encode (table, arg))) =
      (decodeIndex index).elim Part.none (fun p => p.eval (finiteOracleTable table) arg)
  cases decodeIndex index
  · rfl
  · exact eval_replayCode _ _ _

end OracleCode
end Guo

#print axioms Guo.OracleCode.eval_replayCode
#print axioms Guo.OracleCode.replayIndex_primrec
#print axioms Guo.OracleCode.replayIndex_correct
