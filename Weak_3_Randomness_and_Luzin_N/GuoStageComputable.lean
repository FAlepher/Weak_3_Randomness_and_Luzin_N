import Weak_3_Randomness_and_Luzin_N.GuoOracleCover
import Weak_3_Randomness_and_Luzin_N.GuoCandidateComputable

namespace Guo

private abbrev ListStageState := OracleWord × OracleWord

private def paddedBit (word : OracleWord) (n : ℕ) : Bool :=
  word[n]?.getD false

private theorem paddedBit_primrec : Primrec₂ paddedBit :=
  (Primrec.option_getD.comp Primrec.list_getElem? (Primrec.const false)).to₂

private theorem paddedBit_eq_extendWord (word : OracleWord) (n : ℕ) :
    paddedBit word n = extendWord (decodeOracleWord word).2 n := by
  by_cases hn : n < word.length
  all_goals simp [paddedBit, extendWord, decodeOracleWord, hn]

private def paddedInputBlock (word : OracleWord) (offset count : ℕ) : OracleWord :=
  (List.range count).map fun j => paddedBit word (offset + j)

private theorem paddedInputBlock_primrec :
    Primrec (fun p : OracleWord × ℕ × ℕ => paddedInputBlock p.1 p.2.1 p.2.2) := by
  refine Primrec.list_map (Primrec.list_range.comp (Primrec.snd.comp Primrec.snd)) ?_
  exact (paddedBit_primrec.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)).to₂

private theorem paddedInputBlock_eq_readBits (word : OracleWord) (offset count : ℕ) :
    paddedInputBlock word offset count =
      (readBits (fun j => extendWord (decodeOracleWord word).2 (offset + j)) count).toList := by
  refine List.ext_getElem (by simp [paddedInputBlock]) fun j hj hj' => ?_
  simp [paddedInputBlock, paddedBit_eq_extendWord]

private def listReadLastBits (word : OracleWord) (offset : ℕ) (state : ListStageState) : ListStageState :=
  (state.1 ++ [paddedBit word offset], state.2 ++ [paddedBit word (offset + 1)])

private theorem listReadLastBits_primrec :
    Primrec (fun p : OracleWord × ℕ × ListStageState => listReadLastBits p.1 p.2.1 p.2.2) := by
  have offset : Primrec (fun p : OracleWord × ℕ × ListStageState => p.2.1) := Primrec.fst.comp Primrec.snd
  have out : Primrec (fun p : OracleWord × ℕ × ListStageState => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have buffer : Primrec (fun p : OracleWord × ℕ × ListStageState => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_concat.comp out (paddedBit_primrec.comp Primrec.fst offset)).pair
    (Primrec.list_concat.comp buffer (paddedBit_primrec.comp Primrec.fst (Primrec.succ.comp offset)))

private def listIdleStep (word : OracleWord) (state : ListStageState) : ListStageState :=
  listReadLastBits word (state.1.length + state.2.length) state

private theorem listIdleStep_primrec : Primrec₂ listIdleStep := by
  have n : Primrec (fun p : OracleWord × ListStageState => p.2.1.length + p.2.2.length) :=
    Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
  exact (listReadLastBits_primrec.comp (Primrec.fst.pair (n.pair Primrec.snd))).to₂

private def listSelectedStep (word : OracleWord) (state : ListStageState) (i : ℕ) (probe : OracleWord) :
    ListStageState :=
  let n := state.1.length + state.2.length
  let k := state.2.length - i
  let a := state.2.take i
  let b := state.2.drop i
  let c := paddedInputBlock word n k
  let next := if paddedInputBlock word 0 probe.length = probe then
    (state.1 ++ b, a ++ c) else (state.1 ++ c, a ++ b)
  listReadLastBits word (n + k) next

private theorem listSelectedStep_primrec :
    Primrec (fun p : OracleWord × ListStageState × ℕ × OracleWord =>
      listSelectedStep p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let Input := OracleWord × ListStageState × ℕ × OracleWord
  have u : Primrec (fun p : Input => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have v : Primrec (fun p : Input => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have i : Primrec (fun p : Input => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have probe : Primrec (fun p : Input => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have bufferSize := Primrec.list_length.comp v
  have n := Primrec.nat_add.comp (Primrec.list_length.comp u) bufferSize
  have k := Primrec.nat_sub.comp bufferSize i
  have a := Primrec.list_take.comp i v
  have b := Primrec.list_drop.comp i v
  have c := paddedInputBlock_primrec.comp (Primrec.fst.pair (n.pair k))
  have start := paddedInputBlock_primrec.comp
    (Primrec.fst.pair ((Primrec.const 0).pair (Primrec.list_length.comp probe)))
  have hit := Primrec.eq.comp start probe
  have next := Primrec.ite hit
    ((Primrec.list_append.comp u b).pair (Primrec.list_append.comp a c))
    ((Primrec.list_append.comp u c).pair (Primrec.list_append.comp a b))
  exact listReadLastBits_primrec.comp (Primrec.fst.pair ((Primrec.nat_add.comp n k).pair next))

private def listStageStep (probe : ℕ → OracleWord) (word : OracleWord)
    (selected : Option ℕ) (state : ListStageState) : ListStageState :=
  selected.elim (listIdleStep word state) (fun i => listSelectedStep word state i (probe i))

private theorem listStageStep_primrec (probe : ℕ → OracleWord) (hProbe : Primrec probe)
    (selected : ℕ → Option ℕ) (hSelected : Primrec selected) :
    Primrec (fun p : OracleWord × ℕ × ListStageState => listStageStep probe p.1 (selected p.2.1) p.2.2) := by
  let Input := OracleWord × ℕ × ListStageState
  have action : Primrec (fun p : Input => selected p.2.1) :=
    hSelected.comp (Primrec.fst.comp Primrec.snd)
  have idle : Primrec (fun p : Input => listIdleStep p.1 p.2.2) :=
    listIdleStep_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have select : Primrec₂ (fun (p : Input) i => listSelectedStep p.1 p.2.2 i (probe i)) :=
    (listSelectedStep_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair
        (Primrec.snd.pair (hProbe.comp Primrec.snd))))).to₂
  exact (Primrec.option_casesOn action idle select).of_eq (fun p => by cases selected p.2.1 <;> rfl)

private def listStageRead (selected : ℕ → Option ℕ) (probe : ℕ → OracleWord)
    (word : OracleWord) (t : ℕ) : ListStageState :=
  t.rec ([paddedBit word 0], [paddedBit word 1])
    (fun k state => listStageStep probe word (selected k) state)

private theorem listStageRead_primrec (probe : ℕ → OracleWord) (hProbe : Primrec probe)
    (selected : ℕ → Option ℕ) (hSelected : Primrec selected) :
    Primrec (fun p : OracleWord × ℕ => listStageRead selected probe p.1 p.2) := by
  have singleton (n : ℕ) : Primrec (fun w => [paddedBit w n]) :=
    Primrec.list_cons.comp (paddedBit_primrec.comp Primrec.id (Primrec.const n)) (Primrec.const [])
  exact Primrec.nat_rec ((singleton 0).pair (singleton 1))
    (listStageStep_primrec probe hProbe selected hSelected).to₂

private theorem head_toList_eq_take (v : Bits (i + k)) : (head v).toList = v.toList.take i := by
  rw [head, takePrefix, Vector.toList_cast, Vector.toList_take]

private theorem tail_toList_eq_drop (v : Bits (i + k)) : (tail v).toList = v.toList.drop i := by
  rw [tail, Vector.toList_cast, Vector.toList_extract]
  simp [List.length_drop]

private theorem listStageStep_correct (action : StageAction s) (code : StageCode h s)
    (word : OracleWord) (probe : ℕ → OracleWord)
    (classifies : ∀ i, action.index = some i → ∀ x,
      action.hitsAt i x ↔ (readBits x (probe i).length).toList = probe i) :
    let x := extendWord (decodeOracleWord word).2
    let old := code.read x
    let next := (action.run code).read x
    listStageStep probe word action.index (old.1.toList, old.2.toList) =
      (next.1.toList, next.2.toList) := by
  dsimp only
  let x := extendWord (decodeOracleWord word).2
  change listStageStep probe word action.index ((code.read x).1.toList, (code.read x).2.toList) = _
  have readBit (n : ℕ) : paddedBit word n = x n := paddedBit_eq_extendWord word n
  cases action with
  | idle s =>
    change listStageStep probe word none ((code.read x).1.toList, (code.read x).2.toList) =
      ((code.idle.read x).1.toList, (code.idle.read x).2.toList)
    rw [code.read_idle x]
    simp [listStageStep, listIdleStep, listReadLastBits, Vector.toList_push, readBit]
  | @selected i k l σ hl =>
    have agrees : ((readBits x (probe i).length).toList = probe i) ↔
        hits σ hl (readBits x i) = true := by
      have branch := hits_stream_iff σ hl x (show i ≤ h + (i + k) by omega)
      rw [takePrefix_readBits] at branch
      rw [branch, ← classifies i rfl]
      simp [StageAction.hitsAt]
    have zeroStart : paddedInputBlock word 0 (probe i).length = (readBits x (probe i).length).toList := by
      simp [paddedInputBlock_eq_readBits, x]
    have chunk : paddedInputBlock word (h + (i + k)) k =
        (readBits (fun r => x (h + (i + k) + r)) k).toList := paddedInputBlock_eq_readBits word _ _
    change listStageStep probe word (some i) ((code.read x).1.toList, (code.read x).2.toList) =
      (((code.selected σ hl).read x).1.toList, ((code.selected σ hl).read x).2.toList)
    rw [code.read_selected σ hl x]
    simp only [forward, StageCode.focus, takePrefix_readBits, listStageStep, Option.elim_some,
      listSelectedStep, Vector.length_toList, Nat.add_sub_cancel_left, zeroStart, agrees]
    by_cases hit : hits σ hl (readBits x i) = true <;>
      simp [hit, listReadLastBits, StageCode.read, head_toList_eq_take, tail_toList_eq_drop,
        readBit, chunk, Vector.toList_push, Vector.toList_append]

private theorem listStageRead_correct (schedule : Schedule) (probe : ℕ → OracleWord)
    (classifies : ∀ t i, (schedule t).index = some i → ∀ x,
      (schedule t).hitsAt i x ↔ (readBits x (probe i).length).toList = probe i)
    (word : OracleWord) (t : ℕ) :
    let x := extendWord (decodeOracleWord word).2
    listStageRead (fun t => (schedule t).index) probe word t =
      ((stageRead schedule t x).1.toList, (stageRead schedule t x).2.toList) := by
  dsimp only
  let x := extendWord (decodeOracleWord word).2
  induction t with
  | zero =>
    have first : (readBits x 1).toList = [x 0] := by
      rw [readBits_succ]
      simp [Vector.toList_push, readBits]
    have second : (readBits (fun j => x (1 + j)) 1).toList = [x 1] := by
      rw [readBits_succ]
      simp [Vector.toList_push, readBits]
    change _ = ((head (readBits x (1 + 1))).toList, (tail (readBits x (1 + 1))).toList)
    rw [readBits_add, head_append, tail_append, first, second]
    simp [listStageRead, paddedBit_eq_extendWord, x]
  | succ t ih =>
    change listStageStep probe word (schedule t).index
      (listStageRead (fun t => (schedule t).index) probe word t) = _
    rw [ih]
    exact listStageStep_correct (schedule t) (stagedCode schedule t) word probe (classifies t)

/-- The whole pair of finite stage strings is computed by the verified list simulator. -/
theorem stageRead_listState_primrec (schedule : Schedule) (probe : ℕ → OracleWord)
    (hSelected : Primrec (fun t => (schedule t).index)) (hProbe : Primrec probe)
    (classifies : ∀ t i, (schedule t).index = some i → ∀ x,
      (schedule t).hitsAt i x ↔ (readBits x (probe i).length).toList = probe i) :
    Primrec (fun p : OracleWord × ℕ =>
      let s := stageRead schedule p.2 (extendWord (decodeOracleWord p.1).2)
      (s.1.toList, s.2.toList)) :=
  (listStageRead_primrec probe hProbe (fun t => (schedule t).index) hSelected).of_eq
    (fun p => listStageRead_correct schedule probe classifies p.1 p.2)

/-- Finite output prefixes of the paper's stream map are primitive recursive from the
finite input, requested precision, selection indices, and defining cylinder words. -/
theorem cantorOutput_listPrefix_primrec (schedule : Schedule) (probe : ℕ → OracleWord)
    (hSelected : Primrec (fun t => (schedule t).index)) (hProbe : Primrec probe)
    (classifies : ∀ t i, (schedule t).index = some i → ∀ x,
      (schedule t).hitsAt i x ↔ (readBits x (probe i).length).toList = probe i) :
    Primrec (fun p : OracleWord × ℕ =>
      (readBits (cantorOutput schedule (extendWord (decodeOracleWord p.1).2)) p.2).toList) := by
  have output := Primrec.fst.comp (stageRead_listState_primrec schedule probe hSelected hProbe classifies)
  refine (Primrec.list_take.comp Primrec.snd output).of_eq ?_
  intro ⟨w, n⟩
  let x := extendWord (decodeOracleWord w).2
  change (stageRead schedule n x).1.toList.take n = (readBits (cantorOutput schedule x) n).toList
  have bound : n ≤ outputWidth schedule n :=
    Nat.le_trans (Nat.le_succ _) (outputWidth_ge schedule n)
  have readPrefix := congrArg Vector.toList (takePrefix_readBits (cantorOutput schedule x) bound)
  rw [cantorOutput_reads schedule n x] at readPrefix
  simpa only [takePrefix, Vector.toList_cast, Vector.toList_take] using readPrefix

/-- Specialization to the actual paired record schedule with effectively presented words. -/
theorem candidate_cantorOutput_listPrefix_primrec (C : CandidateWords)
    (hWitness : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2))
    (hWord : Primrec (fun i => (C.word i).toList)) :
    Primrec (fun p : OracleWord × ℕ =>
      (readBits (cantorOutput (candidateSchedule pairedReservation C)
        (extendWord (decodeOracleWord p.1).2)) p.2).toList) := by
  refine cantorOutput_listPrefix_primrec _ _ (candidateSchedule_index_primrec C hWitness) hWord ?_
  intro t i chosen x
  rw [candidateSchedule_hitsAt pairedReservation C t i chosen]
  change readBits x (C.width i) = C.word i ↔ _
  have size : (C.word i).toList.length = C.width i := Vector.length_toList
  rw [size, Vector.toList_inj]

end Guo

#print axioms Guo.cantorOutput_listPrefix_primrec
#print axioms Guo.candidate_cantorOutput_listPrefix_primrec
#print axioms Guo.stageRead_listState_primrec
