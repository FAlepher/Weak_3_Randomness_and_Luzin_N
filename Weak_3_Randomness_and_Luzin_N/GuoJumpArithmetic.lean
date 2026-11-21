import Weak_3_Randomness_and_Luzin_N.GuoOracleNormalForm
import Weak_3_Randomness_and_Luzin_N.GuoOracleRates

open Encodable

namespace Guo

/-- Numeric compilation of the program indices used by `oracleJump`. -/
structure EffectiveReplayCompiler where
  code : ℕ → Option Nat.Partrec.Code
  primitive : Primrec code
  correct : ∀ index (table : List ℕ) argument,
    (code index).elim Part.none (fun p => p.eval (encode (table, argument))) =
      (decode (α := OracleCode) index).elim Part.none
        (fun p => p.eval (finiteOracleTable table) argument)

private def numericBit (b : Bool) : ℕ := bif b then 0 else 1

private theorem numericBit_primrec : Primrec numericBit :=
  Primrec.cond Primrec.id (Primrec.const 0) (Primrec.const 1)

private abbrev StopInput := ℕ × ℕ × List Bool

private def replayStops (compiler : EffectiveReplayCompiler) (p : StopInput) : Bool :=
  let (query, fuel, table) := p
  (compiler.code query.unpair.1).elim false
    (fun code => (code.evaln fuel (encode (table.map numericBit, query.unpair.2))).isSome)

private theorem replayStops_primrec (compiler : EffectiveReplayCompiler) : Primrec (replayStops compiler) := by
  have program := compiler.primitive.comp (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.fst : Primrec (Prod.fst : StopInput → ℕ))))
  let Input := StopInput × Nat.Partrec.Code
  have rest : Primrec (Prod.snd : StopInput → _) := Primrec.snd
  have query : Primrec (fun p : Input => p.1.1.unpair) :=
    Primrec.unpair.comp (Primrec.fst.comp Primrec.fst)
  have table : Primrec (fun p : Input => p.1.2.2.map numericBit) :=
    Primrec.list_map (Primrec.snd.comp (rest.comp Primrec.fst))
      (numericBit_primrec.comp (Primrec.snd : Primrec (Prod.snd : Input × Bool → Bool))).to₂
  have input := Primrec.encode.comp (table.pair (Primrec.snd.comp query))
  have fuel : Primrec (fun p : Input => p.1.2.1) := Primrec.fst.comp (rest.comp Primrec.fst)
  have run : Primrec (fun p : Input =>
      p.2.evaln p.1.2.1 (encode (p.1.2.2.map numericBit, p.1.1.unpair.2))) :=
    Nat.Partrec.Code.primrec_evaln.comp ((fuel.pair Primrec.snd).pair input)
  have present : Primrec (Option.isSome : Option ℕ → Bool) :=
    (Primrec.option_casesOn (Primrec.id : Primrec (id : Option ℕ → Option ℕ))
      (Primrec.const false) (Primrec.const true : Primrec (fun _ : Option ℕ × ℕ => true)).to₂).of_eq
      (fun a => by cases a <;> rfl)
  exact (Primrec.option_casesOn program (Primrec.const false) (present.comp run).to₂).of_eq
    fun p => by
      rcases p with ⟨q, f, t⟩
      cases h : compiler.code q.unpair.1 <;> simp [replayStops, h]

private theorem jump_iff_replay (compiler : EffectiveReplayCompiler) (bits : ℕ → Bool) (query : ℕ) :
    oracleJump (fun j => Part.some (numericBit (bits j))) query = Part.some 0 ↔
      ∃ len fuel, replayStops compiler (query, fuel, (List.range len).map bits) = true := by
  let Z : Oracle := fun j => Part.some (numericBit (bits j))
  have tableEval (len : ℕ) :
      (compiler.code query.unpair.1).elim Part.none
          (fun p => p.eval (encode (((List.range len).map bits).map numericBit, query.unpair.2))) =
        (decode (α := OracleCode) query.unpair.1).elim Part.none
          (fun p => p.eval (finiteOracleTable ((List.range len).map (fun j => numericBit (bits j))))
            query.unpair.2) := by
    simpa only [List.map_map, Function.comp_def] using
      compiler.correct query.unpair.1 (((List.range len).map bits).map numericBit) query.unpair.2
  have spent (len : ℕ) :
      (∃ f, replayStops compiler (query, f, (List.range len).map bits) = true) ↔
        ((decode (α := OracleCode) query.unpair.1).elim Part.none
          (fun p => p.eval
            (finiteOracleTable ((List.range len).map (fun j => numericBit (bits j)))) query.unpair.2)).Dom := by
    rw [← tableEval]
    cases h : compiler.code query.unpair.1 with
    | none => simp [replayStops, h]
    | some code =>
      change (∃ f, replayStops compiler (query, f, (List.range len).map bits) = true) ↔
        (code.eval _).Dom
      rw [Part.dom_iff_mem]
      simp only [replayStops, h, Option.elim_some, Option.isSome_iff_exists]
      exact ⟨fun ⟨f, v, hv⟩ => ⟨v, Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv)⟩,
        fun ⟨v, hv⟩ => by
          obtain ⟨f, hf⟩ := Nat.Partrec.Code.evaln_complete.mp hv
          exact ⟨f, v, Option.mem_def.mp hf⟩⟩
  change oracleJump Z query = Part.some 0 ↔ _
  simp only [oracleJump, Part.eq_some_iff, Part.mem_some_iff]
  cases h : decode (α := OracleCode) query.unpair.1 with
  | none =>
    have no (len : ℕ) : ¬ ∃ f, replayStops compiler (query, f, (List.range len).map bits) = true := by
      rw [spent]
      simp [h]
    simp [no]
  | some code =>
    change 0 = haltingFlag (code.eval Z) query.unpair.2 ↔ _
    rw [eq_comm, haltingFlag_eq_zero_iff]
    have collapse :
        (∃ len fuel, replayStops compiler (query, fuel, (List.range len).map bits) = true) ↔
          ∃ len, (code.eval (finiteOracleTable
            ((List.range len).map (fun j => numericBit (bits j)))) query.unpair.2).Dom :=
      exists_congr (fun len => by simpa only [h, Option.elim_some] using spent len)
    rw [collapse]
    simp only [Part.dom_iff_mem]
    exact ⟨fun ⟨v, hv⟩ => by
      obtain ⟨b, hb⟩ := (code.eval_finiteTable_iff (fun j => numericBit (bits j)) _ _).mp hv
      exact ⟨b, v, hb⟩, fun ⟨b, v, hv⟩ =>
        ⟨v, (code.eval_finiteTable_iff (fun j => numericBit (bits j)) _ _).mpr ⟨b, hv⟩⟩⟩

private noncomputable def jumpBit (Z : Oracle) (j : ℕ) : Bool := by
  classical
  exact decide (oracleJump Z j = Part.some 0)

private theorem jumpBit_graph (Z : Oracle) (j : ℕ) :
    oracleJump Z j = Part.some (if jumpBit Z j then 0 else 1) := by
  classical
  unfold jumpBit oracleJump haltingFlag
  cases decode (α := OracleCode) j.unpair.1 <;> simp

private def firstJumpMatrix (compiler : EffectiveReplayCompiler) (p : ℕ × ℕ) : Bool :=
  replayStops compiler (p.1, p.2.unpair.2, (List.range p.2.unpair.1).map (fun _ => true))

private theorem firstJumpMatrix_primrec (compiler : EffectiveReplayCompiler) : Primrec (firstJumpMatrix compiler) := by
  have decoded : Primrec (fun p : ℕ × ℕ => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have table : Primrec (fun p : ℕ × ℕ => (List.range p.2.unpair.1).map (fun _ => true)) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp decoded)) (Primrec.const true).to₂
  exact (replayStops_primrec compiler).comp (Primrec.fst.pair ((Primrec.snd.comp decoded).pair table))

private theorem firstJumpMatrix_correct (compiler : EffectiveReplayCompiler) (query : ℕ) :
    jumpBit emptyOracle query = true ↔ ∃ w, firstJumpMatrix compiler (query, w) = true := by
  classical
  simp only [jumpBit, decide_eq_true_eq]
  have constant : emptyOracle = fun _ => Part.some (numericBit true) := rfl
  rw [constant, jump_iff_replay]
  constructor
  · rintro ⟨len, fuel, hf⟩
    exact ⟨Nat.pair len fuel, by simpa only [firstJumpMatrix, Nat.unpair_pair] using hf⟩
  · rintro ⟨w, h⟩
    exact ⟨w.unpair.1, w.unpair.2, h⟩

private abbrev TableAudit := List Bool × List ℕ × ℕ

private def auditEntry (R : ℕ × ℕ → Bool) (p : ℕ × TableAudit) : Bool :=
  let (j, table, positive, challenge) := p
  bif table[j]?.getD false then R (j, positive[j]?.getD 0) else !R (j, challenge)

private theorem auditEntry_primrec (R : ℕ × ℕ → Bool) (hR : Primrec R) : Primrec (auditEntry R) := by
  have fields : Primrec (Prod.snd : ℕ × TableAudit → TableAudit) := Primrec.snd
  have j : Primrec (Prod.fst : ℕ × TableAudit → ℕ) := Primrec.fst
  have bit := Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.fst.comp fields) j) (Primrec.const false)
  have pos := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (Primrec.fst.comp (Primrec.snd.comp fields)) j) (Primrec.const 0)
  have n := Primrec.snd.comp (Primrec.snd.comp fields)
  exact Primrec.cond bit (hR.comp (j.pair pos)) (Primrec.not.comp (hR.comp (j.pair n)))

private def auditTable (R : ℕ × ℕ → Bool) (q : TableAudit) : Bool :=
  (List.range q.1.length).all (fun j => auditEntry R (j, q))

private theorem auditTable_primrec (R : ℕ × ℕ → Bool) (hR : Primrec R) : Primrec (auditTable R) := by
  have localCheck : PrimrecRel (fun j (q : TableAudit) => auditEntry R (j, q) = true) :=
    Primrec.eq.comp (auditEntry_primrec R hR) (Primrec.const true)
  have bounded := localCheck.forall_mem_list.comp
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)) Primrec.id
  refine bounded.decide.of_eq ?_
  intro q
  apply Bool.eq_iff_iff.mpr
  simp [auditTable, List.all_eq_true]

private theorem auditTable_iff (bits : ℕ → Bool) (R : ℕ × ℕ → Bool)
    (answer : ∀ j, bits j = true ↔ ∃ w, R (j, w) = true) (table : List Bool) :
    table = (List.range table.length).map bits ↔
      ∃ positive : List ℕ, ∀ challenge, auditTable R (table, positive, challenge) = true := by
  classical
  have full {j : ℕ} (hj : j < table.length) (f : ℕ → ℕ) :
      ((List.range table.length).map f)[j]?.getD 0 = f j := by simp [hj]
  have hasYes (j : ℕ) : ∃ w, bits j = true → R (j, w) = true := by
    by_cases h : bits j = true
    · obtain ⟨w, hw⟩ := (answer j).mp h
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun hb => (h hb).elim⟩
  choose positive ok using hasYes
  constructor
  · intro agreement
    refine ⟨(List.range table.length).map positive, fun n => ?_⟩
    rw [auditTable, List.all_eq_true]
    intro j hj
    have lt : j < table.length := List.mem_range.mp hj
    have value : table[j]?.getD false = bits j := by
      have e := congrArg (fun l : List Bool => l[j]?) agreement
      simp [lt] at e
      simpa only [List.getElem?_eq_getElem lt, Option.getD_some] using e
    cases h : bits j
    · have reject : R (j, n) = false := Bool.eq_false_iff.mpr (fun yes => by
        have := (answer j).mpr ⟨n, yes⟩
        simp [h] at this)
      simp only [auditEntry, value, h, Bool.cond_false, reject, Bool.not_false]
    · have confirmed := ok j h
      simp only [auditEntry, value, h, Bool.cond_true, full lt, confirmed]
  · rintro ⟨pos, audit⟩
    apply List.ext_get (by simp)
    intro j hj h'
    have getBit : table[j]?.getD false = bits j := by
      cases h : table[j]?.getD false
      · symm
        apply Bool.eq_false_iff.mpr
        intro yes
        obtain ⟨n, hn⟩ := (answer j).mp yes
        have checked := List.all_eq_true.mp (audit n) j (List.mem_range.mpr hj)
        simp [auditEntry, h, hn] at checked
      · symm
        apply (answer j).mpr
        refine ⟨pos[j]?.getD 0, ?_⟩
        have checked := List.all_eq_true.mp (audit 0) j (List.mem_range.mpr hj)
        simpa [auditEntry, h] using checked
    simpa [List.getElem?_eq_getElem hj, List.get_eq_getElem] using getBit

private abbrev JumpWitness := ℕ × List Bool × List ℕ

private def jumpMatrix (compiler : EffectiveReplayCompiler) (p : ℕ × ℕ × ℕ) : Bool :=
  (decode (α := JumpWitness) p.2.1).elim false (fun (fuel, table, pos) =>
    replayStops compiler (p.1, fuel, table) &&
      auditTable (firstJumpMatrix compiler) (table, pos, p.2.2))

private theorem jumpMatrix_primrec (compiler : EffectiveReplayCompiler) : Primrec (jumpMatrix compiler) := by
  have cert : Primrec (fun p : ℕ × ℕ × ℕ => decode (α := JumpWitness) p.2.1) :=
    Primrec.decode.comp (Primrec.fst.comp Primrec.snd)
  let Input := (ℕ × ℕ × ℕ) × JumpWitness
  have args : Primrec (fun p : Input => (p.1.1, p.2.1, p.2.2.1)) :=
    (Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have audit : Primrec (fun p : Input => (p.2.2.1, p.2.2.2, p.1.2.2)) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      ((Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have checked := Primrec.and.comp ((replayStops_primrec compiler).comp args)
    ((auditTable_primrec _ (firstJumpMatrix_primrec compiler)).comp audit)
  exact (Primrec.option_casesOn cert (Primrec.const false) checked.to₂).of_eq
    fun p => by
      cases h : decode (α := JumpWitness) p.2.1 <;> simp [jumpMatrix, h]

/-- The second jump has the required arithmetic presentation once its numeric
replay compiler is available. -/
noncomputable def secondJump_binarySigmaTwo (compiler : EffectiveReplayCompiler) :
    BinarySigmaTwoOracle secondJump where
  bit := jumpBit firstJump
  matrix := jumpMatrix compiler
  matrix_primrec := jumpMatrix_primrec compiler
  graph := jumpBit_graph firstJump
  answer query := by
    classical
    simp only [jumpBit, decide_eq_true_eq]
    have graph : firstJump = fun j => Part.some (numericBit (jumpBit emptyOracle j)) := by
      funext j
      rw [show firstJump j = Part.some (if jumpBit emptyOracle j then 0 else 1) from jumpBit_graph _ _]
      cases jumpBit emptyOracle j <;> rfl
    rw [congrArg (fun Z => oracleJump Z query) graph, jump_iff_replay compiler]
    constructor
    · rintro ⟨len, fuel, halted⟩
      let table := (List.range len).map (jumpBit emptyOracle)
      have passed : replayStops compiler (query, fuel, table) = true := halted
      have ok : table = (List.range table.length).map (jumpBit emptyOracle) := by simp [table]
      obtain ⟨pos, each⟩ := (auditTable_iff _ _ (firstJumpMatrix_correct compiler) table).mp ok
      refine ⟨encode ((fuel, table, pos) : JumpWitness), fun b => ?_⟩
      simp only [jumpMatrix, encodek, Option.elim_some, passed, Bool.true_and, each b]
    · rintro ⟨a, ha⟩
      cases certified : decode (α := JumpWitness) a with
      | none =>
        have h := ha 0
        simp [jumpMatrix, certified] at h
      | some certificate =>
        rcases certificate with ⟨fuel, table, pos⟩
        have each (b : ℕ) : replayStops compiler (query, fuel, table) = true ∧
            auditTable (firstJumpMatrix compiler) (table, pos, b) = true := by
          simpa [jumpMatrix, certified] using ha b
        have eq := (auditTable_iff _ _ (firstJumpMatrix_correct compiler) table).mpr
          ⟨pos, fun b => (each b).2⟩
        exact ⟨table.length, fuel, eq ▸ (each 0).1⟩

end Guo

#print axioms Guo.secondJump_binarySigmaTwo
