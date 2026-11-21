import Weak_3_Randomness_and_Luzin_N.GuoLocalization
import Weak_3_Randomness_and_Luzin_N.GuoEnumeratedCover
import Mathlib.Computability.Primrec.List

namespace Guo

private theorem validLength_primrec (C : CandidateWords)
    (h : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2)) :
    Primrec (fun p : (ℕ × ℕ) × ℕ => validLength (C.witness p.1.1) p.1.2 p.2) := by
  have witness : PrimrecRel (fun (b : ℕ) (args : ℕ × ℕ) =>
      C.witness args.1 args.2 b = true) :=
    Primrec.eq.comp
      (h.comp ((Primrec.fst.comp Primrec.snd).pair ((Primrec.snd.comp Primrec.snd).pair Primrec.fst)))
      (Primrec.const true)
  have cutoff : Primrec (fun p : ℕ × ℕ × ℕ => List.range (p.2.2 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
  have args : Primrec (fun p : ℕ × ℕ × ℕ => (p.2.1, p.1)) :=
    (Primrec.fst.comp Primrec.snd).pair Primrec.fst
  have verified : PrimrecRel (fun (n : ℕ) (args : ℕ × ℕ) =>
      ∃ b < args.2 + 1, C.witness args.1 n b = true) :=
    (witness.exists_mem_list.comp cutoff args).of_eq (by simp)
  have checked : PrimrecPred (fun p : (ℕ × ℕ) × ℕ =>
      validLength (C.witness p.1.1) p.1.2 p.2 = true) :=
    (verified.forall_mem_list.comp (Primrec.list_range.comp Primrec.snd) Primrec.fst).of_eq
      (fun p => by
        simpa only [List.mem_range, Nat.lt_succ_iff] using
          (validLength_iff (C.witness p.1.1) p.1.2 p.2).symm)
  apply checked.decide.of_eq
  intro p
  simp

private theorem greatestVerified_primrec (C : CandidateWords)
    (h : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2)) :
    Primrec (fun p : (ℕ × ℕ) × ℕ => greatestVerified (C.witness p.1.1) p.1.2 p.2) := by
  let Input := (ℕ × ℕ) × ℕ × ℕ
  have successor : Primrec (fun q : Input => q.2.1 + 1) :=
    Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
  have verified : Primrec (fun q : Input =>
      validLength (C.witness q.1.1) q.1.2 (q.2.1 + 1)) :=
    (validLength_primrec C h).comp (Primrec.fst.pair successor)
  let next (p : ℕ × ℕ) (n value : ℕ) :=
    bif validLength (C.witness p.1) p.2 (n + 1) then n + 1 else value
  have step : Primrec (fun q : Input => next q.1 q.2.1 q.2.2) :=
    Primrec.cond verified successor (Primrec.snd.comp Primrec.snd)
  have run : Primrec (fun p : (ℕ × ℕ) × ℕ => Nat.rec (motive := fun _ => ℕ) 0 (next p.1) p.2) :=
    Primrec.nat_rec (Primrec.const (0 : ℕ)) step.to₂
  apply run.of_eq
  rintro ⟨⟨i, t⟩, n⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    change next (i, t) n (Nat.rec (motive := fun _ => ℕ) 0 (next (i, t)) n) =
      greatestVerified (C.witness i) t (n + 1)
    rw [ih, greatestVerified]
    cases checked : validLength (C.witness i) t (n + 1) <;> simp [next, checked]

private theorem score_primrec (C : CandidateWords)
    (h : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2)) :
    Primrec (fun p : ℕ × ℕ => score (C.witness p.1) p.2) :=
  (greatestVerified_primrec C h).comp (Primrec.id.pair Primrec.snd)

private theorem recordTest_primrec (C : CandidateWords)
    (h : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2)) :
    Primrec (fun p : ℕ × ℕ => recordTest pairedReservation C p.1 p.2) := by
  have now : Primrec (fun p : ℕ × ℕ => score (C.witness p.1) (Nat.pair p.1 p.2 + 1)) :=
    (score_primrec C h).comp (Primrec.fst.pair
      (Primrec.succ.comp (Primrec₂.natPair.comp Primrec.fst Primrec.snd)))
  have prevScore : Primrec (fun p : ℕ × ℕ =>
      score (C.witness p.1) (Nat.pair p.1 (Nat.pred p.2) + 1)) :=
    now.comp (Primrec.fst.pair ((Primrec.nat_iff.mpr Nat.Primrec.pred).comp Primrec.snd))
  have prev : Primrec (fun p : ℕ × ℕ =>
      if p.2 = 0 then 0 else score (C.witness p.1) (Nat.pair p.1 (Nat.pred p.2) + 1)) :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0) prevScore
  refine ((Primrec.nat_lt.comp prev now).decide).of_eq ?_
  rintro ⟨i, m⟩
  cases m <;> simp [recordTest, pairedReservation]

/-- The index of the actual record schedule is primitive recursive when the witness relation is. -/
theorem candidateSchedule_index_primrec (C : CandidateWords)
    (h : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2)) :
    Primrec (fun t => (candidateSchedule pairedReservation C t).index) := by
  have decode : Primrec Nat.unpair := Primrec.unpair
  have hasRecord : Primrec (fun t : ℕ => recordTest pairedReservation C t.unpair.1 t.unpair.2) :=
    (recordTest_primrec C h).comp decode
  have index : Primrec (fun t : ℕ => bif recordTest pairedReservation C t.unpair.1 t.unpair.2
      then some t.unpair.1 else none) :=
    Primrec.cond hasRecord (Primrec.option_some.comp (Primrec.fst.comp decode)) (Primrec.const none)
  refine index.of_eq ?_
  intro t
  let chosen := (candidateSchedule pairedReservation C t).index
  by_cases yes : recordTest pairedReservation C t.unpair.1 t.unpair.2 = true
  · rw [yes]
    exact ((candidateSchedule_index_iff pairedReservation C t t.unpair.1).mpr
      ⟨t.unpair.2, rfl, yes⟩).symm
  · rw [show recordTest pairedReservation C t.unpair.1 t.unpair.2 = false from Bool.eq_false_iff.mpr yes]
    cases action : chosen with
    | none => exact action.symm
    | some i =>
      obtain ⟨m, eq, rec⟩ := (candidateSchedule_index_iff pairedReservation C t i).mp action
      have pairing : t.unpair = (i, m) := Option.some.inj eq
      rw [pairing] at yes
      exact (yes rec).elim

private def addedWidth (stage : ℕ) (selected : Option ℕ) : ℕ :=
  selected.elim 0 (fun i => stage - i)

private theorem nextWidth_index {s : ℕ} (action : StageAction s) (h : ℕ) :
    action.nextWidth h = h + addedWidth s action.index + 1 := by
  cases action <;> simp [StageAction.nextWidth, StageAction.index, addedWidth]

theorem candidateSchedule_outputWidth_primrec (C : CandidateWords)
    (h : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2)) :
    Primrec (outputWidth (candidateSchedule pairedReservation C)) := by
  let schedule := candidateSchedule pairedReservation C
  have selected : Primrec (fun t : ℕ => (schedule t).index) := candidateSchedule_index_primrec C h
  have difference : Primrec₂ (fun (t i : ℕ) => t + 1 - i) :=
    (Primrec.nat_sub.comp (Primrec.succ.comp Primrec.fst) Primrec.snd).to₂
  have addAt : Primrec (fun t : ℕ => addedWidth (t + 1) (schedule t).index) :=
    (Primrec.option_casesOn selected (Primrec.const 0) difference).of_eq
      (fun t => by cases (schedule t).index <;> rfl)
  let step (t width : ℕ) := width + addedWidth (t + 1) (schedule t).index + 1
  have stepRec : Primrec₂ step :=
    (Primrec.succ.comp (Primrec.nat_add.comp Primrec.snd (addAt.comp Primrec.fst))).to₂
  refine (Primrec.nat_rec₁ 1 stepRec).of_eq ?_
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    change step t (Nat.rec (motive := fun _ => ℕ) 1 step t) =
      (schedule t).nextWidth (outputWidth schedule t)
    rw [ih, nextWidth_index]

/-- The time selection in the finite covering kernel is a bounded computation. -/
theorem firstSuitableStage_primrec_of_index (schedule : Schedule) (i : ℕ)
    (selected : Primrec (fun t => (schedule t).index)) :
    Primrec₂ (firstSuitableStage schedule i) := by
  have lateEnough : PrimrecRel (fun depth t => max i depth ≤ t) :=
    Primrec.nat_le.comp (Primrec.nat_max.comp (Primrec.const i) Primrec.fst) Primrec.snd
  have chosen : PrimrecRel (fun (_ : ℕ) t => (schedule t).index = some i) :=
    Primrec.eq.comp (selected.comp Primrec.snd) (Primrec.const (some i))
  have suitable : Primrec (fun p : ℕ × ℕ => suitableStage schedule i p.1 p.2) := by
    refine (lateEnough.and chosen).decide.of_eq ?_
    rintro ⟨d, t⟩
    apply Bool.eq_iff_iff.mpr
    simp [suitableStage_iff]
  have eligible : PrimrecRel (fun d t => suitableStage schedule i d t = true) :=
    Primrec.eq.comp suitable (Primrec.const true)
  have early : PrimrecRel (fun t d => suitableStage schedule i d t ≠ true) :=
    eligible.swap.not
  have noEarlier : PrimrecRel (fun d t => ∀ u ∈ List.range t, suitableStage schedule i d u ≠ true) :=
    early.forall_mem_list.comp (Primrec.list_range.comp Primrec.snd) Primrec.fst
  have first : Primrec (fun p : ℕ × ℕ => firstSuitableStage schedule i p.1 p.2) := by
    refine (eligible.and noEarlier).decide.of_eq ?_
    rintro ⟨d, t⟩
    apply Bool.eq_iff_iff.mpr
    simp [firstSuitableStage_iff]
  exact first.to₂

end Guo

#print axioms Guo.candidateSchedule_index_primrec
#print axioms Guo.candidateSchedule_outputWidth_primrec
#print axioms Guo.firstSuitableStage_primrec_of_index
