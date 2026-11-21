import Weak_3_Randomness_and_Luzin_N.GuoOracleCover

namespace Guo

/-- Enumerate Boolean lists in the same order as the dependent words at a fixed depth. -/
def oracleWordsAtDepth : ℕ → List OracleWord
  | 0 => [[]]
  | n + 1 => (oracleWordsAtDepth n).flatMap (fun w => [w ++ [false], w ++ [true]])

theorem oracleWordsAtDepth_primrec : Primrec oracleWordsAtDepth := by
  have appendBit (b : Bool) : Primrec (fun w : OracleWord => w ++ [b]) :=
    Primrec.list_concat.comp Primrec.id (Primrec.const b)
  have children : Primrec (fun w : OracleWord => [w ++ [false], w ++ [true]]) :=
    Primrec.list_cons.comp (appendBit false)
      (Primrec.list_cons.comp (appendBit true) (Primrec.const []))
  have step : Primrec (fun ws : List OracleWord =>
      ws.flatMap (fun w => [w ++ [false], w ++ [true]])) :=
    Primrec.list_flatMap Primrec.id (children.comp Primrec.snd).to₂
  exact (Primrec.nat_rec₁ [[]] (step.comp Primrec.snd).to₂).of_eq (fun d => by
    induction d with
    | zero => rfl
    | succ d ih =>
      change _ = (oracleWordsAtDepth d).flatMap _
      rw [← ih])

theorem oracleWordsAtDepth_eq_map (n : ℕ) :
    oracleWordsAtDepth n = (wordsAtDepth n).map Vector.toList := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [oracleWordsAtDepth, wordsAtDepth, ih, List.map_flatMap, List.flatMap_map,
      Vector.toList_push]

@[simp] theorem decodeOracleWord_toList (w : Bits n) :
    decodeOracleWord w.toList = ⟨n, w⟩ :=
  decode_encodeOracleWord ⟨n, w⟩

theorem oracleWordPrefix_toList (p : OracleWord) (w : Bits n) :
    oracleWordPrefix p w.toList = hasWordPrefix (decodeOracleWord p) w := by
  rw [← hasWordPrefix_decodeOracleWord p w.toList, decodeOracleWord_toList]

@[simp] theorem extendWord_decodeOracleWord_toList (w : Bits n) :
    extendWord (decodeOracleWord w.toList).2 = extendWord w :=
  congrArg (fun p : FiniteWord => extendWord p.2) (decodeOracleWord_toList w)

/-- The finite stage cover, using the list representation throughout. -/
def oracleCoverWordsAt (schedule : Schedule) (i : ℕ) (p : ℕ × OracleWord) :
    List OracleWord :=
  let n := outputWidth schedule p.1 + (p.1 + 1)
  ((oracleWordsAtDepth n).filter (oracleWordPrefix p.2)).map (fun w =>
    (readBits (cantorOutput schedule (extendWord (decodeOracleWord w).2)) (n - i)).toList)

theorem oracleCoverWordsAt_eq_map (schedule : Schedule) (i : ℕ) (p : ℕ × OracleWord) :
    oracleCoverWordsAt schedule i p =
      (coverWordsAt schedule p.1 i (decodeOracleWord p.2)).map encodeOracleWord := by
  simp only [oracleCoverWordsAt, coverWordsAt, oracleWordsAtDepth_eq_map, List.filter_map,
    List.map_map, Function.comp_def, oracleWordPrefix_toList, encodeOracleWord,
    extendWord_decodeOracleWord_toList]

/-- Primitive recursiveness of the exact finite stage cover from primitive recursive reads. -/
theorem coverWordsAt_primrec (schedule : Schedule) (i : ℕ)
    (hWidth : Primrec (outputWidth schedule))
    (hRead : Primrec (fun p : ℕ × OracleWord =>
      (readBits (cantorOutput schedule (extendWord (decodeOracleWord p.2).2)) p.1).toList)) :
    Primrec (fun p : ℕ × OracleWord =>
      (coverWordsAt schedule p.1 i (decodeOracleWord p.2)).map encodeOracleWord) := by
  let Input := ℕ × OracleWord
  let depth (p : Input) := outputWidth schedule p.1 + (p.1 + 1)
  have hDepth : Primrec depth :=
    Primrec.nat_add.comp (hWidth.comp Primrec.fst) (Primrec.succ.comp Primrec.fst)
  have hPrefix : PrimrecRel (fun (w : OracleWord) (p : Input) => oracleWordPrefix p.2 w = true) :=
    Primrec.eq.comp (oracleWordPrefix_primrec.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
      (Primrec.const true)
  have hWords : Primrec (fun p : Input => (oracleWordsAtDepth (depth p)).filter (oracleWordPrefix p.2)) :=
    (hPrefix.listFilter.comp (oracleWordsAtDepth_primrec.comp hDepth) Primrec.id).of_eq (by simp)
  have hOutput : Primrec₂ (fun (p : Input) (w : OracleWord) =>
      (readBits (cantorOutput schedule (extendWord (decodeOracleWord w).2)) (depth p - i)).toList) :=
    (hRead.comp ((Primrec.nat_sub.comp (hDepth.comp Primrec.fst) (Primrec.const i)).pair
      Primrec.snd)).to₂
  exact (Primrec.list_map hWords hOutput).of_eq (oracleCoverWordsAt_eq_map schedule i)

end Guo

#print axioms Guo.oracleWordsAtDepth_primrec
#print axioms Guo.coverWordsAt_primrec
