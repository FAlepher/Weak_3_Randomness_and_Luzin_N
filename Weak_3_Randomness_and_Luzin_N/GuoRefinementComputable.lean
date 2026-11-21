import Weak_3_Randomness_and_Luzin_N.GuoCoverWordsComputable

namespace Guo

private def oracleDepthBound (words : List OracleWord) : ℕ :=
  words.foldr (fun w d => max w.length d) 0

private theorem oracleDepthBound_primrec : Primrec oracleDepthBound :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

private theorem depthBound_decode (words : List OracleWord) :
    depthBound (words.map decodeOracleWord) = oracleDepthBound words := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    change max w.length (depthBound (ws.map decodeOracleWord)) =
      max w.length (oracleDepthBound ws)
    rw [ih]

private def removeEarlierOracleWords (words : List OracleWord) (p : OracleWord) :
    List OracleWord :=
  let d := oracleDepthBound (p :: words)
  (oracleWordsAtDepth d).filter (fun w => oracleWordPrefix p w && !(words.any (oracleWordPrefix · w)))

private theorem removeEarlierOracleWords_primrec : Primrec₂ removeEarlierOracleWords := by
  let Input := List OracleWord × OracleWord
  have inside : PrimrecRel (fun w (p : Input) => oracleWordPrefix p.2 w = true) :=
    Primrec.eq.comp (oracleWordPrefix_primrec.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
      (Primrec.const true)
  have avoids : PrimrecRel (fun v w => oracleWordPrefix v w ≠ true) :=
    (Primrec.eq.comp oracleWordPrefix_primrec (Primrec.const true)).not
  have outside : PrimrecRel (fun w (p : Input) => ∀ v ∈ p.1, oracleWordPrefix v w ≠ true) :=
    avoids.forall_mem_list.comp (Primrec.fst.comp Primrec.snd) Primrec.fst
  have depth : Primrec (fun p : Input => oracleDepthBound (p.2 :: p.1)) :=
    oracleDepthBound_primrec.comp (Primrec.list_cons.comp Primrec.snd Primrec.fst)
  have keep : PrimrecRel (fun w (p : Input) =>
      oracleWordPrefix p.2 w = true ∧ ∀ v ∈ p.1, oracleWordPrefix v w ≠ true) :=
    inside.and outside
  have step : Primrec (fun p : Input => removeEarlierOracleWords p.1 p.2) := by
    refine (keep.listFilter.comp
      (oracleWordsAtDepth_primrec.comp depth) Primrec.id).of_eq ?_
    rintro ⟨words, p⟩
    unfold removeEarlierOracleWords
    apply List.filter_congr
    intro w _
    apply Bool.eq_iff_iff.mpr
    simp [Bool.and_eq_true, List.any_eq_false]
  exact step.to₂

private theorem removeEarlierOracleWords_encode (words : List OracleWord) (p : OracleWord) :
    removeEarlierOracleWords words p =
      (removeEarlierCylinders (words.map decodeOracleWord) (decodeOracleWord p)).map
        encodeOracleWord := by
  unfold removeEarlierOracleWords removeEarlierCylinders
  rw [← List.map_cons, depthBound_decode]
  dsimp only
  rw [oracleWordsAtDepth_eq_map, List.filter_map, List.map_map]
  apply congrArg (List.map Vector.toList)
  apply List.filter_congr
  intro w _
  simp [Function.comp_def, oracleWordPrefix_toList]

private def clippedOracleEntry (σ : OracleWord) (words : List (Option OracleWord)) (k : ℕ) :
    Option OracleWord :=
  intersectOracleOptions (some σ) (words[k]?.getD none)

private theorem clippedOracleEntry_primrec (σ : OracleWord) :
    Primrec₂ (clippedOracleEntry σ) :=
  (intersectOracleOptions_primrec.comp (Primrec.const (some σ)) (Primrec.list_getD none)).to₂

private theorem clippedOracleEntry_decode (σ : OracleWord) (words : List (Option OracleWord))
    (k : ℕ) :
    (clippedOracleEntry σ words k).map decodeOracleWord =
      clipEnumeration (fun j => (words[j]?.getD none).map decodeOracleWord) (decodeOracleWord σ) k := by
  unfold clippedOracleEntry clipEnumeration
  cases eq : words[k]?.getD none <;> simp [intersectOracleOptions, eq]

/-- The clipped and subdivided input words at a cover tick, in enumeration order. -/
def refinedOracleWords (σ : OracleWord) (p : ℕ × List (Option OracleWord)) : List OracleWord :=
  let earlier := (List.range p.1).filterMap (clippedOracleEntry σ p.2)
  match clippedOracleEntry σ p.2 p.1 with
  | none => []
  | some w => removeEarlierOracleWords earlier w

theorem refinedOracleWords_primrec (σ : OracleWord) : Primrec (refinedOracleWords σ) := by
  let Input := ℕ × List (Option OracleWord)
  have earlier : Primrec (fun p : Input => (List.range p.1).filterMap (clippedOracleEntry σ p.2)) :=
    Primrec.listFilterMap (Primrec.list_range.comp Primrec.fst)
      ((clippedOracleEntry_primrec σ).comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have current : Primrec (fun p : Input => clippedOracleEntry σ p.2 p.1) :=
    (clippedOracleEntry_primrec σ).comp Primrec.snd Primrec.fst
  have refineStep : Primrec₂ (fun (p : Input) w =>
      removeEarlierOracleWords ((List.range p.1).filterMap (clippedOracleEntry σ p.2)) w) :=
    (removeEarlierOracleWords_primrec.comp (earlier.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.option_casesOn current (Primrec.const []) refineStep).of_eq
    (fun p => by unfold refinedOracleWords; cases clippedOracleEntry σ p.2 p.1 <;> rfl)

theorem refinedOracleWords_encode (σ : OracleWord) (p : ℕ × List (Option OracleWord)) :
    refinedOracleWords σ p =
      (refinedEnumeration (clipEnumeration (fun k => (p.2[k]?.getD none).map decodeOracleWord)
        (decodeOracleWord σ)) p.1).map encodeOracleWord := by
  let enumerated := clipEnumeration (fun k => (p.2[k]?.getD none).map decodeOracleWord)
    (decodeOracleWord σ)
  have entry (k : ℕ) : (clippedOracleEntry σ p.2 k).map decodeOracleWord = enumerated k :=
    clippedOracleEntry_decode σ p.2 k
  have prior :
      ((List.range p.1).filterMap (clippedOracleEntry σ p.2)).map decodeOracleWord =
        earlierWords enumerated p.1 := by
    rw [List.map_filterMap, earlierWords]
    exact congrArg (List.filterMap · (List.range p.1)) (funext entry)
  change refinedOracleWords σ p = (refinedEnumeration enumerated p.1).map encodeOracleWord
  unfold refinedOracleWords refinedEnumeration
  rw [← entry p.1]
  cases eq : clippedOracleEntry σ p.2 p.1 with
  | none => rfl
  | some w =>
    simp only [Option.map_some]
    rw [removeEarlierOracleWords_encode, prior]

end Guo

#print axioms Guo.refinedOracleWords_primrec
#print axioms Guo.refinedOracleWords_encode
