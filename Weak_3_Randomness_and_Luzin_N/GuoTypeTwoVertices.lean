import Weak_3_Randomness_and_Luzin_N.GuoPolygon
import Weak_3_Randomness_and_Luzin_N.GuoEndpointComputable
import Weak_3_Randomness_and_Luzin_N.GuoRealOraclePullback

open Set

namespace Guo

/-- A dyadic numerator and exponent for each of the horizontal and vertical coordinates. -/
abbrev DyadicPolygonVertex := (ℕ × ℕ) × (ℕ × ℕ)

def dyadicPolygonVertexValue (v : DyadicPolygonVertex) : ℚ × ℚ :=
  (rationalEndpointCodeValue v.1, rationalEndpointCodeValue v.2)

private def dyadicPolygonCodesForWord (schedule : Schedule) (p : ℕ × OracleWord) :
    List DyadicPolygonVertex :=
  let bounds := retainedIntervalCode p.2
  [((bounds.1, bounds.2.2), rationalEndpointCode schedule (p.2, false, p.1)),
    ((bounds.2.1, bounds.2.2), rationalEndpointCode schedule (p.2, true, p.1))]

/-- Dyadic codes for the coordinates of the polygon's rational vertices. -/
def dyadicPolygonCodes (schedule : Schedule) (k : ℕ) : List DyadicPolygonVertex :=
  (oracleWordsAtDepth (polygonInputDepth schedule k)).flatMap
    (fun w => dyadicPolygonCodesForWord schedule (k, w))

private theorem retainedIntervalCode_vertex (p : Bits n) (right : Bool) :
    let bounds := retainedIntervalCode p.toList
    rationalEndpointCodeValue (if right then bounds.2.1 else bounds.1, bounds.2.2) =
      retainedCoordinate p right := by
  let bounds := retainedIntervalCode p.toList
  let a : ℝ := bounds.1 / (2 : ℝ)^bounds.2.2
  let b : ℝ := bounds.2.1 / (2 : ℝ)^bounds.2.2
  let l : ℝ := (retainedEndpoints p).1
  let r : ℝ := (retainedEndpoints p).2
  have original : l ≤ r := by
    dsimp [l, r, retainedEndpoints]
    push_cast
    rw [cast_retainedLengthRat]
    apply le_add_of_nonneg_right
    unfold retainedLength
    positivity
  have intervals : Icc l r = Icc a b := by
    have spec := retainedInterval_eq_grid p.toList
    rw [decodeOracleWord_toList, retainedInterval_eq_Icc] at spec
    exact spec
  have lmem : l ∈ Icc a b := intervals ▸ left_mem_Icc.mpr original
  have rmem : r ∈ Icc a b := intervals ▸ right_mem_Icc.mpr original
  have gridOrder : a ≤ b := lmem.1.trans lmem.2
  have amem : a ∈ Icc l r := intervals.symm ▸ left_mem_Icc.mpr gridOrder
  have bmem : b ∈ Icc l r := intervals.symm ▸ right_mem_Icc.mpr gridOrder
  have low : a = l := le_antisymm lmem.1 amem.1
  have high : b = r := le_antisymm bmem.2 rmem.2
  dsimp only
  apply Rat.cast_injective (α := ℝ)
  cases right
  · simpa [a, l, bounds, rationalEndpointCodeValue, retainedCoordinate] using low
  · simpa [b, r, bounds, rationalEndpointCodeValue, retainedCoordinate] using high

section
attribute [local irreducible] rationalEndpointValue

private theorem dyadicPolygonCodesForWord_values (schedule : Schedule) (k : ℕ) (p : Bits n) :
    (dyadicPolygonCodesForWord schedule (k, p.toList)).map dyadicPolygonVertexValue =
      [retainedVertex schedule p k false, retainedVertex schedule p k true] := by
  simp only [dyadicPolygonCodesForWord, dyadicPolygonVertexValue, List.map_cons, List.map_nil,
    rationalEndpointCode_value, retainedVertex]
  have suffix (right : Bool) :
      rationalEndpointValue schedule (decodeOracleWord p.toList).2 right k =
        rationalEndpointValue schedule p right k := by
    let f (q : FiniteWord) := rationalEndpointValue schedule q.2 right k
    change f (decodeOracleWord p.toList) = f ⟨n, p⟩
    rw [decodeOracleWord_toList]
  rw [suffix false, suffix true]
  have low : rationalEndpointCodeValue ((retainedIntervalCode p.toList).1,
      (retainedIntervalCode p.toList).2.2) = retainedCoordinate p false :=
    retainedIntervalCode_vertex p false
  have high : rationalEndpointCodeValue ((retainedIntervalCode p.toList).2.1,
      (retainedIntervalCode p.toList).2.2) = retainedCoordinate p true :=
    retainedIntervalCode_vertex p true
  rw [low, high]

end

theorem dyadicPolygonCodes_values (schedule : Schedule) (k : ℕ) :
    (dyadicPolygonCodes schedule k).map dyadicPolygonVertexValue = rationalPolygonVertices schedule k := by
  simp only [dyadicPolygonCodes, rationalPolygonVertices, oracleWordsAtDepth_eq_map,
    List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro p _
  apply dyadicPolygonCodesForWord_values

theorem dyadicPolygonCodes_coordinates {schedule : Schedule} {k : ℕ} {v : DyadicPolygonVertex}
    (hv : v ∈ dyadicPolygonCodes schedule k) :
    v.1.2 = 2 * polygonInputDepth schedule k + 1 ∧ v.2.2 = k ∧ v.2.1 ≤ 2 ^ k := by
  obtain ⟨w, hw, hv⟩ := List.mem_flatMap.mp hv
  have len : w.length = polygonInputDepth schedule k := by
    rw [oracleWordsAtDepth_eq_map] at hw
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hw
    simp
  change v ∈ [((_, _), rationalEndpointCode schedule (w, false, k)),
    ((_, _), rationalEndpointCode schedule (w, true, k))] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;>
    exact ⟨by rw [show (retainedIntervalCode w).2.2 = 2 * w.length + 1 from rfl, len],
      rfl, (binaryPrefixIndex_lt _ _).le⟩

/-- The entire polygon code is produced uniformly using the finite endpoint computations. -/
theorem dyadicPolygonCodes_primrec (schedule : Schedule)
    (hWidth : Primrec (outputWidth schedule)) (hValues : Primrec (rationalEndpointCode schedule)) :
    Primrec (dyadicPolygonCodes schedule) := by
  let Input := ℕ × OracleWord
  have depth : Primrec (polygonInputDepth schedule) :=
    Primrec.nat_add.comp hWidth Primrec.succ
  have bounds : Primrec (fun p : Input => retainedIntervalCode p.2) :=
    retainedIntervalCode_primrec.comp Primrec.snd
  have exp : Primrec (fun p : Input => (retainedIntervalCode p.2).2.2) :=
    Primrec.snd.comp (Primrec.snd.comp bounds)
  have value (b : Bool) :
      Primrec (fun p : Input => rationalEndpointCode schedule (p.2, b, p.1)) :=
    hValues.comp (Primrec.snd.pair ((Primrec.const b).pair Primrec.fst))
  have lower := ((Primrec.fst.comp bounds).pair exp).pair (value false)
  have upper := ((Primrec.fst.comp (Primrec.snd.comp bounds)).pair exp).pair (value true)
  have both : Primrec₂ (fun k w => dyadicPolygonCodesForWord schedule (k, w)) :=
    (Primrec.list_cons.comp lower
      (Primrec.list_cons.comp upper (Primrec.const []))).to₂
  exact Primrec.list_flatMap (oracleWordsAtDepth_primrec.comp depth) both

/-- An effective sequence of rational polygons for the concrete candidate map.
The polygon at index `k` approximates the real map uniformly to within `2⁻ᵏ`. -/
theorem candidate_uniform_polygon_approximation (C : CandidateWords)
    (hWitness : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2))
    (hWord : Primrec (fun i => (C.word i).toList)) :
    let g := realAffineExtension (cantorOutput (candidateSchedule pairedReservation C))
    ∃ codes : ℕ → List DyadicPolygonVertex, Primrec codes ∧
      ∀ k x, |g x - realPolygonOfVertices ((codes k).map dyadicPolygonVertexValue) x| ≤
        ((2 : ℝ)^k)⁻¹ := by
  let schedule := candidateSchedule pairedReservation C
  have effective := dyadicPolygonCodes_primrec schedule (candidateSchedule_outputWidth_primrec C hWitness)
    (candidate_rationalEndpointCode_primrec C hWitness hWord)
  refine ⟨fun k => dyadicPolygonCodes schedule (k + 1), effective.comp Primrec.succ, ?_⟩
  intro k x
  rw [dyadicPolygonCodes_values, rationalPolygon_of_vertices]
  have error := rationalPolygon_uniform_error schedule (k + 1) x
  have scale : 2 * ((2 : ℝ)^(k + 1))⁻¹ = ((2 : ℝ)^k)⁻¹ := by
    rw [pow_succ]
    field_simp
  exact error.trans_eq scale

end Guo

#print axioms Guo.candidate_uniform_polygon_approximation
