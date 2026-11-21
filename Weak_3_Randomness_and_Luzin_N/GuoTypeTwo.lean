import Weak_3_Randomness_and_Luzin_N.GuoTypeTwoGrid
import Weak_3_Randomness_and_Luzin_N.GuoTypeTwoVertices

open scoped NNReal

namespace Guo

/-- A fast rational Cauchy name uses precision index `k` for error at most `2⁻ᵏ`. -/
def RationalFastName (x : ℝ) (name : ℕ → RationalNameCode) : Prop :=
  ∀ k, |x - (rationalNameValue (name k) : ℝ)| ≤ ((2 : ℝ)^k)⁻¹

private theorem rationalNameValue_surjective : Function.Surjective rationalNameValue := by
  intro q
  have den : q.den - 1 + 1 = q.den := Nat.sub_add_cancel q.den_pos
  cases sign : q.num with
  | ofNat n =>
    refine ⟨(false, n, q.den - 1), ?_⟩
    calc
      _ = ((Int.ofNat n : ℤ) : ℚ) / q.den := by simp [rationalNameValue, den]
      _ = (q.num : ℚ) / q.den := by rw [sign]
      _ = q := q.num_div_den
  | negSucc n =>
    refine ⟨(true, n + 1, q.den - 1), ?_⟩
    calc
      _ = -((n + 1 : ℕ) : ℚ) / q.den := by
        simp only [rationalNameValue, if_true, den, neg_div]
      _ = (q.num : ℚ) / q.den := by rw [sign, Int.cast_negSucc]
      _ = q := q.num_div_den

theorem exists_rationalFastName (x : ℝ) : ∃ name, RationalFastName x name := by
  classical
  have approx (k : ℕ) : ∃ code : RationalNameCode,
      |x - (rationalNameValue code : ℝ)| ≤ ((2 : ℝ)^k)⁻¹ := by
    have lt : x < x + ((2 : ℝ)^k)⁻¹ := lt_add_of_pos_right _ (by positivity)
    obtain ⟨q, lo, hi⟩ := exists_rat_btwn lt
    obtain ⟨code, rfl⟩ := rationalNameValue_surjective q
    refine ⟨code, ?_⟩
    rw [abs_of_neg (sub_neg.mpr lo)]
    linarith
  choose name correct using approx
  exact ⟨name, correct⟩

/-- Type-2 computability witnessed by a single uniform input-name query per output digit.
Both the query precision and the computation on that answer are primitive recursive. -/
def TypeTwoComputable (f : ℝ → ℝ) : Prop :=
  ∃ query : ℕ → ℕ, ∃ compute : ℕ × RationalNameCode → RationalNameCode,
    Primrec query ∧ Primrec compute ∧
      ∀ x name, RationalFastName x name →
        RationalFastName (f x) (fun k => compute (k, name (query k)))

private def polygonGridExponent (schedule : Schedule) (k : ℕ) : ℕ :=
  2 * polygonInputDepth schedule k + 1

private def polygonGridDenominator (schedule : Schedule) (k : ℕ) : ℕ :=
  2 ^ polygonGridExponent schedule k

private def polygonGridKnots (schedule : Schedule) (k : ℕ) : List GridKnot :=
  (dyadicPolygonCodes schedule k).map fun v => (v.1.1, v.2.1)

private theorem primrec_pow_two : Primrec (fun n : ℕ => (2 : ℕ)^n) :=
  (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id

private theorem polygonGridExponent_primrec (schedule : Schedule)
    (hWidth : Primrec (outputWidth schedule)) : Primrec (polygonGridExponent schedule) := by
  have depth : Primrec (polygonInputDepth schedule) := Primrec.nat_add.comp hWidth Primrec.succ
  exact Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) depth)

private theorem polygonGridKnots_primrec (schedule : Schedule) (hWidth : Primrec (outputWidth schedule))
    (hCodes : Primrec (rationalEndpointCode schedule)) : Primrec (polygonGridKnots schedule) := by
  have coordinates : Primrec (fun v : DyadicPolygonVertex => (v.1.1, v.2.1)) :=
    (Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)
  exact Primrec.list_map (dyadicPolygonCodes_primrec schedule hWidth hCodes)
    (coordinates.comp Primrec.snd).to₂

private theorem polygonGridDenominator_pos (schedule : Schedule) (k : ℕ) :
    0 < polygonGridDenominator schedule k := by
  unfold polygonGridDenominator
  positivity

private theorem polygonGridValues (schedule : Schedule) (k : ℕ) :
    gridRationalVertices (polygonGridKnots schedule k) (polygonGridDenominator schedule k) (2 ^ k) =
      rationalPolygonVertices schedule k := by
  rw [← dyadicPolygonCodes_values schedule k]
  simp only [gridRationalVertices, polygonGridKnots, List.map_map]
  apply List.map_congr_left
  intro v hv
  obtain ⟨x, y, _⟩ := dyadicPolygonCodes_coordinates hv
  apply Prod.ext
  · change (v.1.1 : ℚ) / (polygonGridDenominator schedule k : ℕ) = rationalEndpointCodeValue v.1
    simp only [rationalEndpointCodeValue, x, polygonGridDenominator, polygonGridExponent,
      Nat.cast_pow, Nat.cast_ofNat]
  · change (v.2.1 : ℚ) / (2 ^ k : ℕ) = rationalEndpointCodeValue v.2
    simp only [rationalEndpointCodeValue, y, Nat.cast_pow, Nat.cast_ofNat]

private theorem polygonGridKey_of_mem (schedule : Schedule) (k i : ℕ)
    (h : (i : ℝ) / (polygonGridDenominator schedule k : ℕ) ∈
      retainedLevelKnots (polygonInputDepth schedule k)) :
    ∃ v ∈ polygonGridKnots schedule k, v.1 = i := by
  obtain ⟨⟨p, right⟩, hp⟩ := h
  have entry : retainedVertex schedule p k right ∈ rationalPolygonVertices schedule k := by
    apply List.mem_flatMap.mpr
    exact ⟨p, mem_wordsAtDepth p, by cases right <;> simp⟩
  rw [← polygonGridValues schedule k, gridRationalVertices] at entry
  obtain ⟨v, hv, he⟩ := List.mem_map.mp entry
  refine ⟨v, hv, ?_⟩
  have eq := congrArg (fun q : ℚ × ℚ => (q.1 : ℝ)) he
  change ((↑v.1 / ↑(polygonGridDenominator schedule k) : ℚ) : ℝ) =
    (retainedCoordinate p right : ℝ) at eq
  push_cast at eq
  have eq' := eq.trans hp
  have den : ((polygonGridDenominator schedule k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (polygonGridDenominator_pos schedule k).ne'
  field_simp [den] at eq'
  exact_mod_cast eq'

private theorem polygonGridZero (schedule : Schedule) (k : ℕ) :
    ∃ v ∈ polygonGridKnots schedule k, v.1 = 0 := by
  apply polygonGridKey_of_mem
  simpa using zero_mem_retainedLevelKnots (polygonInputDepth schedule k)

private theorem polygonGridOne (schedule : Schedule) (k : ℕ) :
    ∃ v ∈ polygonGridKnots schedule k, v.1 = polygonGridDenominator schedule k := by
  apply polygonGridKey_of_mem
  have ne : ((polygonGridDenominator schedule k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (polygonGridDenominator_pos schedule k).ne'
  simpa [ne] using one_mem_retainedLevelKnots (polygonInputDepth schedule k)

private theorem polygonGridHeight (schedule : Schedule) (k : ℕ) :
    ∀ v ∈ polygonGridKnots schedule k, v.2 ≤ 2 ^ k := by
  intro v hv
  unfold polygonGridKnots at hv
  obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp hv
  exact (dyadicPolygonCodes_coordinates mem).2.2

private theorem rationalPolygon_lipschitz (schedule : Schedule) (k : ℕ) :
    LipschitzWith (polygonGridDenominator schedule k : ℝ≥0) (rationalPolygon schedule k) := by
  rw [← rationalPolygon_of_vertices, ← polygonGridValues schedule k]
  exact gridRationalPolygon_lipschitz _ _ _ (polygonGridDenominator_pos schedule k)
    (by positivity) (polygonGridZero schedule k) (polygonGridOne schedule k) (polygonGridHeight schedule k)

/-- One precision query to the signed rational input name suffices. -/
def polygonNameQuery (schedule : Schedule) (k : ℕ) : ℕ :=
  (k + 1) + polygonGridExponent schedule (k + 2)

/-- Evaluate the finite rational polygon needed for an output name digit. -/
def polygonNameAnswer (schedule : Schedule) (p : ℕ × RationalNameCode) : RationalNameCode :=
  let k := p.1 + 2
  gridInterpolate (polygonGridKnots schedule k) (polygonGridDenominator schedule k) (2 ^ k) p.2

private theorem polygonNameQuery_primrec (schedule : Schedule)
    (hWidth : Primrec (outputWidth schedule)) : Primrec (polygonNameQuery schedule) :=
  Primrec.nat_add.comp Primrec.succ
    ((polygonGridExponent_primrec schedule hWidth).comp (Primrec.succ.comp Primrec.succ))

private theorem polygonNameAnswer_primrec (schedule : Schedule)
    (hWidth : Primrec (outputWidth schedule)) (hCodes : Primrec (rationalEndpointCode schedule)) :
    Primrec (polygonNameAnswer schedule) := by
  have level : Primrec (fun p : ℕ × RationalNameCode => p.1 + 2) :=
    (Primrec.succ.comp Primrec.succ).comp Primrec.fst
  have knots := (polygonGridKnots_primrec schedule hWidth hCodes).comp level
  have xDen := primrec_pow_two.comp ((polygonGridExponent_primrec schedule hWidth).comp level)
  have yDen := primrec_pow_two.comp level
  exact gridInterpolate_primrec.comp (knots.pair (xDen.pair (yDen.pair Primrec.snd)))

private theorem polygonNameAnswer_value (schedule : Schedule) (p : ℕ × RationalNameCode) :
    (rationalNameValue (polygonNameAnswer schedule p) : ℝ) =
      rationalPolygon schedule (p.1 + 2) (rationalNameValue p.2 : ℝ) := by
  let k := p.1 + 2
  change (rationalNameValue (gridInterpolate _ _ _ p.2) : ℝ) =
    rationalPolygon schedule k (rationalNameValue p.2 : ℝ)
  rw [gridInterpolate_value _ _ _ (polygonGridDenominator_pos schedule k) (by positivity)
    (polygonGridZero schedule k) (polygonGridOne schedule k), polygonGridValues, rationalPolygon_of_vertices]

theorem polygonName_correct (schedule : Schedule) {x : ℝ} {name : ℕ → RationalNameCode}
    (h : RationalFastName x name) :
    RationalFastName (realAffineExtension (cantorOutput schedule) x)
      (fun k => polygonNameAnswer schedule (k, name (polygonNameQuery schedule k))) := by
  intro k
  let n := k + 2
  let m := k + 1
  let e := polygonGridExponent schedule n
  let q : ℝ := rationalNameValue (name (m + e))
  let g := realAffineExtension (cantorOutput schedule)
  rw [polygonNameAnswer_value]
  change |g x - rationalPolygon schedule n q| ≤ ((2 : ℝ)^k)⁻¹
  have near : |x - q| ≤ ((2 : ℝ)^(m + e))⁻¹ := h _
  have error := rationalPolygon_uniform_error schedule n x
  have motion := (rationalPolygon_lipschitz schedule n).dist_le_mul x q
  have den : (polygonGridDenominator schedule n : ℝ) = (2 : ℝ)^e := by
    simp [polygonGridDenominator, e]
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_natCast, den] at motion
  have scale : (2 : ℝ)^e * ((2 : ℝ)^(m + e))⁻¹ = ((2 : ℝ)^m)⁻¹ := by
    rw [pow_add]
    field_simp
  have half : 2 * ((2 : ℝ)^n)⁻¹ = ((2 : ℝ)^m)⁻¹ := by
    change 2 * ((2 : ℝ)^(m + 1))⁻¹ = _
    rw [pow_succ]
    field_simp
  have both : ((2 : ℝ)^m)⁻¹ + ((2 : ℝ)^m)⁻¹ = ((2 : ℝ)^k)⁻¹ := by
    dsimp [m]
    rw [pow_succ]
    field_simp
    ring
  calc
    _ ≤ |g x - rationalPolygon schedule n x| +
        |rationalPolygon schedule n x - rationalPolygon schedule n q| := by
      simpa only [sub_add_sub_cancel] using
        abs_add_le (g x - rationalPolygon schedule n x)
          (rationalPolygon schedule n x - rationalPolygon schedule n q)
    _ ≤ 2 * ((2 : ℝ)^n)⁻¹ + (2 : ℝ)^e * ((2 : ℝ)^(m + e))⁻¹ :=
      add_le_add error (motion.trans (mul_le_mul_of_nonneg_left near (by positivity)))
    _ = _ := by rw [half, scale, both]

/-- The candidate real map has a uniform Type-2 realizer on the whole real line. -/
theorem candidate_realAffineExtension_typeTwoComputable (C : CandidateWords)
    (hWitness : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2))
    (hWord : Primrec (fun i => (C.word i).toList)) :
    TypeTwoComputable (realAffineExtension (cantorOutput (candidateSchedule pairedReservation C))) := by
  let schedule := candidateSchedule pairedReservation C
  have width := candidateSchedule_outputWidth_primrec C hWitness
  exact ⟨polygonNameQuery schedule, polygonNameAnswer schedule,
    polygonNameQuery_primrec schedule width,
    polygonNameAnswer_primrec schedule width (candidate_rationalEndpointCode_primrec C hWitness hWord),
    fun _ _ h => polygonName_correct schedule h⟩

end Guo

#print axioms Guo.candidate_realAffineExtension_typeTwoComputable
