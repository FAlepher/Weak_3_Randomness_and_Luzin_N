import Weak_3_Randomness_and_Luzin_N.GuoAffineExtension
import Weak_3_Randomness_and_Luzin_N.GuoEnumeratedOpen



open Set

namespace Guo

theorem polygon_lastPoint {C : Set ℝ} (compact : IsCompact C) (h0 : 0 ∈ C)
    {x : ℝ} (hx : 0 ≤ x) : IsGreatest (C ∩ Iic x) (lastPoint C x) :=
  (compact.inter_right isClosed_Iic).isGreatest_sSup ⟨0, h0, hx⟩

theorem polygon_nextPoint {C : Set ℝ} (compact : IsCompact C) (h1 : 1 ∈ C)
    {x : ℝ} (hx : x ≤ 1) : IsLeast (C ∩ Ici x) (nextPoint C x) :=
  (compact.inter_right isClosed_Ici).isLeast_sInf ⟨1, h1, hx⟩

theorem polygon_projection_mem (x : ℝ) : max 0 (min x 1) ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

theorem polygon_projection_eq {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    max 0 (min x 1) = x := by
  rw [min_eq_left hx.2, max_eq_right hx.1]

private theorem polygon_affine_at_projection (C : Set ℝ) (f : ℝ → ℝ) (x : ℝ) :
    affineExtension C f x = affineExtension C f (max 0 (min x 1)) := by
  unfold affineExtension
  rw [polygon_projection_eq (polygon_projection_mem x)]

private theorem affineBridge_abs_le (f : ℝ → ℝ) {a b x y δ : ℝ}
    (h : a < b) (hx : x ∈ Icc a b) (ha : |f a - y| ≤ δ) (hb : |f b - y| ≤ δ) :
    |affineBridge f a b x - y| ≤ δ := by
  let w := (x - a) / (b - a)
  have w0 : 0 ≤ w := div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr h).le
  have w1 : w ≤ 1 := (div_le_iff₀ (sub_pos.mpr h)).mpr (by linarith [hx.2])
  change |(1 - w) * f a + w * f b - y| ≤ δ
  rw [show (1 - w) * f a + w * f b - y = (1 - w) * (f a - y) + w * (f b - y) by ring]
  calc
    _ ≤ (1 - w) * |f a - y| + w * |f b - y| := by
      simpa only [abs_mul, abs_of_nonneg (sub_nonneg.mpr w1), abs_of_nonneg w0] using
        abs_add_le ((1 - w) * (f a - y)) (w * (f b - y))
    _ ≤ (1 - w) * δ + w * δ := add_le_add
      (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr w1)) (mul_le_mul_of_nonneg_left hb w0)
    _ = δ := by ring

private theorem affineBridge_error (f g : ℝ → ℝ) {a b x δ : ℝ}
    (h : a < b) (hx : x ∈ Icc a b) (ha : |f a - g a| ≤ δ) (hb : |f b - g b| ≤ δ) :
    |affineBridge f a b x - affineBridge g a b x| ≤ δ := by
  have linear : affineBridge f a b x - affineBridge g a b x =
      affineBridge (fun y => f y - g y) a b x := by unfold affineBridge; ring
  rw [linear]
  simpa only [sub_zero] using
    affineBridge_abs_le (fun y => f y - g y) (y := 0) h hx (by simpa only [sub_zero]) (by simpa only [sub_zero])

private theorem affineExtension_abs_le_on_interval {C : Set ℝ}
    (compact : IsCompact C) (h0 : 0 ∈ C) (h1 : 1 ∈ C)
    {f : ℝ → ℝ} {a b x y δ : ℝ} (ha : a ∈ C) (hb : b ∈ C)
    (hx : x ∈ Icc a b) (unit : x ∈ Icc (0 : ℝ) 1)
    (bound : ∀ z ∈ C, z ∈ Icc a b → |f z - y| ≤ δ) :
    |affineExtension C f x - y| ≤ δ := by
  let l := lastPoint C x
  let r := nextPoint C x
  have left := polygon_lastPoint compact h0 unit.1
  have right := polygon_nextPoint compact h1 unit.2
  have lx : l ≤ x := left.1.2
  have xr : x ≤ r := right.1.2
  have leftBound := bound l left.1.1 ⟨left.2 ⟨ha, hx.1⟩, lx.trans hx.2⟩
  have rightBound := bound r right.1.1 ⟨hx.1.trans xr, right.2 ⟨hb, hx.2⟩⟩
  rw [affineExtension, polygon_projection_eq unit]
  by_cases eq : l = r
  · change |(if l = r then f l else affineBridge f l r x) - y| ≤ δ
    rw [if_pos eq]
    exact leftBound
  · change |(if l = r then f l else affineBridge f l r x) - y| ≤ δ
    rw [if_neg eq]
    exact affineBridge_abs_le f ((lx.trans xr).lt_of_ne eq) ⟨lx, xr⟩ leftBound rightBound

theorem affineExtension_on_gap_with_own_values {C : Set ℝ}
    (compact : IsCompact C) (h0 : 0 ∈ C) (h1 : 1 ∈ C) (rangeC : C ⊆ Icc (0 : ℝ) 1)
    (f : ℝ → ℝ) {a b x : ℝ} (ha : a ∈ C) (hb : b ∈ C)
    (gap : Disjoint C (Ioo a b)) (hx : x ∈ Ioo a b) :
    affineExtension C f x = affineBridge (affineExtension C f) a b x := by
  rw [affineExtension_on_gap rangeC f ha hb gap hx]
  simp only [affineBridge, affineExtension_of_mem compact h0 h1 rangeC f ha,
    affineExtension_of_mem compact h0 h1 rangeC f hb]

def retainedCoordinate (p : Bits n) (right : Bool) : ℚ :=
  if right then (retainedEndpoints p).2 else (retainedEndpoints p).1

/-- All interpolation nodes at a fixed retained level. -/
noncomputable def retainedLevelKnots (n : ℕ) : Set ℝ :=
  range fun p : Bits n × Bool => ((retainedCoordinate p.1 p.2 : ℚ) : ℝ)

private theorem retainedCoordinate_mem (p : Bits n) (right : Bool) :
    (retainedCoordinate p right : ℝ) ∈ retainedLevelKnots n := ⟨(p, right), rfl⟩

theorem retainedLevelKnots_finite (n : ℕ) : (retainedLevelKnots n).Finite :=
  finite_range _

theorem retainedCoordinate_mem_fatCantorSet (p : Bits n) (right : Bool) :
    (retainedCoordinate p right : ℝ) ∈ fatCantorSet :=
  ⟨extendRetained p right, fatAddress_extendRetained p right⟩

theorem retainedLevelKnots_subset_fatCantorSet (n : ℕ) :
    retainedLevelKnots n ⊆ fatCantorSet := by
  rintro x ⟨⟨p, right⟩, rfl⟩
  exact retainedCoordinate_mem_fatCantorSet p right

private theorem zero_mem_fatCantor : 0 ∈ fatCantorSet := by
  simpa [retainedCoordinate, retainedEndpoints, retainedLeftRat] using
    retainedCoordinate_mem_fatCantorSet (#v[] : Bits 0) false

private theorem one_mem_fatCantor : 1 ∈ fatCantorSet := by
  have endpoint := retainedCoordinate_mem_fatCantorSet (#v[] : Bits 0) true
  norm_num [retainedCoordinate, retainedEndpoints, retainedLeftRat, retainedLengthRat] at endpoint
  exact endpoint

private theorem fatCantor_mem_level {x : ℝ} (hx : x ∈ fatCantorSet) (n : ℕ) :
    ∃ p : Bits n, x ∈ retainedInterval p := by
  rw [fatCantorSet_levels] at hx
  exact mem_iUnion.mp (mem_iInter.mp hx n)

theorem zero_mem_retainedLevelKnots (n : ℕ) : 0 ∈ retainedLevelKnots n := by
  obtain ⟨p, hp⟩ := fatCantor_mem_level zero_mem_fatCantor n
  rw [retainedInterval_eq_Icc] at hp
  have ge := (fatCantorSet_subset_Icc (retainedCoordinate_mem_fatCantorSet p false)).1
  change 0 ≤ ((retainedEndpoints p).1 : ℝ) at ge
  have eq : ((retainedEndpoints p).1 : ℝ) = 0 := le_antisymm hp.1 ge
  exact ⟨(p, false), eq⟩

theorem one_mem_retainedLevelKnots (n : ℕ) : 1 ∈ retainedLevelKnots n := by
  obtain ⟨p, hp⟩ := fatCantor_mem_level one_mem_fatCantor n
  rw [retainedInterval_eq_Icc] at hp
  have le := (fatCantorSet_subset_Icc (retainedCoordinate_mem_fatCantorSet p true)).2
  change ((retainedEndpoints p).2 : ℝ) ≤ 1 at le
  exact ⟨(p, true), le_antisymm le hp.2⟩

def polygonInputDepth (schedule : Schedule) (k : ℕ) : ℕ :=
  outputWidth schedule k + (k + 1)

def retainedVertex (schedule : Schedule) (p : Bits n) (k : ℕ) (right : Bool) : ℚ × ℚ :=
  (retainedCoordinate p right, rationalEndpointValue schedule p right k)

/-- List of rational coordinates and rational approximations at the retained endpoints. -/
def rationalPolygonVertices (schedule : Schedule) (k : ℕ) : List (ℚ × ℚ) :=
  (wordsAtDepth (polygonInputDepth schedule k)).flatMap fun p =>
    [retainedVertex schedule p k false, retainedVertex schedule p k true]

noncomputable def polygonVertexValue (vertices : List (ℚ × ℚ)) (x : ℝ) : ℝ := by
  classical
  exact ((((vertices.find? fun v => decide ((v.1 : ℝ) = x)).map Prod.snd).getD 0 : ℚ) : ℝ)

/-- The real piecewise-affine interpolation of the finite rational vertex data,
with the endpoint constants used outside the unit interval. -/
noncomputable def rationalPolygon (schedule : Schedule) (k : ℕ) : ℝ → ℝ :=
  affineExtension (retainedLevelKnots (polygonInputDepth schedule k))
    (polygonVertexValue (rationalPolygonVertices schedule k))

private theorem polygonVertexValue_error_of_mem (schedule : Schedule) (k : ℕ) {x : ℝ}
    (hx : x ∈ retainedLevelKnots (polygonInputDepth schedule k)) :
    |realAffineExtension (cantorOutput schedule) x -
      polygonVertexValue (rationalPolygonVertices schedule k) x| ≤ ((2 : ℝ)^k)⁻¹ := by
  classical
  let vertices := rationalPolygonVertices schedule k
  let pred : ℚ × ℚ → Bool := fun v => decide ((v.1 : ℝ) = x)
  have has : (vertices.find? pred).isSome := by
    obtain ⟨⟨p, right⟩, heq⟩ := hx
    apply List.find?_isSome.mpr
    refine ⟨retainedVertex schedule p k right, ?_, by simpa [pred, retainedVertex] using heq⟩
    apply List.mem_flatMap.mpr
    exact ⟨p, mem_wordsAtDepth p, by cases right <;> simp⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp has
  have satisfies : pred v = true := List.find?_some hv
  have xEq : (v.1 : ℝ) = x := of_decide_eq_true satisfies
  have vmem := List.mem_of_find?_eq_some hv
  obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp vmem
  have cases : v = retainedVertex schedule p k false ∨ v = retainedVertex schedule p k true := by
    simpa using hp
  unfold polygonVertexValue
  change |realAffineExtension (cantorOutput schedule) x - (((vertices.find? pred).map Prod.snd).getD 0 : ℚ)| ≤ _
  rw [hv]
  rcases cases with rfl | rfl
  · rw [← xEq]
    exact rationalEndpointValue_error schedule p false k
  · rw [← xEq]
    exact rationalEndpointValue_error schedule p true k

private theorem realAffineExtension_cylinder_oscillation (schedule : Schedule) (k : ℕ)
    (p : Bits (polygonInputDepth schedule k)) {x y : ℝ} (hx : x ∈ fatCantorSet)
    (hy : y ∈ fatCantorSet) (xp : x ∈ retainedInterval p) (yp : y ∈ retainedInterval p) :
    |realAffineExtension (cantorOutput schedule) x - realAffineExtension (cantorOutput schedule) y| ≤
      ((2 : ℝ)^k)⁻¹ := by
  obtain ⟨xs, rfl⟩ := hx
  obtain ⟨ys, rfl⟩ := hy
  change xs ∈ fatAddress ⁻¹' retainedInterval p at xp
  change ys ∈ fatAddress ⁻¹' retainedInterval p at yp
  rw [fatAddress_preimage_retainedInterval] at xp yp
  have heq : readBits xs (polygonInputDepth schedule k) = readBits ys (polygonInputDepth schedule k) :=
    (show readBits xs _ = p from xp).trans (show readBits ys _ = p from yp).symm
  rw [realAffineExtension_fatAddress, realAffineExtension_fatAddress]
  exact binaryEvaluation_oscillation _ _ (cantorOutput_finite_precision schedule k _ _ heq)

private theorem realAffineExtension_retained_oscillation (schedule : Schedule) (k : ℕ)
    (p : Bits (polygonInputDepth schedule k)) {x y : ℝ} (hx : x ∈ retainedInterval p)
    (unit : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ fatCantorSet) (yp : y ∈ retainedInterval p) :
    |realAffineExtension (cantorOutput schedule) x - realAffineExtension (cantorOutput schedule) y| ≤
      ((2 : ℝ)^k)⁻¹ := by
  let g := realAffineExtension (cantorOutput schedule)
  have compact : IsCompact fatCantorSet := isCompact_range fatAddress_continuous
  change |g x - g y| ≤ _
  rw [retainedInterval_eq_Icc] at hx
  unfold g realAffineExtension
  apply affineExtension_abs_le_on_interval compact zero_mem_fatCantor one_mem_fatCantor
    (retainedCoordinate_mem_fatCantorSet p false) (retainedCoordinate_mem_fatCantorSet p true) hx unit
  intro z hz zp
  calc
    _ = |g z - g y| := by
      unfold g realAffineExtension
      rw [affineExtension_of_mem compact zero_mem_fatCantor one_mem_fatCantor fatCantorSet_subset_Icc _ hz]
    _ ≤ _ := realAffineExtension_cylinder_oscillation schedule k p hz hy
      ((retainedInterval_eq_Icc p).symm ▸ zp) yp

theorem outside_level_knots_gap (n : ℕ) {x : ℝ}
    (unit : x ∈ Icc (0 : ℝ) 1) (outside : ¬∃ p : Bits n, x ∈ retainedInterval p) :
    let K := retainedLevelKnots n
    x ∈ Ioo (lastPoint K x) (nextPoint K x) ∧
      Disjoint K (Ioo (lastPoint K x) (nextPoint K x)) ∧
      Disjoint fatCantorSet (Ioo (lastPoint K x) (nextPoint K x)) := by
  let K := retainedLevelKnots n
  let a := lastPoint K x
  let b := nextPoint K x
  have compact : IsCompact K := (retainedLevelKnots_finite n).isCompact
  have ha := polygon_lastPoint compact (zero_mem_retainedLevelKnots n) unit.1
  have hb := polygon_nextPoint compact (one_mem_retainedLevelKnots n) unit.2
  have noK : x ∉ K := by
    intro hx
    exact outside (fatCantor_mem_level (retainedLevelKnots_subset_fatCantorSet n hx) n)
  have between : x ∈ Ioo a b := by
    refine ⟨ha.1.2.lt_of_ne ?_, hb.1.2.lt_of_ne ?_⟩
    · intro eq
      exact noK (eq ▸ ha.1.1)
    · intro eq
      exact noK (eq.symm ▸ hb.1.1)
  have gap : Disjoint K (Ioo a b) := by
    refine disjoint_left.mpr fun y hy hbetween => ?_
    rcases le_total y x with h | h
    · exact hbetween.1.not_ge (ha.2 ⟨hy, h⟩)
    · exact hbetween.2.not_ge (hb.2 ⟨hy, h⟩)
  refine ⟨between, gap, disjoint_left.mpr fun y hy hyGap => ?_⟩
  obtain ⟨p, hp⟩ := fatCantor_mem_level hy n
  rw [retainedInterval_eq_Icc] at hp
  have leftK := retainedCoordinate_mem p false
  have rightK := retainedCoordinate_mem p true
  have lower : ((retainedEndpoints p).1 : ℝ) ≤ a := by
    by_contra! lt
    apply disjoint_left.mp gap leftK
    exact ⟨lt, hp.1.trans_lt hyGap.2⟩
  have upper : b ≤ ((retainedEndpoints p).2 : ℝ) := by
    by_contra! lt
    apply disjoint_left.mp gap rightK
    exact ⟨hyGap.1.trans_le hp.2, lt⟩
  apply outside
  refine ⟨p, ?_⟩
  rw [retainedInterval_eq_Icc]
  exact ⟨lower.trans between.1.le, between.2.le.trans upper⟩

/-- The rational vertex data of the paper gives an approximation on the entire real line. -/
theorem rationalPolygon_uniform_error (schedule : Schedule) (k : ℕ) (x : ℝ) :
    |realAffineExtension (cantorOutput schedule) x - rationalPolygon schedule k x| ≤
      2 * ((2 : ℝ)^k)⁻¹ := by
  let C := fatCantorSet
  let n := polygonInputDepth schedule k
  let K := retainedLevelKnots n
  let δ := ((2 : ℝ)^k)⁻¹
  let values := polygonVertexValue (rationalPolygonVertices schedule k)
  let g := realAffineExtension (cantorOutput schedule)
  let z := max 0 (min x 1)
  have unit : z ∈ Icc (0 : ℝ) 1 := polygon_projection_mem x
  have cC : IsCompact C := isCompact_range fatAddress_continuous
  have cK : IsCompact K := (retainedLevelKnots_finite n).isCompact
  have k0 : 0 ∈ K := zero_mem_retainedLevelKnots n
  have k1 : 1 ∈ K := one_mem_retainedLevelKnots n
  have included : K ⊆ C := retainedLevelKnots_subset_fatCantorSet n
  have approx (y : ℝ) (hy : y ∈ K) : |g y - values y| ≤ δ :=
    polygonVertexValue_error_of_mem schedule k hy
  have gz : g x = g z := by
    unfold g realAffineExtension
    exact polygon_affine_at_projection _ _ x
  rw [show realAffineExtension (cantorOutput schedule) x = g z from gz]
  rw [show rationalPolygon schedule k x = affineExtension K values z from polygon_affine_at_projection _ _ x]
  change |g z - affineExtension K values z| ≤ 2 * δ
  by_cases inside : ∃ p : Bits n, z ∈ retainedInterval p
  · obtain ⟨p, hp⟩ := inside
    have hx := hp
    rw [retainedInterval_eq_Icc] at hx
    rw [abs_sub_comm]
    apply affineExtension_abs_le_on_interval cK k0 k1 (retainedCoordinate_mem p false)
      (retainedCoordinate_mem p true) hx unit
    intro y hy yp
    have yp' : y ∈ retainedInterval p := (retainedInterval_eq_Icc p).symm ▸ yp
    have osc := realAffineExtension_retained_oscillation schedule k p hp unit (included hy) yp'
    have err : |values y - g y| ≤ δ := by rw [abs_sub_comm]; exact approx y hy
    have delta : |g y - g z| ≤ δ := by rw [abs_sub_comm]; exact osc
    calc
      _ ≤ |values y - g y| + |g y - g z| := by
        simpa only [sub_add_sub_cancel] using abs_add_le (values y - g y) (g y - g z)
      _ ≤ δ + δ := add_le_add err delta
      _ = 2 * δ := by ring
  · obtain ⟨point, gapK, gapC⟩ := outside_level_knots_gap n unit inside
    let a := lastPoint K z
    let b := nextPoint K z
    have ha : a ∈ K := (polygon_lastPoint cK k0 unit.1).1.1
    have hb : b ∈ K := (polygon_nextPoint cK k1 unit.2).1.1
    have unitK : K ⊆ Icc (0 : ℝ) 1 := included.trans fatCantorSet_subset_Icc
    have eq : g z = affineBridge g a b z := by
      unfold g realAffineExtension
      exact affineExtension_on_gap_with_own_values cC zero_mem_fatCantor one_mem_fatCantor
        fatCantorSet_subset_Icc _ (included ha) (included hb) gapC point
    rw [eq, affineExtension_on_gap unitK values ha hb gapK point]
    have bound : |affineBridge g a b z - affineBridge values a b z| ≤ δ :=
      affineBridge_error g values (point.1.trans point.2) ⟨point.1.le, point.2.le⟩ (approx a ha) (approx b hb)
    have nonnegative : 0 ≤ δ := by positivity
    exact bound.trans (by linarith)

/-- Interpret rational vertex data as a real piecewise-affine map. -/
noncomputable def realPolygonOfVertices (vertices : List (ℚ × ℚ)) : ℝ → ℝ :=
  affineExtension {x | ∃ v ∈ vertices, (v.1 : ℝ) = x} (polygonVertexValue vertices)

theorem rationalPolygon_of_vertices (schedule : Schedule) (k : ℕ) :
    realPolygonOfVertices (rationalPolygonVertices schedule k) = rationalPolygon schedule k := by
  unfold realPolygonOfVertices rationalPolygon
  congr 1
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hv
    have cases : v = retainedVertex schedule p k false ∨ v = retainedVertex schedule p k true := by
      simpa using hp
    rcases cases with rfl | rfl
    · exact retainedCoordinate_mem p false
    · exact retainedCoordinate_mem p true
  · rintro ⟨⟨p, right⟩, rfl⟩
    refine ⟨retainedVertex schedule p k right, List.mem_flatMap.mpr ?_, rfl⟩
    exact ⟨p, mem_wordsAtDepth p, by cases right <;> simp⟩

end Guo

#print axioms Guo.rationalPolygon_uniform_error
