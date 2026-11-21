import Weak_3_Randomness_and_Luzin_N.GuoPolygon

open Set
open scoped NNReal

namespace Guo

private theorem bridge_weight_mem {x a b : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    (x - a) / (b - a) ∈ Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hab).le, ?_⟩
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  simpa using sub_le_sub_right hx.2 a

private theorem extendOnUnit_bounded {C : Set ℝ} (compact : IsCompact C) (h0 : 0 ∈ C)
    (h1 : 1 ∈ C) {f : ℝ → ℝ} (mono : MonotoneOn f C)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    extendOnUnit C f x ∈ Icc (f (lastPoint C x)) (f (nextPoint C x)) := by
  let a := lastPoint C x
  let b := nextPoint C x
  have ha := polygon_lastPoint compact h0 hx.1
  have hb := polygon_nextPoint compact h1 hx.2
  have ab : a ≤ b := ha.1.2.trans hb.1.2
  have fab : f a ≤ f b := mono ha.1.1 hb.1.1 ab
  by_cases e : a = b
  · change (if a = b then f a else affineBridge f a b x) ∈ Icc (f a) (f b)
    simpa only [e, if_true] using (show f b ∈ Icc (f b) (f b) from ⟨le_rfl, le_rfl⟩)
  · let w := (x - a) / (b - a)
    have wt : w ∈ Icc (0 : ℝ) 1 := bridge_weight_mem (ab.lt_of_ne e) ⟨ha.1.2, hb.1.2⟩
    change (if a = b then f a else (1 - w) * f a + w * f b) ∈ Icc (f a) (f b)
    rw [if_neg e]
    exact ⟨by nlinarith [mul_nonneg wt.1 (sub_nonneg.mpr fab)],
      by nlinarith [mul_nonneg (sub_nonneg.mpr wt.2) (sub_nonneg.mpr fab)]⟩

private theorem extendOnUnit_monotone {C : Set ℝ} (compact : IsCompact C) (h0 : 0 ∈ C)
    (h1 : 1 ∈ C) {f : ℝ → ℝ} (mono : MonotoneOn f C) :
    MonotoneOn (extendOnUnit C f) (Icc (0 : ℝ) 1) := by
  intro x hx y hy xy
  let a := lastPoint C x
  let b := nextPoint C x
  let c := lastPoint C y
  let d := nextPoint C y
  have ha := polygon_lastPoint compact h0 hx.1
  have hb := polygon_nextPoint compact h1 hx.2
  have hc := polygon_lastPoint compact h0 hy.1
  have hd := polygon_nextPoint compact h1 hy.2
  by_cases inside : ∃ t ∈ C, t ∈ Icc x y
  · obtain ⟨t, ht, htx, hty⟩ := inside
    have bc : b ≤ c := (hb.2 ⟨ht, htx⟩).trans (hc.2 ⟨ht, hty⟩)
    have left := (extendOnUnit_bounded compact h0 h1 mono hx).2
    have right := (extendOnUnit_bounded compact h0 h1 mono hy).1
    exact left.trans ((mono hb.1.1 hc.1.1 bc).trans right)
  · have cx : c ≤ x := by
      by_contra! xc
      exact inside ⟨c, hc.1.1, xc.le, hc.1.2⟩
    have yb : y ≤ b := by
      by_contra! by'
      exact inside ⟨b, hb.1.1, hb.1.2, by'.le⟩
    have ac : a = c := le_antisymm (hc.2 ⟨ha.1.1, ha.1.2.trans xy⟩) (ha.2 ⟨hc.1.1, cx⟩)
    have bd : b = d := le_antisymm (hb.2 ⟨hd.1.1, xy.trans hd.1.2⟩) (hd.2 ⟨hb.1.1, yb⟩)
    change (if a = b then f a else affineBridge f a b x) ≤
      (if c = d then f c else affineBridge f c d y)
    rw [← ac, ← bd]
    by_cases e : a = b
    · simp only [if_pos e, le_refl]
    · rw [if_neg e, if_neg e]
      have ab : a < b := (ha.1.2.trans hb.1.2).lt_of_ne e
      have slope : f a ≤ f b := mono ha.1.1 hb.1.1 ab.le
      have weights : (x - a) / (b - a) ≤ (y - a) / (b - a) :=
        div_le_div_of_nonneg_right (sub_le_sub_right xy a) (sub_nonneg.mpr ab.le)
      unfold affineBridge
      nlinarith [mul_nonneg (sub_nonneg.mpr weights) (sub_nonneg.mpr slope)]

private theorem extendOnUnit_linear {C : Set ℝ} (compact : IsCompact C) (h0 : 0 ∈ C)
    (h1 : 1 ∈ C) (f : ℝ → ℝ) (r s : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    extendOnUnit C (fun t => r * t + s * f t) x = r * x + s * extendOnUnit C f x := by
  let a := lastPoint C x
  let b := nextPoint C x
  have ax : a ≤ x := (polygon_lastPoint compact h0 hx.1).1.2
  have xb : x ≤ b := (polygon_nextPoint compact h1 hx.2).1.2
  change (if a = b then r * a + s * f a else affineBridge (fun t => r * t + s * f t) a b x) =
    r * x + s * (if a = b then f a else affineBridge f a b x)
  by_cases e : a = b
  · simp only [if_pos e]
    rw [le_antisymm ax (e.symm ▸ xb)]
  · simp only [if_neg e, affineBridge]
    field_simp [sub_ne_zero.mpr (Ne.symm e)]
    ring

/-- Linear interpolation and clamping do not increase a Lipschitz constant. -/
theorem affineExtension_lipschitz {C : Set ℝ} (compact : IsCompact C) (h0 : 0 ∈ C) (h1 : 1 ∈ C)
    {f : ℝ → ℝ} {K : ℝ≥0} (h : LipschitzOnWith K f C) : LipschitzWith K (affineExtension C f) := by
  let r : ℝ := K
  have clamp : LipschitzWith 1 (fun x : ℝ => max 0 (min x 1)) :=
    (LipschitzWith.id.min_const 1).const_max 0
  have plus : MonotoneOn (fun x => r * x + 1 * f x) C := by
    intro x hx y hy xy
    have bound := h.dist_le_mul x hx y hy
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr xy)] at bound
    change |f x - f y| ≤ r * -(x - y) at bound
    linarith [(abs_le.mp bound).2]
  have minus : MonotoneOn (fun x => r * x + (-1) * f x) C := by
    intro x hx y hy xy
    have bound := h.dist_le_mul x hx y hy
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr xy)] at bound
    change |f x - f y| ≤ r * -(x - y) at bound
    linarith [(abs_le.mp bound).1]
  have onUnit : LipschitzOnWith K (extendOnUnit C f) (Icc (0 : ℝ) 1) := by
    refine LipschitzOnWith.of_le_add_mul K ?_
    intro x hx y hy
    rcases le_total x y with xy | yx
    · have up := extendOnUnit_monotone compact h0 h1 plus hx hy xy
      rw [extendOnUnit_linear compact h0 h1 f r 1 hx,
        extendOnUnit_linear compact h0 h1 f r 1 hy] at up
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr xy)]
      change extendOnUnit C f x ≤ extendOnUnit C f y + r * -(x - y)
      linarith only [up]
    · have down := extendOnUnit_monotone compact h0 h1 minus hy hx yx
      rw [extendOnUnit_linear compact h0 h1 f r (-1) hy,
        extendOnUnit_linear compact h0 h1 f r (-1) hx] at down
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr yx)]
      change extendOnUnit C f x ≤ extendOnUnit C f y + r * (x - y)
      linarith only [down]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (onUnit.dist_le_mul _ (polygon_projection_mem x) _ (polygon_projection_mem y)).trans
    (mul_le_mul_of_nonneg_left (by simpa using clamp.dist_le_mul x y) K.2)

end Guo

#print axioms Guo.affineExtension_lipschitz
