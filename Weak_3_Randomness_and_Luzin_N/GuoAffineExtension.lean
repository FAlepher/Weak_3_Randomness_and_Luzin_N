import Weak_3_Randomness_and_Luzin_N.GuoFatCantor
import Weak_3_Randomness_and_Luzin_N.GuoBinaryMeasure
import Weak_3_Randomness_and_Luzin_N.GuoLocalization

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace Guo

noncomputable def lastPoint (C : Set ℝ) (x : ℝ) : ℝ := sSup (C ∩ Iic x)
noncomputable def nextPoint (C : Set ℝ) (x : ℝ) : ℝ := sInf (C ∩ Ici x)

noncomputable def affineBridge (f : ℝ → ℝ) (left right x : ℝ) : ℝ :=
  let weight := (x - left) / (right - left)
  (1 - weight) * f left + weight * f right

noncomputable def extendOnUnit (C : Set ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  let left := lastPoint C x
  let right := nextPoint C x
  if left = right then f left else affineBridge f left right x

/-- Extend affinely across the gaps and constantly on the exterior rays. -/
noncomputable def affineExtension (C : Set ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  extendOnUnit C f (max 0 (min x 1))

private theorem lastPoint_greatest {C : Set ℝ} (compact : IsCompact C) (h0 : 0 ∈ C)
    {x : ℝ} (hx : 0 ≤ x) : IsGreatest (C ∩ Iic x) (lastPoint C x) :=
  (compact.inter_right isClosed_Iic).isGreatest_sSup ⟨0, h0, hx⟩

private theorem nextPoint_least {C : Set ℝ} (compact : IsCompact C) (h1 : 1 ∈ C)
    {x : ℝ} (hx : x ≤ 1) : IsLeast (C ∩ Ici x) (nextPoint C x) :=
  (compact.inter_right isClosed_Ici).isLeast_sInf ⟨1, h1, hx⟩

private theorem gap_empty {C : Set ℝ} (compact : IsCompact C) (h0 : 0 ∈ C) (h1 : 1 ∈ C)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : Disjoint C (Ioo (lastPoint C x) (nextPoint C x)) := by
  refine disjoint_left.mpr fun y hy bounds => ?_
  rcases le_total y x with lo | hi
  · exact (not_le_of_gt bounds.1) ((lastPoint_greatest compact h0 hx.1).2 ⟨hy, lo⟩)
  · exact (not_le_of_gt bounds.2) ((nextPoint_least compact h1 hx.2).2 ⟨hy, hi⟩)

private theorem extendOnUnit_of_mem {C : Set ℝ} (compact : IsCompact C) (h0 : 0 ∈ C)
    (h1 : 1 ∈ C) {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hxC : x ∈ C) :
    extendOnUnit C f x = f x := by
  have lo := lastPoint_greatest compact h0 hx.1
  have hi := nextPoint_least compact h1 hx.2
  have loEq : lastPoint C x = x := le_antisymm lo.1.2 (lo.2 ⟨hxC, mem_Iic.mpr le_rfl⟩)
  have hiEq : nextPoint C x = x := le_antisymm (hi.2 ⟨hxC, mem_Ici.mpr le_rfl⟩) hi.1.2
  simp [extendOnUnit, loEq, hiEq]

private theorem clamp_eq {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : max 0 (min x 1) = x := by
  rw [min_eq_left hx.2, max_eq_right hx.1]

theorem affineExtension_of_mem {C : Set ℝ} (compact : IsCompact C) (h0 : 0 ∈ C)
    (h1 : 1 ∈ C) (rangeC : C ⊆ Icc (0 : ℝ) 1) (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ C) :
    affineExtension C f x = f x := by
  rw [affineExtension, clamp_eq (rangeC hx)]
  exact extendOnUnit_of_mem compact h0 h1 (rangeC hx) hx

theorem affineExtension_on_gap {C : Set ℝ} (rangeC : C ⊆ Icc (0 : ℝ) 1)
    (f : ℝ → ℝ) {a b x : ℝ} (ha : a ∈ C) (hb : b ∈ C) (gap : Disjoint C (Ioo a b))
    (hx : x ∈ Ioo a b) : affineExtension C f x = affineBridge f a b x := by
  have xmin : 0 ≤ x := (rangeC ha).1.trans hx.1.le
  have xmax : x ≤ 1 := hx.2.le.trans (rangeC hb).2
  have lo : IsGreatest (C ∩ Iic x) a := by
    refine ⟨⟨ha, hx.1.le⟩, fun y hy => ?_⟩
    by_contra! h
    exact disjoint_left.mp gap hy.1 ⟨h, hy.2.trans_lt hx.2⟩
  have hi : IsLeast (C ∩ Ici x) b := by
    refine ⟨⟨hb, hx.2.le⟩, fun y hy => ?_⟩
    by_contra! h
    exact disjoint_left.mp gap hy.1 ⟨hx.1.trans_le hy.2, h⟩
  have loEq : lastPoint C x = a := lo.csSup_eq
  have hiEq : nextPoint C x = b := hi.csInf_eq
  rw [affineExtension, clamp_eq ⟨xmin, xmax⟩]
  simp [extendOnUnit, loEq, hiEq, (hx.1.trans hx.2).ne]

private theorem clamp_mem (x : ℝ) : max 0 (min x 1) ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

theorem affineExtension_mem_Icc {C : Set ℝ} (compact : IsCompact C) (h0 : 0 ∈ C) (h1 : 1 ∈ C)
    {f : ℝ → ℝ} (hf : MapsTo f C (Icc (0 : ℝ) 1)) (x : ℝ) :
    affineExtension C f x ∈ Icc (0 : ℝ) 1 := by
  let z := max 0 (min x 1)
  let a := lastPoint C z
  let b := nextPoint C z
  have lo := (lastPoint_greatest compact h0 (clamp_mem x).1).1
  have hi := (nextPoint_least compact h1 (clamp_mem x).2).1
  change a ∈ C ∧ a ≤ z at lo
  change b ∈ C ∧ z ≤ b at hi
  change extendOnUnit C f z ∈ Icc (0 : ℝ) 1
  by_cases e : a = b
  · change (if a = b then f a else affineBridge f a b z) ∈ Icc (0 : ℝ) 1
    rw [if_pos e]
    exact hf lo.1
  · have aLtB : a < b := (lo.2.trans hi.2).lt_of_ne e
    let w := (z - a) / (b - a)
    have w0 : 0 ≤ w := div_nonneg (sub_nonneg.mpr lo.2) (sub_pos.mpr aLtB).le
    have w1 : w ≤ 1 := (div_le_iff₀ (sub_pos.mpr aLtB)).mpr (by linarith [hi.2])
    have ha := hf lo.1
    have hb := hf hi.1
    change (if a = b then f a else (1 - w) * f a + w * f b) ∈ Icc (0 : ℝ) 1
    rw [if_neg e]
    exact ⟨add_nonneg (mul_nonneg (by linarith) ha.1) (mul_nonneg w0 hb.1), by
      nlinarith [mul_le_mul_of_nonneg_left ha.2 (sub_nonneg.mpr w1),
        mul_le_mul_of_nonneg_left hb.2 w0]⟩

theorem affineExtension_continuous {C : Set ℝ} (compact : IsCompact C) (h0 : 0 ∈ C) (h1 : 1 ∈ C)
    (rangeC : C ⊆ Icc (0 : ℝ) 1) {f : ℝ → ℝ} (hf : MapsTo f C (Icc (0 : ℝ) 1))
    (hfCont : ContinuousOn f C) : Continuous (affineExtension C f) := by
  have onUnit : ContinuousOn (extendOnUnit C f) (Icc (0 : ℝ) 1) := by
    intro x hx
    by_cases hxC : x ∈ C
    · rw [Metric.continuousWithinAt_iff]
      intro ε εpos
      obtain ⟨δ, δpos, near⟩ := Metric.continuousWithinAt_iff.mp (hfCont x hxC) (ε / 2) (by linarith)
      have modulus (z : ℝ) (hz : z ∈ C) : |f z - f x| ≤ ε / 2 + |z - x| / δ := by
        by_cases h : |z - x| < δ
        · have h' := near hz (by simpa only [Real.dist_eq] using h)
          rw [Real.dist_eq] at h'
          exact h'.le.trans (le_add_of_nonneg_right (div_nonneg (abs_nonneg _) δpos.le))
        · have h' : |f z - f x| ≤ 1 := by
            have hz' := hf hz
            have hx' := hf hxC
            exact abs_le.mpr ⟨by linarith [hz'.1, hx'.2], by linarith [hz'.2, hx'.1]⟩
          have one : 1 ≤ |z - x| / δ := (le_div_iff₀ δpos).mpr (by simpa using le_of_not_gt h)
          linarith
      refine ⟨δ * (ε / 2), mul_pos δpos (by linarith), ?_⟩
      intro y hy distSmall
      rw [Real.dist_eq, extendOnUnit_of_mem compact h0 h1 hx hxC]
      rw [Real.dist_eq] at distSmall
      have small : |y - x| / δ < ε / 2 := (div_lt_iff₀ δpos).mpr (by linarith)
      let a := lastPoint C y
      let b := nextPoint C y
      have pa := lastPoint_greatest compact h0 hy.1
      have pb := nextPoint_least compact h1 hy.2
      have ha : a ≤ y := pa.1.2
      have hb : y ≤ b := pb.1.2
      have am := modulus a pa.1.1
      have bm := modulus b pb.1.1
      by_cases eq : a = b
      · have ay : a = y := le_antisymm ha (eq ▸ hb)
        change |(if a = b then f a else affineBridge f a b y) - f x| < ε
        rw [if_pos eq, ay]
        rw [ay] at am
        linarith
      · have lt : a < b := (ha.trans hb).lt_of_ne eq
        let w := (y - a) / (b - a)
        have w0 : 0 ≤ w := div_nonneg (sub_nonneg.mpr ha) (sub_pos.mpr lt).le
        have w1 : w ≤ 1 := (div_le_iff₀ (sub_pos.mpr lt)).mpr (by linarith)
        have yEq : (1 - w) * a + w * b = y := by
          rw [show (1 - w) * a + w * b = a + w * (b - a) by ring]
          dsimp only [w]
          field_simp [sub_ne_zero.mpr (ne_of_gt lt)]
          ring
        have distEq : (1 - w) * |a - x| + w * |b - x| = |y - x| := by
          rcases le_total x y with xy | yx
          · have xa : x ≤ a := pa.2 ⟨hxC, xy⟩
            rw [abs_of_nonneg (sub_nonneg.mpr xa), abs_of_nonneg (sub_nonneg.mpr (xa.trans (ha.trans hb))),
              abs_of_nonneg (sub_nonneg.mpr xy)]
            linarith [yEq]
          · have bx : b ≤ x := pb.2 ⟨hxC, yx⟩
            rw [abs_of_nonpos (sub_nonpos.mpr ((ha.trans hb).trans bx)),
              abs_of_nonpos (sub_nonpos.mpr bx), abs_of_nonpos (sub_nonpos.mpr yx)]
            linarith [yEq]
        change |(if a = b then f a else (1 - w) * f a + w * f b) - f x| < ε
        rw [if_neg eq, show (1 - w) * f a + w * f b - f x =
          (1 - w) * (f a - f x) + w * (f b - f x) by ring]
        calc
          _ ≤ (1 - w) * |f a - f x| + w * |f b - f x| := by
            simpa only [abs_mul, abs_of_nonneg (sub_nonneg.mpr w1), abs_of_nonneg w0] using
              abs_add_le ((1 - w) * (f a - f x)) (w * (f b - f x))
          _ ≤ (1 - w) * (ε / 2 + |a - x| / δ) + w * (ε / 2 + |b - x| / δ) :=
            add_le_add (mul_le_mul_of_nonneg_left am (sub_nonneg.mpr w1))
              (mul_le_mul_of_nonneg_left bm w0)
          _ = ε / 2 + |y - x| / δ := by
            rw [← distEq]
            ring
          _ < ε := by linarith
    · let a := lastPoint C x
      let b := nextPoint C x
      have pa := (lastPoint_greatest compact h0 hx.1).1
      have pb := (nextPoint_least compact h1 hx.2).1
      have xGap : x ∈ Ioo a b := by
        refine ⟨pa.2.lt_of_ne ?_, pb.2.lt_of_ne ?_⟩
        · intro eq
          exact hxC (eq ▸ pa.1)
        · intro eq
          exact hxC (eq.symm ▸ pb.1)
      have hbridge : Continuous (affineBridge f a b) := by unfold affineBridge; fun_prop
      have eqOn (y : ℝ) (hy : y ∈ Ioo a b) : extendOnUnit C f y = affineBridge f a b y := by
        have hy' : y ∈ Icc (0 : ℝ) 1 :=
          ⟨(rangeC pa.1).1.trans hy.1.le, hy.2.le.trans (rangeC pb.1).2⟩
        simpa only [affineExtension, clamp_eq hy'] using
          affineExtension_on_gap rangeC f pa.1 pb.1 (gap_empty compact h0 h1 hx) hy
      have eventuallyEq : extendOnUnit C f =ᶠ[𝓝 x] affineBridge f a b :=
        mem_of_superset (isOpen_Ioo.mem_nhds xGap) eqOn
      exact (hbridge.continuousAt.congr_of_eventuallyEq eventuallyEq).continuousWithinAt
  exact onUnit.comp_continuous (continuous_const.max (continuous_id.min continuous_const)) clamp_mem

theorem affineExtension_on_left_ray (C : Set ℝ) (f : ℝ → ℝ) {x : ℝ} (hx : x ≤ 0) :
    affineExtension C f x = affineExtension C f 0 := by
  have clamp : max (0 : ℝ) (min x 1) = 0 :=
    max_eq_left ((min_le_left x 1).trans hx)
  simp [affineExtension, clamp]

theorem affineExtension_on_right_ray (C : Set ℝ) (f : ℝ → ℝ) {x : ℝ} (hx : 1 ≤ x) :
    affineExtension C f x = affineExtension C f 1 := by
  have clamp : max (0 : ℝ) (min x 1) = 1 := by rw [min_eq_right hx]; norm_num
  simp [affineExtension, clamp]

private theorem zero_mem_fatCantorSet : 0 ∈ fatCantorSet := by
  refine ⟨extendRetained (#v[] : Bits 0) false, ?_⟩
  rw [fatAddress_extendRetained]
  norm_num [retainedEndpoints, retainedLeftRat]

private theorem one_mem_fatCantorSet : 1 ∈ fatCantorSet := by
  refine ⟨extendRetained (#v[] : Bits 0) true, ?_⟩
  rw [fatAddress_extendRetained]
  norm_num [retainedEndpoints, retainedLeftRat, retainedLengthRat]

private noncomputable def realTrace (F : Cantor → Cantor) (x : ℝ) : ℝ := by
  classical
  exact if hx : x ∈ fatCantorSet then binaryEvaluation (F (fatCantorHomeomorph.symm ⟨x, hx⟩)) else 0

private theorem realTrace_values (F : Cantor → Cantor) :
    MapsTo (realTrace F) fatCantorSet (Icc (0 : ℝ) 1) := by
  intro x hx
  simp only [realTrace, dif_pos hx]
  exact binaryEvaluation_mem_Icc _

private theorem realTrace_continuousOn {F : Cantor → Cantor} (hF : Continuous F) :
    ContinuousOn (realTrace F) fatCantorSet := by
  rw [continuousOn_iff_continuous_restrict]
  have h := binaryEvaluation_continuous.comp (hF.comp fatCantorHomeomorph.symm.continuous)
  convert h using 2
  funext x
  simp [Set.restrict, realTrace, x.property, Function.comp_def]

/-- The real function prescribed by the paper from a given Cantor-space map. -/
noncomputable def realAffineExtension (F : Cantor → Cantor) : ℝ → ℝ :=
  affineExtension fatCantorSet (realTrace F)

theorem realAffineExtension_continuous {F : Cantor → Cantor} (hF : Continuous F) :
    Continuous (realAffineExtension F) :=
  affineExtension_continuous (isCompact_range fatAddress_continuous) zero_mem_fatCantorSet
    one_mem_fatCantorSet fatCantorSet_subset_Icc (realTrace_values F) (realTrace_continuousOn hF)

theorem realAffineExtension_mem_Icc (F : Cantor → Cantor) (x : ℝ) :
    realAffineExtension F x ∈ Icc (0 : ℝ) 1 :=
  affineExtension_mem_Icc (isCompact_range fatAddress_continuous) zero_mem_fatCantorSet
    one_mem_fatCantorSet (realTrace_values F) x

theorem realAffineExtension_fatAddress (F : Cantor → Cantor) (x : Cantor) :
    realAffineExtension F (fatAddress x) = binaryEvaluation (F x) := by
  have hx : fatAddress x ∈ fatCantorSet := ⟨x, rfl⟩
  rw [realAffineExtension, affineExtension_of_mem (C := fatCantorSet) (isCompact_range fatAddress_continuous)
    zero_mem_fatCantorSet one_mem_fatCantorSet fatCantorSet_subset_Icc _ hx]
  simp only [realTrace, dif_pos hx]
  change binaryEvaluation (F (fatCantorHomeomorph.symm (fatCantorHomeomorph x))) = _
  rw [fatCantorHomeomorph.symm_apply_apply]

/-- At every point outside the fat Cantor set the extension agrees locally with an affine map. -/
theorem realAffineExtension_locally_affine (F : Cantor → Cantor) {x : ℝ}
    (hx : x ∉ fatCantorSet) :
    ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ ∃ a d : ℝ, ∀ y ∈ U, realAffineExtension F y = a * y + d := by
  by_cases h0 : x < 0
  · refine ⟨Iio 0, isOpen_Iio, h0, 0, realAffineExtension F 0, fun y hy => ?_⟩
    simpa [realAffineExtension] using
      affineExtension_on_left_ray fatCantorSet (realTrace F) (mem_Iio.mp hy).le
  · by_cases h1 : 1 < x
    · refine ⟨Ioi 1, isOpen_Ioi, h1, 0, realAffineExtension F 1, fun y hy => ?_⟩
      simpa [realAffineExtension] using
        affineExtension_on_right_ray fatCantorSet (realTrace F) (mem_Ioi.mp hy).le
    · have unit : x ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_gt h0, le_of_not_gt h1⟩
      have c : IsCompact fatCantorSet := isCompact_range fatAddress_continuous
      let l := lastPoint fatCantorSet x
      let r := nextPoint fatCantorSet x
      have lo := (lastPoint_greatest c zero_mem_fatCantorSet unit.1).1
      have hi := (nextPoint_least c one_mem_fatCantorSet unit.2).1
      have xGap : x ∈ Ioo l r := by
        refine ⟨lo.2.lt_of_ne ?_, hi.2.lt_of_ne ?_⟩
        · intro eq
          exact hx (eq ▸ lo.1)
        · intro eq
          exact hx (eq.symm ▸ hi.1)
      let a := (realTrace F r - realTrace F l) / (r - l)
      refine ⟨Ioo l r, isOpen_Ioo, xGap, a, realTrace F l - a * l, fun y hy => ?_⟩
      rw [realAffineExtension, affineExtension_on_gap fatCantorSet_subset_Icc (realTrace F) lo.1 hi.1
        (gap_empty c zero_mem_fatCantorSet one_mem_fatCantorSet unit) hy]
      change affineBridge (realTrace F) l r y = a * y + (realTrace F l - a * l)
      dsimp only [affineBridge, a]
      field_simp [sub_ne_zero.mpr (ne_of_gt (xGap.1.trans xGap.2))]
      ring

/-- An explicit input precision for the first `k` output bits. -/
theorem cantorOutput_finite_precision (schedule : Schedule) (k : ℕ) (x y : Cantor)
    (h : readBits x (outputWidth schedule k + (k + 1)) =
      readBits y (outputWidth schedule k + (k + 1))) :
    readBits (cantorOutput schedule x) k = readBits (cantorOutput schedule y) k := by
  have length : k ≤ outputWidth schedule k := (Nat.le_succ k).trans (outputWidth_ge schedule k)
  have full : readBits (cantorOutput schedule x) (outputWidth schedule k) =
      readBits (cantorOutput schedule y) (outputWidth schedule k) := by
    rw [cantorOutput_reads, cantorOutput_reads]
    exact congrArg (fun p => ((stagedCode schedule k).encode p).1) h
  simpa only [takePrefix_readBits] using congrArg (fun p => takePrefix p k length) full

/-- A rational approximation to the prescribed real value at a retained interval endpoint. -/
def rationalEndpointValue (schedule : Schedule) (p : Bits n) (right : Bool) (k : ℕ) : ℚ :=
  (binaryPrefixIndex (cantorOutput schedule (extendRetained p right)) k : ℚ) / (2 : ℚ)^k

theorem rationalEndpointValue_error (schedule : Schedule) (p : Bits n) (right : Bool) (k : ℕ) :
    |realAffineExtension (cantorOutput schedule)
      ((if right then (retainedEndpoints p).2 else (retainedEndpoints p).1 : ℚ) : ℝ) -
      (rationalEndpointValue schedule p right k : ℝ)| ≤ ((2 : ℝ)^k)⁻¹ := by
  rw [← fatAddress_extendRetained, realAffineExtension_fatAddress]
  let s := cantorOutput schedule (extendRetained p right)
  let tail := binaryEvaluation (fun j => s (j + k))
  have scaled : (2 : ℝ)^k * binaryEvaluation s = (binaryPrefixIndex s k : ℝ) + tail :=
    binaryEvaluation_scaled s k
  have rangeTail : tail ∈ Icc (0 : ℝ) 1 := binaryEvaluation_mem_Icc _
  have bound : 0 < (2 : ℝ)^k := by positivity
  have approximate : (rationalEndpointValue schedule p right k : ℝ) =
      (binaryPrefixIndex s k : ℝ) / (2 : ℝ)^k := by
    simp [rationalEndpointValue, s]
  change |binaryEvaluation s - (rationalEndpointValue schedule p right k : ℝ)| ≤ _
  rw [approximate, show binaryEvaluation s - (binaryPrefixIndex s k : ℝ) / (2 : ℝ)^k =
      tail / (2 : ℝ)^k from (eq_div_iff bound.ne').mpr (by
        rw [sub_mul, div_mul_cancel₀ _ bound.ne']
        linarith [scaled])]
  rw [abs_of_nonneg (div_nonneg rangeTail.1 bound.le), inv_eq_one_div]
  exact div_le_div_of_nonneg_right rangeTail.2 bound.le

/-- The actual extension sends a compact null witness in Cantor space to one on the real line. -/
theorem realAffineExtension_compact_witness {F : Cantor → Cantor} (hF : Continuous F)
    {D : Set Cantor} (hD : IsCompact D) (hNull : fairCoin D = 0) :
    ∃ B : Set ℝ, B ⊆ Icc 0 1 ∧ IsCompact B ∧ volume B = 0 ∧
      fairCoin (F '' D) ≤ volume (realAffineExtension F '' B) :=
  real_compact_witness_of_pushforwards F fatAddress binaryEvaluation (realAffineExtension F)
    fatCantorSet fatAddress_continuous fatAddress_injective Subset.rfl fatCantorSet_subset_Icc
    binaryEvaluation_continuous hF fatAddress_map_fairCoin binaryEvaluation_map_fairCoin
    (realAffineExtension_fatAddress F) D hD hNull

/-- The concrete real extension has a compact null image witness at least as large as the input class. -/
theorem real_candidate_witness (C : CandidateWords) (A : Set Cantor) (hA : IsCompact A)
    (form : Aᶜ = {x : Cantor | ∃ i, cylinder (C.word i) x ∧ ∀ n, ∃ b, C.witness i n b = true}) :
    let g := realAffineExtension (cantorOutput (candidateSchedule pairedReservation C))
    Continuous g ∧ (∀ x, g x ∈ Icc 0 1) ∧
      ∃ B : Set ℝ, B ⊆ Icc 0 1 ∧ IsCompact B ∧ volume B = 0 ∧ fairCoin A ≤ volume (g '' B) := by
  obtain ⟨con, _, _, D, _, dc, dn, lower⟩ := cantor_localization_from_normal_form C A hA form
  obtain ⟨B, into, compact, null, cost⟩ := realAffineExtension_compact_witness con dc dn
  exact ⟨realAffineExtension_continuous con, realAffineExtension_mem_Icc _, B,
    into, compact, null, lower.trans cost⟩

end Guo

#print axioms Guo.affineExtension_continuous
#print axioms Guo.realAffineExtension_compact_witness
#print axioms Guo.real_candidate_witness
#print axioms Guo.realAffineExtension_locally_affine
#print axioms Guo.rationalEndpointValue_error
