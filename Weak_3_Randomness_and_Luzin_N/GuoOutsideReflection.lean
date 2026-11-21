import Weak_3_Randomness_and_Luzin_N.GuoOutsideReflectionCodes

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace Guo

/-- Effective rational enclosures for the values at all rational inputs. -/
structure FractionEnclosure (f : ℝ → ℝ) where
  sample : SignedFraction × ℕ → SignedFraction × SignedFraction
  sample_primrec : Primrec sample
  covers : ∀ q k, |f q.val - (sample (q, k)).1.val| ≤ (sample (q, k)).2.val
  shrinks : ∀ q, Tendsto (fun k => (sample (q, k)).2.val) atTop (𝓝 0)

namespace FractionEnclosure

def upper {f : ℝ → ℝ} (E : FractionEnclosure f) (q : SignedFraction × ℕ) : SignedFraction :=
  (E.sample q).1.add (E.sample q).2

def lower {f : ℝ → ℝ} (E : FractionEnclosure f) (q : SignedFraction × ℕ) : SignedFraction :=
  (E.sample q).1.add (E.sample q).2.neg

theorem upper_primrec {f : ℝ → ℝ} (E : FractionEnclosure f) : Primrec E.upper :=
  SignedFraction.add_primrec.comp (Primrec.fst.comp E.sample_primrec) (Primrec.snd.comp E.sample_primrec)

theorem lower_primrec {f : ℝ → ℝ} (E : FractionEnclosure f) : Primrec E.lower :=
  SignedFraction.add_primrec.comp (Primrec.fst.comp E.sample_primrec)
    (SignedFraction.neg_primrec.comp (Primrec.snd.comp E.sample_primrec))

theorem upper_spec {f : ℝ → ℝ} (E : FractionEnclosure f) (q : SignedFraction) (k : ℕ) :
    f q.val ≤ (E.upper (q, k)).val := by
  have h := (abs_le.mp (E.covers q k)).2
  simp only [upper, SignedFraction.val_add]
  linarith

theorem lower_spec {f : ℝ → ℝ} (E : FractionEnclosure f) (q : SignedFraction) (k : ℕ) :
    (E.lower (q, k)).val ≤ f q.val := by
  have h := (abs_le.mp (E.covers q k)).1
  simp only [lower, SignedFraction.val_add, SignedFraction.val_neg]
  linarith

theorem eventually_upper_lt {f : ℝ → ℝ} (E : FractionEnclosure f) (q : SignedFraction)
    {y : ℝ} (h : f q.val < y) :
    ∀ᶠ k in atTop, (E.upper (q, k)).val < y := by
  have hp : 0 < (y - f q.val) / 2 := by linarith
  filter_upwards [(tendsto_order.1 (E.shrinks q)).2 _ hp] with k hk
  have hh := (abs_le.mp (E.covers q k)).1
  simp only [upper, SignedFraction.val_add]
  linarith

theorem eventually_lt_lower {f : ℝ → ℝ} (E : FractionEnclosure f) (q : SignedFraction)
    {y : ℝ} (h : y < f q.val) :
    ∀ᶠ k in atTop, y < (E.lower (q, k)).val := by
  have hp : 0 < (f q.val - y) / 2 := by linarith
  filter_upwards [(tendsto_order.1 (E.shrinks q)).2 _ hp] with k hk
  have hh := (abs_le.mp (E.covers q k)).2
  simp only [lower, SignedFraction.val_add, SignedFraction.val_neg]
  linarith

end FractionEnclosure

private theorem affineImage_positive {a : ℝ} (ha : 0 < a) (b l r : ℝ) :
    (fun x => a * x + b) '' Ioo l r = Ioo (a * l + b) (a * r + b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨add_lt_add_left (mul_lt_mul_of_pos_left hx.1 ha) b,
      add_lt_add_left (mul_lt_mul_of_pos_left hx.2 ha) b⟩
  · intro hy
    refine ⟨(y - b) / a, ⟨?_, ?_⟩, ?_⟩
    · apply (lt_div_iff₀ ha).mpr
      linarith [hy.1]
    · apply (div_lt_iff₀ ha).mpr
      linarith [hy.2]
    · field_simp [ha.ne']
      ring

private theorem affineImage_negative {a : ℝ} (ha : a < 0) (b l r : ℝ) :
    (fun x => a * x + b) '' Ioo l r = Ioo (a * r + b) (a * l + b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨add_lt_add_left (mul_lt_mul_of_neg_left hx.2 ha) b,
      add_lt_add_left (mul_lt_mul_of_neg_left hx.1 ha) b⟩
  · intro hy
    refine ⟨(b - y) / (-a), ⟨?_, ?_⟩, ?_⟩
    · apply (lt_div_iff₀ (neg_pos.mpr ha)).mpr
      linarith [hy.2]
    · apply (div_lt_iff₀ (neg_pos.mpr ha)).mpr
      linarith [hy.1]
    · field_simp [ha.ne]
      ring

private theorem real_cast_int_decompose (j : ℤ) :
    (j.toNat : ℝ) - ((-j).toNat : ℝ) = (j : ℝ) := by
  cases j <;> simp

/-- Every point of an open real interval lies in a strictly contained dyadic interval. -/
theorem dyadicInterval_strict_basis {l y r : ℝ} (hl : l < y) (hr : y < r) :
    ∃ d : DyadicIntervalCode, y ∈ dyadicInterval d ∧
      l < (intervalLowerCode d).val ∧ (intervalUpperCode d).val < r := by
  have hδ : 0 < min (y - l) (r - y) / 2 := div_pos
    (lt_min (sub_pos.mpr hl) (sub_pos.mpr hr)) (by norm_num)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (show (2 : ℝ)⁻¹ < 1 by norm_num)
  rw [inv_pow, ← one_div] at hk
  have gap₁ := mul_lt_mul_of_pos_left (hk.trans_le (div_le_div_of_nonneg_right
    (min_le_left (y - l) (r - y)) (by norm_num : (0 : ℝ) ≤ 2))) (by norm_num : (0 : ℝ) < 2)
  have gap₂ := (hk.trans_le (div_le_div_of_nonneg_right
    (min_le_right (y - l) (r - y)) (by norm_num : (0 : ℝ) ≤ 2)))
  let p := (2 : ℝ)^k
  have pos : 0 < p := by dsimp [p]; positivity
  let m : ℤ := ⌊y * p⌋
  let j : ℤ := m - 1
  have lower : ((m : ℝ) - 1) / p = (m : ℝ) / p - 1 / p := by ring
  have upper : ((m : ℝ) + 1) / p = (m : ℝ) / p + 1 / p := by ring
  have floor_le : (m : ℝ) / p ≤ y := (div_le_iff₀ pos).mpr (Int.floor_le _)
  have floor_ge : y < ((m : ℝ) + 1) / p := (lt_div_iff₀ pos).mpr (Int.lt_floor_add_one _)
  let c : DyadicIntervalCode := (j.toNat, j.toNat + 2, (-j).toNat, k)
  have lo : (intervalLowerCode c).val = (m : ℝ) / p - 1 / p := by
    dsimp [c, intervalLowerCode, p]
    rw [SignedFraction.val_dyadic, real_cast_int_decompose]
    simp only [j, Int.cast_sub, Int.cast_one]
    exact lower
  have hi : (intervalUpperCode c).val = (m : ℝ) / p + 1 / p := by
    dsimp [c, intervalUpperCode, p]
    rw [SignedFraction.val_dyadic, Nat.cast_add, Nat.cast_ofNat,
      show (j.toNat : ℝ) + 2 - ((-j).toNat : ℝ) =
        (j.toNat : ℝ) - ((-j).toNat : ℝ) + 2 by ring, real_cast_int_decompose]
    simp only [j, Int.cast_sub, Int.cast_one]
    convert upper using 2
    ring
  rw [upper] at floor_ge
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [dyadicInterval_eq_codes, lo, hi]
    exact ⟨by linarith [one_div_pos.mpr pos], floor_ge⟩
  · rw [lo]
    change 2 * (1 / p) < _ at gap₁
    linarith
  · rw [hi]
    change 1 / p < _ at gap₂
    linarith

private abbrev ImageCheckInput := DyadicIntervalCode × DyadicIntervalCode × ℕ

private def orientedInside {f : ℝ → ℝ} (E : FractionEnclosure f)
    (lo hi : SignedFraction) (dst : DyadicIntervalCode) (k : ℕ) : Bool :=
  (E.upper (lo, k)).lt (intervalLowerCode dst) &&
    (intervalUpperCode dst).lt (E.lower (hi, k))

private def affineImageCheck {f : ℝ → ℝ} (E : FractionEnclosure f) (p : ImageCheckInput) : Bool :=
  let lo := intervalLowerCode p.1
  let hi := intervalUpperCode p.1
  lo.lt hi &&
    (orientedInside E lo hi p.2.1 p.2.2 || orientedInside E hi lo p.2.1 p.2.2)

private theorem affineImageCheck_primrec {f : ℝ → ℝ} (E : FractionEnclosure f) :
    Primrec (affineImageCheck E) := by
  let lo := intervalLowerCode_primrec.comp (Primrec.fst : Primrec (Prod.fst : ImageCheckInput → _))
  let hi := intervalUpperCode_primrec.comp (Primrec.fst : Primrec (Prod.fst : ImageCheckInput → _))
  let dstLo := intervalLowerCode_primrec.comp (Primrec.fst.comp
    (Primrec.snd : Primrec (Prod.snd : ImageCheckInput → _)))
  let dstHi := intervalUpperCode_primrec.comp (Primrec.fst.comp
    (Primrec.snd : Primrec (Prod.snd : ImageCheckInput → _)))
  have k : Primrec (fun p : ImageCheckInput => p.2.2) := Primrec.snd.comp Primrec.snd
  have oriented {l r : ImageCheckInput → SignedFraction} (hl : Primrec l) (hr : Primrec r) :
      Primrec (fun p => orientedInside E (l p) (r p) p.2.1 p.2.2) :=
    Primrec.and.comp (SignedFraction.lt_primrec.comp (E.upper_primrec.comp (hl.pair k)) dstLo)
      (SignedFraction.lt_primrec.comp dstHi (E.lower_primrec.comp (hr.pair k)))
  exact Primrec.and.comp (SignedFraction.lt_primrec.comp lo hi)
    (Primrec.or.comp (oriented lo hi) (oriented hi lo))

private theorem affineImageCheck_sound {a b : ℝ} {E : FractionEnclosure (fun x => a * x + b)}
    (p : ImageCheckInput) (valid : affineImageCheck E p = true) :
    dyadicInterval p.2.1 ⊆ (fun x => a * x + b) '' dyadicInterval p.1 := by
  simp only [affineImageCheck, orientedInside, Bool.and_eq_true, Bool.or_eq_true,
    SignedFraction.lt_true_iff] at valid
  have hl := valid.1
  rcases valid.2 with valid | valid
  · have h₁ := (E.upper_spec (intervalLowerCode p.1) p.2.2).trans_lt valid.1
    have h₂ := valid.2.trans_le (E.lower_spec (intervalUpperCode p.1) p.2.2)
    intro y hy
    rw [dyadicInterval_eq_codes] at hy
    have signs : 0 < a := by
      have hh := h₁.trans (hy.1.trans (hy.2.trans h₂))
      by_contra! ha
      have := mul_le_mul_of_nonpos_left hl.le ha
      linarith
    rw [dyadicInterval_eq_codes p.1, affineImage_positive signs]
    exact ⟨h₁.trans hy.1, hy.2.trans h₂⟩
  · have h₁ := (E.upper_spec (intervalUpperCode p.1) p.2.2).trans_lt valid.1
    have h₂ := valid.2.trans_le (E.lower_spec (intervalLowerCode p.1) p.2.2)
    intro y hy
    rw [dyadicInterval_eq_codes] at hy
    have signs : a < 0 := by
      have hh := h₁.trans (hy.1.trans (hy.2.trans h₂))
      by_contra! ha
      have := mul_le_mul_of_nonneg_left hl.le ha
      linarith
    rw [dyadicInterval_eq_codes p.1, affineImage_negative signs]
    exact ⟨h₁.trans hy.1, hy.2.trans h₂⟩

private theorem affineImageCheck_complete {a b : ℝ} (ha : a ≠ 0)
    (E : FractionEnclosure (fun x => a * x + b)) (src : DyadicIntervalCode) {y : ℝ}
    (hy : y ∈ (fun x => a * x + b) '' dyadicInterval src) :
    ∃ dst k, y ∈ dyadicInterval dst ∧ affineImageCheck E (src, dst, k) = true := by
  have hsource : ∃ x, x ∈ dyadicInterval src := by
    obtain ⟨x, hx, _⟩ := hy
    exact ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hsource
  rw [dyadicInterval_eq_codes] at hx hy
  have order := hx.1.trans hx.2
  rcases lt_or_gt_of_ne ha with h | h
  · rw [affineImage_negative h] at hy
    obtain ⟨dst, memD, low, high⟩ := dyadicInterval_strict_basis hy.1 hy.2
    obtain ⟨k, hk₁, hk₂⟩ := ((E.eventually_upper_lt (intervalUpperCode src) low).and
      (E.eventually_lt_lower (intervalLowerCode src) high)).exists
    refine ⟨dst, k, memD, ?_⟩
    simp only [affineImageCheck, orientedInside, Bool.and_eq_true, Bool.or_eq_true,
      SignedFraction.lt_true_iff]
    exact ⟨order, Or.inr ⟨hk₁, hk₂⟩⟩
  · rw [affineImage_positive h] at hy
    obtain ⟨dst, memD, low, high⟩ := dyadicInterval_strict_basis hy.1 hy.2
    obtain ⟨k, hk₁, hk₂⟩ := ((E.eventually_upper_lt (intervalLowerCode src) low).and
      (E.eventually_lt_lower (intervalUpperCode src) high)).exists
    refine ⟨dst, k, memD, ?_⟩
    simp only [affineImageCheck, orientedInside, Bool.and_eq_true, Bool.or_eq_true,
      SignedFraction.lt_true_iff]
    exact ⟨order, Or.inl ⟨hk₁, hk₂⟩⟩

open Encodable

private def affineImageEntry {f : ℝ → ℝ} (E : FractionEnclosure f)
    (q : Option DyadicIntervalCode × ℕ × ℕ) : Option DyadicIntervalCode :=
  q.1.bind fun src => (decode (α := DyadicIntervalCode) q.2.1).bind fun dst =>
    if affineImageCheck E (src, dst, q.2.2) then some dst else none

private theorem affineImageEntry_primrec {f : ℝ → ℝ} (E : FractionEnclosure f) :
    Primrec (affineImageEntry E) := by
  let Input := Option DyadicIntervalCode × ℕ × ℕ
  let WithSrc := Input × DyadicIntervalCode
  let WithDst := WithSrc × DyadicIntervalCode
  have dest : Primrec (Prod.snd : WithDst → DyadicIntervalCode) := Primrec.snd
  have src : Primrec (fun p : WithDst => p.1.2) := Primrec.snd.comp Primrec.fst
  have precision : Primrec (fun p : WithDst => p.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have valid := (affineImageCheck_primrec E).comp (src.pair (dest.pair precision))
  have chooseDest : Primrec (fun p : WithDst =>
      if affineImageCheck E (p.1.2, p.2, p.1.1.2.2) then some p.2 else none) :=
    Primrec.ite (Primrec.eq.comp valid (Primrec.const true))
      (Primrec.option_some.comp dest) (Primrec.const none)
  have decodeDest : Primrec (fun p : WithSrc => decode (α := DyadicIntervalCode) p.1.2.1) :=
    Primrec.decode.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  exact Primrec.option_bind Primrec.fst (Primrec.option_bind decodeDest chooseDest.to₂).to₂

private def affineImageStream {f : ℝ → ℝ} (E : FractionEnclosure f) (stream : RealOracleStream) :
    RealOracleStream := fun p => affineImageEntry E
      (stream (p.1, p.2.unpair.1), p.2.unpair.2.unpair.1, p.2.unpair.2.unpair.2)

section
attribute [local irreducible] ComputableIn

private theorem affineImageStream_computableIn {Z : Oracle} {f : ℝ → ℝ} (E : FractionEnclosure f)
    {stream : RealOracleStream} (h : ComputableIn {Z} stream) :
    ComputableIn {Z} (affineImageStream E stream) := by
  have decodeTick : Primrec (fun p : ℕ × ℕ => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have read : Primrec (fun p : ℕ × ℕ => (p.1, p.2.unpair.1)) :=
    Primrec.fst.pair (Primrec.fst.comp decodeTick)
  have choice : Primrec (fun p : ℕ × ℕ => p.2.unpair.2.unpair) :=
    Primrec.unpair.comp (Primrec.snd.comp decodeTick)
  exact computableIn_comp (affineImageEntry_primrec E).computableIn
    (computableIn_pair (computableIn_comp h read.computableIn) choice.computableIn)

end

private theorem affineImageStream_layer {a b : ℝ} (ha : a ≠ 0)
    (E : FractionEnclosure (fun x => a * x + b)) (stream : RealOracleStream) (n : ℕ) :
    realOracleLayer (affineImageStream E stream) n =
      (fun x => a * x + b) '' realOracleLayer stream n := by
  ext y
  rw [mem_realOracleLayer]
  constructor
  · rintro ⟨tick, dst, hcode, hy⟩
    simp only [affineImageStream, affineImageEntry, Option.bind_eq_some_iff] at hcode
    obtain ⟨src, found, dst', decoded, eq⟩ := hcode
    split at eq
    next yes =>
      cases eq
      obtain ⟨x, hx, rfl⟩ := affineImageCheck_sound _ yes hy
      exact ⟨x, (mem_realOracleLayer _ _ _).mpr ⟨_, src, found, hx⟩, rfl⟩
    next _ => simp at eq
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, src, hcode, inside⟩ := (mem_realOracleLayer _ _ _).mp hx
    obtain ⟨dst, k, hy, accepted⟩ := affineImageCheck_complete ha E src ⟨x, inside, rfl⟩
    refine ⟨Nat.pair t (Nat.pair (encode dst) k), dst, ?_, hy⟩
    simp only [affineImageStream, Nat.unpair_pair, affineImageEntry, hcode, encodek]
    change (if affineImageCheck E (src, dst, k) then some dst else none) = some dst
    rw [if_pos accepted]

/-- A nonconstant affine map with effective enclosures sends each uniformly open
test layer to a uniformly open layer at the same oracle. -/
theorem affineImage_uniform {a b : ℝ} (ha : a ≠ 0)
    (E : FractionEnclosure (fun x => a * x + b))
    {Z : Oracle} {U : ℕ → Set ℝ} (hU : RealOracleUniformOpen Z U) :
    RealOracleUniformOpen Z (fun n => (fun x => a * x + b) '' U n) := by
  obtain ⟨stream, hstream, eq⟩ := hU
  exact ⟨affineImageStream E stream, affineImageStream_computableIn E hstream,
    fun n => (affineImageStream_layer ha E stream n).trans (congrArg _ (eq n))⟩

private theorem affineImage_volume {a : ℝ} (ha : a ≠ 0) (b : ℝ) (U : Set ℝ) :
    volume ((fun x => a * x + b) '' U) = ENNReal.ofReal |a| * volume U := by
  have eq : (fun x => a * x + b) '' U = (fun y => y + (-b)) ⁻¹' ((a⁻¹ * ·) ⁻¹' U) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change a⁻¹ * (a * x + b + -b) ∈ U
      rw [add_neg_cancel_right, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      exact hx
    · intro hy
      refine ⟨a⁻¹ * (y + -b), hy, ?_⟩
      change a * (a⁻¹ * (y + -b)) + b = y
      rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul, add_assoc, neg_add_cancel, add_zero]
  rw [eq, measure_preimage_add_right, Real.volume_preimage_mul_left (inv_ne_zero ha), inv_inv]

private theorem realOracleUniformOpen_shift {Z : Oracle} {U : ℕ → Set ℝ}
    (hU : RealOracleUniformOpen Z U) (d : ℕ) :
    RealOracleUniformOpen Z (fun n => U (n + d)) := by
  obtain ⟨stream, computable, eq⟩ := hU
  let shift : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + d, p.2)
  have hshift : Primrec shift :=
    (Primrec.nat_add.comp Primrec.fst (Primrec.const d)).pair Primrec.snd
  refine ⟨stream ∘ shift, computableIn_comp computable hshift.computableIn, fun n => ?_⟩
  exact eq (n + d)

theorem affine_transfers_weakFailure {a b : ℝ} (ha : a ≠ 0)
    (E : FractionEnclosure (fun x => a * x + b)) {Z : Oracle} {x : ℝ}
    (h : RealFailsWeak Z x) : RealFailsWeak Z (a * x + b) := by
  obtain ⟨U, htest, hx⟩ := h
  let f : ℝ → ℝ := fun y => a * y + b
  have inj : Function.Injective f := by
    intro x y eq
    exact mul_left_cancel₀ ha (add_right_cancel eq)
  refine ⟨fun n => f '' U n, ⟨affineImage_uniform ha E htest.1, ?_⟩, fun n => ⟨x, hx n, rfl⟩⟩
  rw [← inj.injOn.image_iInter_eq, affineImage_volume ha, htest.2, mul_zero]

theorem affine_transfers_martinLofFailure {a b : ℝ} (ha : a ≠ 0)
    (E : FractionEnclosure (fun x => a * x + b)) {Z : Oracle} {x : ℝ}
    (h : RealFailsMartinLof Z x) : RealFailsMartinLof Z (a * x + b) := by
  obtain ⟨U, htest, hx⟩ := h
  obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt |a| (show (1 : ℝ) < 2 by norm_num)
  have scale : ENNReal.ofReal |a| ≤ (2 : ℝ≥0∞)^d := by
    simpa using ENNReal.ofReal_le_ofReal hd.le
  refine ⟨fun n => (fun y => a * y + b) '' U (n + d),
    ⟨affineImage_uniform ha E (realOracleUniformOpen_shift htest.1 d), fun n => ?_⟩,
    fun n => ⟨x, hx (n + d), rfl⟩⟩
  rw [affineImage_volume ha]
  calc
    ENNReal.ofReal |a| * volume (U (n + d)) ≤ (2 : ℝ≥0∞)^d * ((2 : ℝ≥0∞)⁻¹)^(n + d) :=
      mul_le_mul' scale (htest.2 (n + d))
    _ = _ := dyadic_cancel n d

end Guo

#print axioms Guo.affineImage_uniform
#print axioms Guo.affine_transfers_weakFailure
#print axioms Guo.affine_transfers_martinLofFailure
