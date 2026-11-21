import Weak_3_Randomness_and_Luzin_N.GuoRealTransfer

open Set MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace Guo

/-- The integer represented by the first `n` bits of a stream, in reading order. -/
def binaryPrefixIndex (x : Cantor) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 * binaryPrefixIndex x n + (x n).toNat

theorem binaryPrefixIndex_lt (x : Cantor) (n : Nat) : binaryPrefixIndex x n < 2 ^ n := by
  induction n with
  | zero => simp [binaryPrefixIndex]
  | succ n ih =>
    rw [binaryPrefixIndex, pow_succ]
    have bit := Bool.toNat_le (x n)
    omega

theorem binaryPrefixIndex_eq_iff (x y : Cantor) (n : Nat) :
    binaryPrefixIndex x n = binaryPrefixIndex y n ↔ readBits x n = readBits y n := by
  induction n with
  | zero =>
    have h : readBits x 0 = readBits y 0 := by
      apply Vector.ext
      intro i hi
      omega
    simp [binaryPrefixIndex, h]
  | succ n ih =>
    rw [binaryPrefixIndex, binaryPrefixIndex, readBits_succ, readBits_succ]
    constructor
    · intro e
      have parts : binaryPrefixIndex x n = binaryPrefixIndex y n ∧ x n = y n := by
        cases hx : x n <;> cases hy : y n <;>
          simp [hx, hy, Bool.toNat] at e ⊢ <;> omega
      rw [ih.mp parts.1, parts.2]
    · intro e
      have previous : readBits x n = readBits y n := by
        apply Vector.ext
        intro i hi
        simpa only [Vector.getElem_push_lt hi] using
          congrArg (fun p : Bits (n + 1) => p[i]'(Nat.lt_succ_of_lt hi)) e
      have last : x n = y n := by
        simpa using congrArg (fun p : Bits (n + 1) => p[n]) e
      rw [ih.mpr previous, last]

private def binaryWordIndexFin (n : Nat) (p : Bits n) : Fin (2 ^ n) :=
  ⟨binaryPrefixIndex (extendWord p) n, binaryPrefixIndex_lt _ _⟩

/-- All level-`n` binary words index the `2^n` equal dyadic cells. -/
noncomputable def binaryWordIndex (n : Nat) : Bits n ≃ Fin (2 ^ n) := by
  classical
  refine Equiv.ofBijective (binaryWordIndexFin n) ?_
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by rw [card_bits, Fintype.card_fin]⟩
  intro p q e
  have code := congrArg Fin.val e
  change binaryPrefixIndex (extendWord p) n = binaryPrefixIndex (extendWord q) n at code
  simpa only [readBits_extendWord] using (binaryPrefixIndex_eq_iff _ _ n).mp code

@[simp]
theorem binaryWordIndex_readBits (x : Cantor) (n : Nat) :
    (binaryWordIndex n (readBits x n)).val = binaryPrefixIndex x n :=
  (binaryPrefixIndex_eq_iff _ _ n).mpr (readBits_extendWord _)

theorem fairCoin_binaryPrefixIndex_lt (n k : Nat) (hk : k ≤ 2 ^ n) :
    fairCoin {x | binaryPrefixIndex x n < k} =
      (k : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹)^n := by
  classical
  let W (j : Fin k) := (binaryWordIndex n).symm (j.castLE hk)
  have asUnion : {x | binaryPrefixIndex x n < k} = ⋃ j : Fin k, cylinderSet (W j) := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · intro h
      refine ⟨⟨_, h⟩, ?_⟩
      change readBits x n = W _
      apply (binaryWordIndex n).injective
      rw [show binaryWordIndex n (W ⟨binaryPrefixIndex x n, h⟩) =
          Fin.castLE hk ⟨binaryPrefixIndex x n, h⟩ from (binaryWordIndex n).apply_symm_apply _]
      exact Fin.ext (binaryWordIndex_readBits x n)
    · rintro ⟨j, h⟩
      change readBits x n = W j at h
      have e := congrArg (fun p => (binaryWordIndex n p).val) h
      have value : binaryPrefixIndex x n = j.val := by simpa [W] using e
      exact value ▸ j.isLt
  have hd : Pairwise (Function.onFun Disjoint (fun j => cylinderSet (W j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    change readBits x n = W i at hi
    change readBits x n = W j at hj
    apply hij
    apply Fin.ext
    simpa [W] using congrArg (fun p => (binaryWordIndex n p).val) (hi.symm.trans hj)
  rw [asUnion, measure_iUnion hd (fun j => measurable_cylinder (W j))]
  simp only [fairCoin_cylinder, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

private theorem binaryDigit_val (b : Bool) : (binaryDigit b).val = b.toNat := by
  cases b <;> rfl

private theorem binaryPrefixIndex_sum (x : Cantor) (n : Nat) :
    (2 : ℝ)^n * (∑ j ∈ Finset.range n, Real.ofDigitsTerm (fun r => binaryDigit (x r)) j) =
      binaryPrefixIndex x n := by
  induction n with
  | zero => simp [binaryPrefixIndex]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, binaryPrefixIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    congr 1
    · rw [pow_succ, mul_comm ((2 : ℝ)^n) 2, mul_assoc, ih]
    · simp only [Real.ofDigitsTerm, binaryDigit_val, Nat.cast_ofNat]
      calc
        _ = ((x n).toNat : ℝ) * ((2 : ℝ)^(n + 1) * ((2 : ℝ)^(n + 1))⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ (by positivity), mul_one]

theorem binaryEvaluation_mem_Icc (x : Cantor) : binaryEvaluation x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩

/-- Splitting a stream at level `n` separates its grid index and the binary value of its tail. -/
theorem binaryEvaluation_scaled (x : Cantor) (n : Nat) :
    (2 : ℝ)^n * binaryEvaluation x =
      (binaryPrefixIndex x n : ℝ) + binaryEvaluation (fun j => x (j + n)) := by
  unfold binaryEvaluation
  conv_lhs => rw [Real.ofDigits_eq_sum_add_ofDigits _ n]
  rw [mul_add, binaryPrefixIndex_sum]
  norm_num only [Nat.cast_ofNat]
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

private theorem binaryEvaluation_scaled_bounds (x : Cantor) (n : Nat) :
    (binaryPrefixIndex x n : ℝ) ≤ (2 : ℝ)^n * binaryEvaluation x ∧
      (2 : ℝ)^n * binaryEvaluation x ≤ (binaryPrefixIndex x n : ℝ) + 1 := by
  rw [binaryEvaluation_scaled]
  have := binaryEvaluation_mem_Icc (fun j => x (j + n))
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

private theorem fairCoin_binaryPrefixIndex_lt_real (n k : Nat) (hk : k ≤ 2 ^ n) :
    (fairCoin {x | binaryPrefixIndex x n < k}).toReal = (k : ℝ) / (2 : ℝ)^n := by
  rw [fairCoin_binaryPrefixIndex_lt n k hk, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_inv, div_eq_mul_inv, inv_pow]
  norm_num

/-- The distribution function in the interior of the unit interval. -/
private theorem binaryEvaluation_cdf (a : ℝ) (ha : 0 ≤ a) (h1 : a < 1) :
    (fairCoin (binaryEvaluation ⁻¹' Iic a)).toReal = a := by
  let E := binaryEvaluation ⁻¹' Iic a
  have bounds (n : Nat) :
      a - ((2 : ℝ)⁻¹)^n ≤ (fairCoin E).toReal ∧
        (fairCoin E).toReal ≤ a + ((2 : ℝ)⁻¹)^n := by
    let N := (2 : ℝ)^n
    let k := ⌊N * a⌋₊
    have Npos : 0 < N := by dsimp [N]; positivity
    have nonneg : 0 ≤ N * a := mul_nonneg Npos.le ha
    have leFloor : (k : ℝ) ≤ N * a := Nat.floor_le nonneg
    have ltSucc : N * a < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hk : k < 2 ^ n := by
      apply (Nat.floor_lt nonneg).mpr
      simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_one] using
        mul_lt_mul_of_pos_left h1 Npos
    have loSubset : {x | binaryPrefixIndex x n < k} ⊆ E := by
      intro x hx
      have hcast : (binaryPrefixIndex x n : ℝ) + 1 ≤ k := by
        exact_mod_cast (Nat.succ_le_of_lt hx)
      change binaryEvaluation x ≤ a
      exact (mul_le_mul_iff_of_pos_left Npos).mp
        (((binaryEvaluation_scaled_bounds x n).2.trans hcast).trans leFloor)
    have hiSubset : E ⊆ {x | binaryPrefixIndex x n < k + 1} := by
      intro x hx
      have hxa : binaryEvaluation x ≤ a := hx
      have hcast : (binaryPrefixIndex x n : ℝ) < (k : ℝ) + 1 :=
        ((binaryEvaluation_scaled_bounds x n).1.trans
          (mul_le_mul_of_nonneg_left hxa Npos.le)).trans_lt ltSucc
      exact_mod_cast hcast
    have loMeasure := ENNReal.toReal_mono (measure_ne_top fairCoin E) (measure_mono (μ := fairCoin) loSubset)
    rw [fairCoin_binaryPrefixIndex_lt_real n k hk.le] at loMeasure
    have hiMeasure := ENNReal.toReal_mono (measure_ne_top fairCoin _) (measure_mono (μ := fairCoin) hiSubset)
    rw [fairCoin_binaryPrefixIndex_lt_real n (k + 1) hk] at hiMeasure
    have small : ((2 : ℝ)⁻¹)^n * N = 1 := by
      dsimp [N]
      rw [inv_pow, inv_mul_cancel₀ (by positivity)]
    constructor
    · apply le_trans _ loMeasure
      apply (le_div_iff₀ Npos).mpr
      rw [sub_mul, small, mul_comm a N]
      linarith
    · apply hiMeasure.trans
      apply (div_le_iff₀ Npos).mpr
      rw [add_mul, small, mul_comm a N, Nat.cast_add, Nat.cast_one]
      linarith
  have geom : Tendsto (fun n : Nat => ((2 : ℝ)⁻¹)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have lowerLimit : Tendsto (fun n : Nat => a - ((2 : ℝ)⁻¹)^n) atTop (𝓝 a) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub geom
  have upperLimit : Tendsto (fun n : Nat => a + ((2 : ℝ)⁻¹)^n) atTop (𝓝 a) := by
    simpa only [add_zero] using tendsto_const_nhds.add geom
  exact le_antisymm (ge_of_tendsto upperLimit (.of_forall fun n => (bounds n).2))
    (le_of_tendsto lowerLimit (.of_forall fun n => (bounds n).1))

/-- The binary evaluation pushes the fair-coin measure forward to Lebesgue measure on `[0,1]`. -/
theorem binaryEvaluation_map_fairCoin :
    Measure.map binaryEvaluation fairCoin = volume.restrict (Icc (0 : ℝ) 1) := by
  apply Measure.ext_of_Iic
  intro a
  rw [Measure.map_apply binaryEvaluation_continuous.measurable measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  by_cases h0 : a < 0
  · have preimageEmpty : binaryEvaluation ⁻¹' Iic a = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      exact fun x hx => (not_le_of_gt h0) ((binaryEvaluation_mem_Icc x).1.trans hx)
    have interEmpty : Iic a ∩ Icc (0 : ℝ) 1 = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun x hx => (not_le_of_gt h0) (hx.2.1.trans hx.1)
    rw [preimageEmpty, interEmpty, measure_empty, measure_empty]
  · by_cases h1 : 1 ≤ a
    · have preimageUniv : binaryEvaluation ⁻¹' Iic a = univ :=
        Set.eq_univ_of_forall fun x => (binaryEvaluation_mem_Icc x).2.trans h1
      have interEq : Iic a ∩ Icc (0 : ℝ) 1 = Icc 0 1 :=
        inter_eq_right.mpr fun x hx => hx.2.trans h1
      rw [preimageUniv, interEq, measure_univ, Real.volume_Icc]
      norm_num
    · have interEq : Iic a ∩ Icc (0 : ℝ) 1 = Icc 0 a := by
        ext x
        exact ⟨fun hx => ⟨hx.2.1, hx.1⟩,
          fun hx => ⟨hx.2, hx.1, hx.2.trans (le_of_not_ge h1)⟩⟩
      rw [interEq, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_toReal (measure_ne_top fairCoin _),
        binaryEvaluation_cdf a (le_of_not_gt h0) (lt_of_not_ge h1)]

theorem binaryEvaluation_range : range binaryEvaluation = Icc (0 : ℝ) 1 := by
  refine Subset.antisymm (range_subset_iff.mpr binaryEvaluation_mem_Icc) ?_
  intro a ha
  obtain ⟨d, _, eq⟩ := Real.ofDigits_SurjOn (b := 2) (by decide) ha
  refine ⟨fun i => decide ((d i).val = 1), ?_⟩
  rw [← eq]
  unfold binaryEvaluation
  apply congrArg (Real.ofDigits (b := 2))
  funext i
  apply Fin.ext
  by_cases hi : (d i).val = 1
  · simp [binaryDigit, hi]
  · have zero : (d i).val = 0 := by have := (d i).isLt; omega
    simp [binaryDigit, zero]

noncomputable def binaryCylinderLeft (p : Bits n) : ℝ :=
  ((binaryWordIndex n p).val : ℝ) / (2 : ℝ)^n

noncomputable def binaryCylinderRight (p : Bits n) : ℝ :=
  (((binaryWordIndex n p).val : ℝ) + 1) / (2 : ℝ)^n

/-- A binary cylinder has the closed grid cell as its image, including both endpoints. -/
theorem binaryEvaluation_image_cylinder (p : Bits n) :
    binaryEvaluation '' cylinderSet p = Icc (binaryCylinderLeft p) (binaryCylinderRight p) := by
  let N := (2 : ℝ)^n
  let j : ℝ := (binaryWordIndex n p).val
  have Npos : 0 < N := by dsimp [N]; positivity
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    change readBits x n = p at hx
    have indexEq := binaryWordIndex_readBits x n
    rw [hx] at indexEq
    have bounds := binaryEvaluation_scaled_bounds x n
    rw [← indexEq] at bounds
    exact ⟨(div_le_iff₀ Npos).mpr (by simpa [N, j, mul_comm] using bounds.1),
      (le_div_iff₀ Npos).mpr (by simpa [N, j, mul_comm] using bounds.2)⟩
  · intro ha
    change j / N ≤ a ∧ a ≤ (j + 1) / N at ha
    have hLower : j ≤ N * a := by simpa only [mul_comm] using (div_le_iff₀ Npos).mp ha.1
    have hUpper : N * a ≤ j + 1 := by simpa only [mul_comm] using (le_div_iff₀ Npos).mp ha.2
    have residual : N * a - j ∈ range binaryEvaluation := by
      rw [binaryEvaluation_range]
      exact ⟨by linarith, by linarith⟩
    obtain ⟨y, hy⟩ := residual
    let x : Cantor := fun i => if hi : i < n then p[i] else y (i - n)
    have word : readBits x n = p := by
      apply Vector.ext
      intro i hi
      simp [x, hi]
    have shift : (fun i => x (i + n)) = y := by
      funext i
      simp [x, show ¬ i + n < n by omega]
    refine ⟨x, word, ?_⟩
    have indexEq := binaryWordIndex_readBits x n
    rw [word] at indexEq
    have scale := binaryEvaluation_scaled x n
    rw [← indexEq, shift, hy] at scale
    apply mul_left_cancel₀ Npos.ne'
    change N * binaryEvaluation x = j + (N * a - j) at scale
    linarith

noncomputable def binaryCylinderInterior (p : Bits n) : Set ℝ :=
  Ioo (binaryCylinderLeft p) (binaryCylinderRight p)

theorem volume_binaryCylinderInterior (p : Bits n) :
    volume (binaryCylinderInterior p) = fairCoin (cylinderSet p) := by
  rw [binaryCylinderInterior, Real.volume_Ioo, binaryCylinderRight, binaryCylinderLeft,
    div_sub_div_same, add_sub_cancel_left, one_div, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (by norm_num), fairCoin_cylinder]
  norm_num [ENNReal.inv_pow]

def IsBinaryDyadic (a : ℝ) : Prop :=
  ∃ (n k : Nat), a = (k : ℝ) / (2 : ℝ)^n

/-- The union of the grid interiors has no greater measure and covers all nondyadic images. -/
theorem binaryCylinderInterior_cover {ι : Type*} [Countable ι] (words : ι → Σ n, Bits n)
    (disjoint : Pairwise (Function.onFun Disjoint (fun i => cylinderSet (words i).2))) :
    IsOpen (⋃ i, binaryCylinderInterior (words i).2) ∧
    volume (⋃ i, binaryCylinderInterior (words i).2) ≤ fairCoin (⋃ i, cylinderSet (words i).2) ∧
    ∀ a ∈ binaryEvaluation '' (⋃ i, cylinderSet (words i).2),
      ¬ IsBinaryDyadic a → a ∈ ⋃ i, binaryCylinderInterior (words i).2 := by
  refine ⟨isOpen_iUnion (fun _ => isOpen_Ioo), ?_, ?_⟩
  · rw [measure_iUnion disjoint (fun i => measurable_cylinder (words i).2)]
    simpa only [volume_binaryCylinderInterior] using
      measure_iUnion_le (μ := volume) (fun i => binaryCylinderInterior (words i).2)
  · rintro a ⟨x, hx, rfl⟩ nondyadic
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    let p := (words i).2
    have hImage : binaryEvaluation x ∈ binaryEvaluation '' cylinderSet p := ⟨x, hi, rfl⟩
    rw [binaryEvaluation_image_cylinder] at hImage
    have leftNe : binaryEvaluation x ≠ binaryCylinderLeft p :=
      fun e => nondyadic ⟨(words i).1, (binaryWordIndex _ p).val, e⟩
    have rightNe : binaryEvaluation x ≠ binaryCylinderRight p := by
      intro e
      apply nondyadic
      refine ⟨(words i).1, (binaryWordIndex _ p).val + 1, ?_⟩
      simpa [binaryCylinderRight] using e
    exact mem_iUnion.mpr ⟨i, hImage.1.lt_of_ne leftNe.symm, hImage.2.lt_of_ne rightNe⟩

end Guo

#print axioms Guo.binaryEvaluation_map_fairCoin
#print axioms Guo.binaryEvaluation_image_cylinder
#print axioms Guo.binaryCylinderInterior_cover
