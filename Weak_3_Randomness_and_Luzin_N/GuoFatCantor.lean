import Weak_3_Randomness_and_Luzin_N.GuoRealTransfer

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace Guo

private theorem retainedLength_pos (n : Nat) : 0 < retainedLength n := by
  unfold retainedLength
  positivity

theorem retainedLength_tendsto_zero : Tendsto retainedLength atTop (𝓝 0) := by
  have geom := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by norm_num) (show (2 : ℝ)⁻¹ < 1 by norm_num)
  have h := (geom.mul_const ((2 : ℝ)⁻¹)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).add geom)
  change Tendsto (fun n : Nat => ((2 : ℝ)⁻¹)^(n + 1) * (1 + ((2 : ℝ)⁻¹)^n)) atTop (𝓝 0)
  simpa only [zero_mul, mul_zero, add_zero, ← pow_succ] using h

def retainedLengthRat (n : Nat) : ℚ :=
  ((2 : ℚ)⁻¹)^(n + 1) * (1 + ((2 : ℚ)⁻¹)^n)

@[simp] theorem cast_retainedLengthRat (n : Nat) :
    (retainedLengthRat n : ℝ) = retainedLength n := by
  simp [retainedLengthRat, retainedLength]

/-- Left endpoint at depth `n`, with each child abutting an endpoint of its parent. -/
noncomputable def retainedLeft (x : Cantor) : Nat → ℝ
  | 0 => 0
  | n + 1 => retainedLeft x n +
      (if x n then retainedLength n - retainedLength (n + 1) else 0)

def retainedLeftRat (x : Cantor) : Nat → ℚ
  | 0 => 0
  | n + 1 => retainedLeftRat x n +
      (if x n then retainedLengthRat n - retainedLengthRat (n + 1) else 0)

@[simp] theorem cast_retainedLeftRat (x : Cantor) (n : Nat) :
    (retainedLeftRat x n : ℝ) = retainedLeft x n := by
  induction n with
  | zero => simp [retainedLeftRat, retainedLeft]
  | succ n ih =>
    cases h : x n <;> simp [retainedLeftRat, retainedLeft, ih, h]

private theorem retainedLeft_reads (x y : Cantor) (n : Nat)
    (h : readBits x n = readBits y n) : retainedLeft x n = retainedLeft y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have prev : readBits x n = readBits y n := by
      simpa only [takePrefix_readBits] using
        congrArg (fun p => takePrefix p n (Nat.le_succ n)) h
    have bit : x n = y n := by
      simpa only [getElem_readBits] using congrArg
        (fun p : Bits (n + 1) => p[n]) h
    simp only [retainedLeft, ih prev, bit]

private noncomputable def pathInterval (x : Cantor) (n : Nat) : Set ℝ :=
  Icc (retainedLeft x n) (retainedLeft x n + retainedLength n)

/-- The closed retained interval with a given finite address. -/
noncomputable def retainedInterval (p : Bits n) : Set ℝ :=
  pathInterval (extendWord p) n

/-- The endpoints obtained by finite rational arithmetic on the address. -/
def retainedEndpoints (p : Bits n) : ℚ × ℚ :=
  let left := retainedLeftRat (extendWord p) n
  (left, left + retainedLengthRat n)

theorem retainedInterval_eq_Icc (p : Bits n) :
    retainedInterval p = Icc ((retainedEndpoints p).1 : ℝ) ((retainedEndpoints p).2 : ℝ) := by
  simp [retainedInterval, pathInterval, retainedEndpoints]

theorem retainedInterval_subset_rat_Ioo (p : Bits n) (a b : ℚ) :
    retainedInterval p ⊆ Ioo (a : ℝ) (b : ℝ) ↔
      a < (retainedEndpoints p).1 ∧ (retainedEndpoints p).2 < b := by
  rw [retainedInterval_eq_Icc]
  have ordered : ((retainedEndpoints p).1 : ℝ) ≤ ((retainedEndpoints p).2 : ℝ) := by
    simp only [retainedEndpoints, Rat.cast_add, cast_retainedLengthRat, cast_retainedLeftRat]
    exact le_add_of_nonneg_right (retainedLength_pos n).le
  constructor
  · intro h
    have left := (h (left_mem_Icc.mpr ordered)).1
    have right := (h (right_mem_Icc.mpr ordered)).2
    exact ⟨by exact_mod_cast left, by exact_mod_cast right⟩
  · rintro ⟨h₁, h₂⟩ z hz
    exact ⟨(show (a : ℝ) < ((retainedEndpoints p).1 : ℝ) by exact_mod_cast h₁).trans_le hz.1,
      hz.2.trans_lt (show ((retainedEndpoints p).2 : ℝ) < b by exact_mod_cast h₂)⟩

private theorem retainedInterval_readBits (x : Cantor) (n : Nat) :
    retainedInterval (readBits x n) = pathInterval x n := by
  unfold retainedInterval pathInterval
  rw [retainedLeft_reads (extendWord (readBits x n)) x n (readBits_extendWord _)]

private theorem pathInterval_antitone (x : Cantor) : Antitone (pathInterval x) := by
  apply antitone_nat_of_succ_le
  intro n z hz
  have len := retainedLength_pos (n + 1)
  have gap := retainedLength_gap n
  cases bit : x n <;>
    simp only [pathInterval, retainedLeft, bit, Bool.false_eq_true, if_false, if_true,
      add_zero, mem_Icc] at hz ⊢ <;> constructor <;> linarith [hz.1, hz.2]

private theorem pathInterval_zero (x : Cantor) : pathInterval x 0 = Icc 0 1 := by
  simp [pathInterval, retainedLeft, retainedLength_zero]

private theorem readBits_of_mem_pathIntervals (x y : Cantor) (n : Nat) (z : ℝ)
    (hx : z ∈ pathInterval x n) (hy : z ∈ pathInterval y n) :
    readBits x n = readBits y n := by
  induction n with
  | zero =>
    apply Vector.ext
    intro j hj
    omega
  | succ n ih =>
    have pre := ih (pathInterval_antitone x (Nat.le_succ n) hx)
      (pathInterval_antitone y (Nat.le_succ n) hy)
    have left := retainedLeft_reads x y n pre
    have bit : x n = y n := by
      have gap := retainedLength_gap n
      cases ex : x n <;> cases ey : y n
      · rfl
      · simp only [pathInterval, retainedLeft, ex, ey, Bool.false_eq_true, if_false,
          if_true, add_zero, mem_Icc, left] at hx hy
        linarith [hx.2, hy.1]
      · simp only [pathInterval, retainedLeft, ex, ey, Bool.false_eq_true, if_false,
          if_true, add_zero, mem_Icc, left] at hx hy
        linarith [hx.1, hy.2]
      · rfl
    rw [readBits_succ, readBits_succ, pre, bit]

theorem retainedInterval_isCompact (p : Bits n) : IsCompact (retainedInterval p) :=
  isCompact_Icc

theorem retainedInterval_volume (p : Bits n) :
    volume (retainedInterval p) = ENNReal.ofReal (retainedLength n) := by
  simp [retainedInterval, pathInterval, Real.volume_Icc]

theorem retainedIntervals_pairwise (n : Nat) :
    Pairwise (Function.onFun Disjoint (retainedInterval (n := n))) := by
  intro p q ne
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  have e := readBits_of_mem_pathIntervals (extendWord p) (extendWord q) n z hz₁ hz₂
  exact ne (by simpa only [readBits_extendWord] using e)

private theorem allPathIntervals_nonempty (x : Cantor) : (⋂ n, pathInterval x n).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
  · exact fun n => pathInterval_antitone x (Nat.le_succ n)
  · exact fun n => nonempty_Icc.mpr (le_add_of_nonneg_right (retainedLength_pos n).le)
  · exact isCompact_Icc
  · exact fun n => isClosed_Icc

/-- The point picked out by an infinite address in the nested retained intervals. -/
noncomputable def fatAddress (x : Cantor) : ℝ := (allPathIntervals_nonempty x).choose

private theorem fatAddress_mem_pathInterval (x : Cantor) (n : Nat) :
    fatAddress x ∈ pathInterval x n :=
  mem_iInter.mp (allPathIntervals_nonempty x).choose_spec n

theorem fatAddress_mem_retainedInterval (x : Cantor) (n : Nat) :
    fatAddress x ∈ retainedInterval (readBits x n) := by
  rw [retainedInterval_readBits]
  exact fatAddress_mem_pathInterval x n

theorem fatAddress_mem_Icc (x : Cantor) : fatAddress x ∈ Icc (0 : ℝ) 1 := by
  simpa only [pathInterval_zero] using fatAddress_mem_pathInterval x 0

private theorem dist_le_of_mem_retainedInterval {p : Bits n} {a b : ℝ}
    (ha : a ∈ retainedInterval p) (hb : b ∈ retainedInterval p) :
    dist a b ≤ retainedLength n := by
  change _ ≤ a ∧ a ≤ _ at ha
  change _ ≤ b ∧ b ≤ _ at hb
  rw [Real.dist_eq, abs_le]
  exact ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩

theorem fatAddress_oscillation (x y : Cantor) (h : readBits x n = readBits y n) :
    dist (fatAddress x) (fatAddress y) ≤ retainedLength n :=
  dist_le_of_mem_retainedInterval (fatAddress_mem_retainedInterval x n)
    (h.symm ▸ fatAddress_mem_retainedInterval y n)

private theorem eq_fatAddress_of_mem_pathInterval {x : Cantor} {z : ℝ}
    (hz : ∀ n, z ∈ pathInterval x n) : z = fatAddress x := by
  have bound (n : Nat) : dist z (fatAddress x) ≤ retainedLength n := by
    apply dist_le_of_mem_retainedInterval (p := readBits x n) _ (fatAddress_mem_retainedInterval x n)
    rw [retainedInterval_readBits]
    exact hz n
  exact dist_eq_zero.mp
    (le_antisymm (ge_of_tendsto' retainedLength_tendsto_zero bound) dist_nonneg)

/-- Complete a finite address by repeating the specified bit. -/
def extendRetained (p : Bits n) (b : Bool) (i : Nat) : Bool :=
  if hi : i < n then p[i] else b

@[simp] theorem readBits_extendRetained (p : Bits n) (b : Bool) :
    readBits (extendRetained p b) n = p := by
  apply Vector.ext
  intro i hi
  simp [extendRetained, hi]

theorem fatAddress_extendRetained (p : Bits n) (b : Bool) :
    fatAddress (extendRetained p b) =
      (if b then (retainedEndpoints p).2 else (retainedEndpoints p).1 : ℚ) := by
  let x := extendRetained p b
  let z := retainedLeft x n + (if b then retainedLength n else 0)
  have stable (k : Nat) :
      retainedLeft x (n + k) + (if b then retainedLength (n + k) else 0) = z := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have bit : x (n + k) = b := by simp [x, extendRetained]
      change retainedLeft x ((n + k) + 1) + (if b then retainedLength ((n + k) + 1) else 0) = z
      cases b <;> simp only [retainedLeft, bit, Bool.false_eq_true, if_false, if_true, add_zero] at ih ⊢
      · exact ih
      · linarith
  have mem (k : Nat) : z ∈ pathInterval x (n + k) := by
    rw [← stable k]
    have len := retainedLength_pos (n + k)
    cases b <;> simp only [pathInterval, Bool.false_eq_true, if_false, if_true, add_zero, mem_Icc] <;>
      constructor <;> linarith
  have h : fatAddress x = z := (eq_fatAddress_of_mem_pathInterval (fun m =>
    pathInterval_antitone x (show m ≤ n + m by omega) (mem m))).symm
  have left : retainedLeft x n = retainedLeft (extendWord p) n :=
    retainedLeft_reads _ _ _ (by simp [x])
  rw [h]
  cases b <;> simp [z, left, retainedEndpoints]

theorem fatAddress_continuous : Continuous fatAddress := by
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.mp hU (fatAddress x) hx
  obtain ⟨n, hn⟩ := ((tendsto_order.1 retainedLength_tendsto_zero).2 ε εpos).exists
  refine Filter.mem_of_superset ((cylinder_isOpen (readBits x n)).mem_nhds rfl) ?_
  intro y hy
  exact hε ((fatAddress_oscillation y x hy).trans_lt hn)

theorem fatAddress_injective : Function.Injective fatAddress := by
  intro x y h
  funext n
  have same := readBits_of_mem_pathIntervals x y (n + 1) (fatAddress x)
    (fatAddress_mem_pathInterval x (n + 1)) (h ▸ fatAddress_mem_pathInterval y (n + 1))
  simpa only [getElem_readBits] using congrArg (fun p : Bits (n + 1) => p[n]) same

/-- The image of the address map. It coincides with the intersection of the retained levels. -/
def fatCantorSet : Set ℝ := range fatAddress

theorem fatCantorSet_subset_Icc : fatCantorSet ⊆ Icc (0 : ℝ) 1 := by
  rintro z ⟨x, rfl⟩
  exact fatAddress_mem_Icc x

theorem fatAddress_isClosedEmbedding : IsClosedEmbedding fatAddress :=
  fatAddress_continuous.isClosedEmbedding fatAddress_injective

noncomputable def fatCantorHomeomorph : Cantor ≃ₜ fatCantorSet :=
  fatAddress_isClosedEmbedding.isEmbedding.toHomeomorph

theorem fatAddress_preimage_retainedInterval (p : Bits n) :
    fatAddress ⁻¹' retainedInterval p = cylinderSet p := by
  ext x
  constructor
  · intro hx
    have h := readBits_of_mem_pathIntervals x (extendWord p) n (fatAddress x)
      (fatAddress_mem_pathInterval x n) hx
    change readBits x n = p
    simpa only [readBits_extendWord] using h
  · intro hx
    change readBits x n = p at hx
    rw [← hx]
    exact fatAddress_mem_retainedInterval x n

/-- An open set pulls back to the cylinders whose entire retained intervals it contains. -/
theorem fatAddress_preimage_open {U : Set ℝ} (hU : IsOpen U) :
    fatAddress ⁻¹' U = ⋃ n, ⋃ p : Bits n, ⋃ (_ : retainedInterval p ⊆ U), cylinderSet p := by
  ext x
  simp only [mem_preimage, mem_iUnion]
  constructor
  · intro hx
    obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.mp hU (fatAddress x) hx
    obtain ⟨n, hn⟩ := ((tendsto_order.1 retainedLength_tendsto_zero).2 ε εpos).exists
    refine ⟨n, readBits x n, ?_, rfl⟩
    intro z hz
    exact hε ((dist_le_of_mem_retainedInterval hz (fatAddress_mem_retainedInterval x n)).trans_lt hn)
  · rintro ⟨n, p, included, hp⟩
    exact included (by rwa [← fatAddress_preimage_retainedInterval] at hp)

/-- Within an interval of depth `n`, the union remaining after `k` further levels. -/
noncomputable def retainedDescendants (p : Bits n) (k : Nat) : Set ℝ :=
  ⋃ q : Bits k, retainedInterval (p ++ q)

private theorem append_readBits_suffix (p : Bits n) {x : Cantor}
    (hx : x ∈ cylinderSet p) (k : Nat) :
    readBits x (n + k) = p ++ readBits (fun i => x (n + i)) k := by
  rw [readBits_add, show readBits x n = p from hx]

private theorem mem_cylinderSet_extend_append (p : Bits n) (q : Bits k) :
    extendWord (p ++ q) ∈ cylinderSet p := by
  change readBits (extendWord (p ++ q)) n = p
  have h := readBits_extendWord (p ++ q)
  have e := congrArg (fun w => takePrefix w n (Nat.le_add_right n k)) h
  have eq : takePrefix (p ++ q) n (Nat.le_add_right n k) = p := head_append p q
  simpa only [takePrefix_readBits, eq] using e

theorem retainedDescendants_antitone (p : Bits n) : Antitone (retainedDescendants p) := by
  intro k l h z hz
  obtain ⟨q, hq⟩ := mem_iUnion.mp hz
  let x := extendWord (p ++ q)
  have hx : z ∈ pathInterval x (n + l) := hq
  refine mem_iUnion.mpr ⟨readBits (fun i => x (n + i)) k, ?_⟩
  rw [← append_readBits_suffix p (mem_cylinderSet_extend_append p q), retainedInterval_readBits]
  exact pathInterval_antitone x (Nat.add_le_add_left h n) hx

theorem fatAddress_image_cylinder (p : Bits n) :
    fatAddress '' cylinderSet p = ⋂ k, retainedDescendants p k := by
  classical
  ext z
  rw [mem_iInter]
  constructor
  · rintro ⟨x, hx, rfl⟩ k
    refine mem_iUnion.mpr ⟨readBits (fun i => x (n + i)) k, ?_⟩
    rw [← append_readBits_suffix p hx]
    exact fatAddress_mem_retainedInterval x (n + k)
  · intro hz
    choose q hq using fun k => mem_iUnion.mp (hz k)
    let zₖ (k : Nat) : ℝ := fatAddress (extendWord (p ++ q k))
    have inImage (k : Nat) : zₖ k ∈ fatAddress '' cylinderSet p :=
      ⟨extendWord (p ++ q k), mem_cylinderSet_extend_append p (q k), rfl⟩
    have bound (k : Nat) : dist (zₖ k) z ≤ retainedLength (n + k) := by
      apply dist_le_of_mem_retainedInterval (p := p ++ q k) _ (hq k)
      have h := fatAddress_mem_retainedInterval (extendWord (p ++ q k)) (n + k)
      simpa only [readBits_extendWord] using h
    have lengths : Tendsto (fun k => retainedLength (n + k)) atTop (𝓝 0) := by
      have h := retainedLength_tendsto_zero.comp (tendsto_add_atTop_nat n)
      change Tendsto (fun k => retainedLength (k + n)) atTop (𝓝 0) at h
      simpa only [Nat.add_comm] using h
    have limit : Tendsto zₖ atTop (𝓝 z) :=
      tendsto_iff_dist_tendsto_zero.mpr
        (squeeze_zero (fun _ => dist_nonneg) bound lengths)
    have compact : IsCompact (fatAddress '' cylinderSet p) :=
      (cylinder_isClosed p).isCompact.image fatAddress_continuous
    exact compact.isClosed.mem_of_tendsto limit (Eventually.of_forall inImage)

private theorem retainedInterval_cast (eq : m = n) (p : Bits m) :
    retainedInterval (p.cast eq) = retainedInterval p := by
  subst n
  simp

theorem fatCantorSet_levels : fatCantorSet = ⋂ n, ⋃ p : Bits n, retainedInterval p := by
  have h : cylinderSet #v[] = (Set.univ : Set Cantor) := by
    ext x
    constructor
    · exact fun _ => mem_univ x
    · intro _
      change readBits x 0 = #v[]
      apply Vector.ext
      intro i hi
      omega
  simpa only [h, image_univ, retainedDescendants, Vector.empty_append, fatCantorSet,
    retainedInterval_cast]
    using fatAddress_image_cylinder (#v[] : Bits 0)

theorem retainedDescendants_volume (p : Bits n) (k : Nat) :
    volume (retainedDescendants p k) =
      ENNReal.ofReal ((2 : ℝ)^k * retainedLength (n + k)) := by
  classical
  have disj : Pairwise (Function.onFun Disjoint (fun q : Bits k => retainedInterval (p ++ q))) := by
    intro a b hab
    apply retainedIntervals_pairwise (n + k)
    intro e
    exact hab (by simpa only [tail_append] using congrArg (tail (m := n)) e)
  rw [retainedDescendants, measure_iUnion disj (fun q => (retainedInterval_isCompact _).isClosed.measurableSet)]
  simp only [retainedInterval_volume, tsum_fintype, Finset.sum_const, Finset.card_univ,
    card_bits, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  norm_num

theorem fatAddress_image_cylinder_volume (p : Bits n) :
    volume (fatAddress '' cylinderSet p) = ENNReal.ofReal (((2 : ℝ)⁻¹)^(n + 1)) := by
  have finite : ∃ k, volume (retainedDescendants p k) ≠ ∞ :=
    ⟨0, by rw [retainedDescendants_volume]; exact ENNReal.ofReal_ne_top⟩
  have measurable (k : Nat) : MeasurableSet (retainedDescendants p k) :=
    MeasurableSet.iUnion (fun _ => (retainedInterval_isCompact _).isClosed.measurableSet)
  have limMeasure := tendsto_measure_iInter_atTop (μ := volume)
    (fun k => (measurable k).nullMeasurableSet) (retainedDescendants_antitone p) finite
  rw [← fatAddress_image_cylinder p] at limMeasure
  have limFormula := (ENNReal.continuous_ofReal.continuousAt).tendsto.comp
    (retainedLength_mass_limit n)
  exact tendsto_nhds_unique limMeasure (limFormula.congr (fun k => (retainedDescendants_volume p k).symm))

/-- The first pushforward identity in equation (6). -/
theorem fatAddress_map_fairCoin :
    Measure.map fatAddress fairCoin = (2 : ℝ≥0∞) • volume.restrict fatCantorSet := by
  have embedding := fatAddress_isClosedEmbedding.measurableEmbedding
  have eq : fairCoin = (2 : ℝ≥0∞) • Measure.comap fatAddress volume := by
    apply measure_ext_cylinders
    intro n p
    rw [fairCoin_cylinder, Measure.smul_apply, smul_eq_mul, embedding.comap_apply,
      fatAddress_image_cylinder_volume, ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
    simpa only [pow_one] using (dyadic_cancel n 1).symm
  rw [eq, Measure.map_smul, embedding.map_comap]
  rfl

theorem fatAddress_preimage_volume_le {U : Set ℝ} (hU : MeasurableSet U) :
    fairCoin (fatAddress ⁻¹' U) ≤ (2 : ℝ≥0∞) * volume U := by
  rw [← Measure.map_apply fatAddress_continuous.measurable hU, fatAddress_map_fairCoin,
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hU]
  gcongr
  exact inter_subset_left

end Guo

#print axioms Guo.fatAddress_map_fairCoin
#print axioms Guo.fatAddress_extendRetained
