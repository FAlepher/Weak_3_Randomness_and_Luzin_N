import Weak_3_Randomness_and_Luzin_N.GuoBinaryMeasure
import Weak_3_Randomness_and_Luzin_N.GuoOracleRates

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace Guo

/-- A dyadic open interval with endpoints `(lo - shift) / 2^depth` and
`(hi - shift) / 2^depth`. The subtraction in the endpoints is real subtraction. -/
abbrev DyadicIntervalCode := ℕ × ℕ × ℕ × ℕ

noncomputable def dyadicInterval (code : DyadicIntervalCode) : Set ℝ :=
  let (lo, hi, shift, depth) := code
  Ioo (((lo : ℝ) - shift) / (2 : ℝ)^depth) (((hi : ℝ) - shift) / (2 : ℝ)^depth)

abbrev RealOracleStream := ℕ × ℕ → Option DyadicIntervalCode

noncomputable def realOracleLayer (stream : RealOracleStream) (n : ℕ) : Set ℝ :=
  ⋃ tick, (stream (n, tick)).elim ∅ dyadicInterval

def RealOracleUniformOpen (Z : Oracle) (U : ℕ → Set ℝ) : Prop :=
  ∃ stream : RealOracleStream, ComputableIn {Z} stream ∧ ∀ n, realOracleLayer stream n = U n

def RealWeakTest (Z : Oracle) (U : ℕ → Set ℝ) : Prop :=
  RealOracleUniformOpen Z U ∧ volume (⋂ n, U n) = 0

def RealMartinLofTest (Z : Oracle) (U : ℕ → Set ℝ) : Prop :=
  RealOracleUniformOpen Z U ∧ ∀ n, volume (U n) ≤ ((2 : ℝ≥0∞)⁻¹)^n

def RealFailsWeak (Z : Oracle) (x : ℝ) : Prop :=
  ∃ U, RealWeakTest Z U ∧ ∀ n, x ∈ U n

def RealFailsMartinLof (Z : Oracle) (x : ℝ) : Prop :=
  ∃ U, RealMartinLofTest Z U ∧ ∀ n, x ∈ U n

theorem mem_realOracleLayer (stream : RealOracleStream) (n : ℕ) (x : ℝ) :
    x ∈ realOracleLayer stream n ↔
      ∃ tick code, stream (n, tick) = some code ∧ x ∈ dyadicInterval code := by
  rw [realOracleLayer, mem_iUnion]
  refine exists_congr fun tick => ?_
  cases stream (n, tick) <;> simp

theorem realOracleLayer_isOpen (stream : RealOracleStream) (n : ℕ) :
    IsOpen (realOracleLayer stream n) := by
  apply isOpen_iUnion
  intro tick
  cases stream (n, tick) with
  | none => exact isOpen_empty
  | some code =>
    change IsOpen (dyadicInterval code)
    exact isOpen_Ioo

def wordGridIndex (w : OracleWord) : ℕ :=
  w.foldl (fun acc bit => 2 * acc + bit.toNat) 0

theorem wordGridIndex_primrec : Primrec wordGridIndex := by
  have digit : Primrec Bool.toNat :=
    (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).of_eq (by decide)
  exact Primrec.list_foldl Primrec.id (Primrec.const 0)
    ((Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd))
      (digit.comp (Primrec.snd.comp Primrec.snd))).to₂)

theorem wordGridIndex_readBits (x : Cantor) (n : ℕ) :
    wordGridIndex (readBits x n).toList = binaryPrefixIndex x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [readBits_succ]
    simp [wordGridIndex, binaryPrefixIndex, ← ih]

def wordIntervalCode (w : OracleWord) : DyadicIntervalCode :=
  (wordGridIndex w, wordGridIndex w + 1, 0, w.length)

theorem wordIntervalCode_primrec : Primrec wordIntervalCode :=
  wordGridIndex_primrec.pair ((Primrec.succ.comp wordGridIndex_primrec).pair
    ((Primrec.const 0).pair Primrec.list_length))

theorem dyadicInterval_wordIntervalCode (w : OracleWord) :
    dyadicInterval (wordIntervalCode w) = binaryCylinderInterior (decodeOracleWord w).2 := by
  let p : Bits w.length := (decodeOracleWord w).2
  have word : p.toList = w := by simp [p, decodeOracleWord, Vector.toList]
  have grid : (binaryWordIndex w.length p).val = wordGridIndex w := by
    rw [← readBits_extendWord p, binaryWordIndex_readBits, ← wordGridIndex_readBits,
      readBits_extendWord, word]
  change dyadicInterval (wordIntervalCode w) = binaryCylinderInterior p
  simp [dyadicInterval, wordIntervalCode, binaryCylinderInterior, binaryCylinderLeft,
    binaryCylinderRight, grid]

def binaryOracleStream (stream : OracleStream) : RealOracleStream :=
  fun p => (stream p).map wordIntervalCode

section
attribute [local irreducible] ComputableIn

theorem binaryOracleStream_computableIn {Z : Oracle} {stream : OracleStream}
    (h : ComputableIn {Z} stream) : ComputableIn {Z} (binaryOracleStream stream) :=
  computableIn_comp (Primrec.option_map₁ wordIntervalCode_primrec).computableIn h
end

/-- Membership in a cell interior forces the projected prefix, even for overlapping streams. -/
theorem binaryEvaluation_preimage_interior_subset (p : Bits n) :
    binaryEvaluation ⁻¹' binaryCylinderInterior p ⊆ cylinderSet p := by
  intro x hx
  have grid := binaryWordIndex_readBits x n
  have scale := binaryEvaluation_scaled x n
  let k := (binaryWordIndex n p).val
  have tail := binaryEvaluation_mem_Icc (fun j => x (j + n))
  have pos : 0 < (2 : ℝ)^n := by positivity
  change (k : ℝ) / (2 : ℝ)^n < binaryEvaluation x ∧
    binaryEvaluation x < ((k : ℝ) + 1) / (2 : ℝ)^n at hx
  have lower := (div_lt_iff₀ pos).mp hx.1
  have upper := (lt_div_iff₀ pos).mp hx.2
  rw [mul_comm (binaryEvaluation x), scale] at lower upper
  have inequalities : (k : ℝ) < (binaryPrefixIndex x n : ℝ) + 1 ∧
      (binaryPrefixIndex x n : ℝ) < (k : ℝ) + 1 := ⟨by linarith [tail.2], by linarith [tail.1]⟩
  have inequalitiesNat : k < binaryPrefixIndex x n + 1 ∧ binaryPrefixIndex x n < k + 1 := by
    exact ⟨by exact_mod_cast inequalities.1, by exact_mod_cast inequalities.2⟩
  have eq : binaryPrefixIndex x n = k := by omega
  change readBits x n = p
  apply (binaryWordIndex n).injective
  exact Fin.ext (grid.trans eq)

theorem binaryOracleStream_layer_cost (stream : OracleStream) (n : ℕ) :
    volume (realOracleLayer (binaryOracleStream stream) n) ≤ fairCoin (oracleLayer stream n) := by
  let W := realOracleLayer (binaryOracleStream stream) n
  have openW : IsOpen W := realOracleLayer_isOpen _ _
  have inside : W ⊆ Icc (0 : ℝ) 1 := by
    intro z hz
    obtain ⟨t, code, eq, body⟩ := (mem_realOracleLayer _ _ _).mp hz
    obtain ⟨w, _, rfl⟩ := Option.map_eq_some_iff.mp eq
    rw [dyadicInterval_wordIntervalCode] at body
    have zImage : z ∈ binaryEvaluation '' cylinderSet (decodeOracleWord w).2 := by
      rw [binaryEvaluation_image_cylinder]
      exact ⟨body.1.le, body.2.le⟩
    obtain ⟨x, _, rfl⟩ := zImage
    exact binaryEvaluation_mem_Icc x
  have preimage : binaryEvaluation ⁻¹' W ⊆ oracleLayer stream n := by
    intro x hx
    obtain ⟨t, code, eq, body⟩ := (mem_realOracleLayer _ _ _).mp hx
    obtain ⟨w, occurs, rfl⟩ := Option.map_eq_some_iff.mp eq
    rw [dyadicInterval_wordIntervalCode] at body
    exact (mem_oracleLayer _ _ _).mpr ⟨t, w, occurs, binaryEvaluation_preimage_interior_subset _ body⟩
  calc
    volume W = (volume.restrict (Icc 0 1)) W := by
      rw [Measure.restrict_apply openW.measurableSet, inter_eq_left.mpr inside]
    _ = fairCoin (binaryEvaluation ⁻¹' W) := by
      rw [← binaryEvaluation_map_fairCoin, Measure.map_apply
        binaryEvaluation_continuous.measurable openW.measurableSet]
    _ ≤ fairCoin (oracleLayer stream n) := measure_mono preimage

theorem mem_binaryOracleStream_of_nondyadic (stream : OracleStream) (n : ℕ) (x : Cantor)
    (hx : x ∈ oracleLayer stream n) (nd : ¬ IsBinaryDyadic (binaryEvaluation x)) :
    binaryEvaluation x ∈ realOracleLayer (binaryOracleStream stream) n := by
  obtain ⟨t, w, occurs, hp⟩ := (mem_oracleLayer _ _ _).mp hx
  refine (mem_realOracleLayer _ _ _).mpr ⟨t, wordIntervalCode w, by simp [binaryOracleStream, occurs], ?_⟩
  rw [dyadicInterval_wordIntervalCode]
  let p := (decodeOracleWord w).2
  have hImage : binaryEvaluation x ∈ binaryEvaluation '' cylinderSet p := ⟨x, hp, rfl⟩
  rw [binaryEvaluation_image_cylinder] at hImage
  have leftNe : binaryEvaluation x ≠ binaryCylinderLeft p :=
    fun e => nd ⟨w.length, (binaryWordIndex _ p).val, e⟩
  have rightNe : binaryEvaluation x ≠ binaryCylinderRight p := by
    intro e
    exact nd ⟨(decodeOracleWord w).1, (binaryWordIndex _ p).val + 1,
      by simpa [binaryCylinderRight] using e⟩
  exact ⟨hImage.1.lt_of_ne leftNe.symm, hImage.2.lt_of_ne rightNe⟩

/-- Uniform translation of arbitrary oracle-enumerated cylinder layers into dyadic intervals. -/
theorem binaryEvaluation_uniform_test_layers {Z : Oracle} {U : ℕ → Set Cantor}
    (hU : OracleUniformOpen Z U) :
    ∃ W, RealOracleUniformOpen Z W ∧
      ∀ n, volume (W n) ≤ fairCoin (U n) ∧
        ∀ x ∈ U n, ¬ IsBinaryDyadic (binaryEvaluation x) → binaryEvaluation x ∈ W n := by
  obtain ⟨stream, compiled, eq⟩ := hU
  refine ⟨realOracleLayer (binaryOracleStream stream),
    ⟨_, binaryOracleStream_computableIn compiled, fun _ => rfl⟩, ?_⟩
  intro n
  rw [← eq]
  exact ⟨binaryOracleStream_layer_cost stream n, mem_binaryOracleStream_of_nondyadic stream n⟩

private theorem binaryEvaluation_transfers_martinLofFailure_of_nondyadic {Z : Oracle} {x : Cantor}
    (nd : ¬ IsBinaryDyadic (binaryEvaluation x))
    (fail : FailsMartinLof oracleOpenTestFramework Z x) :
    RealFailsMartinLof Z (binaryEvaluation x) := by
  obtain ⟨U, ⟨uniform, budgets⟩, hx⟩ := fail
  obtain ⟨W, compiled, spec⟩ := binaryEvaluation_uniform_test_layers uniform
  exact ⟨W, ⟨compiled, fun n => (spec n).1.trans (budgets n)⟩,
    fun n => (spec n).2 x (hx n) nd⟩

private theorem binaryEvaluation_transfers_weakFailure_of_nondyadic {Z : Oracle} {x : Cantor}
    (nd : ¬ IsBinaryDyadic (binaryEvaluation x))
    (fail : FailsWeak oracleOpenTestFramework Z x) : RealFailsWeak Z (binaryEvaluation x) := by
  obtain ⟨U, test, hx⟩ := fail
  have shrinks := inf_initialIntersections_zero oracleOpenTestFramework Z U test
  obtain ⟨W, compiled, spec⟩ := binaryEvaluation_uniform_test_layers
    (oracleOpenTestFramework.initialInter test.1)
  refine ⟨W, ⟨compiled, ?_⟩, fun n => (spec n).2 x (by simp [initialIntersections, hx]) nd⟩
  apply le_antisymm _ bot_le
  change volume (⋂ n, W n) ≤ 0
  rw [← shrinks]
  exact le_iInf fun n => (measure_mono (iInter_subset W n)).trans (spec n).1

private def dyadicPointCode (d k n : ℕ) : DyadicIntervalCode :=
  let s := k * 2 ^ (n + 2)
  (s, s + 2, 1, d + (n + 2))

private theorem dyadicPointCode_primrec (d k : ℕ) : Primrec (dyadicPointCode d k) := by
  have shift : Primrec (fun n : ℕ => n + 2) := Primrec.nat_add.comp Primrec.id (Primrec.const 2)
  have exponent : Primrec (fun n : ℕ => d + (n + 2)) :=
    Primrec.nat_add.comp (Primrec.const d) shift
  have scaled : Primrec (fun n : ℕ => k * 2^(n + 2)) := Primrec.nat_mul.comp
    (Primrec.const k) ((Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) shift)
  exact scaled.pair ((Primrec.nat_add.comp scaled (Primrec.const 2)).pair
    ((Primrec.const 1).pair exponent))

private theorem dyadicPointCode_mem (d k n : ℕ) :
    (k : ℝ) / (2 : ℝ)^d ∈ dyadicInterval (dyadicPointCode d k n) := by
  have scaled : (k : ℝ) / (2 : ℝ)^d * (2 : ℝ)^(d + (n + 2)) =
      (k : ℝ) * (2 : ℝ)^(n + 2) := by
    rw [pow_add, ← mul_assoc, div_mul_cancel₀ _ (by positivity)]
  have pos : 0 < (2 : ℝ)^(d + (n + 2)) := by positivity
  simp only [dyadicInterval, dyadicPointCode, mem_Ioo, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  rw [div_lt_iff₀ pos, lt_div_iff₀ pos, scaled]
  constructor <;> linarith

private theorem dyadicPointCode_volume (d k n : ℕ) :
    volume (dyadicInterval (dyadicPointCode d k n)) ≤ ((2 : ℝ≥0∞)⁻¹)^n := by
  simp only [dyadicInterval, dyadicPointCode, Real.volume_Ioo, div_sub_div_same, Nat.cast_add, Nat.cast_ofNat]
  rw [show ((↑(k * 2^(n + 2)) : ℝ) + 2 - ↑(1 : ℕ) -
    ((↑(k * 2^(n + 2)) : ℝ) - ↑(1 : ℕ))) = 2 by ring]
  have e : (2 : ℝ) / (2 : ℝ)^(d + (n + 2)) = ((2 : ℝ)^n)⁻¹ * ((2 : ℝ)^(d + 1))⁻¹ := by
    have exp : d + (n + 2) = n + (d + 1) + 1 := by omega
    rw [exp, pow_succ, pow_add]
    field_simp
  rw [e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_pow (by norm_num)]
  simp only [ENNReal.ofReal_ofNat, ENNReal.inv_pow]
  have unit : ((2 : ℝ≥0∞)⁻¹)^(d + 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (by norm_num)
  calc
    _ ≤ ((2 : ℝ≥0∞)⁻¹)^n * 1 := by gcongr
    _ = _ := mul_one _

/-- Every binary dyadic value is captured by a uniform interval test at any oracle. -/
theorem isBinaryDyadic_failsMartinLof (Z : Oracle) {x : ℝ} (h : IsBinaryDyadic x) :
    RealFailsMartinLof Z x := by
  obtain ⟨d, k, rfl⟩ := h
  let stream : RealOracleStream := fun p => some (dyadicPointCode d k p.1)
  have compiled : ComputableIn {Z} stream :=
    (Primrec.option_some.comp ((dyadicPointCode_primrec d k).comp Primrec.fst)).computableIn
  have eq (n : ℕ) : realOracleLayer stream n = dyadicInterval (dyadicPointCode d k n) := by
    change (⋃ _ : ℕ, dyadicInterval (dyadicPointCode d k n)) = _
    exact iUnion_const _
  exact ⟨realOracleLayer stream, ⟨⟨stream, compiled, fun _ => rfl⟩,
    fun n => eq n ▸ dyadicPointCode_volume d k n⟩,
    fun n => eq n ▸ dyadicPointCode_mem d k n⟩

theorem realFailsWeak_of_failsMartinLof {Z : Oracle} {x : ℝ} (h : RealFailsMartinLof Z x) :
    RealFailsWeak Z x := by
  obtain ⟨U, ⟨uniform, budget⟩, hx⟩ := h
  refine ⟨U, ⟨uniform, ?_⟩, hx⟩
  apply le_antisymm _ bot_le
  have lim := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (2 : ℝ≥0∞)⁻¹ < 1 by norm_num)
  have bound (n : ℕ) : volume (⋂ k, U k) ≤ ((2 : ℝ≥0∞)⁻¹)^n :=
    (measure_mono (iInter_subset U n)).trans (budget n)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds lim (Eventually.of_forall bound)

theorem binaryEvaluation_transfers_martinLofFailure {Z : Oracle} {x : Cantor}
    (fail : FailsMartinLof oracleOpenTestFramework Z x) :
    RealFailsMartinLof Z (binaryEvaluation x) := by
  by_cases h : IsBinaryDyadic (binaryEvaluation x)
  · exact isBinaryDyadic_failsMartinLof Z h
  · exact binaryEvaluation_transfers_martinLofFailure_of_nondyadic h fail

theorem binaryEvaluation_transfers_weakFailure {Z : Oracle} {x : Cantor}
    (fail : FailsWeak oracleOpenTestFramework Z x) :
    RealFailsWeak Z (binaryEvaluation x) := by
  by_cases h : IsBinaryDyadic (binaryEvaluation x)
  · exact realFailsWeak_of_failsMartinLof (isBinaryDyadic_failsMartinLof Z h)
  · exact binaryEvaluation_transfers_weakFailure_of_nondyadic h fail

end Guo

#print axioms Guo.binaryEvaluation_uniform_test_layers
#print axioms Guo.isBinaryDyadic_failsMartinLof
#print axioms Guo.binaryEvaluation_transfers_martinLofFailure
#print axioms Guo.binaryEvaluation_transfers_weakFailure
