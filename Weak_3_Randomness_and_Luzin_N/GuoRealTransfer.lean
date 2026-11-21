import Weak_3_Randomness_and_Luzin_N.GuoCantorTopology
import Mathlib.Analysis.Real.OfDigits
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace Guo

def binaryDigit (b : Bool) : Fin 2 := if b then 1 else 0

noncomputable def binaryEvaluation (x : Cantor) : ℝ :=
  Real.ofDigits (fun n => binaryDigit (x n))

theorem binaryEvaluation_continuous : Continuous binaryEvaluation := by
  have digitContinuous : Continuous binaryDigit := continuous_of_discreteTopology
  exact Real.continuous_ofDigits.comp (continuous_pi (fun n => digitContinuous.comp (continuous_apply n)))

theorem binaryEvaluation_oscillation (x y : Cantor) (h : readBits x n = readBits y n) :
    |binaryEvaluation x - binaryEvaluation y| ≤ ((2 : ℝ)^n)⁻¹ := by
  apply Real.abs_ofDigits_sub_ofDigits_le
  intro j hj
  apply congrArg binaryDigit
  simpa only [getElem_readBits] using congrArg (fun w : Bits n => w[j]) h

/-- The lengths of the retained intervals in the paper's fat Cantor set. -/
noncomputable def retainedLength (n : Nat) : ℝ :=
  ((2 : ℝ)⁻¹)^(n + 1) * (1 + ((2 : ℝ)⁻¹)^n)

theorem retainedLength_zero : retainedLength 0 = 1 := by norm_num [retainedLength]

theorem retainedLength_descendants (n k : Nat) :
    (2 : ℝ)^k * retainedLength (n + k) =
      ((2 : ℝ)⁻¹)^(n + 1) * (1 + ((2 : ℝ)⁻¹)^(n + k)) := by
  unfold retainedLength
  rw [← mul_assoc, show n + k + 1 = (n + 1) + k by omega, pow_add ((2 : ℝ)⁻¹) (n + 1) k]
  have cancel : (2 : ℝ)^k * (((2 : ℝ)⁻¹)^(n + 1) * ((2 : ℝ)⁻¹)^k) = ((2 : ℝ)⁻¹)^(n + 1) := by
    calc
      _ = ((2 : ℝ)⁻¹)^(n + 1) * (((2 : ℝ) * (2 : ℝ)⁻¹)^k) := by rw [mul_pow]; ring
      _ = _ := by norm_num
  rw [cancel]

theorem retainedLength_gap (n : Nat) : 2 * retainedLength (n + 1) < retainedLength n := by
  have powPos : 0 < ((2 : ℝ)⁻¹)^n := by positivity
  calc
    2 * retainedLength (n + 1) =
      ((2 : ℝ)⁻¹)^(n + 1) * (1 + ((2 : ℝ)⁻¹)^(n + 1)) := by
        simpa only [pow_one] using retainedLength_descendants n 1
    _ < retainedLength n := by
      unfold retainedLength
      apply mul_lt_mul_of_pos_left _ (by positivity)
      apply add_lt_add_right
      rw [pow_succ]
      exact mul_lt_of_lt_one_right powPos (by norm_num)

theorem retainedLength_mass_limit (n : Nat) :
    Tendsto (fun k : Nat => (2 : ℝ)^k * retainedLength (n + k)) atTop
      (𝓝 (((2 : ℝ)⁻¹)^(n + 1))) := by
  have geom := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by norm_num) (show (2 : ℝ)⁻¹ < 1 by norm_num)
  have tailLimit : Tendsto (fun k : Nat => ((2 : ℝ)⁻¹)^(n + k)) atTop (𝓝 0) := by
    simpa only [pow_add, mul_zero] using (geom.const_mul (((2 : ℝ)⁻¹)^n))
  have limit := ((tendsto_const_nhds (x := (1 : ℝ))).add tailLimit).const_mul (((2 : ℝ)⁻¹)^(n + 1))
  simpa only [add_zero, mul_one, retainedLength_descendants] using limit

/-- Transfer the compact witness once the two pushforward identities of (6) are available. -/
theorem real_compact_witness_of_pushforwards
    (F : Cantor → Cantor) (h b : Cantor → ℝ) (g : ℝ → ℝ) (C : Set ℝ)
    (hContinuous : Continuous h) (hInj : Function.Injective h)
    (hRange : range h ⊆ C) (hUnit : C ⊆ Icc 0 1)
    (bContinuous : Continuous b) (FContinuous : Continuous F)
    (hPush : Measure.map h fairCoin = (2 : ℝ≥0∞) • volume.restrict C)
    (bPush : Measure.map b fairCoin = volume.restrict (Icc 0 1))
    (gValues : ∀ x, g (h x) = b (F x))
    (D : Set Cantor) (dCompact : IsCompact D) (dNull : fairCoin D = 0) :
    ∃ B : Set ℝ, B ⊆ Icc 0 1 ∧ IsCompact B ∧ volume B = 0 ∧
      fairCoin (F '' D) ≤ volume (g '' B) := by
  let B := h '' D
  have BCompact : IsCompact B := dCompact.image hContinuous
  have BC : B ⊆ C := fun _ ⟨x, _, eq⟩ => hRange ⟨x, eq⟩
  have nullB : volume B = 0 := by
    have eq := congrArg (fun μ : Measure ℝ => μ B) hPush
    rw [Measure.map_apply hContinuous.measurable BCompact.isClosed.measurableSet,
      show h ⁻¹' B = D from preimage_image_eq _ hInj, dNull, Measure.smul_apply,
      Measure.restrict_apply BCompact.isClosed.measurableSet, inter_eq_left.mpr BC] at eq
    exact (mul_eq_zero.mp eq.symm).resolve_left (by norm_num)
  have imageEq : g '' B = b '' (F '' D) := by
    rw [show B = h '' D from rfl, image_image, image_image]
    exact image_congr (fun x _ => gValues x)
  refine ⟨B, BC.trans hUnit, BCompact, nullB, ?_⟩
  rw [imageEq]
  have outMeas : MeasurableSet (b '' (F '' D)) :=
    ((dCompact.image FContinuous).image bContinuous).isClosed.measurableSet
  calc
    fairCoin (F '' D) ≤ fairCoin (b ⁻¹' (b '' (F '' D))) := measure_mono (subset_preimage_image b _)
    _ = volume.restrict (Icc 0 1) (b '' (F '' D)) := by
      rw [← bPush, Measure.map_apply bContinuous.measurable outMeas]
    _ ≤ volume (b '' (F '' D)) := Measure.restrict_apply_le _ _

end Guo

#print axioms Guo.binaryEvaluation_oscillation
#print axioms Guo.retainedLength_mass_limit
#print axioms Guo.real_compact_witness_of_pushforwards
