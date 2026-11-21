import Weak_3_Randomness_and_Luzin_N.GuoEndpointComputable

open Set MeasureTheory
open scoped ENNReal

namespace Guo

private def approximationInterval (num : ℕ → ℕ) (n : ℕ) : DyadicIntervalCode :=
  (num (n + 2), num (n + 2) + 4, 2, n + 2)

private theorem approximationInterval_primrec {num : ℕ → ℕ} (hn : Primrec num) :
    Primrec (approximationInterval num) := by
  have depth : Primrec (fun n : ℕ => n + 2) := Primrec.nat_add.comp Primrec.id (Primrec.const 2)
  have centre := hn.comp depth
  exact centre.pair ((Primrec.nat_add.comp centre (Primrec.const 4)).pair
    ((Primrec.const 2).pair depth))

private theorem approximationInterval_volume (num : ℕ → ℕ) (n : ℕ) :
    volume (dyadicInterval (approximationInterval num n)) = ((2 : ℝ≥0∞)⁻¹)^n := by
  simp only [dyadicInterval, approximationInterval, Real.volume_Ioo, div_sub_div_same,
    Nat.cast_add, Nat.cast_ofNat]
  rw [show ((num (n + 2) : ℝ) + 4 - 2 - ((num (n + 2) : ℝ) - 2)) = 4 by ring]
  rw [show (4 : ℝ) / (2 : ℝ)^(n + 2) = ((2 : ℝ)^n)⁻¹ by
    rw [pow_add]
    norm_num
    field_simp]
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat, ENNReal.inv_pow]

/-- An explicit family of intervals for a point with effective nonnegative dyadic approximations. -/
theorem realFailsMartinLof_of_dyadic_approximation (Z : Oracle) {x : ℝ} (num : ℕ → ℕ)
    (hn : Primrec num)
    (error : ∀ k, |x - (num k : ℝ) / (2 : ℝ)^k| ≤ ((2 : ℝ)^k)⁻¹) :
    RealFailsMartinLof Z x := by
  let stream : RealOracleStream := fun p => some (approximationInterval num p.1)
  have compiled : ComputableIn {Z} stream :=
    (Primrec.option_some.comp ((approximationInterval_primrec hn).comp Primrec.fst)).computableIn
  have eq (n : ℕ) : realOracleLayer stream n = dyadicInterval (approximationInterval num n) := by
    change (⋃ _ : ℕ, dyadicInterval (approximationInterval num n)) = _
    exact iUnion_const _
  refine ⟨realOracleLayer stream, ⟨⟨stream, compiled, fun _ => rfl⟩, fun n => ?_⟩, fun n => ?_⟩
  · rw [eq, approximationInterval_volume]
  · rw [eq]
    have bounds := abs_le.mp (error (n + 2))
    have pos : 0 < ((2 : ℝ)^(n + 2))⁻¹ := by positivity
    change (↑(num (n + 2)) - ↑(2 : ℕ)) / (2 : ℝ)^(n + 2) < x ∧
      x < (↑(num (n + 2) + 4) - ↑(2 : ℕ)) / (2 : ℝ)^(n + 2)
    push_cast
    rw [sub_div, sub_div, add_div, div_eq_mul_inv 2, div_eq_mul_inv 4]
    constructor <;> linarith [bounds.1, bounds.2]

/-- The values at every retained endpoint fail the real tests, even with an arbitrary oracle. -/
theorem retainedEndpoint_failsMartinLof (Z : Oracle) (C : CandidateWords)
    (effective : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2))
    (words : Primrec (fun i => (C.word i).toList)) (w : OracleWord) (right : Bool) :
    let schedule := candidateSchedule pairedReservation C
    RealFailsMartinLof Z (realAffineExtension (cantorOutput schedule)
      ((if right then (retainedEndpoints (decodeOracleWord w).2).2
        else (retainedEndpoints (decodeOracleWord w).2).1 : ℚ) : ℝ)) := by
  let schedule := candidateSchedule pairedReservation C
  let numerator (k : ℕ) := (rationalEndpointCode schedule (w, right, k)).1
  have computed : Primrec numerator :=
    Primrec.fst.comp ((candidate_rationalEndpointCode_primrec C effective words).comp
      ((Primrec.const w).pair ((Primrec.const right).pair Primrec.id)))
  refine realFailsMartinLof_of_dyadic_approximation _ _ computed (fun k => ?_)
  have error := rationalEndpointCode_error schedule (w, right, k)
  simpa only [rationalEndpointCodeValue, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_ofNat, rationalEndpointCode, numerator] using error

end Guo

#print axioms Guo.realFailsMartinLof_of_dyadic_approximation
#print axioms Guo.retainedEndpoint_failsMartinLof
