import Weak_3_Randomness_and_Luzin_N.GuoOutsideReflection
import Weak_3_Randomness_and_Luzin_N.GuoPolygon

open Filter Topology

namespace Guo
namespace SignedFraction

def ofRat (q : ℚ) : SignedFraction := (q.num.toNat, (-q.num).toNat, q.den - 1)

@[simp] theorem val_ofRat (q : ℚ) : (ofRat q).val = (q : ℝ) := by
  have num : (q.num.toNat : ℝ) - ((-q.num).toNat : ℝ) = (q.num : ℝ) := by
    generalize q.num = j
    cases j <;> simp
  have den : (↑(q.den - 1 : ℕ) : ℝ) + 1 = q.den := by
    exact_mod_cast Nat.sub_add_cancel q.den_pos
  rw [val, ofRat, num, den, Rat.cast_def]

end SignedFraction

private def bridgeWeight (l r : ℚ) (q : SignedFraction) : SignedFraction :=
  (q.add (SignedFraction.ofRat l).neg).mul (SignedFraction.ofRat ((r - l)⁻¹))

private def bridgeCoWeight (l r : ℚ) (q : SignedFraction) : SignedFraction :=
  SignedFraction.add (1, 0, 0) (bridgeWeight l r q).neg

private theorem bridgeWeight_primrec (l r : ℚ) : Primrec (bridgeWeight l r) :=
  SignedFraction.mul_primrec.comp
    (SignedFraction.add_primrec.comp Primrec.id (Primrec.const (SignedFraction.ofRat l).neg))
    (Primrec.const (SignedFraction.ofRat ((r - l)⁻¹)))

private theorem bridgeCoWeight_primrec (l r : ℚ) : Primrec (bridgeCoWeight l r) :=
  SignedFraction.add_primrec.comp (Primrec.const (1, 0, 0))
    (SignedFraction.neg_primrec.comp (bridgeWeight_primrec l r))

private theorem bridgeWeight_val (l r : ℚ) (q : SignedFraction) :
    (bridgeWeight l r q).val = (q.val - (l : ℝ)) / ((r : ℝ) - (l : ℝ)) := by
  simp [bridgeWeight, div_eq_mul_inv, sub_eq_add_neg]

private theorem bridgeCoWeight_val (l r : ℚ) (q : SignedFraction) :
    (bridgeCoWeight l r q).val = 1 - (bridgeWeight l r q).val := by
  rw [bridgeCoWeight, SignedFraction.val_add, SignedFraction.val_neg, ← sub_eq_add_neg]
  congr 1
  norm_num [SignedFraction.val]

private def dyadicFraction (code : ℕ × ℕ) : SignedFraction := SignedFraction.dyadic code.1 0 code.2

private theorem dyadicFraction_primrec : Primrec dyadicFraction :=
  SignedFraction.dyadic_primrec.comp (Primrec.fst.pair ((Primrec.const 0).pair Primrec.snd))

private theorem dyadicFraction_val (code : ℕ × ℕ) :
    (dyadicFraction code).val = (rationalEndpointCodeValue code : ℝ) := by
  simp [dyadicFraction, rationalEndpointCodeValue]

private def bridgeRadius (l r : ℚ) (q : SignedFraction) : SignedFraction :=
  (bridgeCoWeight l r q).bound.add (bridgeWeight l r q).bound

private theorem bridgeRadius_primrec (l r : ℚ) : Primrec (bridgeRadius l r) :=
  SignedFraction.add_primrec.comp (SignedFraction.bound_primrec.comp (bridgeCoWeight_primrec l r))
    (SignedFraction.bound_primrec.comp (bridgeWeight_primrec l r))

private def bridgeSample (l r : ℚ) (f₁ f₂ : ℕ → ℕ × ℕ)
    (q : SignedFraction × ℕ) : SignedFraction × SignedFraction :=
  let s₁ := (bridgeCoWeight l r q.1).mul (dyadicFraction (f₁ q.2))
  let s₂ := (bridgeWeight l r q.1).mul (dyadicFraction (f₂ q.2))
  (s₁.add s₂, (bridgeRadius l r q.1).mul (SignedFraction.dyadic 1 0 q.2))

private theorem bridgeSample_primrec (l r : ℚ) (f₁ f₂ : ℕ → ℕ × ℕ)
    (hf₁ : Primrec f₁) (hf₂ : Primrec f₂) : Primrec (bridgeSample l r f₁ f₂) := by
  have weight := (bridgeWeight_primrec l r).comp
    (Primrec.fst : Primrec (Prod.fst : SignedFraction × ℕ → SignedFraction))
  have coWeight := (bridgeCoWeight_primrec l r).comp
    (Primrec.fst : Primrec (Prod.fst : SignedFraction × ℕ → SignedFraction))
  have u := dyadicFraction_primrec.comp (hf₁.comp
    (Primrec.snd : Primrec (Prod.snd : SignedFraction × ℕ → ℕ)))
  have v := dyadicFraction_primrec.comp (hf₂.comp
    (Primrec.snd : Primrec (Prod.snd : SignedFraction × ℕ → ℕ)))
  have radius := SignedFraction.mul_primrec.comp ((bridgeRadius_primrec l r).comp Primrec.fst)
    (SignedFraction.dyadic_primrec.comp ((Primrec.const 1).pair ((Primrec.const 0).pair Primrec.snd)))
  exact (SignedFraction.add_primrec.comp (SignedFraction.mul_primrec.comp coWeight u)
    (SignedFraction.mul_primrec.comp weight v)).pair radius

theorem affineBridge_eq_line (f : ℝ → ℝ) (l r x : ℝ) :
    affineBridge f l r x =
      ((f r - f l) / (r - l)) * x + (f l - ((f r - f l) / (r - l)) * l) := by
  unfold affineBridge
  simp only [div_eq_mul_inv]
  ring

/-- Fixed rational abscissas and computable ordinates give rational enclosures
for the line through the two endpoint values, uniformly at every rational input. -/
def affineBridge_fractionEnclosure (l r : ℚ) (u v : ℝ) (f₁ f₂ : ℕ → ℕ × ℕ)
    (hf₁ : Primrec f₁) (hf₂ : Primrec f₂)
    (err₁ : ∀ k, |u - (rationalEndpointCodeValue (f₁ k) : ℝ)| ≤ ((2 : ℝ)^k)⁻¹)
    (err₂ : ∀ k, |v - (rationalEndpointCodeValue (f₂ k) : ℝ)| ≤ ((2 : ℝ)^k)⁻¹) :
    FractionEnclosure (fun x => ((v - u) / ((r : ℝ) - (l : ℝ))) * x +
      (u - ((v - u) / ((r : ℝ) - (l : ℝ))) * (l : ℝ))) where
  sample := bridgeSample l r f₁ f₂
  sample_primrec := bridgeSample_primrec l r f₁ f₂ hf₁ hf₂
  covers := by
    intro q k
    let w := (bridgeWeight l r q).val
    let cw := (bridgeCoWeight l r q).val
    let cb := (bridgeCoWeight l r q).bound.val
    let b := (bridgeWeight l r q).bound.val
    let u' : ℝ := rationalEndpointCodeValue (f₁ k)
    let v' : ℝ := rationalEndpointCodeValue (f₂ k)
    let δ := ((2 : ℝ)^k)⁻¹
    have er := show
        (v - u) / ((r : ℝ) - (l : ℝ)) * q.val +
            (u - (v - u) / ((r : ℝ) - (l : ℝ)) * (l : ℝ)) =
          cw * u + w * v from by
      dsimp [cw, w]
      rw [bridgeCoWeight_val, bridgeWeight_val]
      simp only [div_eq_mul_inv]
      ring
    have radius_eq : (bridgeSample l r f₁ f₂ (q, k)).2.val = (cb + b) * δ := by
      simp [bridgeSample, bridgeRadius, cb, b, δ, one_div]
    have approx_eq : (bridgeSample l r f₁ f₂ (q, k)).1.val = cw * u' + w * v' := by
      simp [bridgeSample, cw, w, u', v', dyadicFraction_val]
    change |(_ : ℝ) - (bridgeSample l r f₁ f₂ (q, k)).1.val| ≤ _
    rw [er, approx_eq, radius_eq]
    rw [show cw * u + w * v - (cw * u' + w * v') = cw * (u - u') + w * (v - v') by ring]
    have cPos : 0 ≤ cb := (abs_nonneg cw).trans (SignedFraction.val_bound _)
    have wPos : 0 ≤ b := (abs_nonneg w).trans (SignedFraction.val_bound _)
    calc
      _ ≤ |cw * (u - u')| + |w * (v - v')| := abs_add_le _ _
      _ = |cw| * |u - u'| + |w| * |v - v'| := by rw [abs_mul, abs_mul]
      _ ≤ cb * δ + b * δ := by
        exact add_le_add
          (mul_le_mul (SignedFraction.val_bound _) (err₁ k) (abs_nonneg _) cPos)
          (mul_le_mul (SignedFraction.val_bound _) (err₂ k) (abs_nonneg _) wPos)
      _ = _ := (add_mul _ _ _).symm
  shrinks := by
    intro q
    have geom := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by positivity) (show (2 : ℝ)⁻¹ < 1 by norm_num)
    simpa [bridgeSample, one_div, ← inv_pow] using geom.const_mul (bridgeRadius l r q).val

/-- The affine line used on a gap of the paper's candidate construction. -/
noncomputable def candidate_bridge_fractionEnclosure (C : CandidateWords)
    (hWitness : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2))
    (hWord : Primrec (fun i => (C.word i).toList))
    (p : Bits n) (q : Bits m) (left right : Bool) :
    let g := realAffineExtension (cantorOutput (candidateSchedule pairedReservation C))
    let l : ℝ := retainedCoordinate p left
    let r : ℝ := retainedCoordinate q right
    let a := (g r - g l) / (r - l)
    FractionEnclosure (fun x => a * x + (g l - a * l)) := by
  let schedule := candidateSchedule pairedReservation C
  let g := realAffineExtension (cantorOutput schedule)
  let names {d : ℕ} (w : Bits d) (side : Bool) (k : ℕ) :=
    rationalEndpointCode schedule (encodeOracleWord ⟨d, w⟩, side, k)
  have primrecName {d : ℕ} (w : Bits d) (side : Bool) : Primrec (names w side) :=
    (candidate_rationalEndpointCode_primrec C hWitness hWord).comp
      ((Primrec.const (encodeOracleWord ⟨d, w⟩)).pair ((Primrec.const side).pair Primrec.id))
  have nameError {d : ℕ} (w : Bits d) (side : Bool) (k : ℕ) :
      |g (retainedCoordinate w side : ℝ) - (rationalEndpointCodeValue (names w side k) : ℝ)|
        ≤ ((2 : ℝ)^k)⁻¹ := by
    let code := encodeOracleWord ⟨d, w⟩
    have decoded : decodeOracleWord code = ⟨d, w⟩ := decode_encodeOracleWord _
    have h := rationalEndpointCode_error schedule (code, side, k)
    change |g (retainedCoordinate (decodeOracleWord code).2 side : ℝ) -
      (rationalEndpointCodeValue (names w side k) : ℝ)| ≤ ((2 : ℝ)^k)⁻¹ at h
    rw [decoded] at h
    exact h
  exact affineBridge_fractionEnclosure (retainedCoordinate p left) (retainedCoordinate q right)
    (g (retainedCoordinate p left : ℝ)) (g (retainedCoordinate q right : ℝ))
    (names p left) (names q right) (primrecName p left) (primrecName q right)
    (nameError p left) (nameError q right)

#print axioms affineBridge_fractionEnclosure
#print axioms candidate_bridge_fractionEnclosure

end Guo
