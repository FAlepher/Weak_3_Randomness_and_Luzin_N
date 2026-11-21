import Weak_3_Randomness_and_Luzin_N.GuoGapEndpoints
import Weak_3_Randomness_and_Luzin_N.GuoEndpointTests
import Weak_3_Randomness_and_Luzin_N.GuoOutsideReflectionBridge

open Set

namespace Guo

/-- At an exterior point the candidate extension either takes the value of an
effective endpoint or agrees there with a nonconstant, effectively specified affine map. -/
theorem candidate_realAffineExtension_outside (C : CandidateWords)
    (effective : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2))
    (words : Primrec (fun i => (C.word i).toList)) {x : ℝ} (outside : x ∉ fatCantorSet) :
    let g := realAffineExtension (cantorOutput (candidateSchedule pairedReservation C))
    (∀ Z, RealFailsMartinLof Z (g x)) ∨
      ∃ a b : ℝ, a ≠ 0 ∧ g x = a * x + b ∧
        Nonempty (FractionEnclosure (fun y => a * y + b)) := by
  let schedule := candidateSchedule pairedReservation C
  let F := cantorOutput schedule
  let g := realAffineExtension F
  have endpoint {n : ℕ} (p : Bits n) (right : Bool) (Z : Oracle) :
      RealFailsMartinLof Z (g (retainedCoordinate p right)) := by
    let w := encodeOracleWord ⟨n, p⟩
    have value := retainedEndpoint_failsMartinLof Z C effective words w right
    have decoded : decodeOracleWord w = ⟨n, p⟩ := decode_encodeOracleWord _
    change RealFailsMartinLof Z (g (retainedCoordinate (decodeOracleWord w).2 right)) at value
    rw [decoded] at value
    exact value
  by_cases below : x ≤ 0
  · left
    intro Z
    change RealFailsMartinLof Z (g x)
    rw [show g x = g 0 from realAffineExtension_left_ray F below]
    have h := endpoint (#v[] : Bits 0) false Z
    norm_num [retainedCoordinate, retainedEndpoints, retainedLeftRat] at h
    exact h
  by_cases above : 1 ≤ x
  · left
    intro Z
    change RealFailsMartinLof Z (g x)
    rw [show g x = g 1 from realAffineExtension_right_ray F above]
    have h := endpoint (#v[] : Bits 0) true Z
    norm_num [retainedCoordinate, retainedEndpoints, retainedLeftRat, retainedLengthRat] at h
    exact h
  have unit : x ∈ Icc (0 : ℝ) 1 := ⟨(lt_of_not_ge below).le, (lt_of_not_ge above).le⟩
  obtain ⟨n, p, q, left, right, hx, _, onGap⟩ := realAffineExtension_internal_gap F unit outside
  let l : ℚ := retainedCoordinate p left
  let r : ℚ := retainedCoordinate q right
  let u := g l
  let v := g r
  let a := (v - u) / ((r : ℝ) - (l : ℝ))
  let b := u - a * (l : ℝ)
  have affine : g x = a * x + b := (onGap x hx).trans (affineBridge_eq_line g l r x)
  by_cases constant : a = 0
  · left
    intro Z
    change RealFailsMartinLof Z (g x)
    rw [affine, show a * x + b = g l by simp [b, constant, u]]
    exact endpoint p left Z
  · right
    exact ⟨a, b, constant, affine,
      ⟨candidate_bridge_fractionEnclosure C effective words p q left right⟩⟩

theorem candidate_realAffineExtension_reflects_outside (C : CandidateWords)
    (effective : Primrec (fun p : ℕ × ℕ × ℕ => C.witness p.1 p.2.1 p.2.2))
    (words : Primrec (fun i => (C.word i).toList)) (Z : Oracle) {x : ℝ} (outside : x ∉ fatCantorSet) :
    let g := realAffineExtension (cantorOutput (candidateSchedule pairedReservation C))
    (RealFailsWeak Z x → RealFailsWeak Z (g x)) ∧
      (RealFailsMartinLof Z x → RealFailsMartinLof Z (g x)) := by
  rcases candidate_realAffineExtension_outside C effective words outside with
    constant | ⟨_, _, nonzero, equal, ⟨affine⟩⟩
  · exact ⟨fun _ => realFailsWeak_of_failsMartinLof (constant Z), fun _ => constant Z⟩
  · constructor
    · intro h
      rw [equal]
      exact affine_transfers_weakFailure nonzero affine h
    · intro h
      rw [equal]
      exact affine_transfers_martinLofFailure nonzero affine h

end Guo

#print axioms Guo.candidate_realAffineExtension_reflects_outside
