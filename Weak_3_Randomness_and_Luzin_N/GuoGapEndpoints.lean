import Weak_3_Randomness_and_Luzin_N.GuoPolygon

open Set

namespace Guo

/-- Every point of a bounded complementary gap lies between two retained endpoints
from a single finite level. The extension there uses exactly those endpoint values. -/
theorem realAffineExtension_internal_gap (F : Cantor → Cantor) {x : ℝ}
    (unit : x ∈ Icc (0 : ℝ) 1) (outside : x ∉ fatCantorSet) :
    ∃ (n : ℕ) (p q : Bits n) (left right : Bool),
      let a : ℝ := retainedCoordinate p left
      let b : ℝ := retainedCoordinate q right
      x ∈ Ioo a b ∧ Disjoint fatCantorSet (Ioo a b) ∧
        ∀ y ∈ Ioo a b, realAffineExtension F y = affineBridge (realAffineExtension F) a b y := by
  rw [fatCantorSet_levels] at outside
  simp only [mem_iInter, mem_iUnion] at outside
  push Not at outside
  obtain ⟨n, omitted⟩ := outside
  let K := retainedLevelKnots n
  have compact : IsCompact K := (retainedLevelKnots_finite n).isCompact
  have zero : 0 ∈ K := zero_mem_retainedLevelKnots n
  have one : 1 ∈ K := one_mem_retainedLevelKnots n
  have subset : K ⊆ fatCantorSet := retainedLevelKnots_subset_fatCantorSet n
  have a : lastPoint K x ∈ K :=
    ((compact.inter_right isClosed_Iic).isGreatest_sSup ⟨0, zero, unit.1⟩).1.1
  have b : nextPoint K x ∈ K :=
    ((compact.inter_right isClosed_Ici).isLeast_sInf ⟨1, one, unit.2⟩).1.1
  obtain ⟨between, _, disjoint⟩ := outside_level_knots_gap n unit (not_exists.mpr omitted)
  obtain ⟨⟨p, l⟩, peq⟩ := a
  obtain ⟨⟨q, r⟩, qeq⟩ := b
  change (retainedCoordinate p l : ℝ) = lastPoint K x at peq
  change (retainedCoordinate q r : ℝ) = nextPoint K x at qeq
  have between' : x ∈ Ioo (↑(retainedCoordinate p l) : ℝ) (↑(retainedCoordinate q r) : ℝ) := by
    rw [peq, qeq]
    exact between
  have gap' : Disjoint fatCantorSet (Ioo (↑(retainedCoordinate p l) : ℝ) (↑(retainedCoordinate q r) : ℝ)) := by
    rw [peq, qeq]
    exact disjoint
  refine ⟨n, p, q, l, r, between', gap', fun y hy => ?_⟩
  have ha : (retainedCoordinate p l : ℝ) ∈ fatCantorSet := subset ⟨(p, l), rfl⟩
  have hb : (retainedCoordinate q r : ℝ) ∈ fatCantorSet := subset ⟨(q, r), rfl⟩
  unfold realAffineExtension
  exact affineExtension_on_gap_with_own_values (isCompact_range fatAddress_continuous)
    (subset zero) (subset one) fatCantorSet_subset_Icc _ ha hb gap' hy

theorem realAffineExtension_left_ray (F : Cantor → Cantor) {x : ℝ} (h : x ≤ 0) :
    realAffineExtension F x = realAffineExtension F 0 :=
  affineExtension_on_left_ray _ _ h

theorem realAffineExtension_right_ray (F : Cantor → Cantor) {x : ℝ} (h : 1 ≤ x) :
    realAffineExtension F x = realAffineExtension F 1 :=
  affineExtension_on_right_ray _ _ h

end Guo

#print axioms Guo.realAffineExtension_internal_gap
