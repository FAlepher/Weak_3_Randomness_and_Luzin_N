import Weak_3_Randomness_and_Luzin_N.GuoCantorTopology
import Weak_3_Randomness_and_Luzin_N.GuoLocalFinite
import Mathlib.MeasureTheory.Measure.Regular

open MeasureTheory Set
open scoped ENNReal

namespace Guo

private theorem cylinder_completions (p : Bits m) (hm : m ≤ n) :
    (cylinderSet p : Set Cantor) =
      ⋃ w : {w : Bits n // takePrefix w m hm = p}, cylinderSet w.val := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · intro hx
    refine ⟨⟨readBits x n, ?_⟩, rfl⟩
    change readBits x m = p at hx
    simpa only [takePrefix_readBits] using hx
  · rintro ⟨w, hx⟩
    have prefixMatch := cylinder_prefix_subset w.val hm hx
    simpa only [w.property] using prefixMatch

private theorem disjoint_cylinders_of_word_ne {p q : Bits n} (ne : p ≠ q) :
    Disjoint (cylinderSet p : Set Cantor) (cylinderSet q) := by
  rw [Set.disjoint_left]
  intro x hp hq
  exact ne ((show readBits x n = p from hp).symm.trans hq)

def stageCylinderCover (schedule : Schedule) (t i : Nat) (p : Bits m)
    (hm : m ≤ outputWidth schedule t + (t + 1)) : Set Cantor :=
  let n := outputWidth schedule t + (t + 1)
  ⋃ w : {w : Bits n // takePrefix w m hm = p},
    cylinderSet (readBits (cantorOutput schedule (extendWord w.val)) (n - i))

/-- The cylinder-cover estimate of Lemma 4.1, at one sufficiently late selected stage. -/
theorem stageCylinderCover_spec (schedule : Schedule) (t i : Nat) (p : Bits m)
    (hm : m ≤ outputWidth schedule t + (t + 1))
    (hi : i ≤ outputWidth schedule t + (t + 1))
    (hit : ∀ x ∈ cylinderSet p, (schedule t).hitsAt i x) :
    IsOpen (stageCylinderCover schedule t i p hm) ∧
      cantorOutput schedule '' cylinderSet p ⊆ stageCylinderCover schedule t i p hm ∧
      fairCoin (stageCylinderCover schedule t i p hm) ≤ (2 : ℝ≥0∞)^i * fairCoin (cylinderSet p) := by
  classical
  let n := outputWidth schedule t + (t + 1)
  let W := {w : Bits n // takePrefix w m hm = p}
  let V (w : W) : Set Cantor :=
    cylinderSet (readBits (cantorOutput schedule (extendWord w.val)) (n - i))
  have unionInput : (cylinderSet p : Set Cantor) = ⋃ w : W, cylinderSet w.val :=
    cylinder_completions p hm
  have disjointInputs : Pairwise (fun w w' : W =>
      Disjoint (cylinderSet w.val : Set Cantor) (cylinder w'.val)) := by
    intro w w' hNe
    exact disjoint_cylinders_of_word_ne (fun eq => hNe (Subtype.ext eq))
  change IsOpen (⋃ w, V w) ∧ cantorOutput schedule '' cylinderSet p ⊆ (⋃ w, V w) ∧
    fairCoin (⋃ w, V w) ≤ (2 : ℝ≥0∞)^i * fairCoin (cylinderSet p)
  refine ⟨isOpen_iUnion (fun w => cylinder_isOpen _), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [unionInput] at hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx
    have repIn : extendWord w.val ∈ (cylinderSet p : Set Cantor) := by
      rw [unionInput]
      exact mem_iUnion.mpr ⟨w, readBits_extendWord w.val⟩
    apply mem_iUnion.mpr
    refine ⟨w, image_of_hit_cylinder schedule t i (extendWord w.val)
      (hit _ repIn) x ?_⟩
    change readBits x n = readBits (extendWord w.val) n
    change readBits x n = w.val at hw
    simpa only [readBits_extendWord] using hw
  · have cost (w : W) : fairCoin (V w) = (2 : ℝ≥0∞)^i * fairCoin (cylinderSet w.val) := by
      unfold V
      rw [fairCoin_cylinder, fairCoin_cylinder]
      exact (dyadic_cancel (n - i) i).symm.trans
        (congrArg (fun k : Nat => (2 : ℝ≥0∞)^i * ((2 : ℝ≥0∞)⁻¹)^k) (Nat.sub_add_cancel hi))
    calc
      fairCoin (⋃ w, V w) ≤ ∑' w, fairCoin (V w) := measure_iUnion_le V
      _ = (2 : ℝ≥0∞)^i * fairCoin (cylinderSet p) := by
        rw [unionInput, measure_iUnion disjointInputs (fun w => measurable_cylinder w.val)]
        simp only [cost, ENNReal.tsum_mul_left]

theorem cover_cylinder_at_stage (schedule : Schedule) (t i : Nat) (p : Bits m)
    (hm : m ≤ outputWidth schedule t + (t + 1))
    (hi : i ≤ outputWidth schedule t + (t + 1))
    (hit : ∀ x ∈ cylinderSet p, (schedule t).hitsAt i x) :
    ∃ V : Set Cantor, IsOpen V ∧ cantorOutput schedule '' cylinderSet p ⊆ V ∧
      fairCoin V ≤ (2 : ℝ≥0∞)^i * fairCoin (cylinderSet p) :=
  ⟨stageCylinderCover schedule t i p hm, stageCylinderCover_spec schedule t i p hm hi hit⟩

/-- Combine the local bounds on a countable disjoint cylinder decomposition. -/
theorem cover_disjoint_cylinders {ι : Type*} [Countable ι] (F : Cantor → Cantor)
    (U : ι → Set Cantor) (c : ℝ≥0∞)
    (disjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    (measurable : ∀ i, MeasurableSet (U i))
    (covers : ∀ i, ∃ V : Set Cantor, IsOpen V ∧ F '' U i ⊆ V ∧ fairCoin V ≤ c * fairCoin (U i)) :
    ∃ V : Set Cantor, IsOpen V ∧ F '' (⋃ i, U i) ⊆ V ∧
      fairCoin V ≤ c * fairCoin (⋃ i, U i) := by
  classical
  choose V openV inside cost using covers
  refine ⟨⋃ i, V i, isOpen_iUnion openV, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, inside i ⟨x, hi, rfl⟩⟩
  · calc
      fairCoin (⋃ i, V i) ≤ ∑' i, fairCoin (V i) := measure_iUnion_le V
      _ ≤ ∑' i, c * fairCoin (U i) := ENNReal.tsum_le_tsum cost
      _ = c * fairCoin (⋃ i, U i) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion disjoint measurable]

private abbrev FirstCylinder (U : Set Cantor) :=
  {w : Σ n, Bits n // cylinderSet w.2 ⊆ U ∧
    ∀ j, ∀ hj : j < w.1, ¬cylinderSet (takePrefix w.2 j hj.le) ⊆ U}

private theorem first_cylinders_cover {U : Set Cantor} (openU : IsOpen U) :
    U = ⋃ w : FirstCylinder U, cylinderSet w.val.2 := by
  classical
  ext x
  rw [mem_iUnion]
  constructor
  · intro hx
    have existsDepth := exists_cylinder_subset_open openU x hx
    let n := Nat.find existsDepth
    have contained : cylinderSet (readBits x n) ⊆ U := Nat.find_spec existsDepth
    refine ⟨⟨⟨n, readBits x n⟩, contained, ?_⟩, rfl⟩
    intro j hj shallower
    exact Nat.find_min existsDepth hj (by simpa only [takePrefix_readBits] using shallower)
  · rintro ⟨w, hw⟩
    exact w.property.1 hw

private theorem first_cylinders_disjoint (U : Set Cantor) :
    Pairwise (fun w z : FirstCylinder U => Disjoint (cylinderSet w.val.2) (cylinderSet z.val.2)) := by
  intro w z wz
  apply Set.disjoint_left.mpr
  intro x hx hz
  have eqW : readBits x w.val.1 = w.val.2 := hx
  have eqZ : readBits x z.val.1 = z.val.2 := hz
  rcases lt_trichotomy w.val.1 z.val.1 with hlt | hEq | hgt
  · have eq : takePrefix z.val.2 w.val.1 hlt.le = w.val.2 := by
      rw [← eqZ, takePrefix_readBits, eqW]
    exact z.property.2 w.val.1 hlt (by rw [eq]; exact w.property.1)
  · apply wz
    apply Subtype.ext
    exact Sigma.ext hEq (by simpa only [← eqW, ← eqZ] using
      (show HEq (readBits x w.val.1) (readBits x z.val.1) from hEq ▸ HEq.rfl))
  · have eq : takePrefix w.val.2 z.val.1 hgt.le = z.val.2 := by
      rw [← eqW, takePrefix_readBits, eqZ]
    exact w.property.2 z.val.1 hgt (by rw [eq]; exact z.property.1)

/-- All visits to index `i` use the same word `σ`. -/
def UsesCylinder (schedule : Schedule) (i : Nat) (σ : Bits l) : Prop :=
  ∀ t, (schedule t).index = some i → ∀ x, (schedule t).hitsAt i x ↔ x ∈ cylinderSet σ

/-- The open-cover and measure conclusions of Lemma 4.1 with effectivity treated separately. -/
theorem cover_open_at_recurrent_index (schedule : Schedule) (i : Nat) (σ : Bits l)
    (recurs : InfinitelySelected schedule i) (uses : UsesCylinder schedule i σ)
    (U : Set Cantor) (openU : IsOpen U) :
    ∃ V : Set Cantor, IsOpen V ∧ cantorOutput schedule '' (U ∩ cylinderSet σ) ⊆ V ∧
      fairCoin V ≤ (2 : ℝ≥0∞)^i * fairCoin (U ∩ cylinderSet σ) := by
  let W := U ∩ cylinderSet σ
  have openW : IsOpen W := openU.inter (cylinder_isOpen σ)
  change ∃ V : Set Cantor, IsOpen V ∧ cantorOutput schedule '' W ⊆ V ∧
    fairCoin V ≤ (2 : ℝ≥0∞)^i * fairCoin W
  rw [first_cylinders_cover openW]
  apply cover_disjoint_cylinders (cantorOutput schedule) _ _ (first_cylinders_disjoint W)
  · intro w
    exact measurable_cylinder w.val.2
  · intro w
    obtain ⟨t, ht, chosen⟩ := recurs (max w.val.1 i)
    apply cover_cylinder_at_stage schedule t i w.val.2
    · have := (le_max_left w.val.1 i).trans ht
      omega
    · have := (le_max_right w.val.1 i).trans ht
      omega
    · intro x hx
      exact (uses t chosen x).mpr (w.property.1 hx).2

/-- The outer measure estimate for arbitrary subsets of a recurrent cylinder. -/
theorem outer_measure_image_at_recurrent_index (schedule : Schedule) (i : Nat) (σ : Bits l)
    (recurs : InfinitelySelected schedule i) (uses : UsesCylinder schedule i σ)
    (E : Set Cantor) (inside : E ⊆ cylinderSet σ) :
    fairCoin (cantorOutput schedule '' E) ≤ (2 : ℝ≥0∞)^i * fairCoin E := by
  conv_rhs => rw [E.measure_eq_iInf_isOpen fairCoin]
  simp_rw [ENNReal.mul_iInf_of_ne
    (show (2 : ℝ≥0∞)^i ≠ 0 by simp) (show (2 : ℝ≥0∞)^i ≠ ∞ by simp)]
  refine le_iInf fun U => le_iInf fun incl => le_iInf fun openU => ?_
  obtain ⟨V, _, cover, cost⟩ := cover_open_at_recurrent_index schedule i σ recurs uses U openU
  have imageSubset := (image_mono (subset_inter incl inside)).trans cover
  exact (measure_mono imageSubset).trans <|
    cost.trans (mul_le_mul_right (measure_mono inter_subset_left) _)

end Guo

#print axioms Guo.cover_cylinder_at_stage
#print axioms Guo.cover_disjoint_cylinders
#print axioms Guo.cover_open_at_recurrent_index
#print axioms Guo.outer_measure_image_at_recurrent_index
