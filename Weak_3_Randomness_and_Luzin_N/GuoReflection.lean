import Weak_3_Randomness_and_Luzin_N.GuoCantorTopology

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace Guo

def initialIntersections (U : Nat → Set Cantor) (n : Nat) : Set Cantor := ⋂ k ≤ n, U k

theorem initialIntersections_antitone (U : Nat → Set Cantor) :
    Antitone (initialIntersections U) := by
  intro m n hmn x hx
  simp only [initialIntersections, mem_iInter] at hx ⊢
  exact fun k hk => hx k (hk.trans hmn)

theorem initialIntersections_iInter (U : Nat → Set Cantor) :
    (⋂ n, initialIntersections U n) = ⋂ n, U n := by
  ext x
  simp only [initialIntersections, mem_iInter]
  exact ⟨fun hx n => hx n n le_rfl, fun hx _ k _ => hx k⟩

/--
The effective-open operations used in the reflection proof.
`Uniform Z U` is a premise about a sequence, not separate enumerability of its layers.
-/
structure OpenTestFramework (Oracle : Type*) where
  Uniform : Oracle → (Nat → Set Cantor) → Prop
  openLayers : ∀ {Z U}, Uniform Z U → ∀ n, IsOpen (U n)
  measurableLayers : ∀ {Z U}, Uniform Z U → ∀ n, MeasurableSet (U n)
  initialInter : ∀ {Z U}, Uniform Z U → Uniform Z (initialIntersections U)
  shift : ∀ {Z U}, Uniform Z U → ∀ d, Uniform Z (fun n => U (n + d))

variable {Oracle : Type*}

def WeakTest (E : OpenTestFramework Oracle) (Z : Oracle) (U : Nat → Set Cantor) : Prop :=
  E.Uniform Z U ∧ fairCoin (⋂ n, U n) = 0

def MartinLofTest (E : OpenTestFramework Oracle) (Z : Oracle) (U : Nat → Set Cantor) : Prop :=
  E.Uniform Z U ∧ ∀ n, fairCoin (U n) ≤ ((2 : ℝ≥0∞)⁻¹)^n

def FailsWeak (E : OpenTestFramework Oracle) (Z : Oracle) (x : Cantor) : Prop :=
  ∃ U, WeakTest E Z U ∧ ∀ n, x ∈ U n

def FailsMartinLof (E : OpenTestFramework Oracle) (Z : Oracle) (x : Cantor) : Prop :=
  ∃ U, MartinLofTest E Z U ∧ ∀ n, x ∈ U n

/-- A second-jump search for a certified small layer, without a least-index requirement. -/
def EffectiveRateSearch (E : OpenTestFramework Oracle) (first second : Oracle) : Prop :=
  ∀ U, E.Uniform first U →
    (∀ n : Nat, ∃ m, fairCoin (U m) < ((2 : ℝ≥0∞)⁻¹)^n) →
      ∃ chooseLayer : Nat → Nat,
        E.Uniform second (fun n => U (chooseLayer n)) ∧
          ∀ n, fairCoin (U (chooseLayer n)) < ((2 : ℝ≥0∞)⁻¹)^n

/-- The uniform-on-test-layers consequence of Theorem 2.1(1). -/
def EffectiveLocalCover (E : OpenTestFramework Oracle) (F : Cantor → Cantor) (A : Set Cantor) : Prop :=
  ∀ x ∉ A, ∃ (I : Set Cantor) (i : Nat), x ∈ I ∧
    ∀ Z U, E.Uniform Z U → ∃ V,
      E.Uniform Z V ∧ ∀ n, F '' (U n ∩ I) ⊆ V n ∧
        fairCoin (V n) ≤ (2 : ℝ≥0∞)^i * fairCoin (U n ∩ I)

theorem inf_initialIntersections_zero (E : OpenTestFramework Oracle) (Z : Oracle)
    (U : Nat → Set Cantor) (weak : WeakTest E Z U) :
    (⨅ n, fairCoin (initialIntersections U n)) = 0 := by
  have eq := (initialIntersections_antitone U).measure_iInter
    (μ := fairCoin) (fun n => (E.measurableLayers (E.initialInter weak.1) n).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩
  rw [initialIntersections_iInter, weak.2] at eq
  exact eq.symm

theorem failsMartinLof_of_failsWeak (E : OpenTestFramework Oracle) (first second : Oracle)
    (rate : EffectiveRateSearch E first second) (x : Cantor) :
    FailsWeak E first x → FailsMartinLof E second x := by
  rintro ⟨U, weak, hx⟩
  let C := initialIntersections U
  have zero : (⨅ n, fairCoin (C n)) = 0 := inf_initialIntersections_zero E first U weak
  have bounds (n : Nat) : ∃ m, fairCoin (C m) < ((2 : ℝ≥0∞)⁻¹)^n := by
    rw [← iInf_lt_iff, zero]
    exact ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) n
  obtain ⟨chooseLayer, uniform, cost⟩ := rate C (E.initialInter weak.1) bounds
  refine ⟨fun n => C (chooseLayer n), ⟨uniform, fun n => (cost n).le⟩, ?_⟩
  · intro n
    simp only [C, initialIntersections, mem_iInter]
    exact fun m _ => hx m

theorem local_cover_transfers_weak_failure (E : OpenTestFramework Oracle) (Z : Oracle)
    (F : Cantor → Cantor) (A : Set Cantor) (cover : EffectiveLocalCover E F A)
    {x : Cantor} (outside : x ∉ A) :
    FailsWeak E Z x → FailsWeak E Z (F x) := by
  rintro ⟨U, weak, hx⟩
  let C := initialIntersections U
  obtain ⟨I, i, hI, localCover⟩ := cover x outside
  obtain ⟨V, uniformV, bounds⟩ := localCover Z C (E.initialInter weak.1)
  refine ⟨V, ⟨uniformV, ?_⟩, ?_⟩
  · apply le_antisymm _ bot_le
    calc
      fairCoin (⋂ n, V n) ≤ ⨅ n, (2 : ℝ≥0∞)^i * fairCoin (C n) := by
        apply le_iInf
        intro n
        exact (measure_mono (iInter_subset V n)).trans <|
          (bounds n).2.trans <| mul_le_mul_right (measure_mono inter_subset_left) _
      _ = 0 := by
        rw [← ENNReal.mul_iInf_of_ne (by simp) (by simp),
          show (⨅ n, fairCoin (C n)) = 0 from inf_initialIntersections_zero E Z U weak, mul_zero]
  · intro n
    apply (bounds n).1
    refine ⟨x, ⟨?_, hI⟩, rfl⟩
    simp only [C, initialIntersections, mem_iInter]
    exact fun k _ => hx k

theorem local_cover_transfers_martinLof_failure (E : OpenTestFramework Oracle) (Z : Oracle)
    (F : Cantor → Cantor) (A : Set Cantor) (cover : EffectiveLocalCover E F A)
    {x : Cantor} (outside : x ∉ A) :
    FailsMartinLof E Z x → FailsMartinLof E Z (F x) := by
  rintro ⟨U, ml, hx⟩
  obtain ⟨I, i, hI, localCover⟩ := cover x outside
  obtain ⟨V, uniformV, bounds⟩ := localCover Z (fun n => U (n + i)) (E.shift ml.1 i)
  refine ⟨V, ⟨uniformV, ?_⟩, ?_⟩
  · intro n
    exact (bounds n).2.trans <| (mul_le_mul_right ((measure_mono inter_subset_left).trans
      (ml.2 (n + i))) _).trans_eq (dyadic_cancel n i)
  · intro n
    exact (bounds n).1 ⟨x, ⟨hx (n + i), hI⟩, rfl⟩

def UniversalMartinLofTest (E : OpenTestFramework Oracle) (Z : Oracle)
    (G : Nat → Set Cantor) : Prop :=
  MartinLofTest E Z G ∧ ∀ x, FailsMartinLof E Z x → ∀ n, x ∈ G n

/-- Choosing a small universal-test layer and transporting both test notions (Lemma 2.2). -/
theorem reflection_from_universal_test (E : OpenTestFramework Oracle) (first second : Oracle)
    (rate : EffectiveRateSearch E first second) (G : Nat → Set Cantor)
    (universal : UniversalMartinLofTest E second G) (ε : ℝ≥0∞) (εpos : 0 < ε) (εlt : ε < 1)
    (localize : ∀ n, 0 < fairCoin (G n)ᶜ → ∃ F : Cantor → Cantor,
      Continuous F ∧ MeasurePreserving F fairCoin fairCoin ∧ EffectiveLocalCover E F (G n)ᶜ) :
    ∃ n, ∃ F : Cantor → Cantor,
      IsClosed (G n)ᶜ ∧ 1 - ε ≤ fairCoin (G n)ᶜ ∧
      Continuous F ∧ MeasurePreserving F fairCoin fairCoin ∧
      (∀ x ∈ (G n)ᶜ, ¬FailsWeak E first x ∧ ¬FailsMartinLof E second x) ∧
      (∀ x, FailsWeak E first x → FailsWeak E first (F x)) ∧
      (∀ x, FailsMartinLof E second x → FailsMartinLof E second (F x)) := by
  have small (n : Nat) : fairCoin (G n) ≤ ((2 : ℝ≥0∞)⁻¹)^n := universal.1.2 n
  have limit := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (show ((2 : ℝ≥0∞)⁻¹) < 1 by norm_num)
  obtain ⟨n, hn⟩ := ((tendsto_order.1 limit).2 ε εpos).exists
  have measurable := E.measurableLayers universal.1.1 n
  have measureBound : 1 - ε ≤ fairCoin (G n)ᶜ := by
    rw [measure_compl measurable (measure_ne_top _ _), measure_univ]
    exact tsub_le_tsub_left ((small n).trans hn.le) _
  obtain ⟨F, continuous, preserving, cover⟩ :=
    localize n ((tsub_pos_of_lt εlt).trans_le measureBound)
  refine ⟨n, F, (E.openLayers universal.1.1 n).isClosed_compl, measureBound,
    continuous, preserving, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨fun fail => hx (universal.2 x (failsMartinLof_of_failsWeak E first second rate x fail) n),
      fun fail => hx (universal.2 x fail n)⟩
  · intro x fail
    have outside : x ∉ (G n)ᶜ := not_not_intro <|
      universal.2 x (failsMartinLof_of_failsWeak E first second rate x fail) n
    exact local_cover_transfers_weak_failure E first F _ cover outside fail
  · intro x fail
    have outside : x ∉ (G n)ᶜ := not_not_intro (universal.2 x fail n)
    exact local_cover_transfers_martinLof_failure E second F _ cover outside fail

end Guo

#print axioms Guo.failsMartinLof_of_failsWeak
#print axioms Guo.reflection_from_universal_test
