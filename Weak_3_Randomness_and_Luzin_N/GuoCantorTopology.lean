import Weak_3_Randomness_and_Luzin_N.GuoCantorMeasure
import Mathlib.Topology.Order

open Set Filter Topology
open MeasureTheory

namespace Guo

def extendWord (p : Bits n) (i : Nat) : Bool :=
  if hi : i < n then p[i] else false

@[simp] theorem readBits_extendWord (p : Bits n) : readBits (extendWord p) n = p := by
  apply Vector.ext
  intro i hi
  simp [extendWord, hi]

theorem cylinder_isOpen (p : Bits n) : IsOpen (cylinderSet p) := by
  rw [cylinder_eq_pi]
  exact isOpen_set_pi (Finset.finite_toSet _) (fun _ _ => isOpen_discrete _)

theorem cylinder_isClosed (p : Bits n) : IsClosed (cylinderSet p) := by
  rw [cylinder_eq_pi]
  exact isClosed_set_pi (fun _ _ => isClosed_discrete _)

theorem cylinder_prefix_subset (p : Bits n) (h : m ≤ n) :
    (cylinderSet p : Set Cantor) ⊆ cylinderSet (takePrefix p m h) := by
  intro x hx
  have eq : readBits x n = p := hx
  change readBits x m = takePrefix p m h
  rw [← eq, takePrefix_readBits]

theorem tendsto_of_prefixes (f : Nat → Cantor) (x : Cantor)
    (matching : ∀ n, readBits (f n) n = readBits x n) :
    Tendsto f atTop (𝓝 x) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  change ∀ᶠ n in atTop, x i = f n i
  rw [eventually_atTop]
  refine ⟨i + 1, fun n hn => ?_⟩
  have eq := congrArg (fun w : Bits n => w[i]'(by omega)) (matching n)
  simpa only [getElem_readBits] using eq.symm

/-- Prefix cylinders form a neighbourhood basis in the product topology. -/
theorem exists_cylinder_subset_open {U : Set Cantor} (hU : IsOpen U) (x : Cantor) (hx : x ∈ U) :
    ∃ n, (cylinderSet (readBits x n) : Set Cantor) ⊆ U := by
  classical
  by_contra! h
  have outside (n : Nat) : ∃ y ∈ cylinderSet (readBits x n), y ∉ U := by
    simpa only [Set.not_subset] using h n
  choose f hf hOut using outside
  have xOutside : x ∈ Uᶜ :=
    hU.isClosed_compl.mem_of_tendsto (tendsto_of_prefixes f x hf) (Eventually.of_forall hOut)
  exact xOutside hx

theorem continuous_of_finite_read (f : Bits n → Bool) :
    Continuous (fun x => f (readBits x n)) := by
  apply continuous_def.mpr
  intro U _
  have eq : (fun x => f (readBits x n)) ⁻¹' U =
      ⋃ p : {p : Bits n // f p ∈ U}, (cylinderSet p.val : Set Cantor) := by
    ext x
    simp only [mem_preimage, mem_iUnion]
    constructor
    · intro hx
      exact ⟨⟨readBits x n, hx⟩, rfl⟩
    · rintro ⟨⟨p, hp⟩, hx⟩
      change readBits x n = p at hx
      rwa [hx]
  rw [eq]
  exact isOpen_iUnion (fun p => cylinder_isOpen p.val)

theorem cantorOutput_continuous (schedule : Schedule) : Continuous (cantorOutput schedule) := by
  apply continuous_pi
  intro r
  exact continuous_of_finite_read
    (fun w => ((stagedCode schedule r).encode w).1[r]'(by have := outputWidth_ge schedule r; omega))

theorem stageOutput_continuous_bit (schedule : Schedule) (t : Nat) (r : Nat)
    (hr : r < outputWidth schedule t) :
    Continuous (fun x => (stageRead schedule t x).1[r]) :=
  continuous_of_finite_read (fun w => ((stagedCode schedule t).encode w).1[r])

theorem stageStored_continuous_bit (schedule : Schedule) (t : Nat) (r : Nat) (hr : r < t + 1) :
    Continuous (fun x => (stageRead schedule t x).2[r]) :=
  continuous_of_finite_read (fun w => ((stagedCode schedule t).encode w).2[r])

private abbrev Word := Σ n : Nat, Bits n

private def prefixGenerator : Set (Set Cantor) := Set.range (fun w : Word => cylinderSet w.2)

private theorem prefixGenerator_measurable :
    (inferInstance : MeasurableSpace Cantor) = MeasurableSpace.generateFrom prefixGenerator := by
  apply le_antisymm
  · rw [show (inferInstance : MeasurableSpace Cantor) = borel Cantor from BorelSpace.measurable_eq]
    apply MeasurableSpace.generateFrom_le
    intro U openU
    let W := {w : Word // cylinderSet w.2 ⊆ U}
    have union : U = ⋃ w : W, cylinderSet w.val.2 := by
      ext x
      simp only [mem_iUnion]
      constructor
      · intro hx
        obtain ⟨n, h⟩ := exists_cylinder_subset_open openU x hx
        exact ⟨⟨⟨n, readBits x n⟩, h⟩, rfl⟩
      · rintro ⟨w, hw⟩
        exact w.property hw
    rw [union]
    exact MeasurableSet.iUnion (fun w => MeasurableSpace.GenerateMeasurable.basic _ ⟨w.val, rfl⟩)
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨⟨_, p⟩, rfl⟩
    exact measurable_cylinder p

private theorem cylinder_subset_of_overlap {p : Bits m} {q : Bits n} (hmn : m ≤ n)
    (overlap : (cylinderSet p ∩ cylinderSet q).Nonempty) : cylinderSet q ⊆ cylinderSet p := by
  obtain ⟨x, hx, hy⟩ := overlap
  have prefixEq := cylinder_prefix_subset q hmn hy
  have eq : takePrefix q m hmn = p := (show readBits x m = takePrefix q m hmn from prefixEq).symm.trans hx
  simpa only [eq] using cylinder_prefix_subset q hmn

private theorem prefixGenerator_pi : IsPiSystem prefixGenerator := by
  rintro _ ⟨⟨m, p⟩, rfl⟩ _ ⟨⟨n, q⟩, rfl⟩ overlap
  rcases le_total m n with h | h
  · have included := cylinder_subset_of_overlap h overlap
    rw [inter_eq_right.mpr included]
    exact ⟨⟨n, q⟩, rfl⟩
  · have included := cylinder_subset_of_overlap h (by simpa only [inter_comm] using overlap)
    rw [inter_eq_left.mpr included]
    exact ⟨⟨m, p⟩, rfl⟩

theorem fairCoin_output_cylinder (schedule : Schedule) (p : Bits n) :
    fairCoin (cantorOutput schedule ⁻¹' cylinderSet p) = fairCoin (cylinderSet p) := by
  let code := stagedCode schedule n
  have hp : n ≤ outputWidth schedule n := (Nat.le_succ n).trans (outputWidth_ge schedule n)
  have eq : cantorOutput schedule ⁻¹' cylinderSet p = stageReadingEvent code p #v[] hp (Nat.zero_le _) := by
    ext x
    have outEq : takePrefix (code.read x).1 n hp = readBits (cantorOutput schedule x) n := by
      change takePrefix (stageRead schedule n x).1 n hp = _
      rw [← cantorOutput_reads]
      exact takePrefix_readBits _ _
    have empty : takePrefix (code.read x).2 0 (Nat.zero_le _) = #v[] := by
      apply Vector.ext
      intro r hr
      omega
    change readBits (cantorOutput schedule x) n = p ↔
      takePrefix (code.read x).1 n hp = p ∧ takePrefix (code.read x).2 0 (Nat.zero_le _) = #v[]
    simp only [outEq, empty, and_true]
  rw [eq, fairCoin_stageReadingEvent, fairCoin_cylinder, Nat.add_zero]

/-- A finite measure on Cantor space is determined by its values on prefix cylinders. -/
theorem measure_ext_cylinders {μ ν : Measure Cantor} [IsFiniteMeasure μ]
    (h : ∀ (n : Nat) (p : Bits n), μ (cylinderSet p) = ν (cylinderSet p)) : μ = ν := by
  have univEq : cylinderSet #v[] = (Set.univ : Set Cantor) := by
    ext x
    refine ⟨fun _ => mem_univ _, fun _ => ?_⟩
    change readBits x 0 = #v[]
    apply Vector.ext
    intro r hr
    omega
  refine Measure.ext_of_generateFrom_of_iUnion prefixGenerator (fun _ => Set.univ)
    prefixGenerator_measurable prefixGenerator_pi (iUnion_const _) (fun _ => ?_) (fun _ => ?_) ?_
  · exact ⟨⟨0, #v[]⟩, univEq⟩
  · exact measure_ne_top _ _
  · rintro _ ⟨⟨n, p⟩, rfl⟩
    exact h n p

/-- The permanent output preserves the fair-coin probability measure. -/
theorem cantorOutput_measurePreserving (schedule : Schedule) :
    MeasurePreserving (cantorOutput schedule) fairCoin fairCoin := by
  have hm := (cantorOutput_continuous schedule).measurable
  refine ⟨hm, measure_ext_cylinders (fun n p => ?_)⟩
  rw [Measure.map_apply hm (measurable_cylinder p)]
  exact fairCoin_output_cylinder schedule p

end Guo

#print axioms Guo.cantorOutput_measurePreserving
