import Weak_3_Randomness_and_Luzin_N.GuoCantorTopology
import Weak_3_Randomness_and_Luzin_N.GuoLocalFinite
import Mathlib.MeasureTheory.Integral.Average

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace Guo

section StableStorage

variable (schedule : Schedule) (A : Set Cantor)
variable (misses : ∀ t i x, x ∈ A → InfinitelySelected schedule i → ¬(schedule t).hitsAt i x)

private noncomputable def storageCutoff (n : Nat) : Nat :=
  Classical.choose (stored_prefix_stabilizes schedule A misses n)

private theorem storageCutoff_bound (n : Nat) : n ≤ storageCutoff schedule A misses n + 1 :=
  (Classical.choose_spec (stored_prefix_stabilizes schedule A misses n)).choose

private theorem storageCutoff_spec (n t : Nat) (ht : storageCutoff schedule A misses n ≤ t)
    (x : A) :
    takePrefix (stageRead schedule t x.val).2 n (by
        have := storageCutoff_bound schedule A misses n
        omega) =
      takePrefix (stageRead schedule (storageCutoff schedule A misses n) x.val).2 n
        (storageCutoff_bound schedule A misses n) :=
  (Classical.choose_spec (stored_prefix_stabilizes schedule A misses n)).choose_spec t ht x x.property

/-- The stable Cantor-space coordinate on `A`, defined bit by bit. -/
noncomputable def stableStorage (x : A) (r : Nat) : Bool :=
  (stageRead schedule (storageCutoff schedule A misses (r + 1)) x.val).2[r]'(by
    have := storageCutoff_bound schedule A misses (r + 1)
    omega)

theorem stableStorage_continuous : Continuous (stableStorage schedule A misses) := by
  apply continuous_pi
  intro r
  exact (stageStored_continuous_bit schedule (storageCutoff schedule A misses (r + 1)) r
    (by have := storageCutoff_bound schedule A misses (r + 1); omega)).comp continuous_subtype_val

theorem stableStorage_reads (n t : Nat) (ht : storageCutoff schedule A misses n ≤ t) (x : A) :
    readBits (stableStorage schedule A misses x) n =
      takePrefix (stageRead schedule t x.val).2 n (by
        have := storageCutoff_bound schedule A misses n
        omega) := by
  apply Vector.ext
  intro r hr
  simp only [getElem_readBits, getElem_takePrefix, stableStorage]
  let u := max t (storageCutoff schedule A misses (r + 1))
  have hu₀ : storageCutoff schedule A misses n ≤ u :=
    ht.trans (Nat.le_max_left _ _)
  have hu₁ : storageCutoff schedule A misses (r + 1) ≤ u := Nat.le_max_right _ _
  have sameWidth := (storageCutoff_spec schedule A misses n u hu₀ x).trans
    (storageCutoff_spec schedule A misses n t ht x).symm
  have sameBit := congrArg (fun w : Bits n => w[r]) sameWidth
  have cutoffBit := congrArg (fun w : Bits (r + 1) => w[r])
    (storageCutoff_spec schedule A misses (r + 1) u hu₁ x)
  simpa only [getElem_takePrefix] using cutoffBit.symm.trans (by
    simpa only [getElem_takePrefix] using sameBit)

end StableStorage

section ProductApproximation

private abbrev prefixPair (n : Nat) (z : Cantor × Cantor) : Bits n × Bits n :=
  (readBits z.1 n, readBits z.2 n)

private abbrev RelevantCell (H : Set (Cantor × Cantor)) (n : Nat) :=
  {pq : Bits n × Bits n // pq ∈ prefixPair n '' H}

private def approximation (H : Set (Cantor × Cantor)) (n : Nat) : Set (Cantor × Cantor) :=
  ⋃ pq : RelevantCell H n, cylinderSet pq.val.1 ×ˢ cylinderSet pq.val.2

private theorem mem_approximation_iff {H : Set (Cantor × Cantor)} {n : Nat} {z : Cantor × Cantor} :
    z ∈ approximation H n ↔ ∃ y ∈ H, prefixPair n z = prefixPair n y := by
  unfold approximation
  simp only [mem_iUnion, mem_prod]
  constructor
  · rintro ⟨⟨pq, y, hy, rfl⟩, hx, hz⟩
    exact ⟨y, hy, Prod.ext hx hz⟩
  · rintro ⟨y, hy, eq⟩
    exact ⟨⟨prefixPair n y, y, hy, rfl⟩, congrArg Prod.fst eq, congrArg Prod.snd eq⟩

private theorem approximation_measurable (H : Set (Cantor × Cantor)) (n : Nat) :
    MeasurableSet (approximation H n) :=
  .iUnion (fun pq => (measurable_cylinder pq.val.1).prod (measurable_cylinder pq.val.2))

private theorem approximation_antitone (H : Set (Cantor × Cantor)) : Antitone (approximation H) := by
  intro m n hmn z hz
  obtain ⟨y, hy, eq⟩ := mem_approximation_iff.mp hz
  refine mem_approximation_iff.mpr ⟨y, hy, Prod.ext ?_ ?_⟩
  · simpa only [takePrefix_readBits] using
      congrArg (fun pq : Bits n × Bits n => takePrefix pq.1 m hmn) eq
  · simpa only [takePrefix_readBits] using
      congrArg (fun pq : Bits n × Bits n => takePrefix pq.2 m hmn) eq

private theorem approximation_iInter (H : Set (Cantor × Cantor)) (hH : IsClosed H) :
    (⋂ n, approximation H n) = H := by
  ext z
  rw [mem_iInter]
  constructor
  · intro every
    have existsMatch n := mem_approximation_iff.mp (every n)
    choose y inH matching using existsMatch
    have leftLimit : Tendsto (fun n => (y n).1) atTop (𝓝 z.1) :=
      tendsto_of_prefixes _ _ (fun n => (congrArg Prod.fst (matching n)).symm)
    have rightLimit : Tendsto (fun n => (y n).2) atTop (𝓝 z.2) :=
      tendsto_of_prefixes _ _ (fun n => (congrArg Prod.snd (matching n)).symm)
    exact hH.mem_of_tendsto (leftLimit.prodMk_nhds rightLimit) (Eventually.of_forall inH)
  · intro hz n
    exact mem_approximation_iff.mpr ⟨z, hz, rfl⟩

private theorem measure_approximation_eq (code : StageCode h s) (H : Set (Cantor × Cantor))
    (n : Nat) (ho : n ≤ h) (hs : n ≤ s) :
    (fairCoin.prod fairCoin) (approximation H n) =
      fairCoin (⋃ pq : RelevantCell H n, stageReadingEvent code pq.val.1 pq.val.2 ho hs) := by
  have lhsDisjoint : Pairwise (fun p q : RelevantCell H n =>
      Disjoint (cylinderSet p.val.1 ×ˢ cylinderSet p.val.2) (cylinderSet q.val.1 ×ˢ cylinderSet q.val.2)) := by
    intro p q ne
    apply Set.disjoint_left.mpr
    intro z hp hq
    have pEq : prefixPair n z = p.val := Prod.ext hp.1 hp.2
    have qEq : prefixPair n z = q.val := Prod.ext hq.1 hq.2
    exact ne (Subtype.ext (pEq.symm.trans qEq))
  have rhsDisjoint : Pairwise (fun p q : RelevantCell H n =>
      Disjoint (stageReadingEvent code p.val.1 p.val.2 ho hs)
        (stageReadingEvent code q.val.1 q.val.2 ho hs)) := by
    intro p q ne
    let reading (x : Cantor) := (takePrefix (code.read x).1 n ho, takePrefix (code.read x).2 n hs)
    apply Set.disjoint_left.mpr
    intro x hx hy
    have pEq : reading x = p.val := Prod.ext hx.1 hx.2
    have qEq : reading x = q.val := Prod.ext hy.1 hy.2
    exact ne (Subtype.ext (pEq.symm.trans qEq))
  rw [approximation, measure_iUnion lhsDisjoint, measure_iUnion rhsDisjoint]
  · apply tsum_congr
    intro pq
    rw [Measure.prod_prod, fairCoin_cylinder, fairCoin_cylinder, fairCoin_stageReadingEvent, pow_add]
  · exact fun pq => measurable_stageReadingEvent code pq.val.1 pq.val.2 ho hs
  · exact fun pq => (measurable_cylinder pq.val.1).prod (measurable_cylinder pq.val.2)

end ProductApproximation

/-- Lemma 4.2 for the constructed Cantor-space map and a compact class missed by recurrent hits. -/
theorem compact_null_witness (schedule : Schedule) (A : Set Cantor) (hA : IsCompact A)
    (misses : ∀ t i x, x ∈ A → InfinitelySelected schedule i → ¬(schedule t).hitsAt i x) :
    ∃ D : Set Cantor, D ⊆ A ∧ IsCompact D ∧ fairCoin D = 0 ∧
      fairCoin A ≤ fairCoin (cantorOutput schedule '' D) := by
  classical
  let T := stableStorage schedule A misses
  let F := cantorOutput schedule
  let trace (x : A) : Cantor × Cantor := (F x.val, T x)
  let H : Set (Cantor × Cantor) := Set.range trace
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have conT : Continuous T := stableStorage_continuous schedule A misses
  have conF : Continuous F := cantorOutput_continuous schedule
  have compactH : IsCompact H := isCompact_range ((conF.comp continuous_subtype_val).prodMk conT)
  have massApprox (n : Nat) : fairCoin A ≤ (fairCoin.prod fairCoin) (approximation H n) := by
    let t := storageCutoff schedule A misses n
    have hs : n ≤ t + 1 := storageCutoff_bound schedule A misses n
    have ho := hs.trans (outputWidth_ge schedule t)
    let code := stagedCode schedule t
    rw [measure_approximation_eq code H n ho hs]
    apply measure_mono
    intro x hx
    let pq := prefixPair n (trace ⟨x, hx⟩)
    refine mem_iUnion.mpr ⟨⟨pq, trace ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩, ?_⟩
    constructor
    · change takePrefix (stageRead schedule t x).1 n ho = readBits (F x) n
      rw [← cantorOutput_reads schedule t x]
      exact takePrefix_readBits _ _
    · exact (stableStorage_reads schedule A misses n t (Nat.le_refl _) ⟨x, hx⟩).symm
  have massH : fairCoin A ≤ (fairCoin.prod fairCoin) H := by
    rw [← approximation_iInter H compactH.isClosed,
      (approximation_antitone H).measure_iInter
        (fun n => (approximation_measurable H n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
    exact le_iInf massApprox
  have integralH := Measure.prod_apply_symm (μ := fairCoin) (ν := fairCoin) compactH.isClosed.measurableSet
  have finiteIntegral :
      (∫⁻ y, fairCoin ((fun x : Cantor => (x, y)) ⁻¹' H) ∂fairCoin) ≠ ∞ := by
    rw [← integralH]
    exact measure_ne_top _ _
  obtain ⟨y, hy⟩ := exists_lintegral_le finiteIntegral
  let D : Set Cantor := Subtype.val '' (T ⁻¹' {y})
  have compactD : IsCompact D :=
    (isClosed_singleton.preimage conT).isCompact.image continuous_subtype_val
  have nullD : fairCoin D = 0 := by
    apply le_antisymm _ bot_le
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (show ((2 : ℝ≥0∞)⁻¹) < 1 by norm_num))
    intro n
    let t := storageCutoff schedule A misses n
    have hs : n ≤ t + 1 := storageCutoff_bound schedule A misses n
    have includesD : D ⊆ stageReadingEvent (stagedCode schedule t) #v[] (readBits y n)
        (Nat.zero_le _) hs := by
      rintro _ ⟨x, hx, rfl⟩
      have eq : T x = y := hx
      constructor
      · apply Vector.ext
        intro r hr
        omega
      · rw [← eq]
        exact (stableStorage_reads schedule A misses n t (Nat.le_refl _) x).symm
    simpa only [fairCoin_stageReadingEvent, Nat.zero_add] using (measure_mono (μ := fairCoin) includesD)
  have sectionImage : (fun x : Cantor => (x, y)) ⁻¹' H = F '' D := by
    ext f
    constructor
    · rintro ⟨x, eq⟩
      exact ⟨x.val, ⟨x, congrArg Prod.snd eq, rfl⟩, congrArg Prod.fst eq⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, Prod.ext rfl hx⟩
  refine ⟨D, ?_, compactD, nullD, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.property
  · exact massH.trans (integralH.le.trans (hy.trans_eq (congrArg fairCoin sectionImage)))

end Guo

#print axioms Guo.stableStorage_reads
#print axioms Guo.compact_null_witness
