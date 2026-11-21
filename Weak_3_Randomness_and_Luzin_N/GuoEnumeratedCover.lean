import Weak_3_Randomness_and_Luzin_N.GuoEnumeratedOpen
import Weak_3_Randomness_and_Luzin_N.GuoCover
import Mathlib.Data.Nat.Pairing

open Set MeasureTheory
open scoped ENNReal

namespace Guo

def enumeratedOpen (enum : Nat → Option FiniteWord) : Set Cantor :=
  {x | ∃ n, listedAt enum n x}

def unionOfWords (words : List FiniteWord) : Set Cantor :=
  {x | ∃ w ∈ words, x ∈ wordCylinder w}

/-- Compute the finite list associated to a single input cylinder and selected stage. -/
def coverWordsAt (schedule : Schedule) (t i : Nat) (p : FiniteWord) : List FiniteWord :=
  let n := outputWidth schedule t + (t + 1)
  ((wordsAtDepth n).filter (hasWordPrefix p)).map
    (fun w => ⟨n - i, readBits (cantorOutput schedule (extendWord w)) (n - i)⟩)

theorem union_coverWordsAt (schedule : Schedule) (t i : Nat) (p : FiniteWord)
    (hp : p.1 ≤ outputWidth schedule t + (t + 1)) :
    unionOfWords (coverWordsAt schedule t i p) = stageCylinderCover schedule t i p.2 hp := by
  ext x
  simp only [unionOfWords, mem_setOf_eq, coverWordsAt, List.mem_map, List.mem_filter,
    hasWordPrefix, dif_pos hp, decide_eq_true_eq, stageCylinderCover, mem_iUnion]
  constructor
  · rintro ⟨_, ⟨w, ⟨_, hpw⟩, rfl⟩, hx⟩
    exact ⟨⟨w, hpw⟩, hx⟩
  · rintro ⟨⟨w, eq⟩, hx⟩
    exact ⟨_, ⟨w, ⟨mem_wordsAtDepth w, eq⟩, rfl⟩, hx⟩

def suitableStage (schedule : Schedule) (i depth t : Nat) : Bool :=
  decide (max i depth ≤ t) && ((schedule t).index == some i)

theorem suitableStage_iff (schedule : Schedule) (i depth t : Nat) :
    suitableStage schedule i depth t = true ↔ max i depth ≤ t ∧ (schedule t).index = some i := by
  simp [suitableStage]

/-- A bounded check that this tick is the first suitable selection. -/
def firstSuitableStage (schedule : Schedule) (i depth t : Nat) : Bool :=
  suitableStage schedule i depth t &&
    !(List.range t).any (suitableStage schedule i depth)

theorem firstSuitableStage_iff (schedule : Schedule) (i depth t : Nat) :
    firstSuitableStage schedule i depth t = true ↔ suitableStage schedule i depth t = true ∧
      ∀ u < t, suitableStage schedule i depth u ≠ true := by
  simp [firstSuitableStage]

/-- At tick `(n,t)`, output the finite cover for pieces from enumeration step `n`. -/
def coverBatch (schedule : Schedule) (i : Nat) (enum : Nat → Option FiniteWord)
    (n t : Nat) : List FiniteWord :=
  (refinedEnumeration enum n).flatMap (fun p =>
    if firstSuitableStage schedule i p.1 t then coverWordsAt schedule t i p else [])

theorem coverBatch_finite_queries (schedule : Schedule) (i n t : Nat)
    (enum₀ enum₁ : Nat → Option FiniteWord) (agree : ∀ k ≤ n, enum₀ k = enum₁ k) :
    coverBatch schedule i enum₀ n t = coverBatch schedule i enum₁ n t := by
  simp only [coverBatch, refinedEnumeration_finite_queries enum₀ enum₁ n agree]

def enumeratedOutputCover (schedule : Schedule) (i : Nat) (enum : Nat → Option FiniteWord) :
    Set Cantor := {x | ∃ n t, x ∈ unionOfWords (coverBatch schedule i enum n t)}

/-- Dovetail enumeration time, selection time, and position in a finite output batch. -/
def coverEnumeration (schedule : Schedule) (i : Nat) (enum : Nat → Option FiniteWord)
    (tick : Nat) : Option FiniteWord :=
  let step := Nat.unpair tick
  let times := Nat.unpair step.1
  (coverBatch schedule i enum times.1 times.2)[step.2]?

theorem enumeratedOpen_coverEnumeration (schedule : Schedule) (i : Nat)
    (enum : Nat → Option FiniteWord) :
    enumeratedOpen (coverEnumeration schedule i enum) = enumeratedOutputCover schedule i enum := by
  ext x
  constructor
  · rintro ⟨tick, w, found, hx⟩
    exact ⟨(Nat.unpair (Nat.unpair tick).1).1, (Nat.unpair (Nat.unpair tick).1).2,
      w, List.mem_of_getElem? found, hx⟩
  · rintro ⟨n, t, w, hw, hx⟩
    obtain ⟨k, nth⟩ := List.mem_iff_getElem?.mp hw
    refine ⟨Nat.pair (Nat.pair n t) k, w, ?_, hx⟩
    simpa only [coverEnumeration, Nat.unpair_pair] using nth

private abbrev Region (enum : Nat → Option FiniteWord) :=
  {a : Nat × FiniteWord // a.2 ∈ refinedEnumeration enum a.1}

private theorem regions_cover (enum : Nat → Option FiniteWord) :
    enumeratedOpen enum = ⋃ a : Region enum, wordCylinder a.val.2 := by
  ext x
  simp only [enumeratedOpen, mem_setOf_eq, mem_iUnion]
  rw [← refinedEnumeration_covers enum x]
  exact ⟨fun ⟨n, w, hw, hx⟩ => ⟨⟨(n, w), hw⟩, hx⟩,
    fun ⟨a, hx⟩ => ⟨a.val.1, a.val.2, a.property, hx⟩⟩

private theorem regions_disjoint (enum : Nat → Option FiniteWord) :
    Pairwise (fun a b : Region enum => Disjoint (wordCylinder a.val.2) (wordCylinder b.val.2)) := by
  intro a b ne
  apply Set.disjoint_left.mpr
  intro x ha hb
  by_cases eq : a.val.1 = b.val.1
  · apply ne
    apply Subtype.ext
    apply Prod.ext eq
    have hb' : b.val.2 ∈ refinedEnumeration enum a.val.1 := by rw [eq]; exact b.property
    have depths := refinedEnumeration_same_depth enum a.val.1 a.property hb'
    have aw : readBits x a.val.2.1 = a.val.2.2 := ha
    have bw : readBits x b.val.2.1 = b.val.2.2 := hb
    exact Sigma.ext depths (by simpa only [← aw, ← bw] using
      (show HEq (readBits x a.val.2.1) (readBits x b.val.2.1) from depths ▸ HEq.rfl))
  · exact Set.disjoint_left.mp (refinedEnumeration_stage_disjoint enum eq)
      ⟨a.val.2, a.property, ha⟩ ⟨b.val.2, b.property, hb⟩

/-- The cover algorithm, at the level of cylinder streams, has the cost of Lemma 4.1. -/
theorem enumerated_output_cover_spec (schedule : Schedule) (i : Nat)
    (enum : Nat → Option FiniteWord) (σ : Bits l)
    (recurs : InfinitelySelected schedule i) (uses : UsesCylinder schedule i σ)
    (within : enumeratedOpen enum ⊆ cylinderSet σ) :
    IsOpen (enumeratedOutputCover schedule i enum) ∧
      cantorOutput schedule '' enumeratedOpen enum ⊆ enumeratedOutputCover schedule i enum ∧
      fairCoin (enumeratedOutputCover schedule i enum) ≤ (2 : ℝ≥0∞)^i * fairCoin (enumeratedOpen enum) := by
  classical
  have existsSuitable (w : FiniteWord) : ∃ t, suitableStage schedule i w.1 t = true := by
    obtain ⟨t, ht, chosen⟩ := recurs (max i w.1)
    exact ⟨t, (suitableStage_iff schedule i w.1 t).mpr ⟨ht, chosen⟩⟩
  let time (w : FiniteWord) := Nat.find (existsSuitable w)
  have first (w : FiniteWord) (t : Nat) :
      firstSuitableStage schedule i w.1 t = true ↔ t = time w := by
    rw [firstSuitableStage_iff]
    constructor
    · rintro ⟨works, noEarlier⟩
      have small : time w ≤ t := Nat.find_min' (existsSuitable w) works
      have notLess : ¬time w < t := fun lt => noEarlier (time w) lt (Nat.find_spec (existsSuitable w))
      omega
    · rintro rfl
      exact ⟨Nat.find_spec (existsSuitable w), fun _ hu => Nat.find_min (existsSuitable w) hu⟩
  have timeSpec (w : FiniteWord) : max i w.1 ≤ time w ∧ (schedule (time w)).index = some i :=
    (suitableStage_iff schedule i w.1 _).mp (Nat.find_spec (existsSuitable w))
  have enough (w : FiniteWord) : w.1 ≤ outputWidth schedule (time w) + (time w + 1) :=
    le_trans ((le_max_right i w.1).trans (timeSpec w).1) (by omega)
  let V (a : Region enum) : Set Cantor := stageCylinderCover schedule (time a.val.2) i a.val.2.2 (enough a.val.2)
  have exactOutput : enumeratedOutputCover schedule i enum = ⋃ a, V a := by
    ext x
    simp only [enumeratedOutputCover, mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨n, t, w, hw, hx⟩
      obtain ⟨p, hp, sent⟩ := List.mem_flatMap.mp hw
      have picked : firstSuitableStage schedule i p.1 t = true := by
        by_cases h : firstSuitableStage schedule i p.1 t = true
        · exact h
        · simp [h] at sent
      have when := (first p t).mp picked
      rw [if_pos picked, when] at sent
      refine ⟨⟨(n, p), hp⟩, ?_⟩
      change x ∈ stageCylinderCover schedule (time p) i p.2 (enough p)
      rw [← union_coverWordsAt]
      exact ⟨w, sent, hx⟩
    · rintro ⟨a, ha⟩
      let p := a.val.2
      change x ∈ stageCylinderCover schedule (time p) i p.2 (enough p) at ha
      rw [← union_coverWordsAt] at ha
      obtain ⟨w, hw, hx⟩ := ha
      refine ⟨a.val.1, time p, w, List.mem_flatMap.mpr ⟨p, a.property, ?_⟩, hx⟩
      simpa only [if_pos ((first p (time p)).mpr rfl)] using hw
  have regionSpec (a : Region enum) :
      IsOpen (V a) ∧ cantorOutput schedule '' wordCylinder a.val.2 ⊆ V a ∧
        fairCoin (V a) ≤ (2 : ℝ≥0∞)^i * fairCoin (wordCylinder a.val.2) := by
    let w := a.val.2
    apply stageCylinderCover_spec schedule (time w) i w.2 (enough w)
    · have bound := (le_max_left i w.1).trans (timeSpec w).1
      omega
    · intro x hx
      apply (uses (time w) (timeSpec w).2 x).mpr
      apply within
      rw [regions_cover]
      exact mem_iUnion.mpr ⟨a, hx⟩
  rw [exactOutput, regions_cover]
  refine ⟨isOpen_iUnion (fun a => (regionSpec a).1), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨a, (regionSpec a).2.1 ⟨x, ha, rfl⟩⟩
  · calc
      fairCoin (⋃ a, V a) ≤ ∑' a, fairCoin (V a) := measure_iUnion_le V
      _ ≤ ∑' a, (2 : ℝ≥0∞)^i * fairCoin (wordCylinder a.val.2) :=
        ENNReal.tsum_le_tsum (fun a => (regionSpec a).2.2)
      _ = (2 : ℝ≥0∞)^i * fairCoin (⋃ a : Region enum, wordCylinder a.val.2) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion (regions_disjoint enum) (fun a => measurable_cylinder a.val.2.2)]

theorem enumeratedOpen_clip (enum : Nat → Option FiniteWord) (p : FiniteWord) :
    enumeratedOpen (clipEnumeration enum p) = enumeratedOpen enum ∩ wordCylinder p := by
  ext x
  simp only [enumeratedOpen, mem_setOf_eq, mem_inter_iff, listedAt_clipEnumeration]
  exact ⟨fun ⟨n, hp, hx⟩ => ⟨⟨n, hx⟩, hp⟩, fun ⟨⟨n, hx⟩, hp⟩ => ⟨n, hp, hx⟩⟩

/-- The stream-level local cover starting from an arbitrary enumerated input open set. -/
theorem enumerated_local_cover (schedule : Schedule) (i : Nat) (σ : Bits l)
    (recurs : InfinitelySelected schedule i) (uses : UsesCylinder schedule i σ)
    (enum : Nat → Option FiniteWord) :
    let U := enumeratedOpen enum ∩ cylinderSet σ
    let V := enumeratedOutputCover schedule i (clipEnumeration enum ⟨l, σ⟩)
    IsOpen V ∧ cantorOutput schedule '' U ⊆ V ∧ fairCoin V ≤ (2 : ℝ≥0∞)^i * fairCoin U := by
  have inputEq := enumeratedOpen_clip enum ⟨l, σ⟩
  have spec := enumerated_output_cover_spec schedule i (clipEnumeration enum ⟨l, σ⟩) σ
    recurs uses (by rw [inputEq]; exact inter_subset_right)
  rw [inputEq] at spec
  exact spec

theorem enumerated_local_cover_stream (schedule : Schedule) (i : Nat) (σ : Bits l)
    (recurs : InfinitelySelected schedule i) (uses : UsesCylinder schedule i σ)
    (enum : Nat → Option FiniteWord) :
    let U := enumeratedOpen enum ∩ cylinderSet σ
    let V := enumeratedOpen (coverEnumeration schedule i (clipEnumeration enum ⟨l, σ⟩))
    IsOpen V ∧ cantorOutput schedule '' U ⊆ V ∧ fairCoin V ≤ (2 : ℝ≥0∞)^i * fairCoin U := by
  dsimp only
  rw [enumeratedOpen_coverEnumeration]
  exact enumerated_local_cover schedule i σ recurs uses enum

end Guo

#print axioms Guo.enumerated_output_cover_spec
#print axioms Guo.enumerated_local_cover
#print axioms Guo.enumerated_local_cover_stream
#print axioms Guo.coverEnumeration
