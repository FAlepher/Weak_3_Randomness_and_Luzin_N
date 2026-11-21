import Weak_3_Randomness_and_Luzin_N.GuoCantorCoding
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Guo

def cylinderSet (p : Bits n) : Set Cantor := {x | cylinder p x}

noncomputable def coin : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac false + (2 : ℝ≥0∞)⁻¹ • Measure.dirac true

instance : IsProbabilityMeasure coin where
  measure_univ := by
    simpa [coin, Measure.add_apply, Measure.smul_apply] using ENNReal.inv_two_add_inv_two

theorem coin_singleton (b : Bool) : coin {b} = (2 : ℝ≥0∞)⁻¹ := by
  cases b <;> simp [coin, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']

noncomputable def fairCoin : Measure Cantor := Measure.infinitePi (fun _ : Nat => coin)

instance : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

private def padded (p : Bits n) (i : Nat) : Bool :=
  if hi : i < n then p[i] else false

theorem cylinder_eq_pi (p : Bits n) :
    (cylinderSet p : Set Cantor) = Set.pi (↑(Finset.range n)) (fun i => {padded p i}) := by
  ext x
  change readBits x n = p ↔ ∀ i ∈ (↑(Finset.range n) : Set Nat), x i ∈ ({padded p i} : Set Bool)
  constructor
  · intro hx i hi
    have h : i < n := Finset.mem_range.mp hi
    have bit := congrArg (fun w : Bits n => w[i]) hx
    simpa [padded, h] using bit
  · intro hx
    apply Vector.ext
    intro i hi
    have bit := hx i (Finset.mem_range.mpr hi)
    simpa [padded, hi] using bit

theorem measurable_cylinder (p : Bits n) : MeasurableSet (cylinderSet p) := by
  rw [cylinder_eq_pi]
  exact MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_singleton _)

theorem fairCoin_cylinder (p : Bits n) : fairCoin (cylinderSet p) = ((2 : ℝ≥0∞)⁻¹) ^ n := by
  rw [fairCoin, cylinder_eq_pi, Measure.infinitePi_pi]
  · simp [coin_singleton]
  · exact fun _ _ => measurableSet_singleton _

def bitsEquiv (n : Nat) : Bits n ≃ (Fin n → Bool) where
  toFun w i := w[i.val]
  invFun := Vector.ofFn
  left_inv w := by apply Vector.ext; intro i hi; simp
  right_inv f := by funext i; simp

noncomputable instance bitsFintype (n : Nat) : Fintype (Bits n) :=
  Fintype.ofEquiv (Fin n → Bool) (bitsEquiv n).symm

theorem card_bits (n : Nat) : Fintype.card (Bits n) = 2 ^ n := by
  rw [Fintype.card_congr (bitsEquiv n), Fintype.card_fun]
  simp

theorem dyadic_cancel (base extra : Nat) :
    (2 : ℝ≥0∞)^extra * ((2 : ℝ≥0∞)⁻¹)^(base + extra) = ((2 : ℝ≥0∞)⁻¹)^base := by
  rw [pow_add]
  calc
    _ = ((2 : ℝ≥0∞)⁻¹)^base * ((((2 : ℝ≥0∞)⁻¹) * 2)^extra) := by
      rw [mul_pow]
      simp only [mul_comm, mul_left_comm]
    _ = _ := by rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow, mul_one]

def completionsEquiv (p : Bits j) (hj : j ≤ n) :
    {w : Bits n // takePrefix w j hj = p} ≃ Bits (n - j) := by
  have hn : n = j + (n - j) := by omega
  let k := n - j
  change {w : Bits n // takePrefix w j hj = p} ≃ Bits k
  have eq : n = j + k := hn
  refine {
    toFun := fun w => tail (w.val.cast eq)
    invFun := fun r => ⟨(p ++ r).cast eq.symm, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · apply Vector.ext
    intro i hi
    simp [Vector.getElem_append_left hi]
  · intro w
    apply Subtype.ext
    have headEq : head (m := j) (n := k) (w.val.cast eq) = p := by
      refine Eq.trans ?_ w.property
      apply Vector.ext
      intro i hi
      simp [head]
    have restored := congrArg (fun b : Bits (j + k) => b.cast eq.symm)
      (append_head_tail (w.val.cast eq))
    rwa [headEq, Vector.cast_cast, Vector.cast_rfl] at restored
  · intro r
    simp only [Vector.cast_cast, Vector.cast_rfl, tail_append]

section StageDistribution

variable (code : StageCode h s) (p : Bits j) (q : Bits k) (hp : j ≤ h) (hq : k ≤ s)

def stageReadingEvent : Set Cantor :=
  {x | takePrefix (code.read x).1 j hp = p ∧ takePrefix (code.read x).2 k hq = q}

private abbrev MatchingWords :=
  {w : Bits (h + s) //
    takePrefix (code.encode w).1 j hp = p ∧ takePrefix (code.encode w).2 k hq = q}

private def matchingEquiv :
    MatchingWords code p q hp hq ≃
      {u : Bits h // takePrefix u j hp = p} × {v : Bits s // takePrefix v k hq = q} where
  toFun w := (⟨(code.encode w).1, w.property.1⟩, ⟨(code.encode w).2, w.property.2⟩)
  invFun uv := ⟨code.decode (uv.1.val, uv.2.val), by
    rw [code.encode_decode]
    exact ⟨uv.1.property, uv.2.property⟩⟩
  left_inv w := Subtype.ext (code.decode_encode w)
  right_inv uv := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst (code.encode_decode _)
    · exact congrArg Prod.snd (code.encode_decode _)

private theorem stageReadingEvent_union :
    stageReadingEvent code p q hp hq = ⋃ w : MatchingWords code p q hp hq, cylinderSet w.val := by
  ext x
  simp only [stageReadingEvent, StageCode.read, mem_setOf_eq, mem_iUnion]
  constructor
  · intro matchRead
    exact ⟨⟨readBits x (h + s), matchRead⟩, rfl⟩
  · rintro ⟨w, hx⟩
    have eq : readBits x (h + s) = w.val := hx
    rw [eq]
    exact w.property

theorem measurable_stageReadingEvent : MeasurableSet (stageReadingEvent code p q hp hq) := by
  classical
  rw [stageReadingEvent_union]
  exact MeasurableSet.iUnion (fun w => measurable_cylinder w.val)

private theorem card_matchingWords :
    letI : Fintype (MatchingWords code p q hp hq) := Fintype.ofFinite _
    Fintype.card (MatchingWords code p q hp hq) = 2 ^ ((h - j) + (s - k)) := by
  classical
  letI : Fintype (MatchingWords code p q hp hq) := Fintype.ofFinite _
  let equiv := (matchingEquiv code p q hp hq).trans
    (Equiv.prodCongr (completionsEquiv p hp) (completionsEquiv q hq))
  rw [Fintype.card_congr equiv, Fintype.card_prod, card_bits, card_bits, pow_add]

/-- The fair-coin product formula of equation (4) for any stage code. -/
theorem fairCoin_stageReadingEvent :
    fairCoin (stageReadingEvent code p q hp hq) = ((2 : ℝ≥0∞)⁻¹) ^ (j + k) := by
  classical
  letI : Fintype (MatchingWords code p q hp hq) := Fintype.ofFinite _
  have disjoint : Pairwise (fun w w' : MatchingWords code p q hp hq =>
      Disjoint (cylinderSet w.val) (cylinderSet w'.val)) := by
    intro w w' ne
    apply Set.disjoint_left.mpr
    intro x hx hx'
    exact ne (Subtype.ext (show w.val = w'.val from Eq.trans (Eq.symm hx) hx'))
  rw [stageReadingEvent_union, measure_iUnion disjoint (fun w => measurable_cylinder w.val)]
  simp only [fairCoin_cylinder, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_matchingWords, Nat.cast_pow, Nat.cast_ofNat]
  have lengths : j + k + ((h - j) + (s - k)) = h + s := by omega
  rw [← lengths]
  exact dyadic_cancel _ _

end StageDistribution

end Guo

#print axioms Guo.fairCoin_cylinder
#print axioms Guo.fairCoin_stageReadingEvent
