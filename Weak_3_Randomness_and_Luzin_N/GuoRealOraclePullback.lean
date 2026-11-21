import Weak_3_Randomness_and_Luzin_N.GuoFatCantor
import Weak_3_Randomness_and_Luzin_N.GuoRealOracleTests

open Set MeasureTheory Encodable
open scoped ENNReal

namespace Guo

private def retainedGridStep (s : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  (4 * s.1 + (bif b then 2 * s.2 + 3 else 0), 2 * s.2)

private theorem retainedGridStep_primrec : Primrec₂ retainedGridStep := by
  have base : Primrec (fun p : (ℕ × ℕ) × Bool => 4 * p.1.1) :=
    Primrec.nat_mul.comp (Primrec.const 4) (Primrec.fst.comp Primrec.fst)
  have scale : Primrec (fun p : (ℕ × ℕ) × Bool => 2 * p.1.2) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.fst)
  have move : Primrec (fun p : (ℕ × ℕ) × Bool => bif p.2 then 2 * p.1.2 + 3 else 0) :=
    Primrec.cond Primrec.snd (Primrec.nat_add.comp scale (Primrec.const 3)) (Primrec.const 0)
  exact ((Primrec.nat_add.comp base move).pair scale).to₂

private def retainedGrid (w : OracleWord) : ℕ × ℕ := w.foldl retainedGridStep (0, 1)

private theorem retainedGrid_primrec : Primrec retainedGrid :=
  Primrec.list_foldl Primrec.id (Primrec.const _) (retainedGridStep_primrec.comp
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

private theorem retainedLength_scaled (n : ℕ) :
    retainedLength n * (2 : ℝ)^(2 * n + 1) = (2 : ℝ)^n + 1 := by
  rw [retainedLength, inv_pow, inv_pow, show 2 * n + 1 = (n + 1) + n by omega, pow_add]
  field_simp
  rw [pow_add, pow_succ]
  ring

private theorem retainedGrid_readBits (x : Cantor) (n : ℕ) :
    let s := retainedGrid (readBits x n).toList
    (s.1 : ℝ) = retainedLeft x n * (2 : ℝ)^(2 * n + 1) ∧ s.2 = 2 ^ n := by
  induction n with
  | zero =>
    have empty : readBits x 0 = (#v[] : Bits 0) := by
      apply Vector.ext
      intro i hi
      omega
    rw [empty]
    norm_num [retainedGrid, retainedLeft]
  | succ n ih =>
    let s := retainedGrid (readBits x n).toList
    change (s.1 : ℝ) = retainedLeft x n * (2 : ℝ)^(2 * n + 1) ∧ s.2 = 2^n at ih
    have step : retainedGrid (readBits x (n + 1)).toList = retainedGridStep s (x n) := by
      simp [readBits_succ, retainedGrid, s]
    have depth : (2 : ℝ)^(2 * (n + 1) + 1) = 4 * (2 : ℝ)^(2 * n + 1) := by
      rw [show 2 * (n + 1) + 1 = 2 + (2 * n + 1) by omega, pow_add]
      norm_num
    have current := retainedLength_scaled (n + 1)
    rw [depth, show (2 : ℝ)^(n + 1) + 1 = 2 * (2 : ℝ)^n + 1 by rw [pow_succ]; ring] at current
    have previous := retainedLength_scaled n
    dsimp only
    rw [step, depth, retainedLeft]
    constructor
    · cases x n <;>
        simp only [retainedGridStep, Bool.cond_false, Bool.cond_true, Bool.false_eq_true,
          if_false, if_true, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
          add_zero, ih.1, ih.2] <;> linarith only [current, previous]
    · simp only [retainedGridStep, ih.2, pow_succ, Nat.mul_comm]

/-- The two endpoint numerators and their common dyadic denominator exponent. -/
def retainedIntervalCode (w : OracleWord) : ℕ × ℕ × ℕ :=
  let s := retainedGrid w
  (s.1, s.1 + s.2 + 1, 2 * w.length + 1)

theorem retainedIntervalCode_primrec : Primrec retainedIntervalCode := by
  have lower := Primrec.fst.comp retainedGrid_primrec
  have scale := Primrec.snd.comp retainedGrid_primrec
  exact lower.pair ((Primrec.succ.comp (Primrec.nat_add.comp lower scale)).pair
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.list_length)))

theorem retainedInterval_eq_grid (w : OracleWord) :
    let (lo, hi, d) := retainedIntervalCode w
    retainedInterval (decodeOracleWord w).2 =
      Icc ((lo : ℝ) / (2 : ℝ)^d) ((hi : ℝ) / (2 : ℝ)^d) := by
  let p : Bits w.length := (decodeOracleWord w).2
  have wEq : (readBits (extendWord p) w.length).toList = w := by
    rw [readBits_extendWord p]
    simp [p, decodeOracleWord, Vector.toList]
  have h := retainedGrid_readBits (extendWord p) w.length
  dsimp only at h
  rw [wEq] at h
  have len := retainedLength_scaled w.length
  have pos : 0 < (2 : ℝ)^(2 * w.length + 1) := by positivity
  have lo := (eq_div_iff pos.ne').mpr h.1.symm
  have hi : retainedLeft (extendWord p) w.length + retainedLength w.length =
      ((↑(retainedGrid w).1 : ℝ) + ↑(retainedGrid w).2 + 1) / (2 : ℝ)^(2 * w.length + 1) := by
    apply (eq_div_iff pos.ne').mpr
    rw [add_mul, ← h.1, len, h.2]
    push_cast
    ring
  change retainedInterval p = _
  rw [retainedInterval_eq_Icc]
  simp only [retainedEndpoints, Rat.cast_add, cast_retainedLengthRat, cast_retainedLeftRat,
    Nat.cast_add, Nat.cast_one]
  rw [hi, lo]

private def gridContained (w : OracleWord) (interval : DyadicIntervalCode) : Prop :=
  let (l, r, d) := retainedIntervalCode w
  let (a, b, s, e) := interval
  a * 2^d < s * 2^d + l * 2^e ∧ s * 2^d + r * 2^e < b * 2^d

private instance (w : OracleWord) (interval : DyadicIntervalCode) : Decidable (gridContained w interval) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem gridContained_primrec : PrimrecRel gridContained := by
  have power : Primrec (fun n : ℕ => 2^n) :=
    (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id
  have word : Primrec (fun p : OracleWord × DyadicIntervalCode => retainedIntervalCode p.1) :=
    retainedIntervalCode_primrec.comp Primrec.fst
  have d := power.comp (Primrec.snd.comp (Primrec.snd.comp word))
  have interval : Primrec (Prod.snd : OracleWord × DyadicIntervalCode → _) := Primrec.snd
  have e := power.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp interval)))
  have a := Primrec.fst.comp interval
  have b := Primrec.fst.comp (Primrec.snd.comp interval)
  have s := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp interval))
  have lo := Primrec.fst.comp word
  have hi := Primrec.fst.comp (Primrec.snd.comp word)
  have shift := Primrec.nat_mul.comp s d
  exact (Primrec.nat_lt.comp (Primrec.nat_mul.comp a d)
    (Primrec.nat_add.comp shift (Primrec.nat_mul.comp lo e))).and
    (Primrec.nat_lt.comp (Primrec.nat_add.comp shift (Primrec.nat_mul.comp hi e))
      (Primrec.nat_mul.comp b d))

private theorem gridContained_iff (w : OracleWord) (v : DyadicIntervalCode) :
    gridContained w v ↔ retainedInterval (decodeOracleWord w).2 ⊆ dyadicInterval v := by
  obtain ⟨a, b, s, e⟩ := v
  generalize h : retainedIntervalCode w = code
  obtain ⟨l, r, d⟩ := code
  have grid := retainedInterval_eq_grid w
  rw [h] at grid
  change retainedInterval (decodeOracleWord w).2 =
    Icc ((l : ℝ) / (2 : ℝ)^d) ((r : ℝ) / (2 : ℝ)^d) at grid
  unfold gridContained
  rw [h, grid]
  change _ ↔ Icc ((l : ℝ) / (2 : ℝ)^d) ((r : ℝ) / (2 : ℝ)^d) ⊆
    Ioo (((a : ℝ) - s) / (2 : ℝ)^e) (((b : ℝ) - s) / (2 : ℝ)^e)
  have le : l ≤ r := by
    simp only [retainedIntervalCode, Prod.mk.injEq] at h
    omega
  have posD : 0 < (2 : ℝ)^d := by positivity
  have posE : 0 < (2 : ℝ)^e := by positivity
  have ordered : (l : ℝ) / (2 : ℝ)^d ≤ (r : ℝ) / (2 : ℝ)^d :=
    div_le_div_of_nonneg_right (by exact_mod_cast le) posD.le
  rw [show (Icc ((l : ℝ) / (2 : ℝ)^d) ((r : ℝ) / (2 : ℝ)^d) ⊆
      Ioo (((a : ℝ) - s) / (2 : ℝ)^e) (((b : ℝ) - s) / (2 : ℝ)^e)) ↔
      ((a : ℝ) - s) / (2 : ℝ)^e < (l : ℝ) / (2 : ℝ)^d ∧
        (r : ℝ) / (2 : ℝ)^d < ((b : ℝ) - s) / (2 : ℝ)^e from
    ⟨fun h => ⟨(h (left_mem_Icc.mpr ordered)).1, (h (right_mem_Icc.mpr ordered)).2⟩,
      fun ⟨hl, hr⟩ _ hz => ⟨hl.trans_le hz.1, hz.2.trans_lt hr⟩⟩]
  rw [div_lt_div_iff₀ posE posD, div_lt_div_iff₀ posD posE, sub_mul, sub_mul,
    sub_lt_iff_lt_add, lt_sub_iff_add_lt, add_comm ((l : ℝ) * (2 : ℝ)^e),
    add_comm ((r : ℝ) * (2 : ℝ)^e)]
  norm_cast

private def pullbackEntry (p : Option DyadicIntervalCode × ℕ) : Option OracleWord :=
  (decode (α := OracleWord) p.2).bind fun w =>
    p.1.bind fun v => if gridContained w v then some w else none

private theorem pullbackEntry_primrec : Primrec pullbackEntry := by
  have word : Primrec (fun p : ((Option DyadicIntervalCode × ℕ) × OracleWord) × DyadicIntervalCode =>
      p.1.2) := Primrec.snd.comp Primrec.fst
  have emit := Primrec.ite (gridContained_primrec.comp word Primrec.snd)
    (Primrec.option_some.comp word) (Primrec.const none)
  exact Primrec.option_bind (Primrec.decode.comp Primrec.snd)
    (Primrec.option_bind (Primrec.fst.comp Primrec.fst) emit.to₂).to₂

def fatAddressPullbackStream (stream : RealOracleStream) : OracleStream :=
  fun p => pullbackEntry (stream (p.1, p.2.unpair.1), p.2.unpair.2)

section
attribute [local irreducible] ComputableIn

theorem fatAddressPullbackStream_computableIn {Z : Oracle} {stream : RealOracleStream}
    (h : ComputableIn {Z} stream) : ComputableIn {Z} (fatAddressPullbackStream stream) := by
  have unpair := Primrec.unpair.comp (Primrec.snd : Primrec (Prod.snd : ℕ × ℕ → ℕ))
  have address := Primrec.fst.pair (Primrec.fst.comp unpair)
  exact computableIn_comp pullbackEntry_primrec.computableIn
    (computableIn_pair (computableIn_comp h address.computableIn)
      (Primrec.snd.comp unpair).computableIn)
end

theorem fatAddressPullbackStream_layer (stream : RealOracleStream) (n : ℕ) :
    oracleLayer (fatAddressPullbackStream stream) n = fatAddress ⁻¹' realOracleLayer stream n := by
  ext x
  constructor
  · intro hx
    obtain ⟨tick, w, eq, hp⟩ := (mem_oracleLayer _ _ _).mp hx
    obtain ⟨v, occurs⟩ : ∃ v, stream (n, tick.unpair.1) = some v := by
      cases hs : stream (n, tick.unpair.1)
      · simp [fatAddressPullbackStream, pullbackEntry, hs] at eq
      · exact ⟨_, rfl⟩
    have contained : gridContained w v := by
      simp only [fatAddressPullbackStream, pullbackEntry, occurs] at eq
      obtain ⟨w', _, heq⟩ := Option.bind_eq_some_iff.mp eq
      change (if gridContained w' v then some w' else none) = some w at heq
      split at heq
      · cases heq
        assumption
      · simp at heq
    apply (mem_realOracleLayer _ _ _).mpr
    refine ⟨tick.unpair.1, v, occurs, (gridContained_iff w v).mp contained ?_⟩
    rw [← mem_preimage, fatAddress_preimage_retainedInterval]
    exact hp
  · intro hx
    obtain ⟨tick, v, occurs, body⟩ := (mem_realOracleLayer _ _ _).mp hx
    have openInterval : IsOpen (dyadicInterval v) := isOpen_Ioo
    have member : x ∈ fatAddress ⁻¹' dyadicInterval v := body
    rw [fatAddress_preimage_open openInterval] at member
    simp only [mem_iUnion] at member
    obtain ⟨d, p, incl, hp⟩ := member
    let w := encodeOracleWord ⟨d, p⟩
    have decoded : decodeOracleWord w = ⟨d, p⟩ := decode_encodeOracleWord _
    have contained : gridContained w v := by
      apply (gridContained_iff _ _).mpr
      rwa [decoded]
    apply (mem_oracleLayer _ _ _).mpr
    refine ⟨Nat.pair tick (encode w), w, ?_, ?_⟩
    · simp [fatAddressPullbackStream, pullbackEntry, occurs, contained]
    · rw [decoded]
      exact hp

/-- Effective inverse image along the concrete fat Cantor embedding. -/
theorem fatAddress_uniform_test_pullback {Z : Oracle} {U : ℕ → Set ℝ}
    (hU : RealOracleUniformOpen Z U) :
    OracleUniformOpen Z (fun n => fatAddress ⁻¹' U n) := by
  obtain ⟨stream, compiled, eq⟩ := hU
  refine ⟨fatAddressPullbackStream stream, fatAddressPullbackStream_computableIn compiled, fun n => ?_⟩
  rw [fatAddressPullbackStream_layer, eq]

theorem fatAddress_pulls_back_weakFailure {Z : Oracle} {x : Cantor}
    (h : RealFailsWeak Z (fatAddress x)) : FailsWeak oracleOpenTestFramework Z x := by
  obtain ⟨U, ⟨uniform, null⟩, hx⟩ := h
  have measurable (n : ℕ) : MeasurableSet (U n) := by
    obtain ⟨stream, _, eq⟩ := uniform
    rw [← eq]
    exact (realOracleLayer_isOpen _ _).measurableSet
  refine ⟨fun n => fatAddress ⁻¹' U n, ⟨fatAddress_uniform_test_pullback uniform, ?_⟩, hx⟩
  rw [← preimage_iInter]
  apply le_antisymm _ bot_le
  change fairCoin (fatAddress ⁻¹' ⋂ n, U n) ≤ 0
  simpa only [null, mul_zero] using fatAddress_preimage_volume_le (MeasurableSet.iInter measurable)

theorem fatAddress_pulls_back_martinLofFailure {Z : Oracle} {x : Cantor}
    (h : RealFailsMartinLof Z (fatAddress x)) : FailsMartinLof oracleOpenTestFramework Z x := by
  obtain ⟨U, ⟨uniform, costs⟩, hx⟩ := h
  have measurable (n : ℕ) : MeasurableSet (U n) := by
    obtain ⟨stream, _, eq⟩ := uniform
    rw [← eq]
    exact (realOracleLayer_isOpen _ _).measurableSet
  refine ⟨fun n => fatAddress ⁻¹' U (n + 1),
    ⟨oracleUniformOpen_shift (fatAddress_uniform_test_pullback uniform) 1, ?_⟩,
    fun n => hx (n + 1)⟩
  intro n
  refine (fatAddress_preimage_volume_le (measurable (n + 1))).trans ?_
  exact (mul_le_mul_right (costs (n + 1)) _).trans_eq
    (by simpa only [pow_one] using dyadic_cancel n 1)

end Guo

#print axioms Guo.retainedInterval_eq_grid
#print axioms Guo.fatAddress_uniform_test_pullback
#print axioms Guo.fatAddress_pulls_back_weakFailure
#print axioms Guo.fatAddress_pulls_back_martinLofFailure
