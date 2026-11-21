import Weak_3_Randomness_and_Luzin_N.GuoOutsideReflectionBridge

open Set MeasureTheory Encodable
open scoped ENNReal

namespace Guo

abbrev RationalIntervalCode := SignedFraction × SignedFraction
abbrev RationalOracleStream := ℕ × ℕ → Option RationalIntervalCode

/-- The two rational endpoints of an open interval, encoded as signed fractions. -/
noncomputable def rationalInterval (c : RationalIntervalCode) : Set ℝ := Ioo c.1.val c.2.val

theorem rationalInterval_ofRat (l r : ℚ) :
    rationalInterval (SignedFraction.ofRat l, SignedFraction.ofRat r) = Ioo (l : ℝ) (r : ℝ) := by
  simp [rationalInterval]

theorem rationalInterval_has_rational_endpoints (c : RationalIntervalCode) :
    ∃ l r : ℚ, rationalInterval c = Ioo (l : ℝ) (r : ℝ) := by
  let endpoint (q : SignedFraction) : ℚ :=
    ((q.1 : ℚ) - q.2.1) / ((q.2.2 : ℚ) + 1)
  refine ⟨endpoint c.1, endpoint c.2, ?_⟩
  simp [rationalInterval, endpoint, SignedFraction.val]

noncomputable def rationalOracleLayer (stream : RationalOracleStream) (n : ℕ) : Set ℝ :=
  ⋃ t, (stream (n, t)).elim ∅ rationalInterval

def RationalOracleUniformOpen (Z : Oracle) (U : ℕ → Set ℝ) : Prop :=
  ∃ stream : RationalOracleStream, ComputableIn {Z} stream ∧ ∀ n, rationalOracleLayer stream n = U n

theorem mem_rationalOracleLayer (stream : RationalOracleStream) (n : ℕ) (x : ℝ) :
    x ∈ rationalOracleLayer stream n ↔
      ∃ t c, stream (n, t) = some c ∧ x ∈ rationalInterval c := by
  rw [rationalOracleLayer, mem_iUnion]
  refine exists_congr fun t => ?_
  cases stream (n, t) <;> simp

private def dyadicToRational (c : DyadicIntervalCode) : RationalIntervalCode :=
  (intervalLowerCode c, intervalUpperCode c)

private theorem dyadicToRational_primrec : Primrec dyadicToRational :=
  intervalLowerCode_primrec.pair intervalUpperCode_primrec

private def dyadicToRationalStream (stream : RealOracleStream) : RationalOracleStream :=
  fun p => (stream p).map dyadicToRational

private theorem dyadicToRationalStream_computableIn {Z : Oracle} {stream : RealOracleStream}
    (h : ComputableIn {Z} stream) : ComputableIn {Z} (dyadicToRationalStream stream) :=
  computableIn_comp (Primrec.option_map₁ dyadicToRational_primrec).computableIn h

private theorem dyadicToRationalStream_layer (stream : RealOracleStream) (n : ℕ) :
    rationalOracleLayer (dyadicToRationalStream stream) n = realOracleLayer stream n := by
  ext x
  rw [mem_rationalOracleLayer, mem_realOracleLayer]
  constructor
  · rintro ⟨t, c, hcode, contains⟩
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hcode
    refine ⟨t, d, hd, ?_⟩
    rwa [dyadicInterval_eq_codes]
  · rintro ⟨t, d, hcode, contains⟩
    refine ⟨t, dyadicToRational d, by simp [dyadicToRationalStream, hcode], ?_⟩
    rwa [dyadicInterval_eq_codes] at contains

private def rationalContainsDyadic (p : RationalIntervalCode × DyadicIntervalCode) : Bool :=
  p.1.1.lt (intervalLowerCode p.2) && (intervalUpperCode p.2).lt p.1.2

private theorem rationalContainsDyadic_primrec : Primrec rationalContainsDyadic :=
  Primrec.and.comp
    (SignedFraction.lt_primrec.comp (Primrec.fst.comp Primrec.fst)
      (intervalLowerCode_primrec.comp Primrec.snd))
    (SignedFraction.lt_primrec.comp (intervalUpperCode_primrec.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst))

private def rationalToDyadicEntry (p : Option RationalIntervalCode × ℕ) : Option DyadicIntervalCode :=
  p.1.bind fun r => (decode (α := DyadicIntervalCode) p.2).bind fun d =>
    if rationalContainsDyadic (r, d) then some d else none

private theorem rationalToDyadicEntry_primrec : Primrec rationalToDyadicEntry := by
  let Input := Option RationalIntervalCode × ℕ
  let WithRational := Input × RationalIntervalCode
  let WithDyadic := WithRational × DyadicIntervalCode
  have rational : Primrec (fun p : WithDyadic => p.1.2) := Primrec.snd.comp Primrec.fst
  have dyadic : Primrec (Prod.snd : WithDyadic → DyadicIntervalCode) := Primrec.snd
  have valid := rationalContainsDyadic_primrec.comp (rational.pair dyadic)
  have chooseCode : Primrec (fun p : WithDyadic =>
      if rationalContainsDyadic (p.1.2, p.2) then some p.2 else none) :=
    Primrec.ite (Primrec.eq.comp valid (Primrec.const true))
      (Primrec.option_some.comp dyadic) (Primrec.const none)
  have decodeCode : Primrec (fun p : WithRational => decode (α := DyadicIntervalCode) p.1.2) :=
    Primrec.decode.comp (Primrec.snd.comp Primrec.fst)
  exact Primrec.option_bind Primrec.fst (Primrec.option_bind decodeCode chooseCode.to₂).to₂

private def rationalToDyadicStream (stream : RationalOracleStream) : RealOracleStream :=
  fun p => rationalToDyadicEntry (stream (p.1, p.2.unpair.1), p.2.unpair.2)

section
attribute [local irreducible] ComputableIn

private theorem rationalToDyadicStream_computableIn {Z : Oracle} {stream : RationalOracleStream}
    (h : ComputableIn {Z} stream) : ComputableIn {Z} (rationalToDyadicStream stream) := by
  have tick : Primrec (fun p : ℕ × ℕ => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have read : Primrec (fun p : ℕ × ℕ => (p.1, p.2.unpair.1)) :=
    Primrec.fst.pair (Primrec.fst.comp tick)
  have code : Primrec (fun p : ℕ × ℕ => p.2.unpair.2) := Primrec.snd.comp tick
  exact computableIn_comp rationalToDyadicEntry_primrec.computableIn
    (computableIn_pair (computableIn_comp h read.computableIn) code.computableIn)

end

private theorem rationalToDyadicStream_layer (stream : RationalOracleStream) (n : ℕ) :
    realOracleLayer (rationalToDyadicStream stream) n = rationalOracleLayer stream n := by
  ext x
  rw [mem_realOracleLayer, mem_rationalOracleLayer]
  constructor
  · rintro ⟨t, d, hcode, hx⟩
    simp only [rationalToDyadicStream, rationalToDyadicEntry, Option.bind_eq_some_iff] at hcode
    obtain ⟨r, read, d', _, emitted⟩ := hcode
    split at emitted
    next accepted =>
      cases emitted
      simp only [rationalContainsDyadic, Bool.and_eq_true, SignedFraction.lt_true_iff] at accepted
      rw [dyadicInterval_eq_codes] at hx
      exact ⟨_, r, read, accepted.1.trans hx.1, hx.2.trans accepted.2⟩
    next _ =>
      simp at emitted
  · rintro ⟨t, r, read, hx⟩
    obtain ⟨d, inside, low, high⟩ := dyadicInterval_strict_basis hx.1 hx.2
    have accepted : rationalContainsDyadic (r, d) = true := by
      simp only [rationalContainsDyadic, Bool.and_eq_true, SignedFraction.lt_true_iff]
      exact ⟨low, high⟩
    refine ⟨Nat.pair t (encode d), d, ?_, inside⟩
    simp only [rationalToDyadicStream, Nat.unpair_pair, rationalToDyadicEntry, read, encodek]
    change (if rationalContainsDyadic (r, d) then some d else none) = some d
    rw [if_pos accepted]

/-- The rational and dyadic bases give the same uniformly effective open sequences at every oracle. -/
theorem rationalOracleUniformOpen_iff_real {Z : Oracle} {U : ℕ → Set ℝ} :
    RationalOracleUniformOpen Z U ↔ RealOracleUniformOpen Z U := by
  constructor
  · rintro ⟨stream, compiled, layers⟩
    exact ⟨rationalToDyadicStream stream, rationalToDyadicStream_computableIn compiled,
      fun n => (rationalToDyadicStream_layer stream n).trans (layers n)⟩
  · rintro ⟨stream, compiled, layers⟩
    exact ⟨dyadicToRationalStream stream, dyadicToRationalStream_computableIn compiled,
      fun n => (dyadicToRationalStream_layer stream n).trans (layers n)⟩

def RationalWeakTest (Z : Oracle) (U : ℕ → Set ℝ) : Prop :=
  RationalOracleUniformOpen Z U ∧ volume (⋂ n, U n) = 0

def RationalMartinLofTest (Z : Oracle) (U : ℕ → Set ℝ) : Prop :=
  RationalOracleUniformOpen Z U ∧ ∀ n, volume (U n) ≤ ((2 : ℝ≥0∞)⁻¹)^n

def RationalFailsWeak (Z : Oracle) (x : ℝ) : Prop :=
  ∃ U, RationalWeakTest Z U ∧ ∀ n, x ∈ U n

def RationalFailsMartinLof (Z : Oracle) (x : ℝ) : Prop :=
  ∃ U, RationalMartinLofTest Z U ∧ ∀ n, x ∈ U n

theorem rationalWeakTest_iff_real {Z : Oracle} {U : ℕ → Set ℝ} :
    RationalWeakTest Z U ↔ RealWeakTest Z U := by
  simp only [RationalWeakTest, RealWeakTest, rationalOracleUniformOpen_iff_real]

theorem rationalMartinLofTest_iff_real {Z : Oracle} {U : ℕ → Set ℝ} :
    RationalMartinLofTest Z U ↔ RealMartinLofTest Z U := by
  simp only [RationalMartinLofTest, RealMartinLofTest, rationalOracleUniformOpen_iff_real]

theorem rationalFailsWeak_iff_real {Z : Oracle} {x : ℝ} :
    RationalFailsWeak Z x ↔ RealFailsWeak Z x := by
  simp only [RationalFailsWeak, RealFailsWeak, rationalWeakTest_iff_real]

theorem rationalFailsMartinLof_iff_real {Z : Oracle} {x : ℝ} :
    RationalFailsMartinLof Z x ↔ RealFailsMartinLof Z x := by
  simp only [RationalFailsMartinLof, RealFailsMartinLof, rationalMartinLofTest_iff_real]

end Guo

#print axioms Guo.rationalOracleUniformOpen_iff_real
#print axioms Guo.rationalWeakTest_iff_real
#print axioms Guo.rationalMartinLofTest_iff_real
