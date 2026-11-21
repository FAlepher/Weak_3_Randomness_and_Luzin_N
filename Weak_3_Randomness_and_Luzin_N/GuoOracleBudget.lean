import Weak_3_Randomness_and_Luzin_N.GuoOracleMeasure

open Set MeasureTheory
open scoped ENNReal

namespace Guo

private noncomputable def budget (n : ℕ) : ℝ≥0∞ := ((2 : ℝ≥0∞)⁻¹)^n

def withinBudget (n : ℕ) (words : List OracleWord) : Bool :=
  let size := finiteOpenMassCode words
  decide (size.1 * 2^n ≤ 2^size.2)

theorem withinBudget_primrec : Primrec₂ withinBudget := by
  have powtwo : Primrec (fun k : ℕ => (2 : ℕ)^k) :=
    (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id
  have sizes := finiteOpenMassCode_primrec.comp (Primrec.snd : Primrec (@Prod.snd ℕ (List OracleWord)))
  have count := Primrec.fst.comp sizes
  have depth := Primrec.snd.comp sizes
  exact (Primrec.nat_le.comp
    (Primrec.nat_mul.comp count (powtwo.comp Primrec.fst)) (powtwo.comp depth)).decide

theorem withinBudget_iff (n : ℕ) (words : List OracleWord) :
    withinBudget n words = true ↔ fairCoin (finiteOpen words) ≤ budget n := by
  rw [fairCoin_finiteOpen]
  unfold withinBudget
  obtain ⟨count, depth⟩ := finiteOpenMassCode words
  change (decide (count * 2^n ≤ 2^depth) = true) ↔
    (count : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹)^depth ≤ budget n
  simp only [decide_eq_true_eq]
  let scale := (2 : ℝ≥0∞)^(n + depth)
  have scaleNe : scale ≠ 0 := by simp [scale]
  have scaleTop : scale ≠ ∞ := by simp [scale]
  have cancel (a b : ℕ) : (2 : ℝ≥0∞)^(a + b) * budget a = (2 : ℝ≥0∞)^b := by
    have h0 : (2 : ℝ≥0∞)^a ≠ 0 := by simp
    have htop : (2 : ℝ≥0∞)^a ≠ ∞ := by simp
    unfold budget
    rw [pow_add, ← ENNReal.inv_pow, mul_right_comm, ENNReal.mul_inv_cancel h0 htop, one_mul]
  have lhs : scale * ((count : ℝ≥0∞) * budget depth) =
      (count : ℝ≥0∞) * (2 : ℝ≥0∞)^n := by
    rw [mul_left_comm, show scale = (2 : ℝ≥0∞)^(depth + n) by simp [scale, add_comm], cancel]
  have rhs : scale * budget n = (2 : ℝ≥0∞)^depth := cancel n depth
  change _ ↔ (count : ℝ≥0∞) * budget depth ≤ budget n
  rw [← ENNReal.mul_le_mul_iff_right scaleNe scaleTop, lhs, rhs]
  exact_mod_cast (Iff.rfl : count * (2 : ℕ)^n ≤ 2^depth ↔ _)

def budgetStep (n : ℕ) (words : List OracleWord) (proposal : Option OracleWord) : List OracleWord :=
  match proposal with
  | none => words
  | some word => bif withinBudget n (word :: words) then word :: words else words

private theorem budgetStep_primrec :
    Primrec (fun p : ℕ × List OracleWord × Option OracleWord => budgetStep p.1 p.2.1 p.2.2) := by
  let Input := ℕ × List OracleWord × Option OracleWord
  let old : Input → List OracleWord := fun p => p.2.1
  have prior : Primrec old := Primrec.fst.comp Primrec.snd
  have next : Primrec₂ (fun p word => word :: old p) :=
    (Primrec.list_cons.comp Primrec.snd (prior.comp Primrec.fst)).to₂
  have allowed := withinBudget_primrec.comp (Primrec.fst.comp Primrec.fst) next
  have useWord : Primrec₂ (fun p word =>
      bif withinBudget p.1 (word :: old p) then word :: old p else old p) :=
    (Primrec.cond allowed next (prior.comp Primrec.fst)).to₂
  exact (Primrec.option_casesOn (Primrec.snd.comp Primrec.snd) prior useWord).of_eq
    (fun p => by cases p.2.2 <;> rfl)

def budgetWords (enum : OracleStream) (n t : ℕ) : List OracleWord :=
  t.rec [] (fun tick words => budgetStep n words (enum (n, tick)))

def budgetStream (enum : OracleStream) : OracleStream :=
  fun p => (budgetWords enum p.1 p.2.unpair.1)[p.2.unpair.2]?

abbrev OracleTestFamily := ℕ × ℕ × ℕ → Option OracleWord

/-- Apply budget trimming separately at every code of a uniformly indexed family. -/
def budgetTestFamily (tests : OracleTestFamily) : OracleTestFamily :=
  fun p => budgetStream (fun q => tests (p.1, q.1, q.2)) p.2

section Computability

attribute [local irreducible] ComputableIn

theorem budgetTestFamily_computableIn {O : Set Oracle} {tests : OracleTestFamily}
    (he : ComputableIn O tests) : ComputableIn O (budgetTestFamily tests) := by
  let State := List OracleWord
  let Input := (ℕ × ℕ) × ℕ × State
  let source (p : ℕ × ℕ) (k : ℕ) := tests (p.1, p.2, k)
  let stage (p : ℕ × ℕ) (k : ℕ) := budgetWords (fun q => tests (p.1, q.1, q.2)) p.2 k
  have layer : ComputableIn O (fun p : Input => p.1.2) :=
    (Primrec.snd.comp Primrec.fst).computableIn
  have tick : Primrec (fun p : Input => (p.1.1, p.1.2, p.2.1)) :=
    (Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair
      (Primrec.fst.comp Primrec.snd))
  have proposal : ComputableIn O (fun p : Input => source p.1 p.2.1) :=
    computableIn_comp he tick.computableIn
  have prior : ComputableIn O (fun p : Input => p.2.2) :=
    (Primrec.snd.comp Primrec.snd).computableIn
  have args : ComputableIn O (fun p : Input => (p.1.2, p.2.2, source p.1 p.2.1)) :=
    computableIn_pair layer (computableIn_pair prior proposal)
  have step : ComputableIn O (fun p : Input => budgetStep p.1.2 p.2.2 (source p.1 p.2.1)) :=
    computableIn_comp budgetStep_primrec.computableIn args
  have all : ComputableIn O (fun p : (ℕ × ℕ) × ℕ => stage p.1 p.2) :=
    computableIn_nat_rec (step := fun p t old => budgetStep p.2 old (source p t))
      (ComputableIn.const ([] : State)) step
  have splitTick : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2.unpair) :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.snd)
  have input : Primrec (fun p : ℕ × ℕ × ℕ => ((p.1, p.2.1), p.2.2.unpair.1)) :=
    (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair (Primrec.fst.comp splitTick)
  have accepted : ComputableIn O (fun p : ℕ × ℕ × ℕ => stage (p.1, p.2.1) p.2.2.unpair.1) :=
    computableIn_comp all input.computableIn
  have query : ComputableIn O (fun p : ℕ × ℕ × ℕ =>
      (stage (p.1, p.2.1) p.2.2.unpair.1, p.2.2.unpair.2)) :=
    computableIn_pair accepted (Primrec.snd.comp splitTick).computableIn
  exact computableIn_comp Primrec.list_getElem?.computableIn₂ query

theorem budgetStream_computableIn {O : Set Oracle} {enum : OracleStream}
    (he : ComputableIn O enum) : ComputableIn O (budgetStream enum) := by
  have family : ComputableIn O (fun p : ℕ × ℕ × ℕ => enum p.2) := computableIn_comp he ComputableIn.snd
  have query : Primrec (fun p : ℕ × ℕ => (0, p)) := (Primrec.const 0).pair Primrec.id
  exact computableIn_comp (budgetTestFamily_computableIn family) query.computableIn

end Computability

private theorem budgetStream_layer (enum : OracleStream) (n : ℕ) :
    oracleLayer (budgetStream enum) n = ⋃ t, finiteOpen (budgetWords enum n t) := by
  ext x
  rw [mem_oracleLayer, mem_iUnion]
  constructor
  · rintro ⟨tick, w, h, hx⟩
    exact ⟨tick.unpair.1, (mem_finiteOpen _ _).mpr ⟨w, List.mem_of_getElem? h, hx⟩⟩
  · rintro ⟨t, h⟩
    obtain ⟨w, hw, hx⟩ := (mem_finiteOpen _ _).mp h
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hw
    exact ⟨Nat.pair t k, w, by simpa only [budgetStream, Nat.unpair_pair] using hk, hx⟩

private theorem budgetWords_mono (enum : OracleStream) (n : ℕ) :
    Monotone (fun t => finiteOpen (budgetWords enum n t)) := by
  apply monotone_nat_of_le_succ
  intro t x hx
  obtain ⟨w, hw, hmem⟩ := (mem_finiteOpen _ _).mp hx
  refine (mem_finiteOpen _ _).mpr ⟨w, ?_, hmem⟩
  change w ∈ budgetStep n (budgetWords enum n t) (enum (n, t))
  cases h : enum (n, t) with
  | none => exact hw
  | some v => cases ok : withinBudget n (v :: budgetWords enum n t) <;> simp [budgetStep, ok, hw]

theorem budgetStream_measure_le (enum : OracleStream) (n : ℕ) :
    fairCoin (oracleLayer (budgetStream enum) n) ≤ ((2 : ℝ≥0∞)⁻¹)^n := by
  rw [budgetStream_layer, (budgetWords_mono enum n).measure_iUnion]
  apply iSup_le
  intro t
  induction t with
  | zero =>
    rw [show budgetWords enum n 0 = [] from rfl]
    simp [finiteOpen]
  | succ t ih =>
    change fairCoin (finiteOpen (budgetStep n (budgetWords enum n t) (enum (n, t)))) ≤ budget n
    cases h : enum (n, t) with
    | none => exact ih
    | some w =>
      cases ok : withinBudget n (w :: budgetWords enum n t)
      · simpa [budgetStep, ok, budget] using ih
      · simpa [budgetStep, ok] using (withinBudget_iff n (w :: budgetWords enum n t)).mp ok

private theorem budgetWords_subset (enum : OracleStream) (n t : ℕ) :
    finiteOpen (budgetWords enum n t) ⊆ oracleLayer enum n := by
  induction t with
  | zero => simp [budgetWords, finiteOpen]
  | succ t ih =>
    change finiteOpen (budgetStep n (budgetWords enum n t) (enum (n, t))) ⊆ _
    cases h : enum (n, t) with
    | none => exact ih
    | some w =>
      cases ok : withinBudget n (w :: budgetWords enum n t)
      · simpa [budgetStep, ok] using ih
      · simp only [budgetStep, ok, Bool.cond_true]
        intro x hx
        obtain ⟨v, hv, body⟩ := (mem_finiteOpen _ _).mp hx
        rcases List.mem_cons.mp hv with rfl | old
        · exact (mem_oracleLayer _ _ _).mpr ⟨t, _, h, body⟩
        · exact ih ((mem_finiteOpen _ _).mpr ⟨v, old, body⟩)

/-- Trimming at the budget preserves the exact open set of any already valid test layer. -/
theorem budgetStream_preserves_small (enum : OracleStream) (n : ℕ)
    (small : fairCoin (oracleLayer enum n) ≤ ((2 : ℝ≥0∞)⁻¹)^n) :
    oracleLayer (budgetStream enum) n = oracleLayer enum n := by
  rw [budgetStream_layer]
  refine Subset.antisymm (iUnion_subset (budgetWords_subset enum n)) ?_
  intro x hx
  obtain ⟨tick, w, found, body⟩ := (mem_oracleLayer _ _ _).mp hx
  have contained : finiteOpen (w :: budgetWords enum n tick) ⊆ oracleLayer enum n := by
    intro y hy
    obtain ⟨v, hv, inCylinder⟩ := (mem_finiteOpen _ _).mp hy
    rcases List.mem_cons.mp hv with rfl | old
    · exact (mem_oracleLayer _ _ _).mpr ⟨tick, _, found, inCylinder⟩
    · exact budgetWords_subset enum n tick ((mem_finiteOpen _ _).mpr ⟨v, old, inCylinder⟩)
  have allowed := (withinBudget_iff n _).mpr ((measure_mono contained).trans small)
  refine mem_iUnion.mpr ⟨tick + 1, ?_⟩
  change x ∈ finiteOpen (budgetStep n (budgetWords enum n tick) (enum (n, tick)))
  rw [found]
  simp only [budgetStep, allowed, Bool.cond_true]
  exact (mem_finiteOpen _ _).mpr ⟨w, List.mem_cons_self, body⟩

def familyLayer (tests : OracleTestFamily) (code layer : ℕ) : Set Cantor :=
  oracleLayer (fun p => tests (code, p.1, p.2)) layer

def diagonalTestStream (tests : OracleTestFamily) : OracleStream :=
  fun p => tests (p.2.unpair.1, p.1 + p.2.unpair.1 + 1, p.2.unpair.2)

theorem diagonalTestStream_layer (tests : OracleTestFamily) (n : ℕ) :
    oracleLayer (diagonalTestStream tests) n = ⋃ e, familyLayer tests e (n + e + 1) := by
  ext x
  simp only [mem_iUnion, familyLayer, mem_oracleLayer]
  constructor
  · rintro ⟨k, w, eq, hx⟩
    exact ⟨k.unpair.1, k.unpair.2, w, eq, hx⟩
  · rintro ⟨e, k, w, eq, hx⟩
    exact ⟨Nat.pair e k, w, by simpa only [diagonalTestStream, Nat.unpair_pair] using eq, hx⟩

/-- A uniformly indexed family of all bounded tests yields a universal test at the same oracle. -/
theorem universalTest_of_enumerated_family (Z : Oracle) (tests : OracleTestFamily)
    (compiled : ComputableIn {Z} tests)
    (bounded : ∀ e n, fairCoin (familyLayer tests e n) ≤ ((2 : ℝ≥0∞)⁻¹)^n)
    (complete : ∀ U, MartinLofTest oracleOpenTestFramework Z U → ∃ e, ∀ n, familyLayer tests e n = U n) :
    UniversalMartinLofTest oracleOpenTestFramework Z (oracleLayer (diagonalTestStream tests)) := by
  have unpair : Primrec (fun p : ℕ × ℕ => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have testCode : Primrec (fun p : ℕ × ℕ => p.2.unpair.1) := Primrec.fst.comp unpair
  have layer : Primrec (fun p : ℕ × ℕ => p.1 + p.2.unpair.1 + 1) :=
    Primrec.succ.comp (Primrec.nat_add.comp Primrec.fst testCode)
  have address : Primrec (fun p : ℕ × ℕ => (p.2.unpair.1, p.1 + p.2.unpair.1 + 1, p.2.unpair.2)) :=
    testCode.pair (layer.pair (Primrec.snd.comp unpair))
  have computed : ComputableIn {Z} (diagonalTestStream tests) := computableIn_comp compiled address.computableIn
  refine ⟨⟨⟨_, computed, fun _ => rfl⟩, ?_⟩, ?_⟩
  · intro n
    rw [diagonalTestStream_layer]
    refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum fun e => bounded e (n + e + 1)).trans_eq ?_)
    simp_rw [show ∀ e : ℕ, n + e + 1 = n + (e + 1) from fun _ => by omega, pow_add]
    rw [ENNReal.tsum_mul_left]
    simp [pow_succ, ENNReal.tsum_mul_right, ENNReal.mul_inv_cancel]
  · intro x failure n
    obtain ⟨U, hU, hx⟩ := failure
    obtain ⟨e, same⟩ := complete U hU
    rw [diagonalTestStream_layer]
    exact mem_iUnion.mpr ⟨e, by rw [same]; exact hx _⟩

/-- Raw streams need no budget guarantee. Uniform trimming precedes the universal union. -/
theorem universalTest_of_raw_enumerated_family (Z : Oracle) (tests : OracleTestFamily)
    (compiled : ComputableIn {Z} tests)
    (complete : ∀ U, MartinLofTest oracleOpenTestFramework Z U → ∃ e, ∀ n, familyLayer tests e n = U n) :
    UniversalMartinLofTest oracleOpenTestFramework Z
      (oracleLayer (diagonalTestStream (budgetTestFamily tests))) := by
  refine universalTest_of_enumerated_family Z _ (budgetTestFamily_computableIn compiled)
    (fun e n => budgetStream_measure_le (fun p => tests (e, p.1, p.2)) n) ?_
  intro U hU
  obtain ⟨e, same⟩ := complete U hU
  refine ⟨e, fun n => ?_⟩
  have small : fairCoin (familyLayer tests e n) ≤ ((2 : ℝ≥0∞)⁻¹)^n := by
    rw [same]
    exact hU.2 n
  exact (budgetStream_preserves_small (fun p => tests (e, p.1, p.2)) n small).trans (same n)

end Guo

#print axioms Guo.budgetStream_computableIn
#print axioms Guo.budgetStream_preserves_small
#print axioms Guo.universalTest_of_enumerated_family
#print axioms Guo.universalTest_of_raw_enumerated_family
