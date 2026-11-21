import Weak_3_Randomness_and_Luzin_N.GuoTypeTwoInterpolation
import Mathlib.Computability.Primrec.List

open Set
open scoped NNReal

namespace Guo

/-- Signed rational code with a positive denominator stored minus one. -/
abbrev RationalNameCode := Bool × ℕ × ℕ

def rationalNameValue (p : RationalNameCode) : ℚ :=
  let q := (p.2.1 : ℚ) / (p.2.2 + 1 : ℕ)
  if p.1 then -q else q

/-- Finite lattice data with common horizontal and vertical denominators. -/
abbrev GridKnot := ℕ × ℕ

private def gridRat (D i : ℕ) : ℚ := (i : ℚ) / D

private noncomputable def gridReal (D i : ℕ) : ℝ := (i : ℝ) / D

private theorem cast_gridRat (D i : ℕ) : (gridRat D i : ℝ) = gridReal D i := by
  simp [gridRat, gridReal]

def gridRationalVertices (knots : List GridKnot) (D V : ℕ) : List (ℚ × ℚ) :=
  knots.map (fun v => (gridRat D v.1, gridRat V v.2))

private noncomputable def gridKnotSet (knots : List GridKnot) (D : ℕ) : Set ℝ :=
  {x | ∃ v ∈ knots, gridReal D v.1 = x}

private theorem gridKnotSet_vertices (knots : List GridKnot) (D V : ℕ) :
    {x | ∃ v ∈ gridRationalVertices knots D V, (v.1 : ℝ) = x} =
      gridKnotSet knots D := by
  ext x
  simp only [gridRationalVertices, gridKnotSet, mem_setOf, List.mem_map]
  constructor
  · rintro ⟨v, ⟨w, hw, rfl⟩, hv⟩
    exact ⟨w, hw, (cast_gridRat D w.1).symm.trans hv⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, cast_gridRat D w.1⟩

private theorem gridKnotSet_compact (knots : List GridKnot) (D : ℕ) :
    IsCompact (gridKnotSet knots D) := by
  have h : gridKnotSet knots D = (fun v : GridKnot => gridReal D v.1) '' (↑knots.toFinset : Set GridKnot) := by
    ext x
    simp [gridKnotSet]
  exact h ▸ (Finset.finite_toSet knots.toFinset).image _ |>.isCompact

private theorem gridReal_le {D a b : ℕ} (hD : 0 < D) :
    gridReal D a ≤ gridReal D b ↔ a ≤ b := by
  have pos : 0 < (D : ℝ) := by exact_mod_cast hD
  simp [gridReal, div_le_div_iff_of_pos_right pos]

private theorem gridReal_eq {D a b : ℕ} (hD : 0 < D) :
    gridReal D a = gridReal D b ↔ a = b := by
  simp only [le_antisymm_iff, gridReal_le hD]

private def gridHeight (knots : List GridKnot) (key : ℕ) : ℕ :=
  knots.foldr (fun v old => if v.1 = key then v.2 else old) 0

private theorem gridHeight_primrec : Primrec₂ gridHeight := by
  let Param := List GridKnot × ℕ
  let Step := Param × GridKnot × ℕ
  have key : Primrec (fun p : Step => p.1.2) := Primrec.snd.comp Primrec.fst
  have select : Primrec (fun p : Step => if p.2.1.1 = p.1.2 then p.2.1.2 else p.2.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) key)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.fst (Primrec.const 0) select.to₂).to₂

private theorem gridHeight_le (knots : List GridKnot) (V : ℕ)
    (h : ∀ v ∈ knots, v.2 ≤ V) (i : ℕ) : gridHeight knots i ≤ V := by
  induction knots with
  | nil => exact Nat.zero_le _
  | cons v knots ih =>
    change (if v.1 = i then v.2 else gridHeight knots i) ≤ V
    split
    · exact h v (List.mem_cons_self)
    · exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp))

private theorem gridVertexValue (knots : List GridKnot) (D V i : ℕ) (hD : 0 < D) :
    polygonVertexValue (gridRationalVertices knots D V) (gridReal D i) =
      gridReal V (gridHeight knots i) := by
  classical
  unfold polygonVertexValue
  induction knots with
  | nil => simp [gridHeight, gridRationalVertices, gridReal]
  | cons v knots ih =>
    by_cases e : v.1 = i
    · simp [gridRationalVertices, gridHeight, e, cast_gridRat]
    · have compare : gridReal D v.1 ≠ gridReal D i := fun he => e ((gridReal_eq hD).mp he)
      simpa [gridRationalVertices, compare, gridHeight, e, cast_gridRat] using ih

private theorem gridReal_gap {D a b : ℕ} (hD : 0 < D) (unequal : a ≠ b) :
    1 ≤ (D : ℝ) * dist (gridReal D a) (gridReal D b) := by
  have pos : 0 < (D : ℝ) := by exact_mod_cast hD
  rw [Real.dist_eq, gridReal, gridReal, ← sub_div, abs_div, abs_of_pos pos,
    mul_comm (D : ℝ), div_mul_cancel₀ _ pos.ne']
  rcases lt_or_gt_of_ne unequal with alt | alt
  · have le : (a : ℝ) + 1 ≤ b := by exact_mod_cast alt
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have le : (b : ℝ) + 1 ≤ a := by exact_mod_cast alt
    rw [abs_of_nonneg (by linarith)]
    linarith

private theorem gridReal_Icc (V i : ℕ) (hV : 0 < V) (hi : i ≤ V) :
    gridReal V i ∈ Icc (0 : ℝ) 1 := by
  have pos : 0 < (V : ℝ) := by exact_mod_cast hV
  refine ⟨div_nonneg (by positivity) pos.le, ?_⟩
  have := (gridReal_le hV).mpr hi
  simpa [gridReal, pos.ne'] using this

theorem gridRationalPolygon_lipschitz (knots : List GridKnot) (D V : ℕ)
    (hD : 0 < D) (hV : 0 < V) (h0 : ∃ v ∈ knots, v.1 = 0)
    (h1 : ∃ v ∈ knots, v.1 = D) (heights : ∀ v ∈ knots, v.2 ≤ V) :
    LipschitzWith (D : ℝ≥0) (realPolygonOfVertices (gridRationalVertices knots D V)) := by
  have zeroMem : 0 ∈ gridKnotSet knots D := by
    obtain ⟨v, hv, eq⟩ := h0
    exact ⟨v, hv, by simp [gridReal, eq]⟩
  have oneMem : 1 ∈ gridKnotSet knots D := by
    obtain ⟨v, hv, eq⟩ := h1
    refine ⟨v, hv, ?_⟩
    have zero' : (D : ℝ) ≠ 0 := by positivity
    simp [gridReal, eq, zero']
  rw [realPolygonOfVertices, gridKnotSet_vertices]
  apply affineExtension_lipschitz (gridKnotSet_compact knots D) zeroMem oneMem
  apply LipschitzOnWith.of_dist_le_mul
  rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
  by_cases eq : u.1 = v.1
  · simp [eq]
  · rw [gridVertexValue knots D V u.1 hD, gridVertexValue knots D V v.1 hD]
    have up := gridReal_Icc V _ hV (gridHeight_le knots V heights u.1)
    have vp := gridReal_Icc V _ hV (gridHeight_le knots V heights v.1)
    have diff : dist (gridReal V (gridHeight knots u.1)) (gridReal V (gridHeight knots v.1)) ≤ 1 := by
      rw [Real.dist_eq, abs_le]
      exact ⟨by linarith [up.1, vp.2], by linarith [up.2, vp.1]⟩
    simpa only [NNReal.coe_natCast] using diff.trans (gridReal_gap hD eq)

private def lowerGridKey (knots : List GridKnot) (den target : ℕ) : ℕ :=
  knots.foldr (fun v old => if v.1 * den ≤ target then max v.1 old else old) 0

private def upperGridKey (knots : List GridKnot) (den target D : ℕ) : ℕ :=
  knots.foldr (fun v old => if target ≤ v.1 * den then min v.1 old else old) D

private theorem lowerGridKey_primrec :
    Primrec (fun p : List GridKnot × ℕ × ℕ => lowerGridKey p.1 p.2.1 p.2.2) := by
  let Input := List GridKnot × ℕ × ℕ
  let Step := Input × GridKnot × ℕ
  have den : Primrec (fun q : Step => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have target : Primrec (fun q : Step => q.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have key : Primrec (fun q : Step => q.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have old : Primrec (fun q : Step => q.2.2) := Primrec.snd.comp Primrec.snd
  have update : Primrec (fun q : Step => if q.2.1.1 * q.1.2.1 ≤ q.1.2.2 then max q.2.1.1 q.2.2 else q.2.2) :=
    Primrec.ite (Primrec.nat_le.comp (Primrec.nat_mul.comp key den) target)
      (Primrec.nat_max.comp key old) old
  exact Primrec.list_foldr Primrec.fst (Primrec.const 0) update.to₂

private theorem upperGridKey_primrec :
    Primrec (fun p : List GridKnot × ℕ × ℕ × ℕ => upperGridKey p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let Input := List GridKnot × ℕ × ℕ × ℕ
  let Step := Input × GridKnot × ℕ
  have den : Primrec (fun q : Step => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have target : Primrec (fun q : Step => q.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have key : Primrec (fun q : Step => q.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have old : Primrec (fun q : Step => q.2.2) := Primrec.snd.comp Primrec.snd
  have maxKey : Primrec (fun p : Input => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have update : Primrec (fun q : Step => if q.1.2.2.1 ≤ q.2.1.1 * q.1.2.1 then min q.2.1.1 q.2.2 else q.2.2) :=
    Primrec.ite (Primrec.nat_le.comp target (Primrec.nat_mul.comp key den))
      (Primrec.nat_min.comp key old) old
  exact Primrec.list_foldr Primrec.fst maxKey update.to₂

private theorem lowerGridKey_spec (knots : List GridKnot) (den target : ℕ) :
    let key := lowerGridKey knots den target
    (key = 0 ∨ ∃ v ∈ knots, v.1 = key) ∧ key * den ≤ target ∧
      ∀ v ∈ knots, v.1 * den ≤ target → v.1 ≤ key := by
  induction knots with
  | nil => simp [lowerGridKey]
  | cons v knots ih =>
    obtain ⟨keyFrom, keyFits, maxKey⟩ := ih
    let old := lowerGridKey knots den target
    change (let key := if v.1 * den ≤ target then max v.1 old else old
      (key = 0 ∨ ∃ w ∈ v :: knots, w.1 = key) ∧ key * den ≤ target ∧
        ∀ w ∈ v :: knots, w.1 * den ≤ target → w.1 ≤ key)
    have survives (h : old = 0 ∨ ∃ w ∈ knots, w.1 = old) :
        old = 0 ∨ ∃ w ∈ v :: knots, w.1 = old := by
      rcases h with h | ⟨w, hw, eq⟩
      · exact Or.inl h
      · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, eq⟩
    by_cases hv : v.1 * den ≤ target
    · simp only [if_pos hv]
      refine ⟨?_, ?_, ?_⟩
      · rcases le_total v.1 old with h | h
        · rw [max_eq_right h]
          exact survives keyFrom
        · rw [max_eq_left h]
          exact Or.inr ⟨v, List.mem_cons_self, rfl⟩
      · rcases le_total v.1 old with h | h
        · rw [max_eq_right h]
          exact keyFits
        · rw [max_eq_left h]
          exact hv
      · intro w hw fits
        rcases List.mem_cons.mp hw with rfl | oldMem
        · exact le_max_left _ _
        · exact (maxKey w oldMem fits).trans (le_max_right _ _)
    · simp only [if_neg hv]
      refine ⟨survives keyFrom, keyFits, ?_⟩
      intro w hw fits
      rcases List.mem_cons.mp hw with rfl | oldMem
      · exact (hv fits).elim
      · exact maxKey w oldMem fits

private theorem upperGridKey_spec (knots : List GridKnot) (den target D : ℕ)
    (baseFits : target ≤ D * den) :
    let key := upperGridKey knots den target D
    (key = D ∨ ∃ v ∈ knots, v.1 = key) ∧ target ≤ key * den ∧
      ∀ v ∈ knots, target ≤ v.1 * den → key ≤ v.1 := by
  induction knots with
  | nil => simp [upperGridKey, baseFits]
  | cons v knots ih =>
    obtain ⟨keyFrom, keyFits, minKey⟩ := ih
    let old := upperGridKey knots den target D
    change (let key := if target ≤ v.1 * den then min v.1 old else old
      (key = D ∨ ∃ w ∈ v :: knots, w.1 = key) ∧ target ≤ key * den ∧
        ∀ w ∈ v :: knots, target ≤ w.1 * den → key ≤ w.1)
    have survives (h : old = D ∨ ∃ w ∈ knots, w.1 = old) :
        old = D ∨ ∃ w ∈ v :: knots, w.1 = old := by
      rcases h with h | ⟨w, hw, eq⟩
      · exact Or.inl h
      · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, eq⟩
    by_cases hv : target ≤ v.1 * den
    · simp only [if_pos hv]
      refine ⟨?_, ?_, ?_⟩
      · rcases le_total v.1 old with h | h
        · rw [min_eq_left h]
          exact Or.inr ⟨v, List.mem_cons_self, rfl⟩
        · rw [min_eq_right h]
          exact survives keyFrom
      · rcases le_total v.1 old with h | h
        · rw [min_eq_left h]
          exact hv
        · rw [min_eq_right h]
          exact keyFits
      · intro w hw fits
        rcases List.mem_cons.mp hw with rfl | oldMem
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (minKey w oldMem fits)
    · simp only [if_neg hv]
      refine ⟨survives keyFrom, keyFits, ?_⟩
      intro w hw fits
      rcases List.mem_cons.mp hw with rfl | oldMem
      · exact (hv fits).elim
      · exact minKey w oldMem fits

private def clampedNumerator (p : RationalNameCode) : ℕ :=
  if p.1 then 0 else min p.2.1 (p.2.2 + 1)

private theorem clampedNumerator_le (p : RationalNameCode) : clampedNumerator p ≤ p.2.2 + 1 := by
  unfold clampedNumerator
  split
  · exact Nat.zero_le _
  · exact min_le_right _ _

private theorem clamp_rationalNameValue (p : RationalNameCode) :
    max 0 (min (rationalNameValue p : ℝ) 1) = gridReal (p.2.2 + 1) (clampedNumerator p) := by
  obtain ⟨negative, n, d⟩ := p
  have pos : 0 < (d : ℝ) + 1 := by positivity
  cases negative
  · have value : (rationalNameValue (false, n, d) : ℝ) = gridReal (d + 1) n := by
      simp [rationalNameValue, gridReal]
    rw [value]
    change max 0 (min (gridReal (d + 1) n) 1) = gridReal (d + 1) (min n (d + 1))
    by_cases h : n ≤ d + 1
    · rw [min_eq_left h]
      have v := gridReal_Icc (d + 1) n (by omega) h
      rw [min_eq_left v.2, max_eq_right v.1]
    · have h' := le_of_not_ge h
      rw [min_eq_right h']
      have one : gridReal (d + 1) (d + 1) = 1 := by
        simp [gridReal, pos.ne']
      rw [← one, min_eq_right ((gridReal_le (D := d + 1) (by omega)).mpr h')]
      rw [one, max_eq_right zero_le_one]
  · change max 0 (min (rationalNameValue (true, n, d) : ℝ) 1) = gridReal (d + 1) 0
    have value : (rationalNameValue (true, n, d) : ℝ) = -gridReal (d + 1) n := by
      simp [rationalNameValue, gridReal]
    have nonneg : 0 ≤ gridReal (d + 1) n := by
      unfold gridReal
      positivity
    rw [value, max_eq_left ((min_le_left _ _).trans (neg_nonpos.mpr nonneg))]
    simp [gridReal]

private theorem rationalNameValue_fraction (n d : ℕ) (hd : 0 < d) :
    (rationalNameValue (false, n, d - 1) : ℝ) = gridReal d n := by
  have sum : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
  simp only [rationalNameValue, Bool.false_eq_true, if_false, gridReal, sum, Rat.cast_div, Rat.cast_natCast]

/-- Evaluate a rational polygon at a rational input by scanning the encoded abscissae. -/
def gridInterpolate (knots : List GridKnot) (D V : ℕ) (p : RationalNameCode) : RationalNameCode :=
  let den := p.2.2 + 1
  let target := clampedNumerator p * D
  let a := lowerGridKey knots den target
  let b := upperGridKey knots den target D
  if a = b then (false, gridHeight knots a, V - 1)
  else
    let above := b * den - target
    let below := target - a * den
    (false, above * gridHeight knots a + below * gridHeight knots b,
      V * (b * den - a * den) - 1)

theorem gridInterpolate_primrec :
    Primrec (fun q : List GridKnot × ℕ × ℕ × RationalNameCode =>
      gridInterpolate q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  let Input := List GridKnot × ℕ × ℕ × RationalNameCode
  have knots : Primrec (fun q : Input => q.1) := Primrec.fst
  have D : Primrec (fun q : Input => q.2.1) := Primrec.fst.comp Primrec.snd
  have V : Primrec (fun q : Input => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have input : Primrec (fun q : Input => q.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have den := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp input))
  have num := Primrec.fst.comp (Primrec.snd.comp input)
  have clamp : Primrec (fun q : Input => clampedNumerator q.2.2.2) :=
    (Primrec.cond (Primrec.fst.comp input) (Primrec.const 0) (Primrec.nat_min.comp num den)).of_eq
      (fun q => by cases h : q.2.2.2.1 <;> simp [clampedNumerator, h])
  have target := Primrec.nat_mul.comp clamp D
  have lo := lowerGridKey_primrec.comp (knots.pair (den.pair target))
  have hi := upperGridKey_primrec.comp (knots.pair (den.pair (target.pair D)))
  have y₀ := gridHeight_primrec.comp knots lo
  have y₁ := gridHeight_primrec.comp knots hi
  have start := Primrec.nat_mul.comp lo den
  have stop := Primrec.nat_mul.comp hi den
  have above := Primrec.nat_sub.comp stop target
  have below := Primrec.nat_sub.comp target start
  have numerator := Primrec.nat_add.comp (Primrec.nat_mul.comp above y₀) (Primrec.nat_mul.comp below y₁)
  have denom := Primrec.nat_mul.comp V (Primrec.nat_sub.comp stop start)
  exact Primrec.ite (Primrec.eq.comp lo hi)
    ((Primrec.const false).pair (y₀.pair (Primrec.nat_sub.comp V (Primrec.const 1))))
    ((Primrec.const false).pair (numerator.pair (Primrec.nat_sub.comp denom (Primrec.const 1))))

private theorem grid_brackets (knots : List GridKnot) {D d x : ℕ} (hD : 0 < D)
    (hd : 0 < d) (hx : x ≤ d) (h0 : ∃ v ∈ knots, v.1 = 0)
    (h1 : ∃ v ∈ knots, v.1 = D) :
    let K := gridKnotSet knots D
    let a := lowerGridKey knots d (x * D)
    let b := upperGridKey knots d (x * D) D
    IsGreatest (K ∩ Iic (gridReal d x)) (gridReal D a) ∧
      IsLeast (K ∩ Ici (gridReal d x)) (gridReal D b) := by
  let a := lowerGridKey knots d (x * D)
  let b := upperGridKey knots d (x * D) D
  have aSpec := lowerGridKey_spec knots d (x * D)
  have xD : x * D ≤ D * d := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right D hx
  have bSpec := upperGridKey_spec knots d (x * D) D xD
  have compares (n : ℕ) :
      gridReal D n ≤ gridReal d x ↔ n * d ≤ x * D := by
    unfold gridReal
    rw [div_le_div_iff₀ (by exact_mod_cast hD) (by exact_mod_cast hd)]
    exact_mod_cast Iff.rfl
  have compares' (n : ℕ) :
      gridReal d x ≤ gridReal D n ↔ x * D ≤ n * d := by
    unfold gridReal
    rw [div_le_div_iff₀ (by exact_mod_cast hd) (by exact_mod_cast hD)]
    exact_mod_cast Iff.rfl
  have aK : gridReal D a ∈ gridKnotSet knots D := by
    rcases aSpec.1 with zero | ⟨v, mem, eq⟩
    · rw [show a = 0 from zero]
      obtain ⟨v, mem, eq⟩ := h0
      exact ⟨v, mem, congrArg (gridReal D) eq⟩
    · exact ⟨v, mem, congrArg (gridReal D) eq⟩
  have bK : gridReal D b ∈ gridKnotSet knots D := by
    rcases bSpec.1 with top | ⟨v, mem, eq⟩
    · rw [show b = D from top]
      obtain ⟨v, mem, eq⟩ := h1
      exact ⟨v, mem, congrArg (gridReal D) eq⟩
    · exact ⟨v, mem, congrArg (gridReal D) eq⟩
  refine ⟨⟨⟨aK, (compares a).mpr aSpec.2.1⟩, ?_⟩, ⟨⟨bK, (compares' b).mpr bSpec.2.1⟩, ?_⟩⟩
  · rintro _ ⟨⟨v, mem, rfl⟩, le⟩
    exact (gridReal_le hD).mpr (aSpec.2.2 v mem ((compares v.1).mp le))
  · rintro _ ⟨⟨v, mem, rfl⟩, le⟩
    exact (gridReal_le hD).mpr (bSpec.2.2 v mem ((compares' v.1).mp le))

theorem gridInterpolate_value (knots : List GridKnot) (D V : ℕ) (hD : 0 < D) (hV : 0 < V)
    (h0 : ∃ v ∈ knots, v.1 = 0) (h1 : ∃ v ∈ knots, v.1 = D) (p : RationalNameCode) :
    (rationalNameValue (gridInterpolate knots D V p) : ℝ) =
      realPolygonOfVertices (gridRationalVertices knots D V) (rationalNameValue p : ℝ) := by
  let d := p.2.2 + 1
  let x := clampedNumerator p
  let a := lowerGridKey knots d (x * D)
  let b := upperGridKey knots d (x * D) D
  let values := polygonVertexValue (gridRationalVertices knots D V)
  have hd : 0 < d := by dsimp [d]; omega
  have hxd : x ≤ d := clampedNumerator_le p
  have ⟨lo, hi⟩ := grid_brackets knots hD hd hxd h0 h1
  change IsGreatest _ (gridReal D a) at lo
  change IsLeast _ (gridReal D b) at hi
  have hle : a ≤ b := (gridReal_le hD).mp (lo.1.2.trans hi.1.2)
  have left := (lowerGridKey_spec knots d (x * D)).2.1
  have right := (upperGridKey_spec knots d (x * D) D (by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right D hxd)).2.1
  change a * d ≤ x * D at left
  change x * D ≤ b * d at right
  rw [realPolygonOfVertices, gridKnotSet_vertices, affineExtension, clamp_rationalNameValue]
  rw [extendOnUnit, show lastPoint _ (gridReal d x) = gridReal D a from lo.csSup_eq,
    show nextPoint _ (gridReal d x) = gridReal D b from hi.csInf_eq]
  by_cases eq : a = b
  · change (rationalNameValue (if a = b then _ else _) : ℝ) = _
    rw [if_pos eq, if_pos ((gridReal_eq hD).mpr eq), rationalNameValue_fraction _ _ hV,
      gridVertexValue knots D V a hD]
  · have ab : a < b := hle.lt_of_ne eq
    have width : a * d < b * d := Nat.mul_lt_mul_of_pos_right ab hd
    have den : 0 < V * (b * d - a * d) := Nat.mul_pos hV (Nat.sub_pos_of_lt width)
    change (rationalNameValue (if a = b then _ else _) : ℝ) = _
    rw [if_neg eq, if_neg (fun e => eq ((gridReal_eq hD).mp e)), rationalNameValue_fraction _ _ den]
    unfold affineBridge
    rw [gridVertexValue knots D V a hD, gridVertexValue knots D V b hD]
    let w := (gridReal d x - gridReal D a) / (gridReal D b - gridReal D a)
    change gridReal (V * (b * d - a * d))
      ((b * d - x * D) * gridHeight knots a + (x * D - a * d) * gridHeight knots b) =
      (1 - w) * gridReal V (gridHeight knots a) + w * gridReal V (gridHeight knots b)
    simp only [gridReal, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (left.trans right), Nat.cast_sub left,
      Nat.cast_sub right, w]
    have Dne : (D : ℝ) ≠ 0 := by positivity
    have Vne : (V : ℝ) ≠ 0 := by positivity
    have dne : (d : ℝ) ≠ 0 := by positivity
    have slope : (b : ℝ) - a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm eq)
    rw [← sub_div]
    field_simp [Dne, Vne, dne, slope]
    ring

end Guo

#print axioms Guo.gridRationalPolygon_lipschitz
#print axioms Guo.gridInterpolate_value
#print axioms Guo.gridInterpolate_primrec
