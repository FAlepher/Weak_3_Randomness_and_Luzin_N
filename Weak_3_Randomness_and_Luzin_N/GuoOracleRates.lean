import Weak_3_Randomness_and_Luzin_N.GuoOracleJump
import Weak_3_Randomness_and_Luzin_N.GuoOracleMeasure

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace Guo

private noncomputable def rateBound (n : ℕ) : ℝ≥0∞ := ((2 : ℝ≥0∞)⁻¹)^n

private noncomputable def margin (n precision : ℕ) : ℝ≥0∞ := rateBound (n + precision + 1)

private def overBudgetCode (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  let (n, k) := q.1
  let (c, d) := q.2
  if 2^(d + k + 1) < c * 2^(n + k + 1) + 2^d then 0 else 1

private theorem primrec_pow_two : Primrec (fun n : ℕ => (2 : ℕ)^n) := by
  have step : Primrec₂ (fun (_ : ℕ) (a : ℕ) => a * 2) :=
    Primrec.nat_mul.comp Primrec.snd (Primrec.const 2)
  apply (Primrec.nat_rec₁ 1 step).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.rec 1 (fun _ a => a * 2) n * 2 = (2 : ℕ)^(n + 1)
    rw [ih, pow_succ]

private theorem overBudgetCode_primrec : Primrec overBudgetCode := by
  let Input := (ℕ × ℕ) × (ℕ × ℕ)
  have n : Primrec (fun q : Input => q.1.1) := Primrec.fst.comp Primrec.fst
  have k : Primrec (fun q : Input => q.1.2) := Primrec.snd.comp Primrec.fst
  have c : Primrec (fun q : Input => q.2.1) := Primrec.fst.comp Primrec.snd
  have d : Primrec (fun q : Input => q.2.2) := Primrec.snd.comp Primrec.snd
  have lhs : Primrec (fun q : Input => 2^(q.2.2 + q.1.2 + 1)) :=
    primrec_pow_two.comp (Primrec.succ.comp (Primrec.nat_add.comp d k))
  have rhs : Primrec (fun q : Input => q.2.1 * 2^(q.1.1 + q.1.2 + 1) + 2^q.2.2) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp c (primrec_pow_two.comp (Primrec.succ.comp (Primrec.nat_add.comp n k))))
      (primrec_pow_two.comp d)
  exact Primrec.ite (Primrec.nat_lt.comp lhs rhs) (Primrec.const 0) (Primrec.const 1)

private theorem pow_mul_rateBound (a b : ℕ) :
    (2 : ℝ≥0∞)^(a + b) * rateBound a = (2 : ℝ≥0∞)^b := by
  have h0 : (2 : ℝ≥0∞)^a ≠ 0 := by simp
  have htop : (2 : ℝ≥0∞)^a ≠ ∞ := by simp
  unfold rateBound
  rw [pow_add, ← ENNReal.inv_pow, mul_right_comm, ENNReal.mul_inv_cancel h0 htop, one_mul]

private theorem overBudgetCode_eq_zero (n k : ℕ) (code : ℕ × ℕ) :
    overBudgetCode ((n, k), code) = 0 ↔ rateBound n < dyadicMass code + margin n k := by
  obtain ⟨c, d⟩ := code
  let m := (2 : ℝ≥0∞)^(d + n + k + 1)
  have hm : 0 < m := ENNReal.pow_pos (by norm_num : (0 : ℝ≥0∞) < 2) _
  have hmTop : m ≠ ∞ := by simp [m]
  have lhs : m * rateBound n = (2 : ℝ≥0∞)^(d + k + 1) := by
    rw [show m = (2 : ℝ≥0∞)^(n + (d + k + 1)) from
      congrArg (fun e : ℕ => (2 : ℝ≥0∞)^e) (by omega), pow_mul_rateBound]
  have rhs₁ : m * dyadicMass (c, d) = (c : ℝ≥0∞) * (2 : ℝ≥0∞)^(n + k + 1) := by
    change m * ((c : ℝ≥0∞) * rateBound d) = _
    rw [mul_left_comm, show m = (2 : ℝ≥0∞)^(d + (n + k + 1)) from
      congrArg (fun e : ℕ => (2 : ℝ≥0∞)^e) (by omega), pow_mul_rateBound]
  have rhs₂ : m * margin n k = (2 : ℝ≥0∞)^d := by
    unfold margin
    rw [show m = (2 : ℝ≥0∞)^((n + k + 1) + d) from
      congrArg (fun e : ℕ => (2 : ℝ≥0∞)^e) (by omega), pow_mul_rateBound]
  rw [← ENNReal.mul_lt_mul_iff_right hm.ne' hmTop, mul_add, lhs, rhs₁, rhs₂]
  simp only [overBudgetCode, ite_eq_left_iff, one_ne_zero, imp_false, not_not]
  exact_mod_cast (Iff.rfl : (2^(d + k + 1) < c * 2^(n + k + 1) + 2^d) ↔ _)

/-- Input coding is `pair (pair n (pair layer precision)) stage`. -/
private def overshoot (enum : OracleStream) (q : ℕ) : ℕ :=
  overBudgetCode ((q.unpair.1.unpair.1, q.unpair.1.unpair.2.unpair.2),
    finiteLayerMassCode enum q.unpair.1.unpair.2.unpair.1 q.unpair.2)

section OvershootComputability

attribute [local irreducible] ComputableIn

private theorem overshoot_computableIn {O : Set Oracle} {enum : OracleStream}
    (he : ComputableIn O enum) : ComputableIn O (overshoot enum) := by
  have fst : Primrec (fun n : ℕ => n.unpair.1) := Primrec.fst.comp Primrec.unpair
  have snd : Primrec (fun n : ℕ => n.unpair.2) := Primrec.snd.comp Primrec.unpair
  have target : Primrec (fun q : ℕ => q.unpair.1.unpair.1) := fst.comp fst
  have choice : Primrec (fun q : ℕ => q.unpair.1.unpair.2) := snd.comp fst
  have queries : Primrec (fun q : ℕ => (q.unpair.1.unpair.2.unpair.1, q.unpair.2)) :=
    (fst.comp choice).pair snd
  have params : ComputableIn O (fun q : ℕ => (q.unpair.1.unpair.1, q.unpair.1.unpair.2.unpair.2)) :=
    (target.pair (snd.comp choice)).computableIn
  have mass : ComputableIn O
      (fun q : ℕ => finiteLayerMassCode enum q.unpair.1.unpair.2.unpair.1 q.unpair.2) :=
    computableIn_comp (f := fun p : ℕ × ℕ => finiteLayerMassCode enum p.1 p.2)
      (finiteLayerMassCode_computableIn he) queries.computableIn
  have args : ComputableIn O (fun q : ℕ =>
      ((q.unpair.1.unpair.1, q.unpair.1.unpair.2.unpair.2),
        finiteLayerMassCode enum q.unpair.1.unpair.2.unpair.1 q.unpair.2)) :=
    computableIn_pair params mass
  exact computableIn_comp overBudgetCode_primrec.computableIn args

end OvershootComputability

private noncomputable def certifiedFlag (enum : OracleStream) (q : ℕ) : ℕ :=
  1 - haltingFlag (oracleSearch (overshoot enum)) q

private theorem certifiedFlag_eq_zero (enum : OracleStream) (n layer precision : ℕ) :
    certifiedFlag enum (Nat.pair n (Nat.pair layer precision)) = 0 ↔
      fairCoin (oracleLayer enum layer) + margin n precision ≤ rateBound n := by
  classical
  have hflip (q : ℕ) :
      certifiedFlag enum q = 0 ↔ ¬(oracleSearch (overshoot enum) q).Dom := by
    by_cases h : (oracleSearch (overshoot enum) q).Dom <;>
      simp [certifiedFlag, haltingFlag, h, -oracleSearch_dom]
  rw [hflip, oracleSearch_dom, oracleLayer_measure_iSup, ENNReal.iSup_add, iSup_le_iff]
  simp only [overshoot, Nat.unpair_pair, overBudgetCode_eq_zero, not_exists, not_lt]

private theorem certifiedFlag_recursiveIn {Z : Oracle} {enum : OracleStream}
    (he : ComputableIn {Z} enum) :
    Nat.RecursiveIn {oracleJump Z} (fun q => Part.some (certifiedFlag enum q)) := by
  have violation : Nat.RecursiveIn {Z} (oracleSearch (overshoot enum)) :=
    oracleSearch_recursiveIn (RecursiveIn.iff_nat.mp (overshoot_computableIn he))
  have flag := oracleJump_decides_domain violation
  have flip : Nat.Primrec (fun n => 1 - n) :=
    Primrec.nat_iff.mp (Primrec.nat_sub.comp (Primrec.const 1) Primrec.id)
  refine (Nat.RecursiveIn.comp flip.recursiveIn flag).of_eq ?_
  intro q
  change (Part.some (haltingFlag (oracleSearch (overshoot enum)) q)).bind
    (fun k => Part.some (1 - k)) = _
  rw [Part.bind_some]
  rfl

private theorem exists_margin_le {value : ℝ≥0∞} {n : ℕ} (h : value < rateBound n) :
    ∃ k, value + margin n k ≤ rateBound n := by
  have geom := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (show ((2 : ℝ≥0∞)⁻¹) < 1 by norm_num)
  have limit : Tendsto (margin n) atTop (𝓝 0) := by
    have e : margin n = (fun k : ℕ => ((2 : ℝ≥0∞)⁻¹)^(k + (n + 1))) := by
      funext k
      unfold margin rateBound
      congr 1
      omega
    rw [e]
    exact geom.comp (tendsto_add_atTop_nat (n + 1))
  have added : Tendsto (fun k => value + margin n k) atTop (𝓝 value) := by
    simpa using tendsto_const_nhds.add limit
  obtain ⟨k, hk⟩ := ((tendsto_order.1 added).2 _ h).exists
  exact ⟨k, hk.le⟩

/-- The jump can uniformly find a layer strictly below each dyadic measure budget. -/
theorem oracleJump_finds_small_layers {Z : Oracle} {enum : OracleStream}
    (he : ComputableIn {Z} enum)
    (small : ∀ n : ℕ, ∃ layer, fairCoin (oracleLayer enum layer) < rateBound n) :
    ∃ selectLayer : ℕ → ℕ, ComputableIn {oracleJump Z} selectLayer ∧
      ∀ n, fairCoin (oracleLayer enum (selectLayer n)) < rateBound n := by
  let search := oracleSearch (certifiedFlag enum)
  have halted (n : ℕ) : (search n).Dom := by
    obtain ⟨layer, hl⟩ := small n
    obtain ⟨precision, hp⟩ := exists_margin_le hl
    exact (oracleSearch_dom _ _).mpr
      ⟨Nat.pair layer precision, (certifiedFlag_eq_zero enum n layer precision).mpr hp⟩
  let selection (n : ℕ) := (search n).get (halted n)
  have selectionRec : Nat.RecursiveIn {oracleJump Z} (fun n => Part.some (selection n)) :=
    (oracleSearch_recursiveIn (certifiedFlag_recursiveIn he)).of_eq_tot
      (fun n => Part.get_mem (halted n))
  have selectionComp : ComputableIn {oracleJump Z} selection := RecursiveIn.iff_nat.mpr selectionRec
  have project : ComputableIn {oracleJump Z} (fun n : ℕ => n.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).computableIn
  refine ⟨fun n => (selection n).unpair.1,
    computableIn_comp (f := fun n : ℕ => n.unpair.1) project selectionComp, ?_⟩
  intro n
  have passed : certifiedFlag enum (Nat.pair n (selection n)) = 0 :=
    oracleSearch_spec (test := certifiedFlag enum) (Part.get_mem (halted n))
  rw [← Nat.pair_unpair (selection n)] at passed
  have h := (certifiedFlag_eq_zero enum n (selection n).unpair.1 (selection n).unpair.2).mp passed
  have positive : 0 < margin n (selection n).unpair.2 :=
    ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) _
  exact (ENNReal.lt_add_right (measure_ne_top _ _) positive.ne').trans_le h

/-- The small-layer operation used in Lemma 2.2, for the concrete oracle open-test model. -/
theorem oracleJump_effectiveRateSearch (Z : Oracle) :
    EffectiveRateSearch oracleOpenTestFramework Z (oracleJump Z) := by
  intro U hU hsmall
  obtain ⟨enum, he, layers⟩ := hU
  obtain ⟨selectLayer, hs, hcost⟩ :=
    oracleJump_finds_small_layers he (by simpa only [layers, rateBound] using hsmall)
  have lift : ComputableIn {oracleJump Z} enum := recursiveIn_oracleJump he
  exact ⟨selectLayer, ⟨_, oracleUniformOpen_reindex lift hs, fun n => layers (selectLayer n)⟩,
    by simpa only [layers, rateBound] using hcost⟩

def emptyOracle : Oracle := fun _ => Part.some 0

noncomputable def firstJump : Oracle := oracleJump emptyOracle

noncomputable def secondJump : Oracle := oracleJump firstJump

/-- The randomness-class inclusion used in Lemma 2.2, with the two concrete jumps. -/
theorem weakFailure_implies_secondJumpFailure (x : Cantor) :
    FailsWeak oracleOpenTestFramework firstJump x →
      FailsMartinLof oracleOpenTestFramework secondJump x :=
  failsMartinLof_of_failsWeak _ _ _ (oracleJump_effectiveRateSearch firstJump) x

end Guo

#print axioms Guo.oracleJump_effectiveRateSearch
#print axioms Guo.weakFailure_implies_secondJumpFailure
