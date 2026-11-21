import Weak_3_Randomness_and_Luzin_N.GuoEndpointComputable

open Set MeasureTheory
open scoped ENNReal

namespace Guo

/-- A rational number represented by the difference of two naturals over a positive denominator. -/
abbrev SignedFraction := ℕ × ℕ × ℕ

namespace SignedFraction

noncomputable def val (a : SignedFraction) : ℝ :=
  ((a.1 : ℝ) - a.2.1) / ((a.2.2 : ℝ) + 1)

def add (a b : SignedFraction) : SignedFraction :=
  let ad := a.2.2 + 1
  let bd := b.2.2 + 1
  (a.1 * bd + b.1 * ad, a.2.1 * bd + b.2.1 * ad, ad * bd - 1)

def neg (a : SignedFraction) : SignedFraction := (a.2.1, a.1, a.2.2)

def mul (a b : SignedFraction) : SignedFraction :=
  (a.1 * b.1 + a.2.1 * b.2.1, a.1 * b.2.1 + a.2.1 * b.1, (a.2.2 + 1) * (b.2.2 + 1) - 1)

def bound (a : SignedFraction) : SignedFraction := (a.1 + a.2.1, 0, a.2.2)

def dyadic (a b d : ℕ) : SignedFraction := (a, b, 2 ^ d - 1)

def lt (a b : SignedFraction) : Bool :=
  decide (a.1 * (b.2.2 + 1) + b.2.1 * (a.2.2 + 1) <
    b.1 * (a.2.2 + 1) + a.2.1 * (b.2.2 + 1))

private theorem prodDen_pos (a b : SignedFraction) : 0 < (a.2.2 + 1) * (b.2.2 + 1) := by
  positivity

private theorem den_prod_cast (a b : SignedFraction) :
    (↑((a.2.2 + 1) * (b.2.2 + 1) - 1) : ℝ) + 1 =
      ((a.2.2 : ℝ) + 1) * ((b.2.2 : ℝ) + 1) := by
  exact_mod_cast Nat.sub_add_cancel (prodDen_pos a b)

@[simp] theorem val_add (a b : SignedFraction) : val (add a b) = val a + val b := by
  simp only [val, add, den_prod_cast, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  field_simp [show (↑a.2.2 : ℝ) + 1 ≠ 0 by positivity,
    show (↑b.2.2 : ℝ) + 1 ≠ 0 by positivity]
  ring

@[simp] theorem val_neg (a : SignedFraction) : val (neg a) = -val a := by
  simp only [val, neg, ← neg_div]
  congr 1
  ring

@[simp] theorem val_mul (a b : SignedFraction) : val (mul a b) = val a * val b := by
  simp only [val, mul, den_prod_cast, Nat.cast_add, Nat.cast_mul, div_mul_div_comm]
  congr 1
  ring

theorem val_bound (a : SignedFraction) : |val a| ≤ val (bound a) := by
  simp only [val, bound, Nat.cast_add, Nat.cast_zero, sub_zero, abs_div,
    abs_of_nonneg (by positivity : 0 ≤ (a.2.2 : ℝ) + 1)]
  gcongr
  rw [abs_le]
  constructor <;> linarith [show (0 : ℝ) ≤ a.1 by positivity, show (0 : ℝ) ≤ a.2.1 by positivity]

@[simp] theorem val_dyadic (a b d : ℕ) : val (dyadic a b d) = ((a : ℝ) - b) / (2 : ℝ)^d := by
  have denom : (↑(2 ^ d - 1 : ℕ) : ℝ) + 1 = (2 : ℝ)^d := by
    exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_iff.mpr (pow_pos (by norm_num : (0 : ℕ) < 2) d))
  rw [val, dyadic, ← denom]

theorem lt_true_iff (a b : SignedFraction) : lt a b = true ↔ val a < val b := by
  unfold lt val
  rw [decide_eq_true_eq, div_lt_div_iff₀ (by positivity) (by positivity)]
  have casts :
      (a.1 * (b.2.2 + 1) + b.2.1 * (a.2.2 + 1) < b.1 * (a.2.2 + 1) + a.2.1 * (b.2.2 + 1)) ↔
        ((a.1 : ℝ) * ((b.2.2 : ℝ) + 1) + (b.2.1 : ℝ) * ((a.2.2 : ℝ) + 1) <
          (b.1 : ℝ) * ((a.2.2 : ℝ) + 1) + (a.2.1 : ℝ) * ((b.2.2 : ℝ) + 1)) := by
    exact_mod_cast Iff.rfl
  rw [casts]
  constructor <;> intro h <;> linarith [h]

private theorem fst_fst : Primrec (fun p : SignedFraction × SignedFraction => p.1.1) :=
  Primrec.fst.comp Primrec.fst

private theorem fst_snd : Primrec (fun p : SignedFraction × SignedFraction => p.2.1) :=
  Primrec.fst.comp Primrec.snd

private theorem second_fst : Primrec (fun p : SignedFraction × SignedFraction => p.1.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.fst)

private theorem second_snd : Primrec (fun p : SignedFraction × SignedFraction => p.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

private theorem denom_fst : Primrec (fun p : SignedFraction × SignedFraction => p.1.2.2 + 1) :=
  Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))

private theorem denom_snd : Primrec (fun p : SignedFraction × SignedFraction => p.2.2.2 + 1) :=
  Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem add_primrec : Primrec₂ add :=
  ((Primrec.nat_add.comp (Primrec.nat_mul.comp fst_fst denom_snd)
    (Primrec.nat_mul.comp fst_snd denom_fst)).pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp second_fst denom_snd)
      (Primrec.nat_mul.comp second_snd denom_fst)).pair
      (Primrec.nat_sub.comp (Primrec.nat_mul.comp denom_fst denom_snd) (Primrec.const 1)))).to₂

theorem neg_primrec : Primrec neg :=
  (Primrec.fst.comp Primrec.snd).pair (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))

theorem mul_primrec : Primrec₂ mul :=
  ((Primrec.nat_add.comp (Primrec.nat_mul.comp fst_fst fst_snd)
    (Primrec.nat_mul.comp second_fst second_snd)).pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp fst_fst second_snd)
      (Primrec.nat_mul.comp second_fst fst_snd)).pair
      (Primrec.nat_sub.comp (Primrec.nat_mul.comp denom_fst denom_snd) (Primrec.const 1)))).to₂

theorem bound_primrec : Primrec bound :=
  (Primrec.nat_add.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
    ((Primrec.const 0).pair (Primrec.snd.comp Primrec.snd))

theorem dyadic_primrec : Primrec (fun p : ℕ × ℕ × ℕ => dyadic p.1 p.2.1 p.2.2) := by
  have power : Primrec (fun k : ℕ => (2 : ℕ)^k) :=
    (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id
  exact Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
    (Primrec.nat_sub.comp (power.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 1)))

theorem lt_primrec : Primrec₂ lt :=
  ((Primrec.nat_lt.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp fst_fst denom_snd)
      (Primrec.nat_mul.comp second_snd denom_fst))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp fst_snd denom_fst)
      (Primrec.nat_mul.comp second_fst denom_snd))).decide).to₂

end SignedFraction

def intervalLowerCode (c : DyadicIntervalCode) : SignedFraction :=
  SignedFraction.dyadic c.1 c.2.2.1 c.2.2.2

def intervalUpperCode (c : DyadicIntervalCode) : SignedFraction :=
  SignedFraction.dyadic c.2.1 c.2.2.1 c.2.2.2

theorem intervalLowerCode_primrec : Primrec intervalLowerCode :=
  SignedFraction.dyadic_primrec.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))

theorem intervalUpperCode_primrec : Primrec intervalUpperCode :=
  SignedFraction.dyadic_primrec.comp
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd))

theorem dyadicInterval_eq_codes (c : DyadicIntervalCode) :
    dyadicInterval c = Ioo (intervalLowerCode c).val (intervalUpperCode c).val := by
  simp [dyadicInterval, intervalLowerCode, intervalUpperCode]

end Guo
