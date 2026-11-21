import Weak_3_Randomness_and_Luzin_N.GuoOracleJump
import Mathlib.Computability.PartrecCode

open Encodable

namespace Guo

private def PreservesPrefix (Z Y : ℕ →. ℕ) (bound : ℕ) : Prop :=
  ∀ i < bound, ∀ v ∈ Z i, v ∈ Y i

private theorem PreservesPrefix.mono {Z Y : ℕ →. ℕ} {m n : ℕ}
    (h : PreservesPrefix Z Y n) (hm : m ≤ n) : PreservesPrefix Z Y m :=
  fun i hi => h i (hi.trans_le hm)

private def PreservedAt (Z : ℕ →. ℕ) (P : (ℕ →. ℕ) → Prop) (bound : ℕ) : Prop :=
  ∀ Y, PreservesPrefix Z Y bound → P Y

private theorem PreservedAt.mono {Z : ℕ →. ℕ} {P : (ℕ →. ℕ) → Prop} {m n : ℕ}
    (h : PreservedAt Z P m) (hm : m ≤ n) : PreservedAt Z P n :=
  fun Y extendsPrefix => h Y (extendsPrefix.mono hm)

private theorem commonPrefix {Z : ℕ →. ℕ} (P : ℕ → (ℕ →. ℕ) → Prop)
    (k : ℕ) (h : ∀ i < k, ∃ b, PreservedAt Z (P i) b) :
    ∃ b, ∀ i < k, PreservedAt Z (P i) b := by
  induction k with
  | zero => exact ⟨0, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ k ih =>
    obtain ⟨b₀, earlier⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    obtain ⟨b₁, last⟩ := h k (Nat.lt_succ_self _)
    refine ⟨max b₀ b₁, fun i hi => ?_⟩
    rcases (Nat.lt_succ_iff_lt_or_eq.mp hi) with lt | rfl
    · exact (earlier i lt).mono (le_max_left _ _)
    · exact last.mono (le_max_right _ _)

/-- Every successful oracle computation uses a bounded prefix of the oracle graph. -/
private theorem OracleCode.eval_preserved_prefix {Z : ℕ →. ℕ} (c : OracleCode)
    {a v : ℕ} (h : v ∈ c.eval Z a) :
    ∃ b, PreservedAt Z (fun Y => v ∈ c.eval Y a) b := by
  induction c generalizing a v with
  | zero => exact ⟨0, fun _ _ => h⟩
  | succ => exact ⟨0, fun _ _ => h⟩
  | left => exact ⟨0, fun _ _ => h⟩
  | right => exact ⟨0, fun _ _ => h⟩
  | call => exact ⟨a + 1, fun _ preserves => preserves a (Nat.lt_succ_self _) v h⟩
  | pair first second hf hs =>
    have decompose (Y : ℕ →. ℕ) :
        v ∈ (first.pair second).eval Y a ↔
          ∃ x ∈ first.eval Y a, ∃ y ∈ second.eval Y a, Nat.pair x y = v := by
      simp only [OracleCode.eval, seq_eq_bind_map, Part.bind_eq_bind, Part.map_eq_map,
        Part.bind_map, Part.mem_bind_iff, Part.mem_map_iff]
    obtain ⟨x, hx, y, hy, same⟩ := (decompose Z).mp h
    obtain ⟨bx, keepX⟩ := hf hx
    obtain ⟨by', keepY⟩ := hs hy
    exact ⟨max bx by', fun Y p => (decompose Y).mpr ⟨x, keepX Y (p.mono (le_max_left _ _)),
      y, keepY Y (p.mono (le_max_right _ _)), same⟩⟩
  | comp outer inner ho hi =>
    simp only [OracleCode.eval, Part.bind_eq_bind, Part.mem_bind_iff] at h ⊢
    obtain ⟨x, hx, hv⟩ := h
    obtain ⟨bx, keepX⟩ := hi hx
    obtain ⟨bv, keepV⟩ := ho hv
    exact ⟨max bx bv, fun Y p => ⟨x, keepX Y (p.mono (le_max_left _ _)),
      keepV Y (p.mono (le_max_right _ _))⟩⟩
  | prec base step hb hs =>
    let run (Y : ℕ →. ℕ) (k : ℕ) : Part ℕ :=
      k.rec (motive := fun _ => Part ℕ) (base.eval Y a.unpair.1) fun j old =>
        old.bind fun x => step.eval Y (Nat.pair a.unpair.1 (Nat.pair j x))
    change v ∈ run Z a.unpair.2 at h
    change ∃ b, PreservedAt Z (fun Y => v ∈ run Y a.unpair.2) b
    generalize a.unpair.2 = k at h ⊢
    induction k generalizing v with
    | zero => exact hb h
    | succ k ih =>
      obtain ⟨x, hx, hv⟩ := Part.mem_bind_iff.mp h
      obtain ⟨bx, keepX⟩ := ih hx
      obtain ⟨bv, keepV⟩ := hs hv
      exact ⟨max bx bv, fun Y p => Part.mem_bind_iff.mpr
        ⟨x, keepX Y (p.mono (le_max_left _ _)), keepV Y (p.mono (le_max_right _ _))⟩⟩
  | search test ih =>
    let check (Y : ℕ →. ℕ) (j : ℕ) :=
      (test.eval Y (Nat.pair a j)).map (fun m => decide (m = 0))
    change v ∈ Nat.rfind (check Z) at h
    change ∃ b, PreservedAt Z (fun Y => v ∈ Nat.rfind (check Y)) b
    have keepAt (j : ℕ) (result : Bool) (hj : result ∈ check Z j) :
        ∃ b, PreservedAt Z (fun Y => result ∈ check Y j) b := by
      obtain ⟨x, hx, rfl⟩ := (Part.mem_map_iff _).mp hj
      obtain ⟨b, replay⟩ := ih hx
      exact ⟨b, fun Y p => Part.mem_map _ (replay Y p)⟩
    have earlier (j : ℕ) (hj : j < v) : ∃ b, PreservedAt Z (fun Y => false ∈ check Y j) b :=
      keepAt j false (Nat.rfind_min h hj)
    obtain ⟨bp, before⟩ := commonPrefix (fun j Y => false ∈ check Y j) v earlier
    obtain ⟨bl, last⟩ := keepAt v true (Nat.rfind_spec h)
    exact ⟨max bp bl, fun Y p => Nat.mem_rfind.mpr
      ⟨last Y (p.mono (le_max_right _ _)), fun {j} hj => before j hj Y (p.mono (le_max_left _ _))⟩⟩

/-- Entries beyond the length of this oracle table are undefined. -/
def finiteOracleTable (table : List ℕ) (i : ℕ) : Part ℕ := Part.ofOption table[i]?

theorem OracleCode.eval_finiteTable_iff (c : OracleCode) (Z : ℕ → ℕ) (a v : ℕ) :
    v ∈ c.eval (fun i => Part.some (Z i)) a ↔
      ∃ len, v ∈ c.eval (finiteOracleTable ((List.range len).map Z)) a := by
  constructor
  · intro h
    obtain ⟨b, run⟩ := c.eval_preserved_prefix h
    refine ⟨b, run _ (fun i hi value mem => ?_)⟩
    have equal : value = Z i := Part.mem_some_iff.mp mem
    simp [finiteOracleTable, hi, equal]
  · rintro ⟨len, h⟩
    obtain ⟨b, run⟩ := c.eval_preserved_prefix h
    refine run _ (fun i _ value mem => ?_)
    by_cases hi : i < len
    · simpa [finiteOracleTable, hi] using mem
    · simp [finiteOracleTable, hi] at mem

abbrev OracleTableInput := List ℕ × ℕ

/-- With a fixed code and a finite table, ordinary partial recursion suffices. -/
theorem OracleCode.eval_finiteTable_partrec (c : OracleCode) :
    Partrec (fun p : OracleTableInput => c.eval (finiteOracleTable p.1) p.2) := by
  induction c with
  | zero => exact Computable.const 0
  | succ => exact Computable.succ.comp Computable.snd
  | left => exact (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  | right => exact (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  | call => exact Computable.ofOption Computable.list_getElem?
  | pair first second hf hs =>
    have withInput : Partrec (fun p : OracleTableInput × ℕ =>
        ((second.eval (finiteOracleTable p.1.1) p.1.2).map (Nat.pair p.2))) :=
      (hs.comp Computable.fst).map (Primrec₂.natPair.comp
        (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂.to_comp
    refine (hf.bind withInput.to₂).of_eq fun _ => ?_
    simp only [OracleCode.eval, seq_eq_bind_map, Part.bind_eq_bind, Part.map_eq_map, Part.bind_map]
  | comp outer inner ho hi =>
    have withInput : Partrec₂ (fun (p : OracleTableInput) (x : ℕ) => outer.eval (finiteOracleTable p.1) x) :=
      (ho.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).to_comp).to₂
    exact hi.bind withInput
  | prec base step hb hs =>
    let head (p : OracleTableInput) := p.2.unpair.1
    have parts : Primrec (fun p : OracleTableInput => p.2.unpair) := Primrec.unpair.comp Primrec.snd
    have headRec : Primrec head := Primrec.fst.comp parts
    have runBase : Partrec (fun p : OracleTableInput => base.eval (finiteOracleTable p.1) (head p)) :=
      hb.comp (Primrec.fst.pair headRec).to_comp
    have stepArgs : Primrec (fun p : OracleTableInput × (ℕ × ℕ) =>
        (p.1.1, Nat.pair (head p.1) (Nat.pair p.2.1 p.2.2))) :=
      (Primrec.fst.comp Primrec.fst).pair (Primrec₂.natPair.comp (headRec.comp Primrec.fst)
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))
    exact Partrec.nat_rec (Primrec.snd.comp parts).to_comp runBase (hs.comp stepArgs.to_comp).to₂
  | search test ht =>
    have arg : Primrec (fun p : OracleTableInput × ℕ => (p.1.1, Nat.pair p.1.2 p.2)) :=
      (Primrec.fst.comp Primrec.fst).pair (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
    have isZero : Computable₂ (fun (_ : OracleTableInput × ℕ) (v : ℕ) => decide (v = 0)) :=
      (Primrec.eq.comp Primrec.snd (Primrec.const 0)).decide.to₂.to_comp
    exact Partrec.rfind ((ht.comp arg.to_comp).map isZero).to₂

/-- Each relative program admits an ordinary code for replay on finite oracle tables. -/
theorem OracleCode.exists_finiteReplayCode (c : OracleCode) :
    ∃ d : Nat.Partrec.Code, ∀ table : List ℕ, ∀ a : ℕ,
      d.eval (encode (table, a)) = c.eval (finiteOracleTable table) a := by
  obtain ⟨d, exactEval⟩ := Nat.Partrec.Code.exists_code.mp (c.eval_finiteTable_partrec)
  refine ⟨d, fun table a => ?_⟩
  rw [exactEval]
  simp [Part.map_id']

end Guo

#print axioms Guo.OracleCode.eval_finiteTable_iff
#print axioms Guo.OracleCode.eval_finiteTable_partrec
