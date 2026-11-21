import Weak_3_Randomness_and_Luzin_N.GuoOracleCode

namespace Guo

namespace OracleCode

def eval (Z : ℕ →. ℕ) : OracleCode → (ℕ →. ℕ)
  | .zero => fun _ => 0
  | .succ => fun n => Nat.succ n
  | .left => fun n => n.unpair.1
  | .right => fun n => n.unpair.2
  | .call => Z
  | .pair f g => fun n => Nat.pair <$> f.eval Z n <*> g.eval Z n
  | .comp f g => fun n => g.eval Z n >>= f.eval Z
  | .prec base step => fun p =>
    let (a, n) := p.unpair
    n.rec (base.eval Z a) fun y val => do
      let i ← val
      step.eval Z (Nat.pair a (Nat.pair y i))
  | .search test => fun a =>
    Nat.rfind fun n => (fun m => m = 0) <$> test.eval Z (Nat.pair a n)

theorem eval_recursiveIn (Z : ℕ →. ℕ) (c : OracleCode) : Nat.RecursiveIn {Z} (c.eval Z) := by
  induction c with
  | zero => exact .zero
  | succ => exact .succ
  | left => exact .left
  | right => exact .right
  | call => exact .oracle Z rfl
  | pair _ _ hf hg => exact .pair hf hg
  | comp _ _ hf hg => exact .comp hf hg
  | prec _ _ hf hg => exact .prec hf hg
  | search _ hf => exact .rfind hf

theorem exists_eval {Z f : ℕ →. ℕ} (h : Nat.RecursiveIn {Z} f) :
    ∃ c : OracleCode, c.eval Z = f := by
  induction h with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | oracle g hg =>
    have eq : g = Z := hg
    exact ⟨.call, eq.symm⟩
  | pair _ _ hf hg =>
    obtain ⟨f, rfl⟩ := hf
    obtain ⟨g, rfl⟩ := hg
    exact ⟨.pair f g, rfl⟩
  | comp _ _ hf hg =>
    obtain ⟨f, rfl⟩ := hf
    obtain ⟨g, rfl⟩ := hg
    exact ⟨.comp f g, rfl⟩
  | prec _ _ hf hg =>
    obtain ⟨f, rfl⟩ := hf
    obtain ⟨g, rfl⟩ := hg
    exact ⟨.prec f g, rfl⟩
  | rfind _ hf =>
    obtain ⟨f, rfl⟩ := hf
    exact ⟨.search f, rfl⟩

end OracleCode

noncomputable def haltingFlag (f : ℕ →. ℕ) (n : ℕ) : ℕ :=
  @ite ℕ (f n).Dom (Classical.propDecidable _) 0 1

@[simp] theorem haltingFlag_eq_zero_iff (f : ℕ →. ℕ) (n : ℕ) :
    haltingFlag f n = 0 ↔ (f n).Dom := by
  classical
  simp [haltingFlag]

/-- The relative halting oracle on a pair of program index and input, with zero for halting. -/
noncomputable def oracleJump (Z : ℕ →. ℕ) (n : ℕ) : Part ℕ :=
  Part.some (match Encodable.decode (α := OracleCode) n.unpair.1 with
    | some code => haltingFlag (code.eval Z) n.unpair.2
    | none => 1)

theorem oracleJump_index (Z : ℕ →. ℕ) (c : OracleCode) (n : ℕ) :
    oracleJump Z (Nat.pair (Encodable.encode c) n) = Part.some (haltingFlag (c.eval Z) n) := by
  simp [oracleJump]

theorem oracleJump_decides_domain {Z f : ℕ →. ℕ} (h : Nat.RecursiveIn {Z} f) :
    Nat.RecursiveIn {oracleJump Z} (fun n => Part.some (haltingFlag f n)) := by
  obtain ⟨code, rfl⟩ := OracleCode.exists_eval h
  have lookup : Nat.Primrec (fun n => Nat.pair (Encodable.encode code) n) :=
    .pair (Nat.Primrec.const _) Nat.Primrec.id
  have query : Nat.RecursiveIn {oracleJump Z} (oracleJump Z) := .oracle _ rfl
  refine (Nat.RecursiveIn.comp query lookup.recursiveIn).of_eq ?_
  intro n
  change (Part.some (Nat.pair (Encodable.encode code) n)).bind (oracleJump Z) = _
  rw [Part.bind_some, oracleJump_index]

/-- Unbounded search over a total relative test that returns zero on success. -/
def oracleSearch (test : ℕ → ℕ) (a : ℕ) : Part ℕ :=
  Nat.rfind fun n => Part.some (test (Nat.pair a n) = 0)

theorem oracleSearch_recursiveIn {O : Set (ℕ →. ℕ)} {test : ℕ → ℕ}
    (h : Nat.RecursiveIn O (fun n => Part.some (test n))) :
    Nat.RecursiveIn O (oracleSearch test) :=
  (Nat.RecursiveIn.rfind h).of_eq fun _ => rfl

@[simp] theorem oracleSearch_dom (test : ℕ → ℕ) (a : ℕ) :
    (oracleSearch test a).Dom ↔ ∃ n, test (Nat.pair a n) = 0 := by
  simp [oracleSearch, Nat.rfind_dom]

theorem oracleSearch_spec {test : ℕ → ℕ} {a n : ℕ} (h : n ∈ oracleSearch test a) :
    test (Nat.pair a n) = 0 := by
  have found := Nat.rfind_spec h
  simpa using found

private def equalityHalt (n : ℕ) : Part ℕ :=
  Part.ofOption (if n.unpair.1 = n.unpair.2 then some 0 else none)

private theorem equalityHalt_partrec : Nat.Partrec equalityHalt := by
  have test : Primrec (fun n : ℕ => if n.unpair.1 = n.unpair.2 then some (0 : ℕ) else none) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
      (Primrec.const _) (Primrec.const _)
  exact Partrec.nat_iff.mp (Computable.ofOption test.to_comp)

private def graphHalt (f : ℕ →. ℕ) (n : ℕ) : Part ℕ :=
  (Nat.pair <$> f n.unpair.1 <*> Part.some n.unpair.2) >>= equalityHalt

private theorem graphHalt_recursiveIn {Z f : ℕ →. ℕ} (h : Nat.RecursiveIn {Z} f) :
    Nat.RecursiveIn {Z} (graphHalt f) := by
  have readFirst := (Nat.RecursiveIn.comp h (.left : Nat.RecursiveIn {Z} _)).of_eq
    (fun n => Part.bind_some (n.unpair.1) f)
  exact .comp equalityHalt_partrec.recursiveIn (.pair readFirst .right)

@[simp] private theorem graphHalt_dom (f : ℕ →. ℕ) (x y : ℕ) :
    (graphHalt f (Nat.pair x y)).Dom ↔ y ∈ f x := by
  rw [Part.dom_iff_mem]
  simp [graphHalt, equalityHalt, seq_eq_bind_map, Part.mem_bind_iff, Part.mem_ofOption]

/-- The jump computes every partial function recursive in its original oracle. -/
theorem recursiveIn_oracleJump {Z f : ℕ →. ℕ} (h : Nat.RecursiveIn {Z} f) :
    Nat.RecursiveIn {oracleJump Z} f := by
  apply (oracleSearch_recursiveIn (oracleJump_decides_domain (graphHalt_recursiveIn h))).of_eq
  intro x
  apply Part.ext
  intro y
  constructor
  · intro hy
    simpa using oracleSearch_spec hy
  · intro hy
    have searchDom : (oracleSearch (haltingFlag (graphHalt f)) x).Dom :=
      (oracleSearch_dom _ _).mpr ⟨y, by simpa using hy⟩
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp searchDom
    have hw' : w ∈ f x := by simpa using oracleSearch_spec hw
    rwa [Part.mem_unique hw' hy] at hw

end Guo

#print axioms Guo.oracleJump_decides_domain
#print axioms Guo.recursiveIn_oracleJump
