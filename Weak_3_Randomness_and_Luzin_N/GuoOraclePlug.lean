import Weak_3_Randomness_and_Luzin_N.GuoOracleJump

namespace Guo.OracleCode

/-- Substitute one program for each oracle instruction in a fixed template. -/
def plug (template driver : OracleCode) : OracleCode :=
  match template with
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .call => driver
  | .pair first second => .pair (first.plug driver) (second.plug driver)
  | .comp outer inner => .comp (outer.plug driver) (inner.plug driver)
  | .prec base step => .prec (base.plug driver) (step.plug driver)
  | .search test => .search (test.plug driver)

theorem eval_plug (template driver : OracleCode) (Z : ℕ →. ℕ) :
    (template.plug driver).eval Z = template.eval (driver.eval Z) := by
  induction template <;> simp [plug, OracleCode.eval, *]

private def consIndex (head tail : ℕ) := Nat.pair (head + 1) tail

private def unaryIndex (tag child : ℕ) := consIndex (Nat.pair 0 tag) (consIndex child 0)

private def binaryIndex (tag first second : ℕ) :=
  consIndex (Nat.pair 0 tag) (consIndex first (consIndex second 0))

private theorem consIndex_primrec : Primrec₂ consIndex :=
  ((Primrec₂.natPair.comp (Primrec.succ.comp Primrec.fst) Primrec.snd) :
    Primrec (fun p : ℕ × ℕ => consIndex p.1 p.2)).to₂

private theorem unaryIndex_primrec (tag : ℕ) : Primrec (unaryIndex tag) :=
  consIndex_primrec.comp (Primrec.const (Nat.pair 0 tag))
    (consIndex_primrec.comp Primrec.id (Primrec.const 0))

private theorem binaryIndex_primrec (tag : ℕ) : Primrec₂ (binaryIndex tag) :=
  (consIndex_primrec.comp (Primrec.const (Nat.pair 0 tag))
    (consIndex_primrec.comp Primrec.fst
      (consIndex_primrec.comp Primrec.snd (Primrec.const 0)))).to₂

/-- Substitute a numeric program index directly into a fixed template.
For valid driver indices this is the index of syntactic substitution. -/
def plugIndex (template : OracleCode) (driverIndex : ℕ) : ℕ :=
  match template with
  | .zero => Encodable.encode OracleCode.zero
  | .succ => Encodable.encode OracleCode.succ
  | .left => Encodable.encode OracleCode.left
  | .right => Encodable.encode OracleCode.right
  | .call => driverIndex
  | .pair first second => binaryIndex 5 (first.plugIndex driverIndex) (second.plugIndex driverIndex)
  | .comp outer inner => binaryIndex 6 (outer.plugIndex driverIndex) (inner.plugIndex driverIndex)
  | .prec base step => binaryIndex 7 (base.plugIndex driverIndex) (step.plugIndex driverIndex)
  | .search test => unaryIndex 8 (test.plugIndex driverIndex)

theorem plugIndex_primrec (template : OracleCode) : Primrec (plugIndex template) := by
  induction template with
  | zero | succ | left | right => exact Primrec.const _
  | call => exact Primrec.id
  | pair _ _ hf hg => exact (binaryIndex_primrec 5).comp hf hg
  | comp _ _ hf hg => exact (binaryIndex_primrec 6).comp hf hg
  | prec _ _ hf hg => exact (binaryIndex_primrec 7).comp hf hg
  | search _ hf => exact (unaryIndex_primrec 8).comp hf

@[simp] theorem plugIndex_encode (template driver : OracleCode) :
    template.plugIndex (Encodable.encode driver) = Encodable.encode (template.plug driver) := by
  induction template with
  | zero | succ | left | right | call => rfl
  | pair f g hf hg | comp f g hf hg | prec f g hf hg =>
    simp only [plugIndex, hf, hg]
    rfl
  | search f hf =>
    simp only [plugIndex, hf]
    rfl

theorem decode_plugIndex_encode (template driver : OracleCode) :
    Encodable.decode (template.plugIndex (Encodable.encode driver)) =
      some (template.plug driver) := by
  simp

end Guo.OracleCode

#print axioms Guo.OracleCode.eval_plug
#print axioms Guo.OracleCode.plugIndex_primrec
#print axioms Guo.OracleCode.plugIndex_encode
