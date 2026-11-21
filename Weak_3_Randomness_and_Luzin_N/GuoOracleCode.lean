import Mathlib.Computability.RecursiveIn

namespace Guo

/-- Programs for Mathlib's partial recursion operators with one oracle instruction. -/
inductive OracleCode where
  | zero
  | succ
  | left
  | right
  | call
  | pair (first second : OracleCode)
  | comp (outer inner : OracleCode)
  | prec (base step : OracleCode)
  | search (test : OracleCode)

namespace OracleCode

private def atomIndex (tag : ℕ) : ℕ := Nat.pair 0 tag

private def indexCons (head tail : ℕ) : ℕ := Nat.pair (head + 1) tail

private def tagged0 (tag : ℕ) : ℕ := indexCons (atomIndex tag) 0
private def tagged1 (tag child : ℕ) : ℕ := indexCons (atomIndex tag) (indexCons child 0)
private def tagged2 (tag first second : ℕ) : ℕ :=
  indexCons (atomIndex tag) (indexCons first (indexCons second 0))

/-- The program index is the paired encoding of a constructor tag followed by its child indices.
This is the same tagged-list convention as Mathlib's derived encoding. -/
def explicitIndex : OracleCode → ℕ
  | .zero => tagged0 0
  | .succ => tagged0 1
  | .left => tagged0 2
  | .right => tagged0 3
  | .call => tagged0 4
  | .pair first second => tagged2 5 first.explicitIndex second.explicitIndex
  | .comp outer inner => tagged2 6 outer.explicitIndex inner.explicitIndex
  | .prec base step => tagged2 7 base.explicitIndex step.explicitIndex
  | .search test => tagged1 8 test.explicitIndex

/-- Parse the top-level tag and child indices. Re-encoding the parsed fields rejects extra data. -/
def indexedShape (n : ℕ) : Option (ℕ × ℕ × ℕ) :=
  let tag := (n.unpair.1 - 1).unpair.2
  let rest := n.unpair.2
  let first := rest.unpair.1 - 1
  let second := rest.unpair.2.unpair.1 - 1
  if tag ≤ 4 then
    if n = tagged0 tag then some (tag, 0, 0) else none
  else if tag ≤ 7 then
    if n = tagged2 tag first second then some (tag, first, second) else none
  else if tag = 8 ∧ n = tagged1 tag first then some (tag, first, 0) else none

theorem indexedShape_primrec : Primrec indexedShape := by
  have head := Primrec.fst.comp Primrec.unpair
  have tail := Primrec.snd.comp Primrec.unpair
  have pred := Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
  have tag := tail.comp (pred.comp head)
  have first := pred.comp (head.comp tail)
  have second := pred.comp (head.comp (tail.comp tail))
  have atom := Primrec₂.natPair.comp (Primrec.const 0) tag
  have cons {f g : ℕ → ℕ} (hf : Primrec f) (hg : Primrec g) :
      Primrec (fun n => indexCons (f n) (g n)) :=
    Primrec₂.natPair.comp (Primrec.succ.comp hf) hg
  have term0 := cons atom (Primrec.const 0)
  have term1 := cons atom (cons first (Primrec.const 0))
  have term2 := cons atom (cons first (cons second (Primrec.const 0)))
  have zPayload := Primrec.option_some.comp (tag.pair ((Primrec.const 0).pair (Primrec.const 0)))
  have uPayload := Primrec.option_some.comp (tag.pair (first.pair (Primrec.const 0)))
  have bPayload := Primrec.option_some.comp (tag.pair (first.pair second))
  exact Primrec.ite (Primrec.nat_le.comp tag (Primrec.const 4))
    (Primrec.ite (Primrec.eq.comp Primrec.id term0) zPayload (Primrec.const none))
    (Primrec.ite (Primrec.nat_le.comp tag (Primrec.const 7))
      (Primrec.ite (Primrec.eq.comp Primrec.id term2) bPayload (Primrec.const none))
      (Primrec.ite ((Primrec.eq.comp tag (Primrec.const 8)).and (Primrec.eq.comp Primrec.id term1))
        uPayload (Primrec.const none)))

private theorem indexedShape_tagged0 (tag : ℕ) (h : tag ≤ 4) :
    indexedShape (tagged0 tag) = some (tag, 0, 0) := by
  simp [indexedShape, tagged0, indexCons, atomIndex, h]

private theorem indexedShape_tagged1 (first : ℕ) :
    indexedShape (tagged1 8 first) = some (8, first, 0) := by
  simp [indexedShape, tagged1, indexCons, atomIndex]

private theorem indexedShape_tagged2 (tag first second : ℕ) (lo : 4 < tag) (hi : tag ≤ 7) :
    indexedShape (tagged2 tag first second) = some (tag, first, second) := by
  simp [indexedShape, tagged2, indexCons, atomIndex, not_le.mpr lo, hi]

private theorem indexCons_left (a b : ℕ) : a < indexCons a b :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.left_le_pair (a + 1) b)

private theorem indexCons_right (a b : ℕ) : b < indexCons a b :=
  (Nat.right_le_pair 0 b).trans_lt (Nat.pair_lt_pair_left b (Nat.succ_pos a))

private theorem tagged1_child (tag a : ℕ) : a < tagged1 tag a :=
  (indexCons_left a 0).trans (indexCons_right _ _)

private theorem tagged2_first (tag a b : ℕ) : a < tagged2 tag a b :=
  (indexCons_left _ _).trans (indexCons_right _ _)

private theorem tagged2_second (tag a b : ℕ) : b < tagged2 tag a b :=
  ((indexCons_left _ _).trans (indexCons_right _ _)).trans (indexCons_right _ _)

def leafAtTag : ℕ → OracleCode
  | 0 => .zero
  | 1 => .succ
  | 2 => .left
  | 3 => .right
  | _ => .call

def binaryAtTag (tag : ℕ) (first second : OracleCode) : OracleCode :=
  if tag = 5 then .pair first second else if tag = 6 then .comp first second else .prec first second

/-- Decode a natural program index. Recursive queries are limited to smaller indices. -/
def decodeIndex (index : ℕ) : Option OracleCode :=
  match indexedShape index with
  | none => none
  | some (tag, first, second) =>
    if tag ≤ 4 then some (leafAtTag tag)
    else if first < index then
      if tag = 8 then (decodeIndex first).map OracleCode.search
      else if second < index then
        (decodeIndex first).bind fun f => (decodeIndex second).map (binaryAtTag tag f)
      else none
    else none
termination_by index

private theorem decodeIndex_leaf {tag : ℕ} (h : tag ≤ 4) :
    decodeIndex (tagged0 tag) = some (leafAtTag tag) := by
  rw [decodeIndex, indexedShape_tagged0 tag h]
  simp only [if_pos h]

private theorem decodeIndex_unary (first : ℕ) :
    decodeIndex (tagged1 8 first) = (decodeIndex first).map OracleCode.search := by
  rw [decodeIndex, indexedShape_tagged1]
  simp [tagged1_child]

private theorem decodeIndex_binary (tag first second : ℕ) (lo : 4 < tag) (hi : tag ≤ 7) :
    decodeIndex (tagged2 tag first second) =
      (decodeIndex first).bind fun f => (decodeIndex second).map (binaryAtTag tag f) := by
  rw [decodeIndex, indexedShape_tagged2 tag first second lo hi]
  have not8 : tag ≠ 8 := by omega
  simp [not_le.mpr lo, tagged2_first, tagged2_second, not8]

@[simp] theorem decodeIndex_explicitIndex (c : OracleCode) : decodeIndex c.explicitIndex = some c := by
  induction c with
  | zero | succ | left | right | call =>
    simp only [explicitIndex]
    rw [decodeIndex_leaf (by decide)]
    rfl
  | pair f g hf hg | comp f g hf hg | prec f g hf hg =>
    simp only [explicitIndex]
    rw [decodeIndex_binary _ _ _ (by decide) (by decide), hf, hg]
    rfl
  | search f hf => rw [explicitIndex, decodeIndex_unary, hf]; rfl

instance : Encodable OracleCode :=
  ⟨explicitIndex, decodeIndex, decodeIndex_explicitIndex⟩

end OracleCode
end Guo

#print axioms Guo.OracleCode.indexedShape_primrec
#print axioms Guo.OracleCode.decodeIndex_explicitIndex
