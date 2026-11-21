import Std

/-!
# One selected stage of the two-string encoding

The parameters are the old output length `h`, the selected index `i`, and
the exchanged block length `k`, so the old buffer length is `i + k`.
The old code and its width-`i` recovery law are inputs to the construction.
-/

namespace Guo

abbrev Bits (n : Nat) := Vector Bool n

/-- The first `j` bits, with the requested length in the result type. -/
def takePrefix (bits : Bits n) (j : Nat) (hj : j ≤ n) : Bits j :=
  (bits.take j).cast (Nat.min_eq_left hj)

@[simp] theorem getElem_takePrefix (bits : Bits n) (j : Nat) (hj : j ≤ n)
    (r : Nat) (hr : r < j) :
    (takePrefix bits j hj)[r] = bits[r]'(Nat.lt_of_lt_of_le hr hj) := by
  unfold takePrefix
  rw [Vector.getElem_cast, Vector.getElem_take]

def head (bits : Bits (m + n)) : Bits m :=
  takePrefix bits m (by omega)

def tail (bits : Bits (m + n)) : Bits n :=
  (bits.extract m (m + n)).cast (by omega)

@[simp] theorem head_append (a : Bits m) (b : Bits n) : head (a ++ b) = a := by
  unfold head takePrefix
  rw [Vector.take_eq_extract, Vector.extract_append_left, Vector.extract_size]
  simp

@[simp] theorem tail_append (a : Bits m) (b : Bits n) : tail (a ++ b) = b := by
  unfold tail
  rw [Vector.extract_append_right, Vector.extract_size]
  simp

@[simp] theorem append_head_tail (bits : Bits (m + n)) : head bits ++ tail bits = bits := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_append]
  split
  · simp [head]
  · rw [tail, Vector.getElem_cast, Vector.getElem_extract]
    congr 1
    omega

/--
The old stage, with output length `h` and buffer length `i + k`.
Only the instance `j = i` of the old prefix recovery invariant is used.
-/
structure OldCode (h i k : Nat) where
  encode : Bits (h + (i + k)) → Bits h × Bits (i + k)
  decode : Bits h × Bits (i + k) → Bits (h + (i + k))
  decode_encode : ∀ x, decode (encode x) = x
  encode_decode : ∀ state, encode (decode state) = state
  recover : Bits h → Bits i → Bits i
  recover_encode : ∀ x, recover (encode x).1 (head (encode x).2) =
    takePrefix x i (by omega)

theorem OldCode.prefix_decode (old : OldCode h i k) (u : Bits h) (v : Bits (i + k)) :
    takePrefix (old.decode (u, v)) i (by omega) = old.recover u (head v) := by
  have recovered := old.recover_encode (old.decode (u, v))
  rw [old.encode_decode (u, v)] at recovered
  exact recovered.symm

/-- Membership in the cylinder with defining word `σ`, read from an `i`-bit prefix. -/
def hits (σ : Bits l) (hl : l ≤ i) (p : Bits i) : Bool :=
  decide (takePrefix p l hl = σ)

theorem hits_iff (σ : Bits l) (hl : l ≤ i) (x : Bits n) (hi : i ≤ n) :
    hits σ hl (takePrefix x i hi) = true ↔ takePrefix x l (Nat.le_trans hl hi) = σ := by
  have nested : takePrefix (takePrefix x i hi) l hl = takePrefix x l (Nat.le_trans hl hi) := by
    apply Vector.ext
    intro j hj
    simp
  simp [hits, nested]

section Selected

variable (old : OldCode h i k) (σ : Bits l) (hl : l ≤ i)

/-- Equation (3). The branch is computed directly from the old input `x`. -/
def forward (input : Bits (h + (i + k)) × Bits k) : Bits (h + k) × Bits (i + k) :=
  let x := input.1
  let c := input.2
  let (u, v) := old.encode x
  let a := head (m := i) (n := k) v
  let b := tail (m := i) (n := k) v
  if hits σ hl (takePrefix x i (by omega)) then (u ++ b, a ++ c)
  else (u ++ c, a ++ b)

/-- Decode from the two intermediate strings, using the recovered old prefix. -/
def inverse (state : Bits (h + k) × Bits (i + k)) : Bits (h + (i + k)) × Bits k :=
  let u := head (m := h) (n := k) state.1
  let w := tail (m := h) (n := k) state.1
  let a := head (m := i) (n := k) state.2
  let z := tail (m := i) (n := k) state.2
  if hits σ hl (old.recover u a) then (old.decode (u, a ++ w), z)
  else (old.decode (u, a ++ z), w)

/-- Every candidate decoded by the inverse has the prefix used to choose its branch. -/
theorem inverse_prefix (state : Bits (h + k) × Bits (i + k)) :
    takePrefix (inverse old σ hl state).1 i (by omega) =
      old.recover (head state.1) (head state.2) := by
  simp only [inverse]
  split <;> simp [old.prefix_decode]

theorem inverse_hits (state : Bits (h + k) × Bits (i + k)) :
    hits σ hl (takePrefix (inverse old σ hl state).1 i (by omega)) =
      hits σ hl (old.recover (head state.1) (head state.2)) :=
  congrArg (hits σ hl) (inverse_prefix old σ hl state)

theorem inverse_forward : Function.LeftInverse (inverse old σ hl) (forward old σ hl) := by
  intro input
  rcases input with ⟨x, c⟩
  by_cases hit : hits σ hl (takePrefix x i (by omega)) = true
  all_goals
    simp [forward, inverse, old.recover_encode, hit, Prod.eta, old.decode_encode]

theorem forward_inverse : Function.RightInverse (inverse old σ hl) (forward old σ hl) := by
  intro state
  -- Use consistency on an arbitrary candidate, before unfolding the inverse.
  change (if hits σ hl (takePrefix (inverse old σ hl state).1 i (by omega)) then _ else _) = state
  rw [inverse_hits]
  by_cases hit : hits σ hl (old.recover (head state.1) (head state.2)) = true
  all_goals
    simp [inverse, hit, old.encode_decode, Prod.eta]

theorem forward_bijective :
    Function.Injective (forward old σ hl) ∧ Function.Surjective (forward old σ hl) :=
  ⟨(inverse_forward old σ hl).injective, (forward_inverse old σ hl).surjective⟩

/-- The selected stage on the contiguous input `x ++ c` followed by two fresh bits. -/
def stageForward (input : Bits (((h + (i + k)) + k) + 1 + 1)) :
    Bits (h + k + 1) × Bits (i + k + 1) :=
  let bodyWithFirstBit : Bits ((h + (i + k)) + k + 1) := input.pop
  let body := bodyWithFirstBit.pop
  let state := forward old σ hl (head body, tail body)
  (state.1.push bodyWithFirstBit.back, state.2.push input.back)

def stageInverse (state : Bits (h + k + 1) × Bits (i + k + 1)) :
    Bits (((h + (i + k)) + k) + 1 + 1) :=
  let input := inverse old σ hl (state.1.pop, state.2.pop)
  ((input.1 ++ input.2).push state.1.back).push state.2.back

private theorem back_push (bits : Bits n) (bit : Bool) : (bits.push bit).back = bit := by
  simp [Vector.back_eq_getElem]

theorem stage_inverse_forward :
    Function.LeftInverse (stageInverse old σ hl) (stageForward old σ hl) := by
  intro input
  simp only [stageForward, stageInverse, Vector.pop_push, back_push]
  rw [inverse_forward old σ hl]
  rw [append_head_tail]
  exact (congrArg (fun bits : Bits (h + (i + k) + k + 1) => bits.push input.back)
    (Vector.push_pop_back (n := h + (i + k) + k) input.pop)).trans
      (Vector.push_pop_back input)

theorem stage_forward_inverse :
    Function.RightInverse (stageInverse old σ hl) (stageForward old σ hl) := by
  intro state
  simp only [stageForward, stageInverse, Vector.pop_push, back_push, head_append, tail_append,
    Prod.eta]
  rw [forward_inverse old σ hl]
  exact Prod.ext (Vector.push_pop_back state.1) (Vector.push_pop_back state.2)

theorem stage_forward_bijective :
    Function.Injective (stageForward old σ hl) ∧ Function.Surjective (stageForward old σ hl) :=
  ⟨(stage_inverse_forward old σ hl).injective, (stage_forward_inverse old σ hl).surjective⟩

end Selected
end Guo

#print axioms Guo.hits_iff
#print axioms Guo.inverse_prefix
#print axioms Guo.inverse_hits
#print axioms Guo.inverse_forward
#print axioms Guo.forward_inverse
#print axioms Guo.forward_bijective
#print axioms Guo.stage_inverse_forward
#print axioms Guo.stage_forward_inverse
#print axioms Guo.stage_forward_bijective
#print axioms Guo.stageForward
#print axioms Guo.stageInverse
