import Weak_3_Randomness_and_Luzin_N.GuoSelectedStage

namespace Guo

@[simp] theorem takePrefix_takePrefix (x : Bits n) (hi : i ≤ n) (hj : j ≤ i) :
    takePrefix (takePrefix x i hi) j hj = takePrefix x j (Nat.le_trans hj hi) := by
  apply Vector.ext
  intro r hr
  simp

@[simp] theorem takePrefix_append (x : Bits m) (y : Bits n) (hj : j ≤ m) :
    takePrefix (x ++ y) j (by omega) = takePrefix x j hj := by
  apply Vector.ext
  intro r hr
  simp [Vector.getElem_append_left (show r < m by omega)]

@[simp] theorem takePrefix_push (x : Bits n) (b : Bool) (hj : j ≤ n) :
    takePrefix (x.push b) j (by omega) = takePrefix x j hj := by
  apply Vector.ext
  intro r hr
  simp [Vector.getElem_push_lt (show r < n by omega)]

@[simp] theorem takePrefix_full (x : Bits n) : takePrefix x n (Nat.le_refl _) = x := by
  apply Vector.ext
  intro r hr
  simp

/-- Equation (2) and the full prefix recovery invariant at the start of a stage. -/
structure StageCode (h s : Nat) where
  encode : Bits (h + s) → Bits h × Bits s
  decode : Bits h × Bits s → Bits (h + s)
  decode_encode : ∀ x, decode (encode x) = x
  encode_decode : ∀ state, encode (decode state) = state
  recover : (j : Nat) → j ≤ s → Bits h → Bits j → Bits j
  recover_encode : ∀ j hj x, recover j hj (encode x).1 (takePrefix (encode x).2 j hj) =
    takePrefix x j (by omega)

def StageCode.focus (code : StageCode h (i + k)) : OldCode h i k where
  encode := code.encode
  decode := code.decode
  decode_encode := code.decode_encode
  encode_decode := code.encode_decode
  recover := code.recover i (by omega)
  recover_encode := code.recover_encode i (by omega)

section Selected

variable (code : StageCode h (i + k)) (σ : Bits l) (hl : l ≤ i)

private theorem bits_back_push (x : Bits n) (b : Bool) : (x.push b).back = b := by
  rw [Vector.back_eq_getElem]
  exact Vector.getElem_push_eq

private theorem stageForward_blocks (x : Bits (h + (i + k))) (c : Bits k) (p q : Bool) :
    stageForward code.focus σ hl (((x ++ c).push p).push q) =
      ((forward code.focus σ hl (x, c)).1.push p,
       (forward code.focus σ hl (x, c)).2.push q) := by
  simp only [stageForward, Vector.pop_push, head_append, tail_append, bits_back_push]

/-- Recover a prefix at a selected stage using the three cases in Lemma 3.1. -/
def selectedRecover (j : Nat) (hj : j ≤ i + k + 1)
    (out : Bits (h + k + 1)) (saved : Bits j) : Bits j :=
  if hOld : j ≤ i + k then
    let u : Bits h := takePrefix out h (by omega)
    if hShort : j ≤ i then
      code.recover j hOld u saved
    else
      let a := takePrefix saved i (by omega)
      if hits σ hl (code.recover i (by omega) u a) then
        let outBeforeLastBit : Bits (h + k) := out.pop
        let b : Bits k := tail outBeforeLastBit
        code.recover j hOld u (takePrefix (a ++ b) j hOld)
      else
        code.recover j hOld u saved
  else
    let allSaved : Bits (i + k + 1) := saved.cast (by omega)
    takePrefix (stageInverse code.focus σ hl (out, allSaved)) j (by omega)

theorem selected_recover_blocks (j : Nat) (hj : j ≤ i + k + 1)
    (x : Bits (h + (i + k))) (c : Bits k) (p q : Bool) :
    let input := ((x ++ c).push p).push q
    let state := stageForward code.focus σ hl input
    selectedRecover code σ hl j hj state.1 (takePrefix state.2 j hj) =
      takePrefix input j (by omega) := by
  dsimp only
  by_cases hOld : j ≤ i + k
  · rw [stageForward_blocks]
    have hInput : j ≤ h + (i + k) := by omega
    rw [takePrefix_push _ _ (show j ≤ h + (i + k) + k + 1 by omega),
      takePrefix_push _ _ (show j ≤ h + (i + k) + k by omega), takePrefix_append _ _ hInput]
    have outputPrefix (b : Bits k) :
        takePrefix (((code.encode x).1 ++ b).push p) h (by omega) = (code.encode x).1 := by
      rw [takePrefix_push _ _ (show h ≤ h + k by omega), takePrefix_append _ _ (Nat.le_refl h),
        takePrefix_full]
    have storedPrefix (r : Nat) (hr : r ≤ i) (b : Bits k) :
        takePrefix ((head (code.encode x).2 ++ b).push q) r (by omega) =
          takePrefix (code.encode x).2 r (by omega) := by
      rw [takePrefix_push _ _ (show r ≤ i + k by omega), takePrefix_append _ _ hr]
      exact takePrefix_takePrefix _ _ _
    simp only [selectedRecover, dif_pos hOld]
    by_cases hShort : j ≤ i
    · simp only [dif_pos hShort, forward, StageCode.focus]
      split <;>
        simpa only [outputPrefix, storedPrefix j hShort] using code.recover_encode j hOld x
    · simp only [dif_neg hShort, forward, StageCode.focus]
      have retained (b : Bits k) :
          takePrefix (takePrefix ((head (code.encode x).2 ++ b).push q) j hj) i (by omega) =
            takePrefix (code.encode x).2 i (by omega) := by
        rw [takePrefix_takePrefix]
        exact storedPrefix i (Nat.le_refl _) b
      have recovery := code.recover_encode i (show i ≤ i + k by omega) x
      by_cases hHit : hits σ hl (takePrefix x i (by omega)) = true
      · simp only [if_pos hHit, outputPrefix, retained, recovery, Vector.pop_push, tail_append]
        rw [show takePrefix (code.encode x).2 i (by omega) ++ tail (code.encode x).2 =
          (code.encode x).2 from append_head_tail _]
        exact code.recover_encode j hOld x
      · simp only [if_neg hHit, outputPrefix, takePrefix_push _ _ hOld, append_head_tail,
          takePrefix_takePrefix, recovery]
        exact code.recover_encode j hOld x
  · have hjEq : j = i + k + 1 := by omega
    subst j
    simp only [selectedRecover, Nat.not_succ_le_self, dite_false, takePrefix_full, Vector.cast_rfl,
      Prod.eta]
    rw [stage_inverse_forward]

private theorem selected_lengths :
    (h + k + 1) + (i + k + 1) = (h + (i + k)) + k + 1 + 1 := by omega

def StageCode.selected : StageCode (h + k + 1) (i + k + 1) where
  encode x := stageForward code.focus σ hl (x.cast selected_lengths)
  decode state := (stageInverse code.focus σ hl state).cast selected_lengths.symm
  decode_encode x := by
    rw [stage_inverse_forward]
    simp
  encode_decode state := by
    simp only [Vector.cast_cast, Vector.cast_rfl]
    exact stage_forward_inverse code.focus σ hl state
  recover := selectedRecover code σ hl
  recover_encode j hj x := by
    let raw := x.cast (selected_lengths (h := h) (i := i) (k := k))
    let first : Bits (h + (i + k) + k + 1) := raw.pop
    let body : Bits (h + (i + k) + k) := first.pop
    have rebuild : (((head body ++ tail body).push first.back).push raw.back) = raw := by
      rw [append_head_tail]
      exact (congrArg (fun a : Bits (h + (i + k) + k + 1) => a.push raw.back)
        (Vector.push_pop_back first)).trans (Vector.push_pop_back raw)
    have recovered := selected_recover_blocks code σ hl j hj (head body) (tail body) first.back raw.back
    dsimp only at recovered
    rw [rebuild] at recovered
    refine recovered.trans ?_
    apply Vector.ext
    intro r hr
    simp [raw]

theorem StageCode.selected_encode_blocks (x : Bits (h + (i + k))) (c : Bits k) (p q : Bool) :
    (code.selected σ hl).encode ((((x ++ c).push p).push q).cast (by omega)) =
      ((forward code.focus σ hl (x, c)).1.push p,
       (forward code.focus σ hl (x, c)).2.push q) := by
  simp only [StageCode.selected, Vector.cast_cast, Vector.cast_rfl]
  exact stageForward_blocks code σ hl x c p q

end Selected

/-- The identity two-bit code at the start of the first stage. -/
def StageCode.initial : StageCode 1 1 where
  encode x := (head x, tail x)
  decode state := state.1 ++ state.2
  decode_encode x := append_head_tail x
  encode_decode state := Prod.ext (head_append _ _) (tail_append _ _)
  recover j hj u _ := takePrefix u j hj
  recover_encode _ hj x := takePrefix_takePrefix x (by decide) hj

/-- The idle operation is the zero-block case, so only the final bits are read. -/
def StageCode.idle (code : StageCode h s) : StageCode (h + 1) (s + 1) :=
  code.selected (i := s) (k := 0) #v[] (Nat.zero_le s)

theorem StageCode.idle_encode_blocks (code : StageCode h s) (x : Bits (h + s)) (p q : Bool) :
    code.idle.encode (((x.push p).push q).cast (by omega)) =
      ((code.encode x).1.push p, (code.encode x).2.push q) := by
  simp only [StageCode.idle, StageCode.selected, Vector.cast_cast, Vector.cast_rfl]
  have raw : ((x.push p).push q) = (((x ++ (#v[] : Bits 0)).push p).push q) := by
    rw [Vector.append_empty]
  rw [raw, stageForward_blocks]
  have emptyTail (v : Bits s) : tail (m := s) (n := 0) v = #v[] := by
    apply Vector.ext
    intro r hr
    omega
  simp only [forward, StageCode.focus, emptyTail, Vector.append_empty]
  have full (v : Bits s) : head (m := s) (n := 0) v = v := takePrefix_full v
  split <;> rw [full]

inductive StageAction : Nat → Type where
  | idle (s : Nat) : StageAction s
  | selected (i k : Nat) {l : Nat} (σ : Bits l) (hl : l ≤ i) : StageAction (i + k)

def StageAction.nextWidth (a : StageAction s) (h : Nat) : Nat :=
  match a with
  | .idle _ => h + 1
  | .selected _ k _ _ => h + k + 1

def StageAction.run (a : StageAction s) (code : StageCode h s) :
    StageCode (a.nextWidth h) (s + 1) :=
  match a with
  | .idle _ => code.idle
  | .selected _ _ σ hl => code.selected σ hl

/-- Schedule position `t` describes paper stage `t + 1`. -/
abbrev Schedule := (t : Nat) → StageAction (t + 1)

def outputWidth (schedule : Schedule) : Nat → Nat
  | 0 => 1
  | t + 1 => (schedule t).nextWidth (outputWidth schedule t)

def stagedCode (schedule : Schedule) : (t : Nat) → StageCode (outputWidth schedule t) (t + 1)
  | 0 => StageCode.initial
  | t + 1 => (schedule t).run (stagedCode schedule t)

theorem stage_bijective (schedule : Schedule) (t : Nat) :
    Function.Injective (stagedCode schedule t).encode ∧
      Function.Surjective (stagedCode schedule t).encode := by
  let code := stagedCode schedule t
  exact ⟨(show Function.LeftInverse code.decode code.encode from code.decode_encode).injective,
    (show Function.RightInverse code.decode code.encode from code.encode_decode).surjective⟩

theorem stage_recovers_prefix (schedule : Schedule) (t j : Nat) (hj : j ≤ t + 1)
    (x : Bits (outputWidth schedule t + (t + 1))) :
    (stagedCode schedule t).recover j hj ((stagedCode schedule t).encode x).1
      (takePrefix ((stagedCode schedule t).encode x).2 j hj) = takePrefix x j (by omega) :=
  (stagedCode schedule t).recover_encode j hj x

end Guo

#print axioms Guo.stage_bijective
#print axioms Guo.stage_recovers_prefix
