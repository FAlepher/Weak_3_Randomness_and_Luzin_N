import Weak_3_Randomness_and_Luzin_N.GuoFiniteStages

namespace Guo

abbrev Cantor := Nat → Bool

/-- The finite word read from an infinite input. -/
def readBits (x : Cantor) (n : Nat) : Bits n :=
  Vector.ofFn (fun j => x j.val)

@[simp] theorem getElem_readBits (x : Cantor) (hr : r < n) :
    (readBits x n)[r] = x r := by simp [readBits]

@[simp] theorem takePrefix_readBits (x : Cantor) (hj : j ≤ n) :
    takePrefix (readBits x n) j hj = readBits x j := by
  apply Vector.ext
  intro r hr
  simp

@[simp] theorem cast_readBits (x : Cantor) (eq : m = n) :
    (readBits x m).cast eq = readBits x n := by
  subst n
  rfl

theorem readBits_succ (x : Cantor) (n : Nat) :
    readBits x (n + 1) = (readBits x n).push (x n) := by
  apply Vector.ext
  intro r hr
  by_cases h : r < n
  · simp [Vector.getElem_push_lt h]
  · have : r = n := by omega
    subst r
    simp

theorem readBits_add (x : Cantor) (m n : Nat) :
    readBits x (m + n) = readBits x m ++ readBits (fun r => x (m + r)) n := by
  apply Vector.ext
  intro r hr
  by_cases h : r < m
  · simp [Vector.getElem_append_left h]
  · rw [Vector.getElem_append_right hr (by omega)]
    simp only [getElem_readBits]
    congr 1
    omega

def StageCode.read (code : StageCode h s) (x : Cantor) : Bits h × Bits s :=
  code.encode (readBits x (h + s))

theorem StageCode.read_idle (code : StageCode h s) (x : Cantor) :
    code.idle.read x =
      ((code.read x).1.push (x (h + s)), (code.read x).2.push (x (h + s + 1))) := by
  unfold StageCode.read
  have input := StageCode.idle_encode_blocks code (readBits x (h + s)) (x (h + s)) (x (h + s + 1))
  rwa [← readBits_succ, ← readBits_succ, cast_readBits] at input

theorem StageCode.read_selected (code : StageCode h (i + k)) (σ : Bits l) (hl : l ≤ i)
    (x : Cantor) :
    let n := h + (i + k)
    let state := forward code.focus σ hl (readBits x n, readBits (fun r => x (n + r)) k)
    (code.selected σ hl).read x =
      (state.1.push (x (n + k)), state.2.push (x (n + k + 1))) := by
  dsimp only [StageCode.read]
  have input := StageCode.selected_encode_blocks code σ hl (readBits x (h + (i + k)))
    (readBits (fun r => x (h + (i + k) + r)) k) (x (h + (i + k) + k)) (x (h + (i + k) + k + 1))
  rwa [← readBits_add, ← readBits_succ, ← readBits_succ, cast_readBits] at input

def cylinder (p : Bits n) (x : Cantor) : Prop := readBits x n = p

theorem hits_stream_iff (σ : Bits l) (hl : l ≤ i) (x : Cantor) (hi : i ≤ n) :
    hits σ hl (takePrefix (readBits x n) i hi) = true ↔ cylinder σ x := by
  rw [hits_iff, takePrefix_readBits]
  rfl

theorem StageAction.le_nextWidth (a : StageAction s) (h : Nat) :
    h + 1 ≤ a.nextWidth h := by
  cases a <;> simp only [StageAction.nextWidth] <;> omega

theorem StageAction.read_output_prefix (a : StageAction s) (code : StageCode h s) (x : Cantor) :
    takePrefix ((a.run code).read x).1 h (by have := a.le_nextWidth h; omega) = (code.read x).1 := by
  cases a with
  | idle s =>
    simp only [StageAction.run, StageAction.nextWidth]
    rw [code.read_idle]
    exact (takePrefix_push _ _ (Nat.le_refl h)).trans (takePrefix_full _)
  | selected i k σ hl =>
    simp only [StageAction.run, StageAction.nextWidth]
    rw [code.read_selected σ hl]
    simp only [forward, StageCode.focus]
    split <;>
      rw [takePrefix_push _ _ (show h ≤ h + k by omega),
        takePrefix_append _ _ (Nat.le_refl h), takePrefix_full] <;> rfl

/-- A transition may change a stored prefix only when it hits below its width. -/
def StageAction.hitsBelow (a : StageAction s) (j : Nat) (x : Cantor) : Prop :=
  match a with
  | .idle _ => False
  | .selected i _ σ _ => i < j ∧ cylinder σ x

theorem StageAction.read_stored_prefix (a : StageAction s) (code : StageCode h s)
    (x : Cantor) (hj : j ≤ s) (safe : ¬a.hitsBelow j x) :
    takePrefix ((a.run code).read x).2 j (by omega) = takePrefix (code.read x).2 j hj := by
  cases a with
  | idle s =>
    simp only [StageAction.run, StageAction.nextWidth]
    rw [code.read_idle]
    exact takePrefix_push _ _ hj
  | selected i k σ hl =>
    simp only [StageAction.run, StageAction.nextWidth]
    rw [code.read_selected σ hl]
    simp only [forward, StageCode.focus]
    split
    · rename_i hit
      have hitCylinder := (hits_stream_iff σ hl x (show i ≤ h + (i + k) by omega)).mp hit
      have hShort : j ≤ i := by
        by_cases h : j ≤ i
        · exact h
        · exact (safe ⟨by omega, hitCylinder⟩).elim
      rw [takePrefix_push _ _ hj, takePrefix_append _ _ hShort]
      exact takePrefix_takePrefix _ _ _
    · rw [takePrefix_push _ _ hj, append_head_tail]
      rfl

theorem outputWidth_succ (schedule : Schedule) (t : Nat) :
    outputWidth schedule t + 1 ≤ outputWidth schedule (t + 1) :=
  (schedule t).le_nextWidth _

theorem outputWidth_ge (schedule : Schedule) (t : Nat) : t + 1 ≤ outputWidth schedule t := by
  induction t with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    have step := outputWidth_succ schedule t
    omega

theorem outputWidth_monotone (schedule : Schedule) (hab : a ≤ b) :
    outputWidth schedule a ≤ outputWidth schedule b := by
  induction b with
  | zero =>
    obtain rfl : a = 0 := by omega
    exact Nat.le_refl _
  | succ b ih =>
    by_cases hb : a ≤ b
    · have step := outputWidth_succ schedule b
      have previous := ih hb
      omega
    · obtain rfl : a = b + 1 := by omega
      exact Nat.le_refl _

def stageRead (schedule : Schedule) (t : Nat) (x : Cantor) :
    Bits (outputWidth schedule t) × Bits (t + 1) :=
  (stagedCode schedule t).read x

theorem stageRead_output_prefix (schedule : Schedule) (x : Cantor) (hab : a ≤ b) :
    takePrefix (stageRead schedule b x).1 (outputWidth schedule a)
      (outputWidth_monotone schedule hab) = (stageRead schedule a x).1 := by
  induction b with
  | zero =>
    obtain rfl : a = 0 := by omega
    exact takePrefix_full _
  | succ b ih =>
    by_cases hb : a ≤ b
    · have step : takePrefix (stageRead schedule (b + 1) x).1 (outputWidth schedule b)
          (outputWidth_monotone schedule (Nat.le_succ b)) = (stageRead schedule b x).1 :=
        (schedule b).read_output_prefix (stagedCode schedule b) x
      calc
        _ = takePrefix (takePrefix (stageRead schedule (b + 1) x).1 (outputWidth schedule b)
            (outputWidth_monotone schedule (Nat.le_succ b))) (outputWidth schedule a)
            (outputWidth_monotone schedule hb) := (takePrefix_takePrefix _ _ _).symm
        _ = _ := by rw [step]; exact ih hb
    · obtain rfl : a = b + 1 := by omega
      exact takePrefix_full _

/-- The permanent output bit at position `r` is present by paper stage `r+1`. -/
def cantorOutput (schedule : Schedule) (x : Cantor) (r : Nat) : Bool :=
  (stageRead schedule r x).1[r]'(by have := outputWidth_ge schedule r; omega)

theorem cantorOutput_reads (schedule : Schedule) (t : Nat) (x : Cantor) :
    readBits (cantorOutput schedule x) (outputWidth schedule t) = (stageRead schedule t x).1 := by
  apply Vector.ext
  intro r hr
  rw [getElem_readBits]
  unfold cantorOutput
  by_cases hrt : r ≤ t
  · simpa only [getElem_takePrefix] using (congrArg (fun v : Bits (outputWidth schedule r) =>
      v[r]'(by have := outputWidth_ge schedule r; omega))
      (stageRead_output_prefix schedule x hrt)).symm
  · have htr : t ≤ r := by omega
    simpa only [getElem_takePrefix] using congrArg (fun v : Bits (outputWidth schedule t) => v[r]'hr)
      (stageRead_output_prefix schedule x htr)

end Guo

#print axioms Guo.cantorOutput_reads
#print axioms Guo.StageAction.read_stored_prefix
#print axioms Guo.cantorOutput
