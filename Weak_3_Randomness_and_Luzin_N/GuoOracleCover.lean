import Weak_3_Randomness_and_Luzin_N.GuoEnumeratedCover
import Weak_3_Randomness_and_Luzin_N.GuoReflection
import Weak_3_Randomness_and_Luzin_N.GuoLocalization
import Mathlib.Computability.RecursiveIn

open Encodable Set MeasureTheory
open scoped ENNReal

namespace Guo

section RecursiveOperations

variable {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
variable {O : Set (ℕ →. ℕ)}

theorem recursiveIn_comp {f : β →. γ} {g : α →. β}
    (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    RecursiveIn O (fun a => (g a).bind f) := by
  unfold RecursiveIn at hf hg ⊢
  refine (hf.comp hg).of_eq fun n => ?_
  cases decode (α := α) n <;> simp [Part.bind_eq_bind, Part.map_bind, Part.bind_map]

theorem computableIn_comp {f : β → γ} {g : α → β}
    (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (f ∘ g) := by
  simpa [ComputableIn, Function.comp_def] using recursiveIn_comp hf hg

theorem computableIn_pair {f : α → β} {g : α → γ}
    (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (fun a => (f a, g a)) := by
  unfold ComputableIn RecursiveIn at hf hg ⊢
  refine (hf.pair hg).of_eq fun n => ?_
  cases decode (α := α) n <;> simp [Seq.seq]

theorem computableIn_nat_rec {base : α → β} {step : α → ℕ → β → β}
    (hb : ComputableIn O base)
    (hs : ComputableIn O (fun p : α × ℕ × β => step p.1 p.2.1 p.2.2)) :
    ComputableIn O (fun p : α × ℕ =>
      Nat.rec (motive := fun _ => β) (base p.1) (step p.1) p.2) := by
  unfold ComputableIn RecursiveIn at hb hs ⊢
  refine (hb.prec hs).of_eq fun n => ?_
  simp only [decode_prod_val, decode_nat, Option.map_some, Part.map_some]
  cases hd : decode (α := α) n.unpair.1 with
  | none =>
    induction n.unpair.2 with
    | zero => simp [hd]
    | succ _ ih =>
      simp [hd] at ih
      simp [hd, ih]
  | some a =>
    induction n.unpair.2 with
    | zero => simp [hd]
    | succ _ ih =>
      simp [hd] at ih
      simp [hd, ih]

end RecursiveOperations

abbrev Oracle := ℕ →. ℕ
abbrev OracleWord := List Bool
abbrev OracleStream := ℕ × ℕ → Option OracleWord

def decodeOracleWord (w : OracleWord) : FiniteWord :=
  ⟨w.length, ⟨w.toArray, by simp⟩⟩

def oracleLayer (enum : OracleStream) (layer : ℕ) : Set Cantor :=
  enumeratedOpen (fun tick => (enum (layer, tick)).map decodeOracleWord)

/-- Uniformly oracle-enumerated open layers. A `none` entry is a completed tick with no output. -/
def OracleUniformOpen (Z : Oracle) (U : ℕ → Set Cantor) : Prop :=
  ∃ enum : OracleStream, ComputableIn {Z} enum ∧ ∀ n, oracleLayer enum n = U n

theorem mem_oracleLayer (enum : OracleStream) (layer : ℕ) (x : Cantor) :
    x ∈ oracleLayer enum layer ↔
      ∃ tick w, enum (layer, tick) = some w ∧ x ∈ wordCylinder (decodeOracleWord w) := by
  change (∃ tick w, (enum (layer, tick)).map decodeOracleWord = some w ∧ x ∈ wordCylinder w) ↔ _
  constructor
  · rintro ⟨tick, v, hv, hx⟩
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hv
    exact ⟨tick, w, hw, hx⟩
  · rintro ⟨tick, w, hw, hx⟩
    exact ⟨tick, decodeOracleWord w, by simp [hw], hx⟩

theorem oracleLayer_eq_iUnion (enum : OracleStream) (n : ℕ) :
    oracleLayer enum n = ⋃ tick, optionCylinder ((enum (n, tick)).map decodeOracleWord) := by
  ext x
  simp [oracleLayer, enumeratedOpen, listedAt_optionCylinder]

theorem oracleLayer_isOpen (enum : OracleStream) (n : ℕ) : IsOpen (oracleLayer enum n) := by
  rw [oracleLayer_eq_iUnion]
  apply isOpen_iUnion
  intro tick
  cases h : enum (n, tick) with
  | none => simp [optionCylinder]
  | some w => simpa [h, optionCylinder, wordCylinder] using cylinder_isOpen (decodeOracleWord w).2

def oracleWordPrefix (w v : OracleWord) : Bool :=
  decide (v.take w.length = w)

theorem oracleWordPrefix_primrec : Primrec₂ oracleWordPrefix := by
  apply primrecRel_iff_primrec_decide.mp
  exact Primrec.eq.comp
    (Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd)
    Primrec.fst

@[simp] theorem hasWordPrefix_decodeOracleWord (w v : OracleWord) :
    hasWordPrefix (decodeOracleWord w) (decodeOracleWord v).2 = oracleWordPrefix w v := by
  by_cases h : w.length ≤ v.length
  · simp only [hasWordPrefix, decodeOracleWord, dif_pos h, oracleWordPrefix]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [← Vector.toList_inj]
    simp [takePrefix]
  · have ne : v.take w.length ≠ w := by
      intro eq
      have bound := congrArg List.length eq
      simp only [List.length_take] at bound
      omega
    simp [hasWordPrefix, decodeOracleWord, oracleWordPrefix, h, ne]

def intersectOracleWords (w v : OracleWord) : Option OracleWord :=
  if w.length ≤ v.length then
    bif oracleWordPrefix w v then some v else none
  else
    bif oracleWordPrefix v w then some w else none

theorem intersectOracleWords_primrec : Primrec₂ intersectOracleWords := by
  exact (Primrec.ite
    (Primrec.nat_le.comp (Primrec.list_length.comp Primrec.fst)
      (Primrec.list_length.comp Primrec.snd))
    (Primrec.cond oracleWordPrefix_primrec (Primrec.option_some.comp Primrec.snd)
      (Primrec.const none))
    (Primrec.cond (oracleWordPrefix_primrec.comp Primrec.snd Primrec.fst)
      (Primrec.option_some.comp Primrec.fst) (Primrec.const none))).to₂

@[simp] theorem intersectOracleWords_decode (w v : OracleWord) :
    (intersectOracleWords w v).map decodeOracleWord =
      intersectWords (decodeOracleWord w) (decodeOracleWord v) := by
  unfold intersectOracleWords intersectWords
  rw [hasWordPrefix_decodeOracleWord, hasWordPrefix_decodeOracleWord]
  change (if w.length ≤ v.length then (bif oracleWordPrefix w v then some v else none)
    else (bif oracleWordPrefix v w then some w else none)).map decodeOracleWord =
      (if w.length ≤ v.length then (if oracleWordPrefix w v then some (decodeOracleWord v) else none)
      else (if oracleWordPrefix v w then some (decodeOracleWord w) else none))
  by_cases h : w.length ≤ v.length
  · cases oracleWordPrefix w v <;> simp [h]
  · cases oracleWordPrefix v w <;> simp [h]

def intersectOracleOptions (w v : Option OracleWord) : Option OracleWord :=
  w.bind fun a => v.bind (intersectOracleWords a)

theorem intersectOracleOptions_primrec : Primrec₂ intersectOracleOptions :=
  (Primrec.option_bind Primrec.fst
    (Primrec.option_bind (Primrec.snd.comp Primrec.fst)
      (intersectOracleWords_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂).to₂

theorem optionCylinder_intersectOracleOptions (w v : Option OracleWord) :
    optionCylinder ((intersectOracleOptions w v).map decodeOracleWord) =
      optionCylinder (w.map decodeOracleWord) ∩ optionCylinder (v.map decodeOracleWord) := by
  cases w <;> cases v <;>
    simp only [intersectOracleOptions, Option.bind_none, Option.bind_some,
      Option.map_none, Option.map_some, intersectOracleWords_decode]
  · simp [optionCylinder]
  · simp [optionCylinder]
  · simp [optionCylinder]
  · exact optionCylinder_intersectWords _ _

def intersectInitialStep (enum : OracleStream) (j : ℕ) (state : ℕ × Option OracleWord) :
    ℕ × Option OracleWord :=
  (state.1.unpair.2, intersectOracleOptions state.2 (enum (j, state.1.unpair.1)))

def intersectInitialState (enum : OracleStream) (tick count : ℕ) : ℕ × Option OracleWord :=
  Nat.rec (tick, some []) (intersectInitialStep enum) count

def initialOracleStream (enum : OracleStream) : OracleStream :=
  fun p => (intersectInitialState enum p.2 (p.1 + 1)).2

attribute [local irreducible] ComputableIn

set_option maxHeartbeats 800000 in
theorem initialOracleStream_computableIn {O : Set Oracle} {enum : OracleStream}
    (he : ComputableIn O enum) : ComputableIn O (initialOracleStream enum) := by
  let State := ℕ × Option OracleWord
  have base : ComputableIn O (fun tick : ℕ => (tick, some ([] : OracleWord))) :=
    computableIn_pair ComputableIn.id (ComputableIn.const _)
  have splitTick : ComputableIn O
      (fun p : ℕ × ℕ × State => Nat.unpair p.2.2.1) :=
    (Primrec.unpair.comp <| Primrec.fst.comp <| Primrec.snd.comp Primrec.snd).computableIn
  have layer : ComputableIn O (fun p : ℕ × ℕ × State => p.2.1) :=
    (Primrec.fst.comp Primrec.snd).computableIn
  have tick : ComputableIn O (fun p : ℕ × ℕ × State => (Nat.unpair p.2.2.1).1) :=
    computableIn_comp ComputableIn.fst splitTick
  have address : ComputableIn O
      (fun p : ℕ × ℕ × State => (p.2.1, (Nat.unpair p.2.2.1).1)) :=
    computableIn_pair layer tick
  have getInput : ComputableIn O
      (fun p : ℕ × ℕ × State => enum (p.2.1, (Nat.unpair p.2.2.1).1)) :=
    computableIn_comp he address
  have rest : ComputableIn O (fun p : ℕ × ℕ × State => (Nat.unpair p.2.2.1).2) :=
    computableIn_comp ComputableIn.snd splitTick
  have prior : ComputableIn O (fun p : ℕ × ℕ × State => p.2.2.2) :=
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).computableIn
  have next : ComputableIn O (fun p : ℕ × ℕ × State =>
      intersectOracleOptions p.2.2.2 (enum (p.2.1, (Nat.unpair p.2.2.1).1))) :=
    computableIn_comp intersectOracleOptions_primrec.computableIn (computableIn_pair prior getInput)
  have step : ComputableIn O (fun p : ℕ × ℕ × State => intersectInitialStep enum p.2.1 p.2.2) := by
    exact computableIn_pair rest next
  have state : ComputableIn O (fun p : ℕ × ℕ => intersectInitialState enum p.1 p.2) :=
    computableIn_nat_rec (step := fun _ => intersectInitialStep enum) base step
  have input : ComputableIn O (fun p : ℕ × ℕ => (p.2, p.1 + 1)) :=
    (Primrec.snd.pair (Primrec.succ.comp Primrec.fst)).computableIn
  have computed : ComputableIn O (fun p : ℕ × ℕ => intersectInitialState enum p.2 (p.1 + 1)) :=
    computableIn_comp state input
  exact computableIn_comp
    (ComputableIn.snd : ComputableIn O (@Prod.snd ℕ (Option OracleWord))) computed

private theorem wordCylinder_empty (x : Cantor) :
    x ∈ wordCylinder (decodeOracleWord []) := by
  change readBits x 0 = (decodeOracleWord []).2
  apply Vector.ext
  intro n hn
  omega

private theorem intersectInitialState_mem (enum : OracleStream) (x : Cantor) (count tick : ℕ)
    (hx : x ∈ optionCylinder ((intersectInitialState enum tick count).2.map decodeOracleWord)) :
    ∀ j < count, x ∈ oracleLayer enum j := by
  induction count with
  | zero => omega
  | succ count ih =>
    let state := intersectInitialState enum tick count
    change x ∈ optionCylinder
      ((intersectOracleOptions state.2 (enum (count, state.1.unpair.1))).map decodeOracleWord) at hx
    rw [optionCylinder_intersectOracleOptions] at hx
    intro j hj
    by_cases hj' : j = count
    · subst j
      exact ⟨state.1.unpair.1, (listedAt_optionCylinder _ _ _).mpr hx.2⟩
    · exact ih hx.1 j (by omega)

private theorem exists_intersectInitialState (enum : OracleStream) (x : Cantor) (count : ℕ)
    (hx : ∀ j < count, x ∈ oracleLayer enum j) (rest : ℕ) :
    ∃ tick, (intersectInitialState enum tick count).1 = rest ∧
      x ∈ optionCylinder ((intersectInitialState enum tick count).2.map decodeOracleWord) := by
  induction count generalizing rest with
  | zero => exact ⟨rest, rfl, wordCylinder_empty x⟩
  | succ count ih =>
    obtain ⟨lastTick, w, hw, hmem⟩ :=
      (mem_oracleLayer enum count x).mp (hx count (Nat.lt_succ_self _))
    obtain ⟨tick, htick, hold⟩ :=
      ih (fun j hj => hx j (Nat.lt_trans hj (Nat.lt_succ_self _))) (Nat.pair lastTick rest)
    refine ⟨tick, ?_, ?_⟩
    · show (intersectInitialState enum tick count).1.unpair.2 = rest
      simp [htick]
    · change x ∈ optionCylinder ((intersectOracleOptions (intersectInitialState enum tick count).2
        (enum (count, (intersectInitialState enum tick count).1.unpair.1))).map decodeOracleWord)
      rw [optionCylinder_intersectOracleOptions, htick, Nat.unpair_pair, hw]
      exact ⟨hold, hmem⟩

theorem oracleLayer_initialOracleStream (enum : OracleStream) (n : ℕ) :
    oracleLayer (initialOracleStream enum) n = initialIntersections (oracleLayer enum) n := by
  ext x
  rw [oracleLayer_eq_iUnion]
  simp only [mem_iUnion, initialIntersections, mem_iInter, initialOracleStream]
  constructor
  · rintro ⟨tick, htick⟩ j hj
    exact intersectInitialState_mem enum x (n+1) tick htick j (Nat.lt_succ_of_le hj)
  · intro h
    obtain ⟨tick, _, htick⟩ := exists_intersectInitialState enum x (n+1)
      (fun j hj => h j (Nat.le_of_lt_succ hj)) 0
    exact ⟨tick, htick⟩

theorem oracleUniformOpen_shift {Z : Oracle} {U : ℕ → Set Cantor}
    (hu : OracleUniformOpen Z U) (d : ℕ) :
    OracleUniformOpen Z (fun n => U (n + d)) := by
  obtain ⟨enum, h, layers⟩ := hu
  refine ⟨fun p => enum (p.1 + d, p.2), ?_, fun n => layers (n+d)⟩
  exact computableIn_comp h
    ((Primrec.nat_add.comp Primrec.fst (Primrec.const d)).pair Primrec.snd).computableIn

def oracleOpenTestFramework : OpenTestFramework Oracle where
  Uniform := OracleUniformOpen
  openLayers := by
    rintro Z U ⟨enum, _, h⟩ n
    rw [← h n]
    exact oracleLayer_isOpen enum n
  measurableLayers := by
    rintro Z U ⟨enum, _, h⟩ n
    rw [← h n]
    exact (oracleLayer_isOpen enum n).measurableSet
  initialInter := by
    rintro Z U ⟨enum, h, layers⟩
    refine ⟨initialOracleStream enum, initialOracleStream_computableIn h, fun n => ?_⟩
    rw [oracleLayer_initialOracleStream, funext layers]
  shift := oracleUniformOpen_shift

theorem oracleUniformOpen_reindex {O : Set Oracle} {enum : OracleStream} {selectLayer : ℕ → ℕ}
    (he : ComputableIn O enum) (hs : ComputableIn O selectLayer) :
    ComputableIn O (fun p : ℕ × ℕ => enum (selectLayer p.1, p.2)) :=
  computableIn_comp he
    (computableIn_pair (computableIn_comp hs ComputableIn.fst) ComputableIn.snd)

def encodeOracleWord (w : FiniteWord) : OracleWord := w.2.toList

@[simp] theorem decode_encodeOracleWord (w : FiniteWord) :
    decodeOracleWord (encodeOracleWord w) = w := by
  rcases w with ⟨n, bits⟩
  cases bits with
  | mk arr eq =>
    subst n
    simp [decodeOracleWord, encodeOracleWord, Vector.toList]

@[simp] theorem encode_decodeOracleWord (w : OracleWord) :
    encodeOracleWord (decodeOracleWord w) = w := by
  simp [decodeOracleWord, encodeOracleWord, Vector.toList]

def readOraclePrefix (enum : OracleStream) (layer count : ℕ) : List (Option OracleWord) :=
  Nat.rec [] (fun tick seen => seen ++ [enum (layer, tick)]) count

theorem readOraclePrefix_eq (enum : OracleStream) (layer count : ℕ) :
    readOraclePrefix enum layer count = (List.range count).map (fun k => enum (layer, k)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp [readOraclePrefix, List.range_succ, ← ih]

theorem readOraclePrefix_getElem? (enum : OracleStream) (layer count tick : ℕ)
    (ht : tick < count) :
    (readOraclePrefix enum layer count)[tick]? = some (enum (layer, tick)) := by
  rw [readOraclePrefix_eq, List.getElem?_map, List.getElem?_range]
  · rfl
  · exact ht

theorem readOraclePrefix_computableIn {O : Set Oracle} {enum : OracleStream}
    (he : ComputableIn O enum) :
    ComputableIn O (fun p : ℕ × ℕ => readOraclePrefix enum p.1 p.2) := by
  let State := List (Option OracleWord)
  let step (layer tick : ℕ) (seen : State) := seen ++ [enum (layer, tick)]
  have address : ComputableIn O (fun p : ℕ × ℕ × State => (p.1, p.2.1)) :=
    (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).computableIn
  have next : ComputableIn O (fun p : ℕ × ℕ × State => enum (p.1, p.2.1)) :=
    computableIn_comp he address
  have previous : ComputableIn O (fun p : ℕ × ℕ × State => p.2.2) :=
    (Primrec.snd.comp Primrec.snd).computableIn
  have args : ComputableIn O (fun p : ℕ × ℕ × State => (p.2.2, enum (p.1, p.2.1))) :=
    computableIn_pair previous next
  have stepComputable : ComputableIn O (fun p : ℕ × ℕ × State => step p.1 p.2.1 p.2.2) :=
    computableIn_comp Primrec.list_concat.computableIn₂ args
  exact computableIn_nat_rec (step := step) (ComputableIn.const ([] : State)) stepComputable

/-- The ordinary computation that remains once the finitely many oracle queries are supplied. -/
def oracleCoverKernel (schedule : Schedule) (i : ℕ) (σ : OracleWord)
    (p : ℕ × List (Option OracleWord)) : Option OracleWord :=
  let enum (k : ℕ) := (p.2[k]?.getD none).map decodeOracleWord
  (coverEnumeration schedule i (clipEnumeration enum (decodeOracleWord σ)) p.1).map encodeOracleWord

def coverInputCount (tick : ℕ) : ℕ := tick.unpair.1.unpair.1 + 1

theorem coverInputCount_primrec : Primrec coverInputCount :=
  Primrec.succ.comp ((Primrec.fst.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair))

def oracleCoverStream (schedule : Schedule) (i : ℕ) (σ : OracleWord) (enum : OracleStream) :
    OracleStream := fun p =>
  oracleCoverKernel schedule i σ (p.2, readOraclePrefix enum p.1 (coverInputCount p.2))

/-- The compiler queries only the input layer and runs the ordinary finite kernel on the replies. -/
theorem oracleCoverStream_computableIn {O : Set Oracle} (schedule : Schedule) (i : ℕ) (σ : OracleWord)
    {enum : OracleStream} (he : ComputableIn O enum) (hk : Computable (oracleCoverKernel schedule i σ)) :
    ComputableIn O (oracleCoverStream schedule i σ enum) := by
  have indices : ComputableIn O (fun p : ℕ × ℕ => (p.1, coverInputCount p.2)) :=
    (Primrec.fst.pair (coverInputCount_primrec.comp Primrec.snd)).computableIn
  have prefixComp : ComputableIn O (fun p : ℕ × ℕ => readOraclePrefix enum p.1 (coverInputCount p.2)) :=
    computableIn_comp (readOraclePrefix_computableIn he) indices
  have args : ComputableIn O (fun p : ℕ × ℕ => (p.2, readOraclePrefix enum p.1 (coverInputCount p.2))) :=
    computableIn_pair ComputableIn.snd prefixComp
  unfold oracleCoverStream
  exact computableIn_comp hk.computableIn args

theorem oracleCoverStream_eq (schedule : Schedule) (i : ℕ) (σ : OracleWord) (enum : OracleStream)
    (layer tick : ℕ) :
    (oracleCoverStream schedule i σ enum (layer, tick)).map decodeOracleWord =
      coverEnumeration schedule i
        (clipEnumeration (fun k => (enum (layer, k)).map decodeOracleWord) (decodeOracleWord σ)) tick := by
  unfold oracleCoverStream oracleCoverKernel
  have maps (o : Option FiniteWord) :
      (o.map encodeOracleWord).map decodeOracleWord = o := by cases o <;> simp
  rw [maps]
  dsimp only [coverEnumeration]
  congr 1
  apply coverBatch_finite_queries
  intro k hk
  dsimp only [clipEnumeration, coverInputCount]
  rw [readOraclePrefix_getElem? enum layer _ k (Nat.lt_succ_of_le hk)]
  rfl

theorem oracleLayer_oracleCoverStream (schedule : Schedule) (i : ℕ) (σ : OracleWord)
    (enum : OracleStream) (layer : ℕ) :
    oracleLayer (oracleCoverStream schedule i σ enum) layer =
      enumeratedOpen (coverEnumeration schedule i
        (clipEnumeration (fun k => (enum (layer, k)).map decodeOracleWord) (decodeOracleWord σ))) := by
  unfold oracleLayer
  congr 1
  funext tick
  exact oracleCoverStream_eq schedule i σ enum layer tick

theorem oracleUniform_local_cover (schedule : Schedule) (i : ℕ) (σ : OracleWord)
    (recurs : InfinitelySelected schedule i) (uses : UsesCylinder schedule i (decodeOracleWord σ).2)
    (hk : Computable (oracleCoverKernel schedule i σ)) {Z : Oracle} {U : ℕ → Set Cantor}
    (hu : OracleUniformOpen Z U) :
    ∃ V, OracleUniformOpen Z V ∧ ∀ n,
      cantorOutput schedule '' (U n ∩ wordCylinder (decodeOracleWord σ)) ⊆ V n ∧
        fairCoin (V n) ≤ (2 : ℝ≥0∞)^i * fairCoin (U n ∩ wordCylinder (decodeOracleWord σ)) := by
  obtain ⟨enum, he, layers⟩ := hu
  refine ⟨oracleLayer (oracleCoverStream schedule i σ enum),
    ⟨_, oracleCoverStream_computableIn schedule i σ he hk, fun _ => rfl⟩, fun n => ?_⟩
  rw [oracleLayer_oracleCoverStream, ← layers n]
  exact (enumerated_local_cover_stream schedule i _ recurs uses
    (fun k => (enum (n, k)).map decodeOracleWord)).2

/-- The bound from each recurrent cylinder gives the reflection framework's local operation. -/
theorem effectiveLocalCover_from_candidate_kernels (C : CandidateWords) (A : Set Cantor)
    (form : Aᶜ = {x : Cantor | ∃ i, cylinder (C.word i) x ∧ ∀ n, ∃ b, C.witness i n b = true})
    (kernels : ∀ i, InfinitelySelected (candidateSchedule pairedReservation C) i →
      Computable (oracleCoverKernel (candidateSchedule pairedReservation C) i
        (encodeOracleWord ⟨C.width i, C.word i⟩))) :
    EffectiveLocalCover oracleOpenTestFramework (cantorOutput (candidateSchedule pairedReservation C)) A := by
  intro x hx
  have outside : x ∈ Aᶜ := hx
  rw [form, candidate_coverage pairedReservation C] at outside
  obtain ⟨i, inCylinder⟩ := mem_iUnion.mp outside
  let σ := encodeOracleWord ⟨C.width i.val, C.word i.val⟩
  have word : decodeOracleWord σ = ⟨C.width i.val, C.word i.val⟩ := decode_encodeOracleWord _
  have uses : UsesCylinder (candidateSchedule pairedReservation C) i.val (decodeOracleWord σ).2 := by
    rw [word]
    intro t chosen y
    exact candidateSchedule_hitsAt pairedReservation C t i.val chosen y
  refine ⟨wordCylinder (decodeOracleWord σ), i.val, ?_, ?_⟩
  · rw [word]
    exact inCylinder
  · intro Z U hU
    exact oracleUniform_local_cover _ i.val σ i.property uses (kernels i.val i.property) hU

#print axioms initialOracleStream_computableIn
#print axioms oracleUniform_local_cover
#print axioms effectiveLocalCover_from_candidate_kernels

end Guo
