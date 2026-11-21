import Weak_3_Randomness_and_Luzin_N.GuoCantorTopology

open Set

namespace Guo

abbrev FiniteWord := Σ n : Nat, Bits n

def wordCylinder (w : FiniteWord) : Set Cantor := cylinderSet w.2

def optionCylinder : Option FiniteWord → Set Cantor
  | none => ∅
  | some w => wordCylinder w

/-- All words of a prescribed length, enumerated by appending one bit. -/
def wordsAtDepth : (n : Nat) → List (Bits n)
  | 0 => [#v[]]
  | n + 1 => (wordsAtDepth n).flatMap (fun p => [p.push false, p.push true])

theorem mem_wordsAtDepth (w : Bits n) : w ∈ wordsAtDepth n := by
  induction n with
  | zero =>
    have e : w = #v[] := by
      apply Vector.ext
      intro j hj
      omega
    simp [wordsAtDepth, e]
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨w.pop, ih w.pop, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    have reconstruct := Vector.push_pop_back w
    cases h : w.back
    · rw [h] at reconstruct
      exact Or.inl reconstruct.symm
    · rw [h] at reconstruct
      exact Or.inr reconstruct.symm

def depthBound : List FiniteWord → Nat
  | [] => 0
  | w :: ws => max w.1 (depthBound ws)

theorem le_depthBound {ws : List FiniteWord} {w : FiniteWord} (hw : w ∈ ws) :
    w.1 ≤ depthBound ws := by
  induction ws with
  | nil => exact (List.not_mem_nil hw).elim
  | cons head tail ih =>
    rcases List.mem_cons.mp hw with eq | h
    · subst head
      exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

def hasWordPrefix (p : FiniteWord) (w : Bits n) : Bool :=
  if h : p.1 ≤ n then decide (takePrefix w p.1 h = p.2) else false

theorem hasWordPrefix_reads (p : FiniteWord) (x : Cantor) (h : p.1 ≤ n) :
    hasWordPrefix p (readBits x n) = true ↔ x ∈ wordCylinder p := by
  simp only [hasWordPrefix, dif_pos h, takePrefix_readBits, decide_eq_true_eq]
  rfl

private theorem comparable_intersection (p q : FiniteWord) (compare : p.1 ≤ q.1) :
    optionCylinder (if hasWordPrefix p q.2 then some q else none) =
      wordCylinder p ∩ wordCylinder q := by
  ext x
  have matchWithin (hq : x ∈ wordCylinder q) :
      hasWordPrefix p q.2 = true ↔ x ∈ wordCylinder p := by
    have eq : readBits x q.1 = q.2 := hq
    rw [← eq]
    exact hasWordPrefix_reads p x compare
  by_cases test : hasWordPrefix p q.2 = true
  · simp only [if_pos test, optionCylinder, mem_inter_iff]
    exact ⟨fun hq => ⟨(matchWithin hq).mp test, hq⟩, And.right⟩
  · simp only [if_neg test, optionCylinder, mem_empty_iff_false, mem_inter_iff, false_iff]
    exact fun ⟨hp, hq⟩ => test ((matchWithin hq).mpr hp)

def intersectWords (p q : FiniteWord) : Option FiniteWord :=
  if p.1 ≤ q.1 then
    if hasWordPrefix p q.2 then some q else none
  else
    if hasWordPrefix q p.2 then some p else none

theorem optionCylinder_intersectWords (p q : FiniteWord) :
    optionCylinder (intersectWords p q) = wordCylinder p ∩ wordCylinder q := by
  by_cases h : p.1 ≤ q.1
  · rw [intersectWords, if_pos h]
    exact comparable_intersection p q h
  · rw [intersectWords, if_neg h, inter_comm]
    exact comparable_intersection q p (by omega)

def clipEnumeration (enum : Nat → Option FiniteWord) (p : FiniteWord) (n : Nat) :
    Option FiniteWord := (enum n).bind (intersectWords p)

/-- Refine one cylinder into equal-depth words after removing a finite list of earlier cylinders. -/
def removeEarlierCylinders (ws : List FiniteWord) (p : FiniteWord) : List FiniteWord :=
  let d := depthBound (p :: ws)
  ((wordsAtDepth d).filter (fun w => hasWordPrefix p w && !(ws.any (hasWordPrefix · w)))).map
    (fun w => ⟨d, w⟩)

/-- Correctness of the finite prefix refinement, including arbitrary repeated inputs. -/
theorem mem_removeEarlierCylinders (ws : List FiniteWord) (p : FiniteWord) (x : Cantor) :
    (∃ w ∈ removeEarlierCylinders ws p, x ∈ wordCylinder w) ↔
      x ∈ wordCylinder p ∧ ∀ w ∈ ws, x ∉ wordCylinder w := by
  let d := depthBound (p :: ws)
  have hp : p.1 ≤ d := le_depthBound (List.mem_cons_self ..)
  have hws : ∀ w ∈ ws, w.1 ≤ d := fun w hw => le_depthBound (List.mem_cons_of_mem _ hw)
  simp only [removeEarlierCylinders, List.mem_map, List.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true', List.any_eq_false]
  constructor
  · rintro ⟨_, ⟨w, ⟨_, inside, outside⟩, rfl⟩, hx⟩
    have eq : readBits x d = w := hx
    rw [← eq] at inside outside
    refine ⟨(hasWordPrefix_reads p x hp).mp inside, ?_⟩
    intro q hq cover
    have hfalse := outside q hq
    have htrue := (hasWordPrefix_reads q x (hws q hq)).mpr cover
    exact hfalse htrue
  · rintro ⟨inside, outside⟩
    refine ⟨⟨d, readBits x d⟩, ⟨readBits x d, ⟨mem_wordsAtDepth _, ?_, ?_⟩, rfl⟩, rfl⟩
    · exact (hasWordPrefix_reads p x hp).mpr inside
    · intro q hq
      cases h : hasWordPrefix q (readBits x d)
      · decide
      · exact (outside q hq ((hasWordPrefix_reads q x (hws q hq)).mp h)).elim

def earlierWords (enumerate : Nat → Option FiniteWord) (n : Nat) : List FiniteWord :=
  (List.range n).filterMap enumerate

def refinedEnumeration (enumerate : Nat → Option FiniteWord) (n : Nat) : List FiniteWord :=
  match enumerate n with
  | none => []
  | some p => removeEarlierCylinders (earlierWords enumerate n) p

def listedAt (enumerate : Nat → Option FiniteWord) (n : Nat) (x : Cantor) : Prop :=
  ∃ p, enumerate n = some p ∧ x ∈ wordCylinder p

def emittedAt (enumerate : Nat → Option FiniteWord) (n : Nat) (x : Cantor) : Prop :=
  ∃ p ∈ refinedEnumeration enumerate n, x ∈ wordCylinder p

theorem listedAt_optionCylinder (enum : Nat → Option FiniteWord) (n : Nat) (x : Cantor) :
    listedAt enum n x ↔ x ∈ optionCylinder (enum n) := by
  cases h : enum n <;> simp [listedAt, optionCylinder, h]

theorem listedAt_clipEnumeration (enum : Nat → Option FiniteWord) (p : FiniteWord)
    (n : Nat) (x : Cantor) :
    listedAt (clipEnumeration enum p) n x ↔ x ∈ wordCylinder p ∧ listedAt enum n x := by
  rw [listedAt_optionCylinder, listedAt_optionCylinder]
  cases h : enum n with
  | none => simp [clipEnumeration, h, optionCylinder]
  | some w =>
    rw [clipEnumeration, h]
    change x ∈ optionCylinder (intersectWords p w) ↔ x ∈ wordCylinder p ∧ x ∈ wordCylinder w
    exact (congrArg (fun s : Set Cantor => x ∈ s) (optionCylinder_intersectWords p w)).to_iff

private theorem filterMap_agree {f g : Nat → Option FiniteWord} (ks : List Nat)
    (agree : ∀ k ∈ ks, f k = g k) : ks.filterMap f = ks.filterMap g := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.filterMap_cons]
    rw [agree k List.mem_cons_self, ih (fun j hj => agree j (List.mem_cons_of_mem _ hj))]

theorem refinedEnumeration_finite_queries (enum₀ enum₁ : Nat → Option FiniteWord) (n : Nat)
    (agree : ∀ k ≤ n, enum₀ k = enum₁ k) :
    refinedEnumeration enum₀ n = refinedEnumeration enum₁ n := by
  have past : earlierWords enum₀ n = earlierWords enum₁ n :=
    filterMap_agree (List.range n) (fun k hk => agree k (List.mem_range.mp hk).le)
  simp [refinedEnumeration, agree n le_rfl, past]

theorem emittedAt_iff (enumerate : Nat → Option FiniteWord) (n : Nat) (x : Cantor) :
    emittedAt enumerate n x ↔ listedAt enumerate n x ∧ ∀ j < n, ¬listedAt enumerate j x := by
  cases h : enumerate n with
  | none => simp [emittedAt, refinedEnumeration, listedAt, h]
  | some p =>
    simp only [emittedAt, refinedEnumeration, h, mem_removeEarlierCylinders,
      listedAt, Option.some.injEq, exists_eq_left']
    apply and_congr_right
    intro _
    constructor
    · intro avoids j hj
      rintro ⟨q, listed, inCylinder⟩
      have earlier : q ∈ earlierWords enumerate n :=
        List.mem_filterMap.mpr ⟨j, List.mem_range.mpr hj, listed⟩
      exact avoids q earlier inCylinder
    · intro avoids q hq hIn
      obtain ⟨j, hj, listed⟩ := List.mem_filterMap.mp hq
      exact avoids j (List.mem_range.mp hj) ⟨q, listed, hIn⟩

theorem refinedEnumeration_covers (enumerate : Nat → Option FiniteWord) (x : Cantor) :
    (∃ n, emittedAt enumerate n x) ↔ ∃ n, listedAt enumerate n x := by
  classical
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, ((emittedAt_iff enumerate n x).mp hn).1⟩
  · intro existsAt
    let n := Nat.find existsAt
    exact ⟨n, (emittedAt_iff enumerate n x).mpr ⟨Nat.find_spec existsAt,
      fun _ hj => Nat.find_min existsAt hj⟩⟩

theorem refinedEnumeration_stage_disjoint (enumerate : Nat → Option FiniteWord) :
    Pairwise (fun m n => Disjoint {x | emittedAt enumerate m x} {x | emittedAt enumerate n x}) := by
  intro m n hmn
  refine Set.disjoint_left.mpr (fun x hm hn => ?_)
  have before := (emittedAt_iff enumerate m x).mp hm
  have after := (emittedAt_iff enumerate n x).mp hn
  rcases lt_or_gt_of_ne hmn with lt | gt
  · exact after.2 m lt before.1
  · exact before.2 n gt after.1

theorem refinedEnumeration_same_depth (enumerate : Nat → Option FiniteWord) (n : Nat)
    {p q : FiniteWord} (hp : p ∈ refinedEnumeration enumerate n)
    (hq : q ∈ refinedEnumeration enumerate n) : p.1 = q.1 := by
  cases h : enumerate n with
  | none => simp [refinedEnumeration, h] at hp
  | some w =>
    simp only [refinedEnumeration, h, removeEarlierCylinders, List.mem_map] at hp hq
    obtain ⟨_, _, rfl⟩ := hp
    obtain ⟨_, _, rfl⟩ := hq
    rfl

end Guo

#print axioms Guo.mem_removeEarlierCylinders
#print axioms Guo.refinedEnumeration_covers
#print axioms Guo.refinedEnumeration_stage_disjoint
