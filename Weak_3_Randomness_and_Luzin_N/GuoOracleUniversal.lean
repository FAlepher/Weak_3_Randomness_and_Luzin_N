import Weak_3_Randomness_and_Luzin_N.GuoOracleBudget
import Weak_3_Randomness_and_Luzin_N.GuoOracleRates
import Weak_3_Randomness_and_Luzin_N.GuoOracleReplay
import Mathlib.Computability.PartrecCode

open Encodable Denumerable Set

namespace Guo

private abbrev ReplayCode := Nat.Partrec.Code
private abbrev ReplayTick := ℕ × ℕ × ℕ

/-- The first `length` values of a total oracle. -/
private def oracleTablePrefix (values : ℕ → ℕ) (length : ℕ) : List ℕ :=
  length.rec [] (fun n table => table ++ [values n])

private theorem oracleTablePrefix_eq (values : ℕ → ℕ) (length : ℕ) :
    oracleTablePrefix values length = (List.range length).map values := by
  induction length with
  | zero => rfl
  | succ n ih => simp [oracleTablePrefix, List.range_succ, ← ih]

private def replayOutput (p : (ℕ × ReplayCode) × (List ℕ × ℕ)) : Option OracleWord :=
  (Nat.Partrec.Code.evaln p.1.1 p.1.2 (encode p.2)).bind fun v =>
    (decode (α := Option OracleWord) v).getD none

private theorem replayOutput_primrec : Primrec replayOutput := by
  have run : Primrec (fun p : (ℕ × ReplayCode) × (List ℕ × ℕ) =>
      Nat.Partrec.Code.evaln p.1.1 p.1.2 (encode p.2)) :=
    Nat.Partrec.Code.primrec_evaln.comp (Primrec.fst.pair (Primrec.encode.comp Primrec.snd))
  have decodeResult : Primrec (fun v : ℕ => (decode (α := Option OracleWord) v).getD none) :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const none)
  exact Primrec.option_bind run (decodeResult.comp Primrec.snd).to₂

/-- A tick encodes a table length, an ordinary computation budget, and a source tick. -/
def rawReplayFamily (values : ℕ → ℕ) : OracleTestFamily := fun p =>
  let tick := ofNat ReplayTick p.2.2
  replayOutput ((tick.2.1, ofNat ReplayCode p.1),
    oracleTablePrefix values tick.1, encode (p.2.1, tick.2.2))

section Computability

attribute [local irreducible] ComputableIn

private theorem oracleTablePrefix_computableIn {O : Set Oracle} {values : ℕ → ℕ}
    (hv : ComputableIn O values) : ComputableIn O (oracleTablePrefix values) := by
  have next : ComputableIn O (fun p : ℕ × ℕ × List ℕ => values p.2.1) :=
    computableIn_comp hv (Primrec.fst.comp Primrec.snd).computableIn
  have old : ComputableIn O (fun p : ℕ × ℕ × List ℕ => p.2.2) :=
    (Primrec.snd.comp Primrec.snd).computableIn
  have step : ComputableIn O (fun p : ℕ × ℕ × List ℕ => p.2.2 ++ [values p.2.1]) :=
    computableIn_comp Primrec.list_concat.computableIn₂ (computableIn_pair old next)
  have read : ComputableIn O (fun p : ℕ × ℕ => oracleTablePrefix values p.2) :=
    computableIn_nat_rec (step := fun _ t acc => acc ++ [values t])
      (ComputableIn.const []) step
  exact computableIn_comp (f := fun p : ℕ × ℕ => oracleTablePrefix values p.2)
    read ((Primrec.const 0).pair Primrec.id).computableIn

theorem rawReplayFamily_computableIn {O : Set Oracle} {values : ℕ → ℕ}
    (hv : ComputableIn O values) : ComputableIn O (rawReplayFamily values) := by
  let Input := ℕ × ℕ × ℕ
  have tick : Primrec (fun p : Input => ofNat ReplayTick p.2.2) :=
    (Primrec.ofNat _).comp (Primrec.snd.comp Primrec.snd)
  have simulation : Primrec (fun p : Input =>
      ((ofNat ReplayTick p.2.2).2.1, ofNat ReplayCode p.1)) :=
    (Primrec.fst.comp (Primrec.snd.comp tick)).pair ((Primrec.ofNat _).comp Primrec.fst)
  have table : ComputableIn O (fun p : Input => oracleTablePrefix values (ofNat ReplayTick p.2.2).1) :=
    computableIn_comp (oracleTablePrefix_computableIn hv) (Primrec.fst.comp tick).computableIn
  have input : Primrec (fun p : Input => encode (p.2.1, (ofNat ReplayTick p.2.2).2.2)) :=
    Primrec.encode.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp tick)))
  exact computableIn_comp replayOutput_primrec.computableIn
    (computableIn_pair simulation.computableIn (computableIn_pair table input.computableIn))

end Computability

private theorem exists_replayCode {values : ℕ → ℕ} {enum : OracleStream}
    (he : ComputableIn {fun n => Part.some (values n)} enum) :
    ∃ d : ReplayCode, ∀ n tick v,
      v = encode (enum (n, tick)) ↔
        ∃ len, v ∈ d.eval (encode (oracleTablePrefix values len, encode (n, tick))) := by
  unfold ComputableIn RecursiveIn at he
  obtain ⟨c, hc⟩ := OracleCode.exists_eval he
  obtain ⟨d, hd⟩ := c.exists_finiteReplayCode
  refine ⟨d, fun n tick v => ?_⟩
  have atInput : c.eval (fun i => Part.some (values i)) (encode (n, tick)) =
      Part.some (encode (enum (n, tick))) := by simp [hc]
  simp only [hd, oracleTablePrefix_eq, ← c.eval_finiteTable_iff, atInput, Part.mem_some_iff]

/-- Every relative stream occurs exactly as a family of open layers at an ordinary code index. -/
theorem rawReplayFamily_complete {values : ℕ → ℕ} {enum : OracleStream}
    (he : ComputableIn {fun n => Part.some (values n)} enum) :
    ∃ e, ∀ n, familyLayer (rawReplayFamily values) e n = oracleLayer enum n := by
  obtain ⟨d, hd⟩ := exists_replayCode he
  refine ⟨encode d, fun n => ?_⟩
  ext x
  unfold familyLayer
  rw [mem_oracleLayer, mem_oracleLayer]
  constructor
  · rintro ⟨k, w, emitted, hx⟩
    let tick : ReplayTick := ofNat ReplayTick k
    let input := encode (oracleTablePrefix values tick.1, encode (n, tick.2.2))
    have found :
        (Nat.Partrec.Code.evaln tick.2.1 d input).bind
          (fun v => (decode (α := Option OracleWord) v).getD none) = some w := by
      simpa only [rawReplayFamily, replayOutput, ofNat_encode] using emitted
    obtain ⟨v, hv, decodeResult⟩ := Option.bind_eq_some_iff.mp found
    have replayed : v ∈ d.eval input := Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv)
    have good := (hd n tick.2.2 v).mpr ⟨tick.1, replayed⟩
    exact ⟨tick.2.2, w, by simpa only [good, encodek, Option.getD_some] using decodeResult, hx⟩
  · rintro ⟨tick, w, emitted, hx⟩
    obtain ⟨len, found⟩ := (hd n tick (encode (enum (n, tick)))).mp rfl
    obtain ⟨fuel, halted⟩ := Nat.Partrec.Code.evaln_complete.mp found
    refine ⟨encode (len, fuel, tick), w, ?_, hx⟩
    simp only [rawReplayFamily, replayOutput, ofNat_encode, Option.mem_def.mp halted,
      Option.bind_some, encodek, Option.getD_some, emitted]

/-- A complete universal Martin–Löf test exists relative to every total oracle. -/
theorem exists_universalMartinLofTest_of_total (Z : Oracle) (hZ : ∀ n, (Z n).Dom) :
    ∃ U, UniversalMartinLofTest oracleOpenTestFramework Z U := by
  let values (n : ℕ) : ℕ := (Z n).get (hZ n)
  have result (n : ℕ) : values n ∈ Z n := Part.get_mem (hZ n)
  have shape : Z = fun n => Part.some (values n) := funext fun n => Part.eq_some_iff.mpr (result n)
  have oracle : Nat.RecursiveIn {Z} Z := .oracle Z rfl
  have valueComputable : ComputableIn {Z} values :=
    RecursiveIn.iff_nat.mpr (oracle.of_eq_tot result)
  refine ⟨oracleLayer (diagonalTestStream (budgetTestFamily (rawReplayFamily values))), ?_⟩
  refine universalTest_of_raw_enumerated_family _ _ (rawReplayFamily_computableIn valueComputable) ?_
  intro U test
  obtain ⟨enum, effective, layers⟩ := test.1
  have compiled : ComputableIn {fun n => Part.some (values n)} enum := shape ▸ effective
  obtain ⟨e, he⟩ := rawReplayFamily_complete compiled
  exact ⟨e, fun n => (he n).trans (layers n)⟩

/-- The universal test used in the paper's reflection argument. -/
theorem exists_universalMartinLofTest_secondJump :
    ∃ U, UniversalMartinLofTest oracleOpenTestFramework secondJump U :=
  exists_universalMartinLofTest_of_total secondJump (fun _ => trivial)

end Guo

#print axioms Guo.rawReplayFamily_complete
#print axioms Guo.exists_universalMartinLofTest_of_total
#print axioms Guo.exists_universalMartinLofTest_secondJump
