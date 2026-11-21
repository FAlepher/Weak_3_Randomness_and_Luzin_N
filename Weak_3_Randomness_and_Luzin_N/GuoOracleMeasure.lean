import Weak_3_Randomness_and_Luzin_N.GuoOracleCover

open Set MeasureTheory
open scoped ENNReal

namespace Guo

def listCylinder (w : OracleWord) : Set Cantor := wordCylinder (decodeOracleWord w)

def finiteOpen (words : List OracleWord) : Set Cantor := ⋃ w ∈ words.toFinset, listCylinder w

@[simp] theorem mem_finiteOpen (words : List OracleWord) (x : Cantor) :
    x ∈ finiteOpen words ↔ ∃ w ∈ words, x ∈ listCylinder w := by
  simp [finiteOpen]

private def booleanWords : ℕ → List OracleWord
  | 0 => [[]]
  | d + 1 => (booleanWords d).map (false :: ·) ++ (booleanWords d).map (true :: ·)

private theorem booleanWords_primrec : Primrec booleanWords := by
  have prepend (b : Bool) : Primrec (fun ws : List OracleWord => ws.map (b :: ·)) :=
    Primrec.list_map Primrec.id (Primrec.list_cons.comp (Primrec.const b) Primrec.snd)
  exact (Primrec.nat_rec₁ [[]] <| (Primrec.list_append.comp
    ((prepend false).comp Primrec.snd) ((prepend true).comp Primrec.snd)).to₂).of_eq (by
      intro d
      induction d with
      | zero => rfl
      | succ d ih => simp [booleanWords, ← ih])

private theorem mem_booleanWords {w : OracleWord} {d : ℕ} :
    w ∈ booleanWords d ↔ w.length = d := by
  induction d generalizing w with
  | zero => simp [booleanWords]
  | succ d ih =>
    cases w with
    | nil => simp [booleanWords]
    | cons b w => cases b <;> simp [booleanWords, ih]

private theorem booleanWords_nodup (d : ℕ) : (booleanWords d).Nodup := by
  induction d with
  | zero => simp [booleanWords]
  | succ d ih =>
    rw [booleanWords, List.nodup_append']
    refine ⟨ih.map (fun _ _ h => List.cons.inj h |>.2), ih.map (fun _ _ h => List.cons.inj h |>.2), ?_⟩
    intro w hw hv
    simp only [List.mem_map] at hw hv
    obtain ⟨u, _, rfl⟩ := hw
    obtain ⟨v, _, impossible⟩ := hv
    cases impossible

private def unionDepth (words : List OracleWord) : ℕ :=
  words.foldr (fun w d => max w.length d) 0

private theorem length_le_unionDepth {words : List OracleWord} {w : OracleWord} (h : w ∈ words) :
    w.length ≤ unionDepth words := by
  induction words with
  | nil => simp at h
  | cons v vs ih =>
    rw [List.mem_cons] at h
    change w.length ≤ max v.length (unionDepth vs)
    rcases h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

private theorem unionDepth_primrec : Primrec unionDepth :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

private def coveredBy (w : OracleWord) (words : List OracleWord) : Prop :=
  ∃ v ∈ words, oracleWordPrefix v w = true

private instance (w : OracleWord) (words : List OracleWord) : Decidable (coveredBy w words) :=
  inferInstanceAs (Decidable (∃ v ∈ words, oracleWordPrefix v w = true))

private theorem coveredBy_primrec : PrimrecRel coveredBy := by
  change PrimrecRel (fun w words => ∃ v ∈ words, oracleWordPrefix v w = true)
  exact (.swap <| PrimrecRel.exists_mem_list <|
    Primrec.eq.comp oracleWordPrefix_primrec (Primrec.const true))

private def coveredWords (words : List OracleWord) : List OracleWord :=
  (booleanWords (unionDepth words)).filter (coveredBy · words)

private theorem coveredWords_primrec : Primrec coveredWords :=
  coveredBy_primrec.listFilter.comp (booleanWords_primrec.comp unionDepth_primrec) Primrec.id

/-- The numerator and dyadic denominator exponent of a finite union of cylinders. -/
def finiteOpenMassCode (words : List OracleWord) : ℕ × ℕ :=
  ((coveredWords words).length, unionDepth words)

theorem finiteOpenMassCode_primrec : Primrec finiteOpenMassCode :=
  (Primrec.list_length.comp coveredWords_primrec).pair unionDepth_primrec

noncomputable def dyadicMass (code : ℕ × ℕ) : ℝ≥0∞ := (code.1 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹)^code.2

private theorem listCylinder_readBits {x : Cantor} {w : OracleWord} :
    x ∈ listCylinder w ↔
      readBits x w.length = (decodeOracleWord w).2 := Iff.rfl

private theorem listCylinder_prefix (x : Cantor) (v w : OracleWord)
    (h : v.length ≤ w.length) (hw : x ∈ listCylinder w) :
    oracleWordPrefix v w = true ↔ x ∈ listCylinder v := by
  have eq := listCylinder_readBits.mp hw
  rw [← hasWordPrefix_decodeOracleWord, ← eq]
  exact hasWordPrefix_reads (decodeOracleWord v) x h

private theorem finiteOpen_coveredWords (words : List OracleWord) :
    finiteOpen words = finiteOpen (coveredWords words) := by
  ext x
  simp only [mem_finiteOpen]
  constructor
  · rintro ⟨v, hv, hx⟩
    let d := unionDepth words
    let w := encodeOracleWord ⟨d, readBits x d⟩
    have wd : decodeOracleWord w = ⟨d, readBits x d⟩ :=
      decode_encodeOracleWord _
    have wl : w.length = d := congrArg Sigma.fst wd
    have xw : x ∈ listCylinder w := by
      change x ∈ wordCylinder (decodeOracleWord w)
      rw [wd]
      rfl
    refine ⟨w, List.mem_filter.mpr ⟨mem_booleanWords.mpr wl, ?_⟩, xw⟩
    apply decide_eq_true
    exact ⟨v, hv, (listCylinder_prefix x v w (wl ▸ length_le_unionDepth hv) xw).mpr hx⟩
  · rintro ⟨w, hw, hx⟩
    have hmem := List.mem_filter.mp hw
    obtain ⟨v, hv, hPrefix⟩ := of_decide_eq_true hmem.2
    have wl := mem_booleanWords.mp hmem.1
    exact ⟨v, hv, (listCylinder_prefix x v w (wl ▸ length_le_unionDepth hv) hx).mp hPrefix⟩

private theorem disjoint_listCylinder {v w : OracleWord} (h : v.length = w.length) (ne : v ≠ w) :
    Disjoint (listCylinder v) (listCylinder w) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hv : (readBits x v.length).toList = v := by
    simpa [decodeOracleWord, Vector.toList] using congrArg Vector.toList (listCylinder_readBits.mp hx)
  have hw : (readBits x w.length).toList = w := by
    simpa [decodeOracleWord, Vector.toList] using congrArg Vector.toList (listCylinder_readBits.mp hy)
  rw [h] at hv
  exact ne (hv.symm.trans hw)

theorem fairCoin_finiteOpen (words : List OracleWord) :
    fairCoin (finiteOpen words) = dyadicMass (finiteOpenMassCode words) := by
  rw [finiteOpen_coveredWords, finiteOpen, measure_biUnion_finset]
  · have lengths (w) (hw : w ∈ (coveredWords words).toFinset) :
        fairCoin (listCylinder w) = ((2 : ℝ≥0∞)⁻¹)^(unionDepth words) := by
      have hw' := (List.mem_filter.mp (List.mem_toFinset.mp hw)).1
      change fairCoin (cylinderSet (decodeOracleWord w).2) = _
      rw [fairCoin_cylinder]
      exact congrArg ((2 : ℝ≥0∞)⁻¹ ^ ·) (mem_booleanWords.mp hw')
    rw [Finset.sum_congr rfl lengths, Finset.sum_const]
    have nodup : (coveredWords words).Nodup :=
      (booleanWords_nodup (unionDepth words)).filter (fun w => decide (coveredBy w words))
    rw [List.toFinset_card_of_nodup nodup, nsmul_eq_mul]
    rfl
  · intro v hv w hw ne
    have len (u) (hu : u ∈ (coveredWords words).toFinset) : u.length = unionDepth words :=
      mem_booleanWords.mp (List.mem_filter.mp (List.mem_toFinset.mp hu)).1
    exact disjoint_listCylinder ((len v hv).trans (len w hw).symm) ne
  · intro w _
    exact measurable_cylinder (decodeOracleWord w).2

def finiteLayerMassCode (enum : OracleStream) (layer stage : ℕ) : ℕ × ℕ :=
  finiteOpenMassCode ((readOraclePrefix enum layer stage).filterMap id)

attribute [local irreducible] ComputableIn

theorem finiteLayerMassCode_computableIn {O : Set Oracle} {enum : OracleStream}
    (he : ComputableIn O enum) :
    ComputableIn O (fun p : ℕ × ℕ => finiteLayerMassCode enum p.1 p.2) := by
  have filter : Primrec (fun ls : List (Option OracleWord) => ls.filterMap id) :=
    Primrec.listFilterMap Primrec.id Primrec₂.right
  have mass : ComputableIn O (fun ls : List (Option OracleWord) => finiteOpenMassCode (ls.filterMap id)) :=
    (finiteOpenMassCode_primrec.comp filter).computableIn
  unfold finiteLayerMassCode
  exact computableIn_comp (f := fun ls => finiteOpenMassCode (ls.filterMap id))
    (g := fun p : ℕ × ℕ => readOraclePrefix enum p.1 p.2) mass
    (readOraclePrefix_computableIn he)

private theorem mem_finiteOracleLayer (enum : OracleStream) (layer stage : ℕ) (x : Cantor) :
    x ∈ finiteOpen ((readOraclePrefix enum layer stage).filterMap id) ↔
      ∃ tick < stage, ∃ w, enum (layer, tick) = some w ∧ x ∈ listCylinder w := by
  simp only [mem_finiteOpen, readOraclePrefix_eq, List.mem_filterMap, List.mem_map,
    List.mem_range, id_eq]
  constructor
  · rintro ⟨w, ⟨_, ⟨tick, ht, rfl⟩, eq⟩, hx⟩
    exact ⟨tick, ht, w, eq, hx⟩
  · rintro ⟨tick, ht, w, eq, hx⟩
    exact ⟨w, ⟨enum (layer, tick), ⟨tick, ht, rfl⟩, eq⟩, hx⟩

/-- Cylinder enumeration yields a uniform sequence of exact finite dyadic lower measures. -/
theorem oracleLayer_measure_iSup (enum : OracleStream) (layer : ℕ) :
    fairCoin (oracleLayer enum layer) = ⨆ stage, dyadicMass (finiteLayerMassCode enum layer stage) := by
  let part (stage : ℕ) := finiteOpen ((readOraclePrefix enum layer stage).filterMap id)
  have increasing : Monotone part := by
    intro s t h x hx
    obtain ⟨k, hk, w, eq, hmem⟩ := (mem_finiteOracleLayer enum layer s x).mp hx
    exact (mem_finiteOracleLayer enum layer t x).mpr ⟨k, hk.trans_le h, w, eq, hmem⟩
  have union : oracleLayer enum layer = ⋃ stage, part stage := by
    ext x
    rw [mem_oracleLayer, mem_iUnion]
    constructor
    · rintro ⟨k, w, eq, hx⟩
      exact ⟨k + 1, (mem_finiteOracleLayer enum layer _ _).mpr ⟨k, Nat.lt_succ_self _, w, eq, hx⟩⟩
    · rintro ⟨s, hx⟩
      obtain ⟨k, _, w, eq, hw⟩ := (mem_finiteOracleLayer enum layer s x).mp hx
      exact ⟨k, w, eq, hw⟩
  rw [union, increasing.measure_iUnion]
  exact iSup_congr fun _ => fairCoin_finiteOpen _

end Guo

#print axioms Guo.finiteLayerMassCode_computableIn
#print axioms Guo.oracleLayer_measure_iSup
