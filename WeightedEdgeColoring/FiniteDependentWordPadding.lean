import WeightedEdgeColoring.FiniteBernoulliChernoff

/-!
# Padding dependent finite words into one common state type

At source `i`, an atom may live in a source-dependent finite type `Atom i`.
If every atom type injects into `Fin M`, then a whole `Color`-indexed word
injects coordinatewise into the common finite type `Color → Fin M`, and
hence into one `Fin` type.  The product law on dependent words can therefore
be padded by zero to a categorical law with a source-independent state type.
-/

namespace WeightedEdgeColoring.FiniteDependentWordPadding

open scoped BigOperators

noncomputable section

universe u₁ u₂ u₃

variable {Source : Type u₁} {Color : Type u₂}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype Color] [DecidableEq Color]
variable (Atom : Source → Type u₃)
variable [∀ i, Fintype (Atom i)] [∀ i, DecidableEq (Atom i)]

/-- A common finite padding of a source-dependent family. -/
structure Encoding (M : ℕ) where
  code : ∀ i, Atom i → Fin M
  code_injective : ∀ i, Function.Injective (code i)

/-- The common coordinatewise state type for a full word. -/
abbrev WordState (M : ℕ) := Color → Fin M

/-- The same common word state written as one `Fin` type. -/
abbrev PackedWordState (M : ℕ) := Fin (Fintype.card (WordState (Color := Color) M))

/-- Coordinatewise encoding of a source-dependent word. -/
def encodeWord {M : ℕ} (E : Encoding Atom M) (i : Source)
    (word : Color → Atom i) : WordState (Color := Color) M :=
  fun c ↦ E.code i (word c)

theorem encodeWord_injective {M : ℕ} (E : Encoding Atom M) (i : Source) :
    Function.Injective (encodeWord Atom (Color := Color) E i) := by
  intro left right h
  funext c
  exact E.code_injective i (congrFun h c)

/-- Encode a full dependent word in one common `Fin` type. -/
def encodePackedWord {M : ℕ} (E : Encoding Atom M) (i : Source)
    (word : Color → Atom i) : PackedWordState (Color := Color) M :=
  Fintype.equivFin (WordState (Color := Color) M)
    (encodeWord Atom (Color := Color) E i word)

theorem encodePackedWord_injective {M : ℕ}
    (E : Encoding Atom M) (i : Source) :
    Function.Injective (encodePackedWord Atom (Color := Color) E i) := by
  intro left right h
  apply encodeWord_injective Atom (Color := Color) E i
  exact (Fintype.equivFin (WordState (Color := Color) M)).injective h

/-- Decode a coordinate code, using a supplied fallback only for padding
codes outside the image. -/
def decodeAtom {M : ℕ} (E : Encoding Atom M)
    (fallback : ∀ i, Atom i) (i : Source) (a : Fin M) : Atom i :=
  if h : ∃ z, E.code i z = a then Classical.choose h else fallback i

@[simp] theorem decodeAtom_code {M : ℕ} (E : Encoding Atom M)
    (fallback : ∀ i, Atom i) (i : Source) (z : Atom i) :
    decodeAtom Atom E fallback i (E.code i z) = z := by
  let h : ∃ x, E.code i x = E.code i z := ⟨z, rfl⟩
  unfold decodeAtom
  rw [dif_pos h]
  exact E.code_injective i (Classical.choose_spec h)

/-- Total decoder from the common packed state.  Padding coordinates are
sent to the supplied fallback atom. -/
def decodePackedWord {M : ℕ} (E : Encoding Atom M)
    (fallback : ∀ i, Atom i) (i : Source)
    (a : PackedWordState (Color := Color) M) : Color → Atom i :=
  fun c ↦ decodeAtom Atom E fallback i
    ((Fintype.equivFin (WordState (Color := Color) M)).symm a c)

@[simp] theorem decodePackedWord_encode {M : ℕ}
    (E : Encoding Atom M) (fallback : ∀ i, Atom i)
    (i : Source) (word : Color → Atom i) :
    decodePackedWord Atom (Color := Color) E fallback i
        (encodePackedWord Atom (Color := Color) E i word) = word := by
  funext c
  simp [decodePackedWord, encodePackedWord, encodeWord]

/-- The common packed state has the expected product cardinality. -/
theorem packedWordState_card {M : ℕ} :
    Fintype.card (PackedWordState (Color := Color) M) =
      M ^ Fintype.card Color := by
  simp [PackedWordState, WordState]

/-- Product mass of one source-dependent word. -/
def wordMass (atomProb : ∀ i, Atom i → ℝ)
    (i : Source) (word : Color → Atom i) : ℝ :=
  ∏ c, atomProb i (word c)

/-- Push a dependent word law into the common packed state type, assigning
zero mass to padding-only codes. -/
def paddedWordProbability {M : ℕ} (E : Encoding Atom M)
    (atomProb : ∀ i, Atom i → ℝ)
    (i : Source) (a : PackedWordState (Color := Color) M) : ℝ :=
  ∑ word : Color → Atom i,
    if encodePackedWord Atom (Color := Color) E i word = a then
      wordMass Atom atomProb i word else 0

theorem paddedWordProbability_nonneg {M : ℕ} (E : Encoding Atom M)
    (atomProb : ∀ i, Atom i → ℝ)
    (hatom0 : ∀ i z, 0 ≤ atomProb i z)
    (i : Source) (a : PackedWordState (Color := Color) M) :
    0 ≤ paddedWordProbability Atom E atomProb i a := by
  apply Finset.sum_nonneg
  intro word _hword
  split
  · exact Finset.prod_nonneg fun c _hc ↦ hatom0 i (word c)
  · exact le_rfl

/-- Padding preserves normalization of the product word law. -/
theorem sum_paddedWordProbability {M : ℕ} (E : Encoding Atom M)
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) :
    (∑ a : PackedWordState (Color := Color) M,
      paddedWordProbability Atom E atomProb i a) = 1 := by
  classical
  unfold paddedWordProbability wordMass
  rw [Finset.sum_comm]
  calc
    (∑ word : Color → Atom i,
        ∑ a, if encodePackedWord Atom (Color := Color) E i word = a then
          ∏ c, atomProb i (word c) else 0) =
        ∑ word : Color → Atom i, ∏ c, atomProb i (word c) := by
      apply Finset.sum_congr rfl
      intro word _hword
      simp
    _ = ∏ _c : Color, ∑ z : Atom i, atomProb i z := by
      rw [← Fintype.prod_sum]
    _ = 1 := by simp [hatomSum i]

/-- Integration against the padded law is exactly integration against the
original dependent word law.  The fallback never contributes because
padding-only codes have mass zero. -/
theorem sum_paddedWordProbability_mul_decode {M : ℕ}
    (E : Encoding Atom M) (fallback : ∀ i, Atom i)
    (atomProb : ∀ i, Atom i → ℝ) (i : Source)
    (f : (Color → Atom i) → ℝ) :
    (∑ a : PackedWordState (Color := Color) M,
      paddedWordProbability Atom E atomProb i a *
        f (decodePackedWord Atom (Color := Color) E fallback i a)) =
      ∑ word : Color → Atom i,
        wordMass Atom atomProb i word * f word := by
  classical
  unfold paddedWordProbability
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro word _hword
  simp [decodePackedWord_encode]

/-- Positive padded mass decodes to an actual source-dependent word of
positive product mass. -/
theorem exists_word_of_paddedWordProbability_pos {M : ℕ}
    (E : Encoding Atom M)
    (atomProb : ∀ i, Atom i → ℝ)
    (hatom0 : ∀ i z, 0 ≤ atomProb i z)
    (i : Source) (a : PackedWordState (Color := Color) M)
    (ha : 0 < paddedWordProbability Atom E atomProb i a) :
    ∃ word : Color → Atom i,
      encodePackedWord Atom (Color := Color) E i word = a ∧
        0 < wordMass Atom atomProb i word := by
  classical
  unfold paddedWordProbability at ha
  have hnonneg : ∀ word : Color → Atom i,
      0 ≤ (if encodePackedWord Atom (Color := Color) E i word = a then
        wordMass Atom atomProb i word else 0) := by
    intro word
    split
    · exact Finset.prod_nonneg fun c _hc ↦ hatom0 i (word c)
    · exact le_rfl
  rcases (Finset.sum_pos_iff_of_nonneg
      (fun word _hword ↦ hnonneg word)).mp ha with
    ⟨word, _hword, hword⟩
  by_cases hcode : encodePackedWord Atom (Color := Color) E i word = a
  · exact ⟨word, hcode, by simpa [wordMass, hcode] using hword⟩
  · simp [hcode] at hword

end

end WeightedEdgeColoring.FiniteDependentWordPadding
