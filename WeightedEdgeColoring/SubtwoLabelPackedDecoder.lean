import WeightedEdgeColoring.SubtwoPackedLabelRows
import WeightedEdgeColoring.FiniteDependentWordPadding

/-!
# Common codes for dependent labelled profile words

At a block source, each color coordinate may have a different finite profile
state type after conditioning on an endpoint label.  The generic encoder
places every labelled coordinate in one common finite code range.  Decoding
recovers both its label and its profile state on every genuine word.
-/

namespace WeightedEdgeColoring.Subtwo

noncomputable section

universe u₁ u₂ u₃

variable {Source : Type u₁} {Color : Type u₂} {Label : Type u₃}
  [Fintype Source] [DecidableEq Source]
  [Fintype Color] [DecidableEq Color]
  (Atom : Source → Color → Type*)
  [∀ src c, Fintype (Atom src c)]
  [∀ src c, DecidableEq (Atom src c)]
  (labelOf : ∀ src c, Atom src c → Label)
  (fallback : ∀ src c, Atom src c)
  (M : ℕ)
  (hcard : ∀ src c, Fintype.card (Atom src c) ≤ M)

/-- A coordinatewise code into the shared alphabet `Fin M`. -/
def labelledAtomCode (src : Source) (c : Color) :
    Atom src c → Fin M :=
  fun z ↦ Fin.castLE (hcard src c) (Fintype.equivFin (Atom src c) z)

theorem labelledAtomCode_injective (src : Source) (c : Color) :
    Function.Injective (labelledAtomCode Atom M hcard src c) := by
  intro z₁ z₂ h
  unfold labelledAtomCode at h
  apply (Fintype.equivFin (Atom src c)).injective
  apply Fin.ext
  simpa using congrArg Fin.val h

/-- Common packed alphabet for one color word. -/
abbrev LabelledPackedWordState (_Atom : Source → Color → Type*) (M : ℕ) :=
  FiniteDependentWordPadding.PackedWordState (Color := Color) M

/-- Encode a genuine source-dependent labelled word. -/
def encodeLabelledPackedWord (src : Source)
    (word : ∀ c : Color, Atom src c) :
    LabelledPackedWordState Atom M :=
  Fintype.equivFin (FiniteDependentWordPadding.WordState
    (Color := Color) M)
    (fun c ↦ labelledAtomCode Atom M hcard src c (word c))

/-- Decode a coordinate of the common packed state, using `fallback` only
for unused padding codes. -/
def decodeLabelledPackedAtom (src : Source)
    (a : LabelledPackedWordState Atom M) (c : Color) : Atom src c :=
  if h : ∃ z : Atom src c,
      labelledAtomCode Atom M hcard src c z =
        ((Fintype.equivFin (FiniteDependentWordPadding.WordState
          (Color := Color) M)).symm a c)
  then Classical.choose h else fallback src c

/-- Extract the selected endpoint label from a packed coordinate. -/
def decodeLabelledPackedLabel (src : Source)
    (a : LabelledPackedWordState Atom M) (c : Color) : Label :=
  labelOf src c
    (decodeLabelledPackedAtom Atom fallback M hcard src a c)

@[simp] theorem decode_encodeLabelledPackedAtom
    (src : Source) (word : ∀ c : Color, Atom src c) (c : Color) :
    decodeLabelledPackedAtom Atom fallback M hcard src
      (encodeLabelledPackedWord Atom M hcard src word) c = word c := by
  classical
  let h : ∃ z : Atom src c,
      labelledAtomCode Atom M hcard src c z =
        labelledAtomCode Atom M hcard src c (word c) := ⟨word c, rfl⟩
  unfold decodeLabelledPackedAtom encodeLabelledPackedWord
  simp only [Equiv.symm_apply_apply]
  rw [dif_pos h]
  exact labelledAtomCode_injective Atom M hcard src c
    (Classical.choose_spec h)

@[simp] theorem decode_encodeLabelledPackedLabel
    (src : Source) (word : ∀ c : Color, Atom src c) (c : Color) :
    decodeLabelledPackedLabel Atom labelOf fallback M hcard src
      (encodeLabelledPackedWord Atom M hcard src word) c =
        labelOf src c (word c) := by
  simp [decodeLabelledPackedLabel]

end

end WeightedEdgeColoring.Subtwo

namespace WeightedEdgeColoring.Subtwo

open scoped BigOperators

/-- A finite label-tagged atom has only the fixed multiplicative cost of
its label alphabet in the common padding range. -/
theorem labelDependentAtom_card_le
    {Label : Type*} [Fintype Label]
    (Payload : Label → Type*) [∀ label, Fintype (Payload label)]
    (N : ℕ) (hcard : ∀ label, Fintype.card (Payload label) ≤ N) :
    Fintype.card (Σ label, Payload label) ≤ Fintype.card Label * N := by
  classical
  calc
    Fintype.card (Σ label, Payload label) =
        ∑ label : Label, Fintype.card (Payload label) := by
      simp
    _ ≤ ∑ _label : Label, N :=
      Finset.sum_le_sum fun label _ ↦ hcard label
    _ = Fintype.card Label * N := by simp

end WeightedEdgeColoring.Subtwo

namespace WeightedEdgeColoring.Subtwo

noncomputable section

variable {Source Vertex State Row Label : Type*}
  [Fintype Source] [DecidableEq Source]
  [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Label] [DecidableEq Label]
  [Fintype Row] [DecidableEq Row]
  {k M : ℕ} (hk : 0 < k)
  (Atom : Source → Fin k → Type*)
  [∀ src c, Fintype (Atom src c)]
  [∀ src c, DecidableEq (Atom src c)]
  (labelOf : ∀ src c, Atom src c → Label)
  (fallback : ∀ src c, Atom src c)
  (hcard : ∀ src c, Fintype.card (Atom src c) ≤ M)

/-- Decoding a selected genuine labelled packed word before measuring its
label row gives exactly the physical number of colors with that label. -/
theorem packedLabel_rowLoad_encoded_eq_count_div
    (baseUse : Source →
      LabelledPackedWordState Atom M → Row → ℝ)
    (vertexOf : Source → Vertex)
    (selected : ∀ src, ∀ c : Fin k, Atom src c)
    (v : Vertex) (label : Label) :
    WeightedEdgeColoring.FiniteCategoricalSelection.rowLoad
      (packedLabelAugmentedUse hk baseUse vertexOf
        (fun src state c ↦
          decodeLabelledPackedLabel Atom labelOf fallback M hcard
            src state c))
      (Sum.inr (v, label))
      (fun src ↦ encodeLabelledPackedWord Atom M hcard src (selected src)) =
      (∑ src : Source,
        if vertexOf src = v then
          ∑ c : Fin k,
            if labelOf src c (selected src c) = label
              then (1 : ℝ) else 0
        else 0) / k := by
  rw [packedLabel_rowLoad_eq_count_div]
  congr 1
  apply Finset.sum_congr rfl
  intro src _
  by_cases hv : vertexOf src = v
  · simp only [hv, ite_true]
    apply Finset.sum_congr rfl
    intro c _
    rw [decode_encodeLabelledPackedLabel]
  · simp [hv]

end

end WeightedEdgeColoring.Subtwo

namespace WeightedEdgeColoring.Subtwo

open scoped BigOperators

noncomputable section

variable {Source Color : Type*}
  [Fintype Source] [DecidableEq Source]
  [Fintype Color] [DecidableEq Color]
  (Atom : Source → Color → Type*)
  [∀ src c, Fintype (Atom src c)]
  [∀ src c, DecidableEq (Atom src c)]
  (fallback : ∀ src c, Atom src c)
  (M : ℕ)
  (hcard : ∀ src c, Fintype.card (Atom src c) ≤ M)

/-- Product probability of one dependent labelled profile word. -/
def labelledWordMass
    (atomProb : ∀ src c, Atom src c → ℝ)
    (src : Source) (word : ∀ c : Color, Atom src c) : ℝ :=
  ∏ c, atomProb src c (word c)

/-- Push the actual dependent product law to the common packed alphabet;
padding-only codes receive zero probability. -/
def paddedLabelledWordProbability
    (atomProb : ∀ src c, Atom src c → ℝ)
    (src : Source) (a : LabelledPackedWordState Atom M) : ℝ :=
  ∑ word : ∀ c : Color, Atom src c,
    if encodeLabelledPackedWord Atom M hcard src word = a then
      labelledWordMass Atom atomProb src word else 0

theorem paddedLabelledWordProbability_nonneg
    (atomProb : ∀ src c, Atom src c → ℝ)
    (hatom0 : ∀ src c z, 0 ≤ atomProb src c z)
    (src : Source) (a : LabelledPackedWordState Atom M) :
    0 ≤ paddedLabelledWordProbability Atom M hcard atomProb src a := by
  unfold paddedLabelledWordProbability
  apply Finset.sum_nonneg
  intro word _
  split
  · exact Finset.prod_nonneg fun c _ ↦ hatom0 src c (word c)
  · exact le_rfl

theorem sum_paddedLabelledWordProbability
    (atomProb : ∀ src c, Atom src c → ℝ)
    (hatomSum : ∀ src c, ∑ z, atomProb src c z = 1)
    (src : Source) :
    (∑ a : LabelledPackedWordState Atom M,
      paddedLabelledWordProbability Atom M hcard atomProb src a) = 1 := by
  classical
  unfold paddedLabelledWordProbability labelledWordMass
  rw [Finset.sum_comm]
  calc
    (∑ word : ∀ c : Color, Atom src c,
      ∑ a, if encodeLabelledPackedWord Atom M hcard src word = a then
        ∏ c, atomProb src c (word c) else 0) =
      ∑ word : ∀ c : Color, Atom src c,
        ∏ c, atomProb src c (word c) := by
      apply Finset.sum_congr rfl
      intro word _
      simp
    _ = ∏ c : Color, ∑ z : Atom src c, atomProb src c z := by
      rw [← Fintype.prod_sum]
    _ = 1 := by simp [hatomSum src]

/-- Positive packed probability guarantees that decoding uses a genuine
labelled profile word rather than a padding fallback. -/
theorem exists_labelledWord_of_paddedProbability_pos
    (atomProb : ∀ src c, Atom src c → ℝ)
    (hatom0 : ∀ src c z, 0 ≤ atomProb src c z)
    (src : Source) (a : LabelledPackedWordState Atom M)
    (ha : 0 < paddedLabelledWordProbability Atom M hcard atomProb src a) :
    ∃ word : ∀ c : Color, Atom src c,
      encodeLabelledPackedWord Atom M hcard src word = a ∧
      0 < labelledWordMass Atom atomProb src word := by
  classical
  unfold paddedLabelledWordProbability at ha
  have hnonneg : ∀ word : ∀ c : Color, Atom src c,
      0 ≤ (if encodeLabelledPackedWord Atom M hcard src word = a then
        labelledWordMass Atom atomProb src word else 0) := by
    intro word
    split
    · exact Finset.prod_nonneg fun c _ ↦ hatom0 src c (word c)
    · exact le_rfl
  rcases (Finset.sum_pos_iff_of_nonneg
      (fun word _ ↦ hnonneg word)).mp ha with
    ⟨word, _hword, hword⟩
  by_cases hcode : encodeLabelledPackedWord Atom M hcard src word = a
  · exact ⟨word, hcode, by simpa [hcode] using hword⟩
  · simp [hcode] at hword

end

end WeightedEdgeColoring.Subtwo

namespace WeightedEdgeColoring.Subtwo

open scoped BigOperators

noncomputable section

variable {Source Color : Type*}
  [Fintype Source] [DecidableEq Source]
  [Fintype Color] [DecidableEq Color]
  (Atom : Source → Color → Type*)
  [∀ src c, Fintype (Atom src c)]
  [∀ src c, DecidableEq (Atom src c)]
  (fallback : ∀ src c, Atom src c)
  (M : ℕ)
  (hcard : ∀ src c, Fintype.card (Atom src c) ≤ M)

/-- Padding and decoding the dependent labelled word preserve every
statistic of the full word, exactly. -/
theorem sum_paddedLabelledWordProbability_mul_decode
    (atomProb : ∀ src c, Atom src c → ℝ)
    (src : Source) (f : (∀ c : Color, Atom src c) → ℝ) :
    (∑ a : LabelledPackedWordState Atom M,
      paddedLabelledWordProbability Atom M hcard atomProb src a *
        f (fun c ↦ decodeLabelledPackedAtom Atom fallback M hcard src a c)) =
      ∑ word : ∀ c : Color, Atom src c,
        labelledWordMass Atom atomProb src word * f word := by
  classical
  unfold paddedLabelledWordProbability
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro word _
  simp [decode_encodeLabelledPackedAtom]

end

end WeightedEdgeColoring.Subtwo

namespace WeightedEdgeColoring.Subtwo

open scoped BigOperators

noncomputable section

variable {Source Color : Type*}
  [Fintype Source] [DecidableEq Source]
  [Fintype Color] [DecidableEq Color]
  (Atom : Source → Color → Type*)
  [∀ src c, Fintype (Atom src c)]
  [∀ src c, DecidableEq (Atom src c)]
  (fallback : ∀ src c, Atom src c)
  (M : ℕ)
  (hcard : ∀ src c, Fintype.card (Atom src c) ≤ M)

/-- A coordinate statistic has its original atom-law expectation under the
independent dependent-word law. -/
theorem sum_labelledWordMass_mul_coordinate
    (atomProb : ∀ src c, Atom src c → ℝ)
    (hatomSum : ∀ src c, ∑ z, atomProb src c z = 1)
    (src : Source) (c : Color) (f : Atom src c → ℝ) :
    (∑ word : ∀ d : Color, Atom src d,
      labelledWordMass Atom atomProb src word * f (word c)) =
      ∑ z : Atom src c, atomProb src c z * f z := by
  classical
  let g : ∀ d : Color, Atom src d → ℝ := fun d z ↦
    atomProb src d z * (if h : d = c then f (h ▸ z) else 1)
  have hpoint : ∀ word : ∀ d : Color, Atom src d,
      labelledWordMass Atom atomProb src word * f (word c) =
        ∏ d, g d (word d) := by
    intro word
    unfold labelledWordMass
    simp only [g, Finset.prod_mul_distrib]
    congr 1
    symm
    calc
      (∏ d : Color, if h : d = c then f (h ▸ word d) else 1) =
          (if h : c = c then f (h ▸ word c) else 1) := by
        apply Finset.prod_eq_single c
        · intro d _ hdc
          simp [hdc]
        · simp
      _ = f (word c) := by simp
  calc
    (∑ word : ∀ d : Color, Atom src d,
      labelledWordMass Atom atomProb src word * f (word c)) =
        ∑ word : ∀ d : Color, Atom src d,
          ∏ d, g d (word d) := by
      apply Finset.sum_congr rfl
      intro word _
      exact hpoint word
    _ = ∏ d : Color, ∑ z : Atom src d, g d z := by
      rw [← Fintype.prod_sum]
    _ = ∑ z : Atom src c, atomProb src c z * f z := by
      rw [Finset.prod_eq_single c]
      · simp [g]
      · intro d _ hdc
        simp [g, hdc, hatomSum src d]
      · simp

/-- The decoded coordinate of a padded labelled-word state has the exact
atom-law mean. -/
theorem sum_paddedLabelledProbability_mul_decode_coordinate
    (atomProb : ∀ src c, Atom src c → ℝ)
    (hatomSum : ∀ src c, ∑ z, atomProb src c z = 1)
    (src : Source) (c : Color) (f : Atom src c → ℝ) :
    (∑ a : LabelledPackedWordState Atom M,
      paddedLabelledWordProbability Atom M hcard atomProb src a *
        f (decodeLabelledPackedAtom Atom fallback M hcard src a c)) =
      ∑ z : Atom src c, atomProb src c z * f z := by
  rw [sum_paddedLabelledWordProbability_mul_decode Atom fallback M hcard
    atomProb src (fun word ↦ f (word c))]
  exact sum_labelledWordMass_mul_coordinate Atom atomProb hatomSum src c f

end

end WeightedEdgeColoring.Subtwo

namespace WeightedEdgeColoring.Subtwo

open scoped BigOperators

noncomputable section

variable {Source Color Label : Type*}
  [Fintype Source] [DecidableEq Source]
  [Fintype Color] [DecidableEq Color]
  [DecidableEq Label]
  (Atom : Source → Color → Type*)
  [∀ src c, Fintype (Atom src c)]
  [∀ src c, DecidableEq (Atom src c)]
  (labelOf : ∀ src c, Atom src c → Label)
  (fallback : ∀ src c, Atom src c)
  (M : ℕ)
  (hcard : ∀ src c, Fintype.card (Atom src c) ≤ M)

/-- Expected label count in a genuine packed product state is the sum of
its one-coordinate label probabilities.  This supplies the exact mean for
appended packed-label selector rows. -/
theorem sum_paddedProbability_mul_labelCount
    (atomProb : ∀ src c, Atom src c → ℝ)
    (hatomSum : ∀ src c, ∑ z, atomProb src c z = 1)
    (src : Source) (label : Label) :
    (∑ a : LabelledPackedWordState Atom M,
      paddedLabelledWordProbability Atom M hcard atomProb src a *
        (∑ c : Color,
          if decodeLabelledPackedLabel Atom labelOf fallback M hcard
              src a c = label then (1 : ℝ) else 0)) =
      ∑ c : Color, ∑ z : Atom src c,
        atomProb src c z *
          (if labelOf src c z = label then (1 : ℝ) else 0) := by
  classical
  calc
    (∑ a : LabelledPackedWordState Atom M,
      paddedLabelledWordProbability Atom M hcard atomProb src a *
        (∑ c : Color,
          if decodeLabelledPackedLabel Atom labelOf fallback M hcard
              src a c = label then (1 : ℝ) else 0)) =
        ∑ c : Color, ∑ a : LabelledPackedWordState Atom M,
          paddedLabelledWordProbability Atom M hcard atomProb src a *
            (if decodeLabelledPackedLabel Atom labelOf fallback M hcard
                src a c = label then (1 : ℝ) else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      exact sum_paddedLabelledProbability_mul_decode_coordinate
        Atom fallback M hcard atomProb hatomSum src c
        (fun z ↦ if labelOf src c z = label then (1 : ℝ) else 0)

end

end WeightedEdgeColoring.Subtwo
