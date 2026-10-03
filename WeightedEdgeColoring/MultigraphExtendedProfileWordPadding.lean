import WeightedEdgeColoring.FiniteDependentWordPadding
import WeightedEdgeColoring.MultigraphSelectedProfileConditionedGlobal

/-!
# A common finite state space for extended profile words

The extended-profile state type depends on the vertex because the concrete
profile menu does.  We first inject every vertex's state type into one common
`Fin (profileStateBound + 3)`: the profile menu needs at most
`profileStateBound` codes and there are three special states.  Applying the
generic dependent-word padding then encodes an entire color word at one
vertex in the same finite type at every vertex.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)

/-- The common number of codes needed for one extended profile state. -/
def extendedProfileStateBound (β q r : ℝ) : ℕ :=
  profileStateBound β q r + 3

theorem extendedProfileState_card_le (v : G.V) :
    Fintype.card (G.ExtendedProfileState R0 v) ≤
      extendedProfileStateBound β q r := by
  have hmenu : Fintype.card {P // P ∈
      G.roundedProfileMenu (R0 v).law hβ hr} ≤
      Fintype.card (G.RoundedProfileIndex (R0 v).law hβ hr) := by
    simp [RoundedProfileIndex]
  have hprofile : Fintype.card {P // P ∈
      G.roundedProfileMenu (R0 v).law hβ hr} ≤
      profileStateBound β q r :=
    hmenu.trans
      (G.roundedProfileIndex_card_le_parameters (R0 v).law hβ hr)
  simpa [ExtendedProfileState, extendedProfileStateBound] using
    Nat.add_le_add_right hprofile 3

/-- A source-dependent extended state encoded in the common one-state
padding range. -/
def extendedProfileStateCode (v : G.V) :
    G.ExtendedProfileState R0 v →
      Fin (extendedProfileStateBound β q r) :=
  fun z ↦ Fin.castLE (G.extendedProfileState_card_le R0 v)
    (Fintype.equivFin (G.ExtendedProfileState R0 v) z)

theorem extendedProfileStateCode_injective (v : G.V) :
    Function.Injective (G.extendedProfileStateCode R0 v) := by
  intro left right h
  unfold extendedProfileStateCode at h
  apply (Fintype.equivFin (G.ExtendedProfileState R0 v)).injective
  apply Fin.ext
  have hv :
      (Fin.castLE (G.extendedProfileState_card_le R0 v)
        (Fintype.equivFin (G.ExtendedProfileState R0 v) left)).val =
      (Fin.castLE (G.extendedProfileState_card_le R0 v)
        (Fintype.equivFin (G.ExtendedProfileState R0 v) right)).val :=
    congrArg (fun z : Fin (extendedProfileStateBound β q r) ↦ z.val) h
  exact hv

/-- The common atom encoding supplied to dependent-word padding. -/
def extendedProfileStateEncoding :
    FiniteDependentWordPadding.Encoding
      (fun v ↦ G.ExtendedProfileState R0 v)
      (extendedProfileStateBound β q r) where
  code := G.extendedProfileStateCode R0
  code_injective := G.extendedProfileStateCode_injective R0

/-- One source-independent state type encoding a full `Fin n`-indexed
extended-profile word at a vertex. -/
abbrev ExtendedProfilePackedWordState (n : ℕ) (β q r : ℝ) :=
  FiniteDependentWordPadding.PackedWordState
    (Color := Fin n) (extendedProfileStateBound β q r)

/-- The inactive extended state is the canonical decoder fallback. -/
def inactiveExtendedProfileState (v : G.V) :
    G.ExtendedProfileState R0 v :=
  Sum.inr ⟨2, by decide⟩

/-- Decode a common packed state to a full word at a specified vertex.
Codes outside the image use the inactive state. -/
def decodeExtendedProfileWord (v : G.V)
    (a : ExtendedProfilePackedWordState n β q r) :
    Fin n → G.ExtendedProfileState R0 v :=
  FiniteDependentWordPadding.decodePackedWord
    (fun v ↦ G.ExtendedProfileState R0 v) (Color := Fin n)
    (G.extendedProfileStateEncoding R0)
    (G.inactiveExtendedProfileState R0) v a

@[simp] theorem decode_encodeExtendedProfileWord (v : G.V)
    (word : Fin n → G.ExtendedProfileState R0 v) :
    G.decodeExtendedProfileWord R0 v
        (FiniteDependentWordPadding.encodePackedWord
          (fun v ↦ G.ExtendedProfileState R0 v) (Color := Fin n)
          (G.extendedProfileStateEncoding R0) v word) = word := by
  exact FiniteDependentWordPadding.decodePackedWord_encode
    (fun v ↦ G.ExtendedProfileState R0 v) (Color := Fin n)
    (G.extendedProfileStateEncoding R0)
    (G.inactiveExtendedProfileState R0) v word

/-- Product probability of one concrete extended-profile word. -/
def extendedProfileWordMass (omega : ℝ) (v : G.V)
    (word : Fin n → G.ExtendedProfileState R0 v) : ℝ :=
  ∏ c, G.smoothedExtendedProfileProbability R0 omega v (word c)

/-- The extended-profile word law padded into the common state type. -/
def paddedExtendedProfileWordProbability (omega : ℝ) (v : G.V)
    (a : ExtendedProfilePackedWordState n β q r) : ℝ :=
  FiniteDependentWordPadding.paddedWordProbability
    (fun v ↦ G.ExtendedProfileState R0 v)
    (G.extendedProfileStateEncoding R0)
    (fun v z ↦ G.smoothedExtendedProfileProbability R0 omega v z) v a

theorem sum_paddedExtendedProfileWordProbability (omega : ℝ) (v : G.V) :
    ∑ a, G.paddedExtendedProfileWordProbability R0 omega v a = 1 := by
  exact FiniteDependentWordPadding.sum_paddedWordProbability
    (fun v ↦ G.ExtendedProfileState R0 v)
    (G.extendedProfileStateEncoding R0)
    (fun v z ↦ G.smoothedExtendedProfileProbability R0 omega v z)
    (G.sum_smoothedExtendedProfileProbability R0 omega) v

theorem paddedExtendedProfileWordProbability_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V) (a : ExtendedProfilePackedWordState n β q r) :
    0 ≤ G.paddedExtendedProfileWordProbability R0 omega v a := by
  apply FiniteDependentWordPadding.paddedWordProbability_nonneg
    (fun v ↦ G.ExtendedProfileState R0 v)
    (G.extendedProfileStateEncoding R0)
    (fun v z ↦ G.smoothedExtendedProfileProbability R0 omega v z)
  intro x z
  exact (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
    homega0 homega1 x z).le

/-- Positive padded mass gives a genuine full extended-profile word. -/
theorem exists_extendedProfileWord_of_padded_pos
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V) (a : ExtendedProfilePackedWordState n β q r)
    (ha : 0 < G.paddedExtendedProfileWordProbability R0 omega v a) :
    ∃ word : Fin n → G.ExtendedProfileState R0 v,
      FiniteDependentWordPadding.encodePackedWord
          (fun v ↦ G.ExtendedProfileState R0 v) (Color := Fin n)
          (G.extendedProfileStateEncoding R0) v word = a ∧
        0 < G.extendedProfileWordMass R0 omega v word := by
  simpa [extendedProfileWordMass] using
    (FiniteDependentWordPadding.exists_word_of_paddedWordProbability_pos
      (fun v ↦ G.ExtendedProfileState R0 v)
      (G.extendedProfileStateEncoding R0)
      (fun v z ↦ G.smoothedExtendedProfileProbability R0 omega v z)
      (fun x z ↦ (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0
        hleft homega0 homega1 x z).le) v a ha)

end WeightedMultigraph

end

end WeightedEdgeColoring
