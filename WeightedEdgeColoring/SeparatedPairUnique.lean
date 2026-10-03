import WeightedEdgeColoring.SeparatedOptionSystems
import WeightedEdgeColoring.PairUniqueOptions

namespace WeightedEdgeColoring

/-! Pair uniqueness is preserved when option families use disjoint slot types. -/

universe u v₁ v₂ w₁ w₂

namespace RankThreeOptionSystem

variable {Job : Type u} {Slot₁ : Type v₁} {Slot₂ : Type v₂}
  {Option₁ : Type w₁} {Option₂ : Type w₂}
  [Fintype Job] [Fintype Slot₁] [Fintype Slot₂]
  [Fintype Option₁] [Fintype Option₂]
  [DecidableEq Job] [DecidableEq Slot₁] [DecidableEq Slot₂]
  [DecidableEq Option₁] [DecidableEq Option₂]

/-- If both component families are pair-unique, their separated sum is
pair-unique.  Mixed real/extra slot pairs occur in no option. -/
theorem separatedSum_pairUnique
    (H : RankThreeOptionSystem Job Slot₁ Option₁)
    (K : RankThreeOptionSystem Job Slot₂ Option₂)
    (hH : H.PairUnique) (hK : K.PairUnique) :
    (H.separatedSum K).PairUnique := by
  intro s t hst o p hso hto hsp htp
  cases s with
  | inl s =>
      cases t with
      | inl t =>
          cases o with
          | inl o =>
              cases p with
              | inl p =>
                  apply congrArg Sum.inl
                  apply hH
                  · intro h
                    exact hst (congrArg Sum.inl h)
                  · simpa [separatedSum, sum, liftSlotsLeft,
                      sumInlEmbedding] using hso
                  · simpa [separatedSum, sum, liftSlotsLeft,
                      sumInlEmbedding] using hto
                  · simpa [separatedSum, sum, liftSlotsLeft,
                      sumInlEmbedding] using hsp
                  · simpa [separatedSum, sum, liftSlotsLeft,
                      sumInlEmbedding] using htp
              | inr p =>
                  exfalso
                  simpa [separatedSum, sum, liftSlotsRight,
                    sumInrEmbedding] using hsp
          | inr o =>
              exfalso
              simpa [separatedSum, sum, liftSlotsRight,
                sumInrEmbedding] using hso
      | inr t =>
          exfalso
          cases o with
          | inl o =>
              simpa [separatedSum, sum, liftSlotsLeft,
                sumInlEmbedding] using hto
          | inr o =>
              simpa [separatedSum, sum, liftSlotsRight,
                sumInrEmbedding] using hso
  | inr s =>
      cases t with
      | inl t =>
          exfalso
          cases o with
          | inl o =>
              simpa [separatedSum, sum, liftSlotsLeft,
                sumInlEmbedding] using hso
          | inr o =>
              simpa [separatedSum, sum, liftSlotsRight,
                sumInrEmbedding] using hto
      | inr t =>
          cases o with
          | inl o =>
              exfalso
              simpa [separatedSum, sum, liftSlotsLeft,
                sumInlEmbedding] using hso
          | inr o =>
              cases p with
              | inl p =>
                  exfalso
                  simpa [separatedSum, sum, liftSlotsLeft,
                    sumInlEmbedding] using hsp
              | inr p =>
                  apply congrArg Sum.inr
                  apply hK
                  · intro h
                    exact hst (congrArg Sum.inr h)
                  · simpa [separatedSum, sum, liftSlotsRight,
                      sumInrEmbedding] using hso
                  · simpa [separatedSum, sum, liftSlotsRight,
                      sumInrEmbedding] using hto
                  · simpa [separatedSum, sum, liftSlotsRight,
                      sumInrEmbedding] using hsp
                  · simpa [separatedSum, sum, liftSlotsRight,
                      sumInrEmbedding] using htp

end RankThreeOptionSystem

end WeightedEdgeColoring
