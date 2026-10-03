import WeightedEdgeColoring.MultigraphExtendedProfileWordPadding
import WeightedEdgeColoring.MultigraphSelectedProfileTinyGlobal

/-!
# Capacity rows carried by packed extended-profile words

These are the concrete rows that the mass-sensitive selector must control.
A large row is a vertex, color, and padded large slot.  A tiny row is a
vertex and color reservoir.  One edge contributes its equation-(23) mass to
the row at each endpoint.  We multiply every physical contribution by `n`;
the fractional large-row scale is then `n * rho`, while the desired additive
error divided by `n` is asymptotically small.

The contribution depends on the packed word at both endpoints.  Therefore it
is a pair coefficient, not yet a `FiniteCategoricalSelection.rowLoad`.  On a
bipartite graph it must be handled in two passes, one shore at a time.
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

/-- A large capacity row `(vertex, color, padded slot)`. -/
abbrev ExtendedProfileLargeRow :=
  G.V × Fin n × Fin (explicitLargeSlotBound β q r)

/-- A tiny reservoir row `(vertex, color)`. -/
abbrev ExtendedProfileTinyRow := G.V × Fin n

/-- The combined selected-profile capacity rows. -/
abbrev ExtendedProfileCapacityRow :=
  Sum (G.ExtendedProfileLargeRow (n := n) (β := β) (q := q) (r := r))
    (G.ExtendedProfileTinyRow (n := n))

/-- Equation-(23) large mass after decoding two packed endpoint words. -/
def packedExtendedProfileLargeMass (rho omega : ℝ) (e : G.E)
    (fstCode sndCode : ExtendedProfilePackedWordState n β q r)
    (c : Fin n) (i j : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  G.extendedProfileProductOptionMass R0 rho omega e
    (G.decodeExtendedProfileWord R0 (G.fst e) fstCode c)
    (G.decodeExtendedProfileWord R0 (G.snd e) sndCode c) i j

/-- Equation-(23) tiny mass after decoding two packed endpoint words. -/
def packedExtendedProfileTinyMass (rho omega : ℝ) (e : G.E)
    (fstCode sndCode : ExtendedProfilePackedWordState n β q r)
    (c : Fin n) : ℝ :=
  G.extendedProfileTinyProductOptionMass R0 rho omega e
    (G.decodeExtendedProfileWord R0 (G.fst e) fstCode c)
    (G.decodeExtendedProfileWord R0 (G.snd e) sndCode c)

/-- Scaled contribution of one edge and its two endpoint words to a large
capacity row. -/
def packedExtendedProfileLargeRowUse (rho omega : ℝ) (e : G.E)
    (fstCode sndCode : ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileLargeRow (n := n) (β := β) (q := q) (r := r)) : ℝ :=
  if row.1 = G.fst e then
    n * ∑ j, G.packedExtendedProfileLargeMass R0 rho omega e
      fstCode sndCode row.2.1 row.2.2 j
  else if row.1 = G.snd e then
    n * ∑ i, G.packedExtendedProfileLargeMass R0 rho omega e
      fstCode sndCode row.2.1 i row.2.2
  else 0

/-- Scaled weighted contribution to one tiny reservoir row. -/
def packedExtendedProfileTinyRowUse (rho omega : ℝ) (e : G.E)
    (fstCode sndCode : ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileTinyRow (n := n)) : ℝ :=
  if row.1 = G.fst e ∨ row.1 = G.snd e then
    n * G.weight e *
      G.packedExtendedProfileTinyMass R0 rho omega e fstCode sndCode row.2
  else 0

/-- Combined pair coefficient for one edge. -/
def packedExtendedProfileCapacityUse (rho omega : ℝ) (e : G.E)
    (fstCode sndCode : ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileCapacityRow (n := n) (β := β) (q := q) (r := r)) : ℝ :=
  match row with
  | Sum.inl large =>
      G.packedExtendedProfileLargeRowUse R0 rho omega e fstCode sndCode large
  | Sum.inr tiny =>
      G.packedExtendedProfileTinyRowUse R0 rho omega e fstCode sndCode tiny

/-- Total scaled capacity load of a packed word choice. -/
def packedExtendedProfileCapacityLoad (rho omega : ℝ)
    (choice : G.V → ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileCapacityRow (n := n) (β := β) (q := q) (r := r)) : ℝ :=
  ∑ e, G.packedExtendedProfileCapacityUse R0 rho omega e
    (choice (G.fst e)) (choice (G.snd e)) row

theorem packedExtendedProfileCapacityUse_nonneg
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (e : G.E)
    (fstCode sndCode : ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileCapacityRow (n := n) (β := β) (q := q) (r := r)) :
    0 ≤ G.packedExtendedProfileCapacityUse R0 rho omega e
      fstCode sndCode row := by
  cases row with
  | inl large =>
    change 0 ≤ G.packedExtendedProfileLargeRowUse R0 rho omega e
      fstCode sndCode large
    unfold packedExtendedProfileLargeRowUse packedExtendedProfileLargeMass
    split
    · exact mul_nonneg (Nat.cast_nonneg n) (Finset.sum_nonneg fun j _ ↦
        G.extendedProfileProductOptionMass_nonneg R0 hs hn hq hr0 hleft
          homega0 homega1 hrho e _ _ _ j)
    · split
      · exact mul_nonneg (Nat.cast_nonneg n) (Finset.sum_nonneg fun i _ ↦
          G.extendedProfileProductOptionMass_nonneg R0 hs hn hq hr0 hleft
            homega0 homega1 hrho e _ _ i _)
      · exact le_rfl
  | inr tiny =>
    change 0 ≤ G.packedExtendedProfileTinyRowUse R0 rho omega e
      fstCode sndCode tiny
    unfold packedExtendedProfileTinyRowUse packedExtendedProfileTinyMass
    split
    · exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg n) (G.weight_nonneg e))
        (G.extendedProfileTinyProductOptionMass_nonneg R0 hs hn hq hr0
          hleft homega0 homega1 hrho e _ _)
    · exact le_rfl

end WeightedMultigraph

end

end WeightedEdgeColoring
