import WeightedEdgeColoring.BoundedMultiplicityWholeEdgeRounding

/-!
# Deficit-aware bounded-multiplicity rounding

The retained-core construction naturally leaves low-proposal-mass edges.
Their fractional covered weight is controlled by the proposal deficit divided
by the trimming gap.  This interface records exactly that loss.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

universe u

/-- Proposal-relative whole-edge rounding with the unavoidable trim-deficit
term displayed explicitly. -/
def DeficitAwareBoundedMultiplicityWholeEdgeUniformRounding : Prop :=
  ∀ L : ℕ, ∀ C0 C1 trim eta : ℝ,
    0 < C0 → 0 < C1 → C1 < 4 → 0 < trim → trim < 1 →
    64 * trim < eta → 0 < eta →
    ∃ N : ℕ,
    ∀ (G : WeightedMultigraph.{u}) (b : G.Bipartition) (n q : ℕ)
      (x : G.E → Fin q → ℝ),
      N ≤ n →
      0 < q →
      (∀ k, (b.orientedPairCell k).card ≤ L) →
      (∀ v, G.starWeight v ≤ n) →
      (q : ℝ) ≤ C1 * n →
      (∀ e c, 0 ≤ x e c ∧ x e c ≤ C0 / n) →
      (∀ e, ∑ c, x e c ≤ 1) →
      (∀ v c, G.IsAverageOfStarFeasibleSets v (fun se ↦ x se.1 c)) →
      ∃ (P : Finset G.E) (color : G.E → Fin q),
        G.IsFeasibleOn P color ∧
        (∀ e ∈ P, 0 < x e (color e)) ∧
        ∀ v,
          (∑ e ∈ Finset.univ \ P,
            if G.Inc v e then G.weight e else 0) ≤
          G.proposalDeficit x v / trim + eta * n

namespace WeightedMultigraph

/-- Support-preserving form of deficit-aware rounding. -/
theorem exists_missingSupported_partialColoring_of_deficitAwareBoundedMultiplicity
    (hround : DeficitAwareBoundedMultiplicityWholeEdgeUniformRounding.{u})
    (L : ℕ) (C0 C1 trim eta : ℝ)
    (hC0 : 0 < C0) (hC1 : 0 < C1) (hC1four : C1 < 4)
    (htrim0 : 0 < trim) (htrim1 : trim < 1)
    (htrimEta : 64 * trim < eta) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (b : G.Bipartition)
      (n q : ℕ) (missing : G.V → Finset (Fin q))
      (x : G.E → Fin q → ℝ),
      N ≤ n →
      0 < q →
      (∀ k, (b.orientedPairCell k).card ≤ L) →
      (∀ v, G.starWeight v ≤ n) →
      (q : ℝ) ≤ C1 * n →
      (∀ e c, 0 ≤ x e c ∧ x e c ≤ C0 / n) →
      (∀ e, ∑ c, x e c ≤ 1) →
      (∀ v c, G.IsAverageOfStarFeasibleSets v (fun se ↦ x se.1 c)) →
      (∀ e c, 0 < x e c →
        c ∈ missing (G.fst e) ∧ c ∈ missing (G.snd e)) →
      ∃ (P : Finset G.E) (color : G.E → Fin q),
        G.IsFeasibleOn P color ∧
        (∀ e ∈ P,
          color e ∈ missing (G.fst e) ∧
            color e ∈ missing (G.snd e)) ∧
        ∀ v,
          (∑ e ∈ Finset.univ \ P,
            if G.Inc v e then G.weight e else 0) ≤
          G.proposalDeficit x v / trim + eta * n := by
  rcases hround L C0 C1 trim eta hC0 hC1 hC1four htrim0 htrim1 htrimEta heta with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro G b n q missing x hn hq hmult hstar hpalette hx hmass havg hsupport
  rcases hN G b n q x hn hq hmult hstar hpalette hx hmass havg with
    ⟨P, color, hfeasible, hselected, hloss⟩
  refine ⟨P, color, hfeasible, ?_, hloss⟩
  · intro e heP
    exact hsupport e (color e) (hselected e heP)

end WeightedMultigraph

end

end WeightedEdgeColoring
