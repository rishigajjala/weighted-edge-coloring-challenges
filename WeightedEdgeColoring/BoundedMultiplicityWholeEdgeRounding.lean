import WeightedEdgeColoring.BoundedMultiplicityPairCodegree
import WeightedEdgeColoring.BoundedMultiplicitySimpleLayers
import WeightedEdgeColoring.MultigraphLocalPolytope
import WeightedEdgeColoring.WeightedInsertion

/-!
# Coordinated whole-edge rounding for bounded-multiplicity multigraphs

This file states the multigraph rounding theorem in the form needed after the
finite harmonic packet decomposition.  The theorem colors one subset of all
indexed residual edges at once.  Its feasibility conclusion is therefore a
joint constraint across every parallel-edge layer.

The structural lemmas connect the oriented multiplicity certificate supplied
by a bipartition (and by `BoundedPairSimpleLayering`) to the unordered
endpoint-pair multiplicity used by the option-system codegree bounds.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u

namespace WeightedMultigraph

variable {G : WeightedMultigraph.{u}}

namespace Bipartition

/-- An oriented endpoint-pair bound in a bipartite graph also bounds every
unordered endpoint fiber.  The two possible orientations cannot both occur,
because the bipartition canonically puts the false shore first. -/
theorem pairMultiplicityAtMost_of_orientedPair
    (b : G.Bipartition) {L : ℕ}
    (hmult : ∀ k, (b.orientedPairCell k).card ≤ L) :
    G.PairMultiplicityAtMost L := by
  intro u v
  by_cases hnonempty : (G.endpointPairCell u v).Nonempty
  · obtain ⟨e, he⟩ := hnonempty
    have hsubset : G.endpointPairCell u v ⊆
        b.orientedPairCell (b.orientedPairKey e) := by
      intro f hf
      have hfends := (G.mem_endpointPairCell_iff u v f).mp hf
      have heends := (G.mem_endpointPairCell_iff u v e).mp he
      have hsame : G.endpoints f = G.endpoints e :=
        hfends.trans heends.symm
      have horiented := b.orientedPair_eq_of_endpoints_eq hsame
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, Prod.ext horiented.1 horiented.2⟩
    exact (Finset.card_le_card hsubset).trans
      (hmult (b.orientedPairKey e))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty]
    simp

end Bipartition

namespace BoundedPairSimpleLayering

variable {b : G.Bipartition} {L : ℕ}

/-- A layering certificate itself recovers the oriented multiplicity bound:
inside one oriented endpoint fiber, the layer map is injective into `Fin L`. -/
theorem orientedPairCell_card_le
    (D : G.BoundedPairSimpleLayering b L) (k : G.V × G.V) :
    (b.orientedPairCell k).card ≤ L := by
  let F := b.orientedPairCell k
  have hmaps : (F : Set G.E).MapsTo D.layer
      (Finset.univ : Finset (Fin L)) := by
    intro e _he
    simp
  have hinj : (F : Set G.E).InjOn D.layer := by
    intro e he f hf hef
    have hekey : b.orientedPairKey e = k :=
      (Finset.mem_filter.mp he).2
    have hfkey : b.orientedPairKey f = k :=
      (Finset.mem_filter.mp hf).2
    exact D.eq_of_same_orientedPair_of_layer_eq
      (hekey.trans hfkey.symm) hef
  calc
    F.card ≤ (Finset.univ : Finset (Fin L)).card :=
      Finset.card_le_card_of_injOn D.layer hmaps hinj
    _ = L := by simp

/-- Hence a bounded simple-layering certificate gives the unordered
endpoint-pair multiplicity assumption used by the coordinated option system. -/
theorem pairMultiplicityAtMost
    (D : G.BoundedPairSimpleLayering b L) :
    G.PairMultiplicityAtMost L :=
  b.pairMultiplicityAtMost_of_orientedPair D.orientedPairCell_card_le

end BoundedPairSimpleLayering

end WeightedMultigraph

/-- The proposal-level whole-edge theorem required for a bounded-multiplicity
bipartite residual.  The threshold may depend on the fixed multiplicity `L`,
but is uniform in graph size and in the smallest edge weight.

Unlike a family of independently rounded simple layers, the conclusion is one
feasible partial coloring of the original multigraph, so loads of parallel
edges using the same color are controlled jointly. -/
def BoundedMultiplicityWholeEdgeUniformRounding : Prop :=
  ∀ L : ℕ, ∀ C0 C1 eta : ℝ,
    0 < C0 → 0 < C1 → 0 < eta → ∃ N : ℕ,
    ∀ (G : WeightedMultigraph.{u}) (b : G.Bipartition) (n q : ℕ)
      (x : G.E → Fin q → ℝ),
      N ≤ n →
      0 < q →
      (∀ k, (b.orientedPairCell k).card ≤ L) →
      (∀ v, G.starWeight v ≤ n) →
      (q : ℝ) ≤ C1 * n →
      (∀ e c, 0 ≤ x e c ∧ x e c ≤ C0 / n) →
      (∀ e, ∑ c, x e c ≤ 1) →
      (∀ v c,
        G.IsAverageOfStarFeasibleSets v (fun se ↦ x se.1 c)) →
      ∃ (P : Finset G.E) (color : G.E → Fin q),
        G.IsFeasibleOn P color ∧
        (∀ e ∈ P, 0 < x e (color e)) ∧
        ∀ v,
          (∑ e : G.E,
              if G.Inc v e then G.weight e * ∑ c, x e c else 0) -
            (∑ e ∈ P,
              if G.Inc v e then G.weight e else 0) ≤ eta * n

namespace WeightedMultigraph

variable (G : WeightedMultigraph.{u})

/-- Weight at a vertex not covered by a fractional multigraph edge-color
proposal. -/
def proposalDeficit {q : ℕ} (x : G.E → Fin q → ℝ) (v : G.V) : ℝ :=
  ∑ e : G.E,
    if G.Inc v e then G.weight e * (1 - ∑ c, x e c) else 0

theorem proposalDeficit_nonneg {q : ℕ} (x : G.E → Fin q → ℝ)
    (hmass : ∀ e, ∑ c, x e c ≤ 1) (v : G.V) :
    0 ≤ G.proposalDeficit x v := by
  apply Finset.sum_nonneg
  intro e _he
  split
  · exact mul_nonneg (G.weight_nonneg e) (sub_nonneg.mpr (hmass e))
  · exact le_rfl

/-- Support-preserving form of coordinated bounded-multiplicity rounding.
The selected residual edges use only colors missing at both endpoints, and
their uncolored weight is the proposal deficit plus the rounding loss. -/
theorem exists_missingSupported_partialColoring_of_boundedMultiplicityWholeEdge
    (hround : BoundedMultiplicityWholeEdgeUniformRounding.{u})
    (L : ℕ) (C0 C1 eta : ℝ)
    (hC0 : 0 < C0) (hC1 : 0 < C1) (heta : 0 < eta) :
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
      (∀ v c,
        G.IsAverageOfStarFeasibleSets v (fun se ↦ x se.1 c)) →
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
          G.proposalDeficit x v + eta * n := by
  rcases hround L C0 C1 eta hC0 hC1 heta with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro G b n q missing x hn hq hmult hstar hpalette hx hmass havg hsupport
  rcases hN G b n q x hn hq hmult hstar hpalette hx hmass havg with
    ⟨P, color, hfeasible, hselected, hloss⟩
  refine ⟨P, color, hfeasible, ?_, ?_⟩
  · intro e heP
    exact hsupport e (color e) (hselected e heP)
  · intro v
    let total : ℝ :=
      ∑ e : G.E, if G.Inc v e then G.weight e else 0
    let proposed : ℝ :=
      ∑ e : G.E,
        if G.Inc v e then G.weight e * ∑ c, x e c else 0
    let selected : ℝ :=
      ∑ e ∈ P, if G.Inc v e then G.weight e else 0
    have hresidual :
        (∑ e ∈ Finset.univ \ P,
          if G.Inc v e then G.weight e else 0) = total - selected := by
      dsimp [total, selected]
      exact Finset.sum_sdiff_eq_sub (Finset.subset_univ P)
    have hdeficit : G.proposalDeficit x v = total - proposed := by
      unfold proposalDeficit
      dsimp [total, proposed]
      calc
        (∑ e : G.E,
            if G.Inc v e then G.weight e * (1 - ∑ c, x e c) else 0) =
            ∑ e : G.E,
              ((if G.Inc v e then G.weight e else 0) -
                (if G.Inc v e then
                  G.weight e * ∑ c, x e c else 0)) := by
          apply Finset.sum_congr rfl
          intro e _he
          by_cases hinc : G.Inc v e
          · simp [hinc]
            ring
          · simp [hinc]
        _ =
            (∑ e : G.E, if G.Inc v e then G.weight e else 0) -
              ∑ e : G.E,
                if G.Inc v e then G.weight e * ∑ c, x e c else 0 := by
          rw [Finset.sum_sub_distrib]
    have hloss' : proposed - selected ≤ eta * n := by
      simpa [proposed, selected] using hloss v
    rw [hresidual, hdeficit]
    linarith

end WeightedMultigraph

end

end WeightedEdgeColoring
