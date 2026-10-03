import WeightedEdgeColoring.SubtwoK6BoundaryRows
import WeightedEdgeColoring.SubtwoPhysicalFiveDomainRows

set_option maxHeartbeats 0

/-!
# Augmented matching rows from the actual physical five-block

The ten internal entries are the physical minimum bundle-cover costs; the
five exterior entries are the physical harmonic exterior charges.
-/

namespace WeightedEdgeColoring.WeightedMultigraph.SubtwoFivePhysicalData

open WeightedEdgeColoring.Subtwo.K6BoundaryRows
open WeightedEdgeColoring.Subtwo.K6MatchingDeficits

universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ} (D : G.SubtwoFivePhysicalData n)

private def starIndex : Fin 5 → Fin 4 → Fin 10 :=
  ![![0,1,2,3],![0,4,5,6],![1,4,7,8],![2,5,7,9],![3,6,8,9]]

private theorem pairIndex_star_eq : ∀ v : Fin 5, ∀ a : Fin 4,
    subtwoFivePairIndex v (v.succAbove a) = starIndex v a := by
  decide

theorem internalDegree_eq_indexed_star (v : Fin 5) :
    internalDegree D.bundleCost v =
      ∑ a : Fin 4,
        D.bundleCost (subtwoFivePairIndex v (v.succAbove a)) := by
  simp_rw [pairIndex_star_eq]
  fin_cases v <;>
    simp [internalDegree, starIndex, Fin.sum_univ_succ] <;> ring

theorem physical_degree_cap (hlocal : G.LocallyPacksInto n) (v : Fin 5) :
    internalDegree D.bundleCost v + D.exteriorCharge v ≤ degreeBound := by
  rw [D.internalDegree_eq_indexed_star]
  have h := D.indexed_star_budget hlocal v
  have hm : subtwoM ≤ degreeBound := by
    norm_num [subtwoM, degreeBound]
  exact h.trans hm

theorem physical_internal_triangle_rows (i : Fin 10) :
    triangleMass (augmented D.bundleCost D.exteriorCharge 0)
      (backTriangle i) ≤ 2 := by
  rw [backTriangle_mass]
  fin_cases i
  all_goals
    first
    | simpa [backTriple, subtwoFivePairIndex] using
        (D.indexed_triangle_cost_row 0 1 2 (by decide) (by decide) (by decide))
    | simpa [backTriple, subtwoFivePairIndex] using
        (D.indexed_triangle_cost_row 0 1 3 (by decide) (by decide) (by decide))
    | simpa [backTriple, subtwoFivePairIndex] using
        (D.indexed_triangle_cost_row 0 1 4 (by decide) (by decide) (by decide))
    | simpa [backTriple, subtwoFivePairIndex] using
        (D.indexed_triangle_cost_row 0 2 3 (by decide) (by decide) (by decide))
    | simpa [backTriple, subtwoFivePairIndex] using
        (D.indexed_triangle_cost_row 0 2 4 (by decide) (by decide) (by decide))
    | simpa [backTriple, subtwoFivePairIndex] using
        (D.indexed_triangle_cost_row 0 3 4 (by decide) (by decide) (by decide))
    | simpa [backTriple, subtwoFivePairIndex] using
        (D.indexed_triangle_cost_row 1 2 3 (by decide) (by decide) (by decide))
    | simpa [backTriple, subtwoFivePairIndex] using
        (D.indexed_triangle_cost_row 1 2 4 (by decide) (by decide) (by decide))
    | simpa [backTriple, subtwoFivePairIndex] using
        (D.indexed_triangle_cost_row 1 3 4 (by decide) (by decide) (by decide))
    | simpa [backTriple, subtwoFivePairIndex] using
        (D.indexed_triangle_cost_row 2 3 4 (by decide) (by decide) (by decide))

theorem physical_density
    (hlocal : G.LocallyPacksInto n)
    (b : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank
      (G.subtwoFloorCost n) b = 2)
    (hset : D.vertexSet =
      G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b) :
    2 * target ≤ internalTotal D.bundleCost := by
  have h := D.indexed_density_row_of_rank_two_block hlocal b hrank hset
  simpa [target, subtwoKappa, internalTotal] using h

theorem physical_augmented_matching_rows
    (hlocal : G.LocallyPacksInto n)
    (b : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank
      (G.subtwoFloorCost n) b = 2)
    (hset : D.vertexSet =
      G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b)
    (hQ0 : 0 < envelope (internalTotal D.bundleCost)) :
    (∀ e : Edge, 0 ≤ augmented D.bundleCost D.exteriorCharge
      (reserveScale (internalTotal D.bundleCost)) e) ∧
    (∀ v : Vertex,
      degree (augmented D.bundleCost D.exteriorCharge
        (reserveScale (internalTotal D.bundleCost))) v ≤
          paletteMass (internalTotal D.bundleCost)) ∧
    (∀ S : Finset Vertex, S.card = 3 →
      triangleMass (augmented D.bundleCost D.exteriorCharge
        (reserveScale (internalTotal D.bundleCost))) S ≤
          paletteMass (internalTotal D.bundleCost)) ∧
    (∀ v : Vertex,
      omitFive (augmented D.bundleCost D.exteriorCharge
        (reserveScale (internalTotal D.bundleCost))) v ≤
          2 * paletteMass (internalTotal D.bundleCost)) := by
  let t := D.bundleCost
  let q := D.exteriorCharge
  have hcap : ∀ v, internalDegree t v + q v ≤ degreeBound :=
    D.physical_degree_cap hlocal
  have hq : ∀ v, 0 ≤ q v := D.exteriorCharge_nonneg
  have ht0 : ∀ e, 0 ≤ t e := fun e ↦ (D.bundleCost_bounds e).1
  have ht1 : ∀ e, t e ≤ 1 := fun e ↦ (D.bundleCost_bounds e).2
  have hT : 2 * target ≤ internalTotal t :=
    D.physical_density hlocal b hrank hset
  have htri : ∀ i,
      triangleMass (augmented t q 0) (backTriangle i) ≤ 2 :=
    D.physical_internal_triangle_rows
  exact ⟨augmented_nonneg t q ht0 hq hT hQ0,
    augmented_degree_le_palette t q hcap hq hT hQ0,
    augmented_triangle_le_palette t q hcap hq ht1 hT hQ0 htri,
    augmented_omit_le_twice_palette t q hcap hq hT hQ0⟩

end WeightedEdgeColoring.WeightedMultigraph.SubtwoFivePhysicalData
