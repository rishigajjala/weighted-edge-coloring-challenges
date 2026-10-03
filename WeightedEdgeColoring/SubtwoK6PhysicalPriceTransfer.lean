import WeightedEdgeColoring.SubtwoK6PerfectMatchingEnumeration
import WeightedEdgeColoring.SubtwoK6PhysicalMatchingPrices
import WeightedEdgeColoring.SubtwoAnalyticBoundaryArithmetic

/-! The six-vertex matching estimate applied to the actual five-block costs
and normalized color prices. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph.SubtwoFivePhysicalData

open WeightedEdgeColoring.Subtwo.K6MatchingDeficits
open WeightedEdgeColoring.Subtwo.K6BoundaryRows

universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ} (D : G.SubtwoFivePhysicalData n)

theorem augmented_weighted_sum (k : ℝ) :
    (∑ e : Edge,
      D.augmentedPrice e * augmented D.bundleCost D.exteriorCharge k e) =
      (∑ e : Fin 10, D.pairPrice e * D.bundleCost e) +
        k * (∑ v : Fin 5, D.avoidingLoss v) := by
  simp [augmentedPrice, augmented, avoidingLoss, subtwoAvoidingPriceLoss,
    Fin.sum_univ_succ]
  ring

theorem physical_augmented_matching_price_bound
    (hlocal : G.LocallyPacksInto n)
    (b : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank
      (G.subtwoFloorCost n) b = 2)
    (hset : D.vertexSet =
      G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b)
    (hQ0 : 0 < envelope (internalTotal D.bundleCost)) :
    (∑ e : Fin 10, D.pairPrice e * D.bundleCost e) +
      reserveScale (internalTotal D.bundleCost) *
        (∑ v : Fin 5, D.avoidingLoss v) ≤
          paletteMass (internalTotal D.bundleCost) := by
  let x := augmented D.bundleCost D.exteriorCharge
    (reserveScale (internalTotal D.bundleCost))
  obtain ⟨hx0, hxd, hxt, hxf⟩ :=
    D.physical_augmented_matching_rows hlocal b hrank hset hQ0
  have hp : ∀ M : Finset Edge, IsPerfectMatching M →
      (∑ e ∈ M, D.augmentedPrice e) ≤ 1 := by
    intro M hM
    obtain ⟨i, rfl⟩ := perfect_matching_is_listed M hM
    exact D.perfect_price_le_one i
  have hmass : 0 < paletteMass (internalTotal D.bundleCost) := by
    have := le_max_left (2:ℝ) (internalTotal D.bundleCost / 2)
    dsimp [paletteMass]
    linarith
  have h := weighted_sum_le_scale_of_perfect_prices x D.augmentedPrice
    (paletteMass (internalTotal D.bundleCost)) hmass
    D.augmentedPrice_nonneg hx0 hxd hxt hxf hp
  dsimp [x] at h
  rw [D.augmented_weighted_sum] at h
  exact h

theorem demandPrice_sum_le_pairPrice_cost :
    (∑ e : Fin 10, D.demandPrice e) ≤
      ∑ e : Fin 10, D.pairPrice e * D.bundleCost e := by
  exact Finset.sum_le_sum (fun e _ ↦ D.indexed_bundle_price_cost_row e)

/-- The analytic transfer for an actual rank-two five-block. The only
remaining input is the local five-vertex price estimate for these exact
physical demand coordinates. -/
theorem physical_reserved_price_transfer_of_local_bound
    (hlocal : G.LocallyPacksInto n)
    (b : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank
      (G.subtwoFloorCost n) b = 2)
    (hset : D.vertexSet =
      G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b)
    (hC : (∑ e : Fin 10, D.demandPrice e) ≤ (157/80:ℝ)) :
    (∑ e : Fin 10, D.demandPrice e) +
      (∑ v : Fin 5, D.avoidingLoss v) < (1999/1000:ℝ) := by
  let T := internalTotal D.bundleCost
  let C := ∑ e : Fin 10, D.demandPrice e
  let Z := ∑ v : Fin 5, D.avoidingLoss v
  have hcap : ∀ v,
      internalDegree D.bundleCost v + D.exteriorCharge v ≤ degreeBound :=
    D.physical_degree_cap hlocal
  have hQnonneg : 0 ≤ envelope T := by
    have hq := reservedTotal_le_envelope D.bundleCost D.exteriorCharge hcap
    have hq0 : 0 ≤ reservedTotal D.exteriorCharge :=
      Finset.sum_nonneg (fun v _ ↦ D.exteriorCharge_nonneg v)
    dsimp [T]
    linarith
  have hZ : Z ≤ envelope T := by
    have h1 : Z ≤ reservedTotal D.exteriorCharge :=
      Finset.sum_le_sum (fun v _ ↦ (D.avoidingLoss_bounds v).2)
    have h2 := reservedTotal_le_envelope D.bundleCost D.exteriorCharge hcap
    exact h1.trans h2
  have hT : 2 * WeightedEdgeColoring.Subtwo.AnalyticBoundary.target ≤ T := by
    simpa only [T, WeightedEdgeColoring.Subtwo.AnalyticBoundary.target, target]
      using D.physical_density hlocal b hrank hset
  have hmatching : 0 < 5 * WeightedEdgeColoring.Subtwo.AnalyticBoundary.degreeBound - 2 * T →
      C + (1 + (max 2 (T / 2) - WeightedEdgeColoring.Subtwo.AnalyticBoundary.degreeBound) /
        (5 * WeightedEdgeColoring.Subtwo.AnalyticBoundary.degreeBound - 2 * T)) * Z ≤
          max 2 (T / 2) := by
    intro hQ
    have hQ' : 0 < envelope T := by
      simpa only [envelope, degreeBound,
        WeightedEdgeColoring.Subtwo.AnalyticBoundary.degreeBound] using hQ
    have h := D.physical_augmented_matching_price_bound
      hlocal b hrank hset hQ'
    have hC' := D.demandPrice_sum_le_pairPrice_cost
    dsimp [C, Z, T] at *
    dsimp [reserveScale, paletteMass, envelope, degreeBound] at h
    dsimp [WeightedEdgeColoring.Subtwo.AnalyticBoundary.degreeBound]
    linarith
  have hfinal := WeightedEdgeColoring.Subtwo.AnalyticBoundary.price_transfer_with_zero_boundary
    C Z T hT (by
      simpa only [envelope, degreeBound,
        WeightedEdgeColoring.Subtwo.AnalyticBoundary.degreeBound] using hQnonneg)
    (by simpa only [WeightedEdgeColoring.Subtwo.AnalyticBoundary.localBound] using hC)
    (by simpa only [envelope, degreeBound,
        WeightedEdgeColoring.Subtwo.AnalyticBoundary.degreeBound] using hZ)
    hmatching
  simpa only [C, Z, WeightedEdgeColoring.Subtwo.AnalyticBoundary.target] using hfinal

end WeightedEdgeColoring.WeightedMultigraph.SubtwoFivePhysicalData
