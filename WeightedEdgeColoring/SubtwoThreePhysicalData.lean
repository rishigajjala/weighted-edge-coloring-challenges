import WeightedEdgeColoring.SubtwoInducedTrianglePrice
import WeightedEdgeColoring.SubtwoTriangleReservedPrice
import WeightedEdgeColoring.SubtwoPhysicalFiveDataFactory
import WeightedEdgeColoring.SubtwoBlockSelection

/-! Three-index physical data for an actual rank-one dense triangle block. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ}

structure SubtwoThreePhysicalData (n : ℕ) where
  vertex : Fin 3 → G.V
  vertex_injective : Function.Injective vertex
  n_pos : 0 < n
  price : G.E → ℝ
  price_nonneg : ∀ e, 0 ≤ price e
  price_max_pos : 0 < G.subtwoColorPriceMax price

namespace SubtwoThreePhysicalData

variable (D : G.SubtwoThreePhysicalData n)

def vertexSet : Finset G.V := Finset.univ.image D.vertex

def oppositePair : Fin 3 → Fin 3 × Fin 3 :=
  ![(1,2),(0,2),(0,1)]

def first (i : Fin 3) : G.V := D.vertex (oppositePair i).1
def second (i : Fin 3) : G.V := D.vertex (oppositePair i).2

theorem first_ne_second (i : Fin 3) : D.first i ≠ D.second i := by
  apply D.vertex_injective.ne
  fin_cases i <;> decide

noncomputable def bundleCost (i : Fin 3) : ℝ :=
  G.subtwoPhysicalBundleCost n (D.first i) (D.second i)

noncomputable def bundlePrice (i : Fin 3) : ℝ :=
  G.subtwoPhysicalBundlePrice n D.price (D.first i) (D.second i)

noncomputable def exteriorCharge (i : Fin 3) : ℝ :=
  G.subtwoExteriorHarmonicCharge D.vertexSet (D.vertex i) / n

noncomputable def avoidingPrice (i : Fin 3) : ℝ :=
  G.subtwoNormalizedAvoidingPrice D.price (D.vertex i)

theorem vertexSet_card : D.vertexSet.card = 3 := by
  classical
  simp [SubtwoThreePhysicalData.vertexSet, Finset.card_image_of_injective,
    D.vertex_injective]

theorem vertex_mem (i : Fin 3) : D.vertex i ∈ D.vertexSet :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem bundlePrice_eq_pairCost (i : Fin 3) :
    D.bundlePrice i = G.subtwoPairCost D.price (D.first i) (D.second i) /
      ((n : ℝ) * G.subtwoColorPriceMax D.price) := by
  unfold bundlePrice subtwoPhysicalBundlePrice subtwoPairCost
  rw [G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween
    (D.first i) (D.second i) (D.first_ne_second i)]
  unfold exactDemandEdgesBetween
  rw [Finset.sum_filter]

theorem bundlePrice_sum_eq_internal :
    (∑ i : Fin 3, D.bundlePrice i) =
      G.subtwoInternalCost D.price D.vertexSet /
        ((n : ℝ) * G.subtwoColorPriceMax D.price) := by
  simp only [D.bundlePrice_eq_pairCost, ← Finset.sum_div]
  apply congrArg (fun x : ℝ => x / ((n : ℝ) * G.subtwoColorPriceMax D.price))
  have h := G.subtwo_triangle_internal_eq_pair_sum D.price
    (D.vertex 0) (D.vertex 1) (D.vertex 2)
    (D.vertex_injective.ne (by decide))
    (D.vertex_injective.ne (by decide))
    (D.vertex_injective.ne (by decide))
  have hS : D.vertexSet = {D.vertex 0, D.vertex 1, D.vertex 2} := by
    ext v
    simp [SubtwoThreePhysicalData.vertexSet, Finset.mem_image]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
    · intro hv
      rcases hv with h0 | h1 | h2
      · exact ⟨0, h0.symm⟩
      · exact ⟨1, h1.symm⟩
      · exact ⟨2, h2.symm⟩
  rw [hS]
  calc
    _ = G.subtwoPairCost D.price (D.vertex 1) (D.vertex 2) +
        G.subtwoPairCost D.price (D.vertex 0) (D.vertex 2) +
        G.subtwoPairCost D.price (D.vertex 0) (D.vertex 1) := by
      simp [Fin.sum_univ_succ, first, second, oppositePair]
      ring
    _ = _ := by
      dsimp [WeightedEdgeColoring.SubtwoDenseTriangles.triangleCost] at h
      linarith [h]

theorem bundlePrice_sum_le_three_halves (hlocal : G.LocallyPacksInto n) :
    (∑ i : Fin 3, D.bundlePrice i) ≤ (3/2:ℝ) := by
  have h := G.inducedTriangle_internalPrice_le D.n_pos hlocal
    D.vertexSet D.vertexSet_card D.price D.price_nonneg
  rw [D.bundlePrice_sum_eq_internal]
  have hn : (0:ℝ) < n := by exact_mod_cast D.n_pos
  exact (div_le_iff₀ (mul_pos hn D.price_max_pos)).mpr (by nlinarith)

end SubtwoThreePhysicalData

theorem exists_subtwoThreePhysicalData_of_rank_one_block
    (G : WeightedMultigraph.{u}) {n : ℕ}
    (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (b : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank
      (G.subtwoFloorCost n) b = 1)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e)
    (hR : 0 < G.subtwoColorPriceMax price) :
    ∃ D : G.SubtwoThreePhysicalData n,
      D.vertexSet = G.floorPacketization.groupedGraph.subtwoFiber
        (G.subtwoFloorBlock n) b ∧ D.price = price := by
  classical
  let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b
  have hcard := G.floorPacketization.groupedGraph.subtwoFinalBlock_fiber_card
    (G.subtwoFloorCost n) (G.subtwoFloorCost_nonneg n)
    (G.subtwoFloorCost_pair_le hn hlocal) (G.subtwoFloorCost_degree_le hn hlocal) b
  change S.card = 1 + 2 *
    G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) b at hcard
  rw [hrank] at hcard
  norm_num at hcard
  let φ : Fin 3 ≃ S := (Finset.equivFinOfCardEq hcard).symm
  let vertex : Fin 3 → G.V := fun i => (φ i).val
  have hinj : Function.Injective vertex := Subtype.val_injective.comp φ.injective
  let D : G.SubtwoThreePhysicalData n :=
    ⟨vertex, hinj, hn, price, hp, hR⟩
  refine ⟨D, ?_, rfl⟩
  change Finset.univ.image vertex = S
  ext v
  constructor
  · intro hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact (φ i).property
  · intro hv
    let i := φ.symm ⟨v, hv⟩
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val (φ.apply_symm_apply ⟨v, hv⟩)

end WeightedEdgeColoring.WeightedMultigraph
