import WeightedEdgeColoring.SubtwoPhysicalObservableCaps
import WeightedEdgeColoring.SubtwoPhysicalSubsetCostRows
import WeightedEdgeColoring.SubtwoPhysicalCrossPriceRows

/-!
# The actual 970 coordinates of a five-vertex block

Pairs and heavy classes use the lexicographic order of the frozen
certificate generator. All observables are defined from physical edges,
one common star packing at each vertex, and genuine color prices.
The last 750 coordinates are the true products of pair prices and the
75 base cost, exterior-charge, and heavy-mass coordinates.
-/

open scoped BigOperators
set_option autoImplicit false

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G : WeightedMultigraph.{u})

def subtwoFivePair : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

theorem subtwoFivePair_ne (e : Fin 10) : (subtwoFivePair e).1 ≠ (subtwoFivePair e).2 := by
  fin_cases e <;> decide

def subtwoFiveClassVertex (d : Fin 60) : Fin 5 := ⟨d.val / 12, by omega⟩
def subtwoFiveClassFirst (d : Fin 60) : Fin 4 := ⟨(d.val % 12) / 3, by omega⟩
def subtwoFiveClassSecond (d : Fin 60) : Fin 4 :=
  (subtwoFiveClassFirst d).succAbove ⟨d.val % 3, by omega⟩

theorem subtwoFiveClass_ne (d : Fin 60) : subtwoFiveClassFirst d ≠ subtwoFiveClassSecond d := by
  have h : ∀ i : Fin 4, ∀ j : Fin 3, i ≠ i.succAbove j := by decide
  exact h _ _

theorem subtwoFiveNeighbor_injective (v : Fin 5) : Function.Injective v.succAbove := by
  have h : ∀ v : Fin 5, Function.Injective v.succAbove := by decide
  exact h v

theorem subtwoFiveNeighbor_ne (v : Fin 5) (a : Fin 4) : v ≠ v.succAbove a := by
  have h : ∀ v : Fin 5, ∀ a : Fin 4, v ≠ v.succAbove a := by decide
  exact h v a

structure SubtwoFivePhysicalData (n : ℕ) where
  vertex : Fin 5 → G.V
  vertex_injective : Function.Injective vertex
  n_pos : 0 < n
  bin : ∀ v : Fin 5, G.StarEdge (vertex v) → Fin n
  bin_load : ∀ v j, G.starBinLoad (bin v) j ≤ 1
  price : G.E → ℝ
  price_nonneg : ∀ e, 0 ≤ price e
  price_max_pos : 0 < G.subtwoColorPriceMax price

/-- Build the data from existing local packings of the original graph. -/
def subtwoFivePhysicalDataOfLocalPacking
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (vertex : Fin 5 → G.V) (hinj : Function.Injective vertex)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) (hR : 0 < G.subtwoColorPriceMax price) :
    G.SubtwoFivePhysicalData n := by
  classical
  exact {
    vertex := vertex
    vertex_injective := hinj
    n_pos := hn
    bin := fun v => Classical.choose (hlocal (vertex v))
    bin_load := fun v => Classical.choose_spec (hlocal (vertex v))
    price := price
    price_nonneg := hp
    price_max_pos := hR }

namespace SubtwoFivePhysicalData
variable {G} {n : ℕ} (D : G.SubtwoFivePhysicalData n)

def vertexSet : Finset G.V := Finset.univ.image D.vertex
def neighbor (v : Fin 5) (a : Fin 4) : G.V := D.vertex (v.succAbove a)

theorem neighbor_injective (v : Fin 5) : Function.Injective (D.neighbor v) :=
  D.vertex_injective.comp (subtwoFiveNeighbor_injective v)

theorem neighbor_ne (v : Fin 5) (a : Fin 4) : D.vertex v ≠ D.neighbor v a :=
  fun h => subtwoFiveNeighbor_ne v a (D.vertex_injective h)

def pairPrice (e : Fin 10) : ℝ :=
  G.subtwoNormalizedSetPrice D.price {D.vertex (subtwoFivePair e).1, D.vertex (subtwoFivePair e).2}

def bundleCost (e : Fin 10) : ℝ :=
  G.subtwoPhysicalBundleCost n (D.vertex (subtwoFivePair e).1) (D.vertex (subtwoFivePair e).2)

def exteriorCharge (v : Fin 5) : ℝ := G.subtwoExteriorHarmonicCharge D.vertexSet (D.vertex v) / n

def heavyMass (d : Fin 60) : ℝ :=
  G.subtwoHeavyClassMass (D.vertex (subtwoFiveClassVertex d))
    (D.neighbor (subtwoFiveClassVertex d)) (D.bin (subtwoFiveClassVertex d))
    (subtwoFiveClassFirst d) (subtwoFiveClassSecond d)

def demandPrice (e : Fin 10) : ℝ :=
  G.subtwoPhysicalBundlePrice n D.price (D.vertex (subtwoFivePair e).1) (D.vertex (subtwoFivePair e).2)

def avoidingLoss (v : Fin 5) : ℝ := G.subtwoAvoidingPriceLoss (D.exteriorCharge v) D.price (D.vertex v)

def bigPrice (d : Fin 60) : ℝ :=
  G.subtwoHeavyBigPrice (D.vertex (subtwoFiveClassVertex d))
    (D.neighbor (subtwoFiveClassVertex d)) (D.bin (subtwoFiveClassVertex d)) D.price
    (subtwoFiveClassFirst d) (subtwoFiveClassSecond d)

def smallPrice (d : Fin 60) : ℝ :=
  G.subtwoHeavySmallPrice (D.vertex (subtwoFiveClassVertex d))
    (D.neighbor (subtwoFiveClassVertex d)) (D.bin (subtwoFiveClassVertex d)) D.price
    (subtwoFiveClassFirst d) (subtwoFiveClassSecond d)

/-- Base coordinates: ten bundle costs, five exterior charges, sixty masses. -/
def baseCoordinate (y : Fin 75) : ℝ :=
  if h0 : y.val < 10 then D.bundleCost ⟨y.val, h0⟩ else
  if h1 : y.val < 15 then D.exteriorCharge ⟨y.val - 10, by omega⟩ else
    D.heavyMass ⟨y.val - 15, by omega⟩

def productCoordinate (e : Fin 10) (y : Fin 75) : ℝ := D.pairPrice e * D.baseCoordinate y

/-- The exact block layout used by the 970-column certificate. -/
def vector (k : Fin 970) : ℝ :=
  if h0 : k.val < 10 then D.pairPrice ⟨k.val, h0⟩ else
  if h1 : k.val < 20 then D.bundleCost ⟨k.val - 10, by omega⟩ else
  if h2 : k.val < 25 then D.exteriorCharge ⟨k.val - 20, by omega⟩ else
  if h3 : k.val < 85 then D.heavyMass ⟨k.val - 25, by omega⟩ else
  if h4 : k.val < 95 then D.demandPrice ⟨k.val - 85, by omega⟩ else
  if h5 : k.val < 100 then D.avoidingLoss ⟨k.val - 95, by omega⟩ else
  if h6 : k.val < 160 then D.bigPrice ⟨k.val - 100, by omega⟩ else
  if h7 : k.val < 220 then D.smallPrice ⟨k.val - 160, by omega⟩ else
    D.productCoordinate ⟨(k.val - 220) / 75, by omega⟩ ⟨(k.val - 220) % 75, by omega⟩

theorem pairPrice_bounds (e : Fin 10) : 0 ≤ D.pairPrice e ∧ D.pairPrice e ≤ 1 :=
  G.subtwoNormalizedSetPrice_bounds D.price D.price_nonneg D.price_max_pos _

theorem bundleCost_bounds (e : Fin 10) : 0 ≤ D.bundleCost e ∧ D.bundleCost e ≤ 1 := by
  apply G.subtwoPhysicalBundleCost_bounds D.n_pos _ _
    (fun h => subtwoFivePair_ne e (D.vertex_injective h))
  exact ⟨D.bin _, D.bin_load _⟩

theorem heavyMass_bounds (d : Fin 60) : 0 ≤ D.heavyMass d ∧ D.heavyMass d ≤ 1 :=
  ⟨G.subtwoHeavyClassMass_nonneg _ _ _ _ _, G.subtwoHeavyClassMass_le_one _ _ D.n_pos _ _ _⟩

theorem demandPrice_bounds (e : Fin 10) : 0 ≤ D.demandPrice e ∧ D.demandPrice e ≤ 1 := by
  constructor
  · exact G.subtwoPhysicalBundlePrice_nonneg D.price D.price_nonneg D.price_max_pos _ _
  · apply G.subtwoPhysicalBundlePrice_le_one D.n_pos D.price D.price_nonneg D.price_max_pos _ _
      (fun h => subtwoFivePair_ne e (D.vertex_injective h))
    exact ⟨D.bin _, D.bin_load _⟩

theorem exteriorCharge_nonneg (v : Fin 5) : 0 ≤ D.exteriorCharge v :=
  div_nonneg (G.subtwoExteriorHarmonicCharge_nonneg _ _) (Nat.cast_nonneg _)

theorem avoidingLoss_bounds (v : Fin 5) :
    0 ≤ D.avoidingLoss v ∧ D.avoidingLoss v ≤ D.exteriorCharge v :=
  G.subtwoAvoidingPriceLoss_bounds _ (D.exteriorCharge_nonneg v)
    D.price D.price_nonneg D.price_max_pos _

theorem bigSmallPrice_bounds (d : Fin 60) :
    (0 ≤ D.bigPrice d ∧ D.bigPrice d ≤ 1) ∧ (0 ≤ D.smallPrice d ∧ D.smallPrice d ≤ 1) :=
  G.subtwoHeavyBigSmallPrice_bounds _ _ (D.neighbor_injective _) (D.neighbor_ne _)
    D.n_pos _ (D.bin_load _) D.price D.price_nonneg D.price_max_pos _ _

theorem baseCoordinate_bounds (hq : ∀ v, D.exteriorCharge v ≤ 1) (y : Fin 75) :
    0 ≤ D.baseCoordinate y ∧ D.baseCoordinate y ≤ 1 := by
  unfold baseCoordinate
  split_ifs
  · exact D.bundleCost_bounds _
  · exact ⟨D.exteriorCharge_nonneg _, hq _⟩
  · exact D.heavyMass_bounds _

theorem productCoordinate_bounds (hq : ∀ v, D.exteriorCharge v ≤ 1) (e : Fin 10) (y : Fin 75) :
    0 ≤ D.productCoordinate e y ∧ D.productCoordinate e y ≤ 1 := by
  obtain ⟨hy0, hy1⟩ := D.baseCoordinate_bounds hq y
  exact G.subtwoPhysicalPriceProduct_bounds D.price D.price_nonneg D.price_max_pos _ _ hy0 hy1

theorem vector_bounds (hq : ∀ v, D.exteriorCharge v ≤ 1) (k : Fin 970) :
    0 ≤ D.vector k ∧ D.vector k ≤ 1 := by
  unfold vector
  split_ifs
  · exact D.pairPrice_bounds _
  · exact D.bundleCost_bounds _
  · exact ⟨D.exteriorCharge_nonneg _, hq _⟩
  · exact D.heavyMass_bounds _
  · exact D.demandPrice_bounds _
  · exact ⟨(D.avoidingLoss_bounds _).1, (D.avoidingLoss_bounds _).2.trans (hq _)⟩
  · exact (D.bigSmallPrice_bounds _).1
  · exact (D.bigSmallPrice_bounds _).2
  · exact D.productCoordinate_bounds hq _ _

/-- In a constructed rank-two block, the exterior cap follows from its
proved physical boundary bound; it is not an extra coordinate assumption. -/
theorem exteriorCharge_bounds_of_rank_two_block
    (hlocal : G.LocallyPacksInto n) (q : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q = 2)
    (hset : D.vertexSet = G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q)
    (v : Fin 5) :
    0 ≤ D.exteriorCharge v ∧ D.exteriorCharge v ≤ (459155 / 1000000 : ℝ) := by
  have hv : D.vertex v ∈ G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q := by
    rw [← hset]
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
  simpa only [exteriorCharge, hset] using
    G.subtwoFloorFive_exterior_normalized_bounds D.n_pos hlocal q hrank (D.vertex v) hv

theorem vector_bounds_of_rank_two_block
    (hlocal : G.LocallyPacksInto n) (q : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q = 2)
    (hset : D.vertexSet = G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q)
    (k : Fin 970) : 0 ≤ D.vector k ∧ D.vector k ≤ 1 := by
  apply D.vector_bounds
  intro v
  exact (D.exteriorCharge_bounds_of_rank_two_block hlocal q hrank hset v).2.trans (by norm_num)

/-- Every lifted column has the exact true-product meaning used by the
RLT and McCormick soundness lemmas. -/
theorem vector_product (e : Fin 10) (y : Fin 75) :
    D.vector ⟨220 + 75 * e.val + y.val, by omega⟩ = D.pairPrice e * D.baseCoordinate y := by
  change D.vector ⟨220 + 75 * e.val + y.val, by omega⟩ = D.productCoordinate e y
  unfold vector
  dsimp only
  split_ifs <;> try omega
  apply congrArg₂ D.productCoordinate
  · apply Fin.ext
    change (220 + 75 * e.val + y.val - 220) / 75 = e.val
    omega
  · apply Fin.ext
    change (220 + 75 * e.val + y.val - 220) % 75 = y.val
    omega

end SubtwoFivePhysicalData
end
end WeightedEdgeColoring.WeightedMultigraph
