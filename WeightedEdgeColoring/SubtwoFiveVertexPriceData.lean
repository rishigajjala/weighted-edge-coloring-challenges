import WeightedEdgeColoring.SubtwoPriceRelabel
import WeightedEdgeColoring.SubtwoGraphPriceInputs

/-! Actual ten-coordinate bundle prices for a graph with at most five
vertices. Missing vertex labels and missing bundles cause no difficulty. -/

namespace WeightedEdgeColoring.Subtwo.FiveVertexPriceData

open scoped BigOperators
open EndpointPotential TwoModelGeometry

universe u
variable (G : WeightedMultigraph.{u})

noncomputable def bundleCode (label : G.V → Vertex) (hlabel : Function.Injective label)
    (e : G.E) : Bundle :=
  PriceRelabel.pairIndex (label (G.fst e)) (label (G.snd e))
    (fun he ↦ G.noLoop e (hlabel he))

def vertexSet (label : G.V → Vertex) (e : Bundle) : Finset G.V :=
  Finset.univ.filter fun v ↦ label v ∈ edge e

noncomputable def prices (label : G.V → Vertex) (price : G.E → ℝ) : Bundle → ℝ :=
  fun e ↦ G.subtwoSupportedPriceMax (vertexSet G label e) price

theorem vertexSet_bundleCode (label : G.V → Vertex) (hlabel : Function.Injective label)
    (e : G.E) : vertexSet G label (bundleCode G label hlabel e) = {G.fst e, G.snd e} := by
  ext v
  simp only [vertexSet, bundleCode, PriceRelabel.edge_pairIndex, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  exact or_congr hlabel.eq_iff hlabel.eq_iff

theorem prices_bundleCode (label : G.V → Vertex) (hlabel : Function.Injective label)
    (price : G.E → ℝ) (e : G.E) :
    prices G label price (bundleCode G label hlabel e) =
      G.subtwoSupportedPriceMax {G.fst e, G.snd e} price := by
  unfold prices
  rw [vertexSet_bundleCode]

theorem vertexSet_disjoint (label : G.V → Vertex) (e f : Bundle)
    (hdis : Disjoint (edge e) (edge f)) :
    Disjoint (vertexSet G label e) (vertexSet G label f) := by
  apply Finset.disjoint_left.mpr
  intro v he hf
  exact Finset.disjoint_left.mp hdis
    (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2

theorem colorPriceMax_le_one (price : G.E → ℝ)
    (hprice : ∀ p : G.SubtwoWeightedPattern, (∑ e, price e * (p.val e : ℝ)) ≤ 1) :
    G.subtwoColorPriceMax price ≤ 1 := by
  exact hprice (Subtwo.paletteMaximizer G.subtwoReservedColorPattern price none)

theorem prices_nonneg (label : G.V → Vertex) (price : G.E → ℝ)
    (hp : ∀ e, 0 ≤ price e) (e : Bundle) : 0 ≤ prices G label price e :=
  G.subtwoSupportedPriceMax_nonneg _ price hp

theorem prices_le_one (label : G.V → Vertex) (price : G.E → ℝ)
    (hprice : ∀ p : G.SubtwoWeightedPattern, (∑ e, price e * (p.val e : ℝ)) ≤ 1)
    (e : Bundle) : prices G label price e ≤ 1 :=
  (G.subtwoSupportedPriceMax_le _ price).trans (colorPriceMax_le_one G price hprice)

theorem prices_disjoint (label : G.V → Vertex) (price : G.E → ℝ)
    (hprice : ∀ p : G.SubtwoWeightedPattern, (∑ e, price e * (p.val e : ℝ)) ≤ 1)
    (e f : Bundle) (hdis : Disjoint (edge e) (edge f)) :
    prices G label price e + prices G label price f ≤ 1 :=
  (G.subtwo_disjointSupportedPriceMax_add_le _ _ (vertexSet_disjoint G label e f hdis) price).trans
    (colorPriceMax_le_one G price hprice)

theorem exists_injective_label (hV : Fintype.card G.V ≤ 5) :
    ∃ label : G.V → Vertex, Function.Injective label := by
  let label : G.V → Vertex := fun v ↦ Fin.castLE hV ((Fintype.equivFin G.V) v)
  refine ⟨label, ?_⟩
  intro v w h
  apply (Fintype.equivFin G.V).injective
  have hv : (label v).val = (label w).val := congrArg (fun x : Vertex ↦ x.val) h
  exact Fin.ext hv

end WeightedEdgeColoring.Subtwo.FiveVertexPriceData
