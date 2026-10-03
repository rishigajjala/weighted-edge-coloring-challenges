import WeightedEdgeColoring.SubtwoK6PhysicalBoundaryRows
import WeightedEdgeColoring.SubtwoK6PerfectMatchings

/-! The fifteen actual perfect-matching price rows for a dense five-block. -/

namespace WeightedEdgeColoring.WeightedMultigraph.SubtwoFivePhysicalData

open WeightedEdgeColoring.Subtwo.K6MatchingDeficits
open WeightedEdgeColoring.Subtwo.K6BoundaryRows

universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ} (D : G.SubtwoFivePhysicalData n)

def pairVertices (e : Fin 10) : Finset (Fin 5) :=
  { (frontPair e).1, (frontPair e).2 }

def pairImage (e : Fin 10) : Finset G.V :=
  (pairVertices e).image D.vertex

theorem pairImage_eq (e : Fin 10) :
    D.pairImage e =
      {D.vertex (subtwoFivePair e).1, D.vertex (subtwoFivePair e).2} := by
  have h : frontPair e = subtwoFivePair e := by
    fin_cases e <;> rfl
  simp [pairImage, pairVertices, h]

theorem pairPrice_eq_image (e : Fin 10) :
    D.pairPrice e = G.subtwoNormalizedSetPrice D.price (D.pairImage e) := by
  simp [SubtwoFivePhysicalData.pairPrice, D.pairImage_eq]

private def matchingData : Fin 15 → Fin 5 × Fin 10 × Fin 10 :=
  ![(0,4,9),(0,5,8),(0,6,7),
    (1,1,9),(1,2,8),(1,3,7),
    (2,0,9),(2,2,6),(2,3,5),
    (3,0,8),(3,1,6),(3,3,4),
    (4,0,7),(4,1,5),(4,2,4)]

private theorem matchingData_disjoint : ∀ i : Fin 15,
    Disjoint (pairVertices (matchingData i).2.1)
      (pairVertices (matchingData i).2.2) ∧
    (matchingData i).1 ∉ pairVertices (matchingData i).2.1 ∧
    (matchingData i).1 ∉ pairVertices (matchingData i).2.2 := by
  decide

theorem pairImage_disjoint (e f : Fin 10)
    (h : Disjoint (pairVertices e) (pairVertices f)) :
    Disjoint (D.pairImage e) (D.pairImage f) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hy
  exact (Finset.disjoint_left.mp h) ha (D.vertex_injective heq.symm ▸ hb)

theorem vertex_not_pairImage (e : Fin 10) (v : Fin 5)
    (h : v ∉ pairVertices e) : D.vertex v ∉ D.pairImage e := by
  intro hv
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hv
  exact h (D.vertex_injective heq.symm ▸ ha)

noncomputable def augmentedPrice : Edge → ℝ :=
  ![1-G.subtwoNormalizedAvoidingPrice D.price (D.vertex 0),
    1-G.subtwoNormalizedAvoidingPrice D.price (D.vertex 1),
    1-G.subtwoNormalizedAvoidingPrice D.price (D.vertex 2),
    1-G.subtwoNormalizedAvoidingPrice D.price (D.vertex 3),
    1-G.subtwoNormalizedAvoidingPrice D.price (D.vertex 4),
    D.pairPrice 0,D.pairPrice 1,D.pairPrice 2,D.pairPrice 3,D.pairPrice 4,
    D.pairPrice 5,D.pairPrice 6,D.pairPrice 7,D.pairPrice 8,D.pairPrice 9]

theorem augmentedPrice_nonneg (e : Edge) : 0 ≤ D.augmentedPrice e := by
  fin_cases e <;>
    simp [augmentedPrice, (G.subtwoNormalizedAvoidingPrice_bounds
      D.price D.price_nonneg D.price_max_pos _).2,
      (D.pairPrice_bounds _).1]

private theorem perfect_price_formula (i : Fin 15) :
    (∑ e ∈ perfect i, D.augmentedPrice e) =
      1 - G.subtwoNormalizedAvoidingPrice D.price
        (D.vertex (matchingData i).1) +
        D.pairPrice (matchingData i).2.1 +
        D.pairPrice (matchingData i).2.2 := by
  fin_cases i <;> simp [perfect, matchingData, augmentedPrice] <;> ring

theorem perfect_price_le_one (i : Fin 15) :
    (∑ e ∈ perfect i, D.augmentedPrice e) ≤ 1 := by
  rw [D.perfect_price_formula]
  obtain ⟨hdis, hv1, hv2⟩ := matchingData_disjoint i
  have hprice := G.subtwoNormalizedSetPrice_disjoint_avoiding
    D.price D.price_max_pos
    (D.pairImage (matchingData i).2.1)
    (D.pairImage (matchingData i).2.2)
    (D.pairImage_disjoint _ _ hdis)
    (D.vertex (matchingData i).1)
    (D.vertex_not_pairImage _ _ hv1)
    (D.vertex_not_pairImage _ _ hv2)
  rw [← D.pairPrice_eq_image, ← D.pairPrice_eq_image] at hprice
  linarith

end WeightedEdgeColoring.WeightedMultigraph.SubtwoFivePhysicalData
