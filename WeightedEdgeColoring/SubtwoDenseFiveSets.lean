import WeightedEdgeColoring.SubtwoBlockBounds
import Mathlib.Tactic

/-!
# Overlap bounds for dense five-vertex sets

The internal-cost valuation inequality works directly with indexed edges,
including parallel edges. It is the combinatorial part of the first three
intersection cases in the manuscript's dense-five-set argument.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Internal edge cost is supermodular as a function of the vertex set. -/
theorem subtwo_internal_supermodular (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e) (S T : Finset G.V) :
    G.subtwoInternalCost cost S + G.subtwoInternalCost cost T ≤
      G.subtwoInternalCost cost (S ∪ T) +
        G.subtwoInternalCost cost (S ∩ T) := by
  classical
  unfold subtwoInternalCost
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  by_cases hfs : G.fst e ∈ S <;> by_cases hft : G.fst e ∈ T <;>
    by_cases hss : G.snd e ∈ S <;> by_cases hst : G.snd e ∈ T <;>
    simp [Finset.mem_union, Finset.mem_inter, hfs, hft, hss, hst] <;>
      linarith [hcost e]

/-- Every singleton has zero internal cost in a loopless multigraph. -/
theorem subtwo_internal_singleton (cost : G.E → ℝ) (v : G.V) :
    G.subtwoInternalCost cost {v} = 0 := by
  classical
  unfold subtwoInternalCost
  apply Finset.sum_eq_zero
  intro e _
  simp only [Finset.mem_singleton]
  split_ifs with h
  · exact False.elim (G.noLoop e (h.1.trans h.2.symm))
  · rfl

/-- Degree bound for the internal cost of any original vertex set. -/
theorem subtwo_internal_le_card_mul (cost : G.E → ℝ)
    (S : Finset G.V) (M : ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v ∈ S, G.subtwoVertexCost cost v ≤ M) :
    G.subtwoInternalCost cost S ≤ (S.card : ℝ) * M / 2 := by
  have hi := G.subtwo_internal_le_half_degree cost S hcost
  have hsum : (∑ v ∈ S, G.subtwoVertexCost cost v) ≤ (S.card : ℝ) * M := by
    calc
      _ ≤ ∑ _v ∈ S, M := Finset.sum_le_sum fun v hv => hdegree v hv
      _ = (S.card : ℝ) * M := by simp
  linarith

/-- If two sets differ from a common core by one vertex each,
    their combined internal cost is charged to degrees in the core. -/
theorem subtwo_two_one_vertex_extensions_le_core_degree
    (cost : G.E → ℝ) (C : Finset G.V) (x y : G.V)
    (hcost : ∀ e, 0 ≤ cost e) (hxy : x ≠ y) :
    G.subtwoInternalCost cost (insert x C) +
      G.subtwoInternalCost cost (insert y C) ≤
        ∑ v ∈ C, G.subtwoVertexCost cost v := by
  classical
  rw [G.subtwo_incidence_identity cost C]
  unfold subtwoInternalCost subtwoBoundaryCost
  rw [← Finset.sum_add_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  have hloop := G.noLoop e
  by_cases hfc : G.fst e ∈ C <;> by_cases hsc : G.snd e ∈ C <;>
    by_cases hfx : G.fst e = x <;> by_cases hfy : G.fst e = y <;>
      by_cases hsx : G.snd e = x <;> by_cases hsy : G.snd e = y <;>
        simp_all [Finset.mem_insert] <;> linarith [hcost e]

/-- The four-vertex overlap case: the two unique outside vertices
    force both five-set costs to be charged to four common degrees. -/
theorem subtwo_dense_fives_overlap_four_impossible
    (cost : G.E → ℝ) (S T : Finset G.V) (M κ : ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ M)
    (hS : S.card = 5) (hT : T.card = 5)
    (hinter : (S ∩ T).card = 4)
    (hdenseS : 2 * κ < G.subtwoInternalCost cost S)
    (hdenseT : 2 * κ < G.subtwoInternalCost cost T)
    (hMk : M < κ) : False := by
  classical
  have hSdiff : (S \ T).card = 1 := by
    rw [Finset.card_sdiff]
    rw [Finset.inter_comm T S]
    omega
  have hTdiff : (T \ S).card = 1 := by
    rw [Finset.card_sdiff]
    omega
  rcases Finset.card_eq_one.mp hSdiff with ⟨x, hx⟩
  rcases Finset.card_eq_one.mp hTdiff with ⟨y, hy⟩
  have hSrep : S = insert x (S ∩ T) := by
    ext v
    have hv : (v ∈ S ∧ v ∉ T) ↔ v = x := by
      have hmem : v ∈ S \ T ↔ v = x := by rw [hx]; simp
      simpa only [Finset.mem_sdiff] using hmem
    simp only [Finset.mem_insert, Finset.mem_inter]
    tauto
  have hTrep : T = insert y (S ∩ T) := by
    ext v
    have hv : (v ∈ T ∧ v ∉ S) ↔ v = y := by
      have hmem : v ∈ T \ S ↔ v = y := by rw [hy]; simp
      simpa only [Finset.mem_sdiff] using hmem
    simp only [Finset.mem_insert, Finset.mem_inter]
    tauto
  have hxy : x ≠ y := by
    have hxNotT : x ∉ T := (Finset.mem_sdiff.mp (by rw [hx]; simp)).2
    have hyT : y ∈ T := (Finset.mem_sdiff.mp (by rw [hy]; simp)).1
    intro h
    exact hxNotT (h ▸ hyT)
  have hcore := G.subtwo_two_one_vertex_extensions_le_core_degree
    cost (S ∩ T) x y hcost hxy
  rw [← hSrep, ← hTrep] at hcore
  have hsum : (∑ v ∈ S ∩ T, G.subtwoVertexCost cost v) ≤ 4 * M := by
    calc
      _ ≤ ∑ _v ∈ S ∩ T, M := Finset.sum_le_sum fun v hv => hdegree v
      _ = 4 * M := by simp [hinter]
  linarith

/-- Two `2κ`-dense five-sets cannot overlap in one, two, or three
    vertices when singleton, pair, and triangle intersections obey the
    manuscript's local bounds. -/
theorem subtwo_dense_fives_overlap_at_most_three_impossible
    (cost : G.E → ℝ) (S T : Finset G.V) (M κ : ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ M)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (htriangle : ∀ C : Finset G.V, C.card = 3 →
      G.subtwoInternalCost cost C ≤ κ)
    (hS : S.card = 5) (hT : T.card = 5)
    (hinter : 1 ≤ (S ∩ T).card ∧ (S ∩ T).card ≤ 3)
    (hdenseS : 2 * κ < G.subtwoInternalCost cost S)
    (hdenseT : 2 * κ < G.subtwoInternalCost cost T)
    (hone : 9 * M / 2 < 4 * κ)
    (htwo : 4 * M + 1 < 4 * κ)
    (hthree : 7 * M / 2 + κ < 4 * κ) : False := by
  have hval := G.subtwo_internal_supermodular cost hcost S T
  have hU := G.subtwo_internal_le_card_mul cost (S ∪ T) M hcost
    (by intro v _; exact hdegree v)
  have hcard := Finset.card_union_add_card_inter S T
  have hcases : (S ∩ T).card = 1 ∨ (S ∩ T).card = 2 ∨
      (S ∩ T).card = 3 := by omega
  rcases hcases with hcase | hcase | hcase
  · have hUcard : (S ∪ T).card = 9 := by omega
    rcases Finset.card_eq_one.mp hcase with ⟨v, hv⟩
    rw [hUcard] at hU
    rw [hv, G.subtwo_internal_singleton] at hval
    norm_num at hU
    linarith only [hval, hU, hdenseS, hdenseT, hone]
  · have hUcard : (S ∪ T).card = 8 := by omega
    have hI := hpair (S ∩ T) hcase
    rw [hUcard] at hU
    norm_num at hU
    linarith only [hval, hU, hI, hdenseS, hdenseT, htwo]
  · have hUcard : (S ∪ T).card = 7 := by omega
    have hI := htriangle (S ∩ T) hcase
    rw [hUcard] at hU
    norm_num at hU
    linarith only [hval, hU, hI, hdenseS, hdenseT, hthree]

/-- The first three five-set overlap cases at the exact manuscript
    constants. -/
theorem subtwo_manuscript_dense_fives_overlap_at_most_three_impossible
    (cost : G.E → ℝ) (S T : Finset G.V)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (htriangle : ∀ C : Finset G.V, C.card = 3 →
      G.subtwoInternalCost cost C ≤ subtwoKappa)
    (hS : S.card = 5) (hT : T.card = 5)
    (hinter : 1 ≤ (S ∩ T).card ∧ (S ∩ T).card ≤ 3)
    (hdenseS : 2 * subtwoKappa < G.subtwoInternalCost cost S)
    (hdenseT : 2 * subtwoKappa < G.subtwoInternalCost cost T) : False := by
  have hc := subtwo_overlap_constant_inequalities
  exact G.subtwo_dense_fives_overlap_at_most_three_impossible cost S T
    subtwoM subtwoKappa hcost hdegree hpair htriangle hS hT hinter
    hdenseS hdenseT hc.2.1 hc.2.2.1 hc.2.2.2.1

/-- Distinct dense five-sets are disjoint once every uncontracted
    triangle is below `κ` and every original pair is at most one. -/
theorem subtwo_dense_fives_disjoint
    (cost : G.E → ℝ) (S T : Finset G.V) (M κ : ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ M)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (htriangle : ∀ C : Finset G.V, C.card = 3 →
      G.subtwoInternalCost cost C ≤ κ)
    (hS : S.card = 5) (hT : T.card = 5)
    (hdenseS : 2 * κ < G.subtwoInternalCost cost S)
    (hdenseT : 2 * κ < G.subtwoInternalCost cost T)
    (hne : S ≠ T)
    (hone : 9 * M / 2 < 4 * κ)
    (htwo : 4 * M + 1 < 4 * κ)
    (hthree : 7 * M / 2 + κ < 4 * κ)
    (hMk : M < κ) : Disjoint S T := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvS hvT
  have hpos : 1 ≤ (S ∩ T).card := by
    exact Finset.one_le_card.mpr ⟨v, Finset.mem_inter.mpr ⟨hvS, hvT⟩⟩
  have hle : (S ∩ T).card ≤ 5 := by
    calc
      _ ≤ S.card := Finset.card_le_card Finset.inter_subset_left
      _ = 5 := hS
  have hnot5 : (S ∩ T).card ≠ 5 := by
    intro hfive
    have hEqS : S ∩ T = S :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hEqT : S ∩ T = T :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hne (hEqS.symm.trans hEqT)
  by_cases hfour : (S ∩ T).card = 4
  · exact G.subtwo_dense_fives_overlap_four_impossible cost S T M κ
      hcost hdegree hS hT hfour hdenseS hdenseT hMk
  · exact G.subtwo_dense_fives_overlap_at_most_three_impossible
      cost S T M κ hcost hdegree hpair htriangle hS hT
      ⟨hpos, by omega⟩ hdenseS hdenseT hone htwo hthree

/-- Pairwise disjointness of the manuscript's ordinary dense five-sets,
    with exact rational constants. -/
theorem subtwo_manuscript_dense_fives_disjoint
    (cost : G.E → ℝ) (S T : Finset G.V)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (htriangle : ∀ C : Finset G.V, C.card = 3 →
      G.subtwoInternalCost cost C ≤ subtwoKappa)
    (hS : S.card = 5) (hT : T.card = 5)
    (hdenseS : 2 * subtwoKappa < G.subtwoInternalCost cost S)
    (hdenseT : 2 * subtwoKappa < G.subtwoInternalCost cost T)
    (hne : S ≠ T) : Disjoint S T := by
  have hc := subtwo_overlap_constant_inequalities
  have hMk := subtwo_constant_inequalities.2.1
  exact G.subtwo_dense_fives_disjoint cost S T subtwoM subtwoKappa
    hcost hdegree hpair htriangle hS hT hdenseS hdenseT hne
    hc.2.1 hc.2.2.1 hc.2.2.2.1 hMk

end WeightedMultigraph
end WeightedEdgeColoring
