import WeightedEdgeColoring.SubtwoDenseTriangles
import WeightedEdgeColoring.SubtwoDenseFiveSets
import Mathlib.Tactic

/-!
# Selection of dense blocks from indexed edge charges

This module bridges the symmetric pair-cost representation used for dense
triangles to the repository's indexed loopless multigraph representation.
It constructs the first family of all dense triangles and proves disjointness.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- The total charge of indexed edges between two original vertices. -/
def subtwoPairCost (cost : G.E → ℝ) (a b : G.V) : ℝ :=
  ∑ e : G.E,
    if (G.fst e = a ∧ G.snd e = b) ∨
       (G.fst e = b ∧ G.snd e = a) then cost e else 0

theorem subtwoPairCost_symm (cost : G.E → ℝ) (a b : G.V) :
    G.subtwoPairCost cost a b = G.subtwoPairCost cost b a := by
  unfold subtwoPairCost
  apply Finset.sum_congr rfl
  intro e _
  simp only [or_comm]

theorem subtwoPairCost_nonneg (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e) (a b : G.V) :
    0 ≤ G.subtwoPairCost cost a b := by
  unfold subtwoPairCost
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> first | exact hcost e | exact le_refl _

theorem subtwoPairCost_self (cost : G.E → ℝ) (a : G.V) :
    G.subtwoPairCost cost a a = 0 := by
  unfold subtwoPairCost
  apply Finset.sum_eq_zero
  intro e _
  by_cases hf : G.fst e = a
  · by_cases hs : G.snd e = a
    · exact False.elim (G.noLoop e (hf.trans hs.symm))
    · simp [hf, hs]
  · simp [hf]

/-- Pair cost agrees with indexed-edge internal cost on a two-set. -/
theorem subtwoPairCost_eq_two_internal (cost : G.E → ℝ)
    (a b : G.V) (hab : a ≠ b) :
    G.subtwoPairCost cost a b = G.subtwoInternalCost cost {a, b} := by
  classical
  unfold subtwoPairCost subtwoInternalCost
  apply Finset.sum_congr rfl
  intro e _
  have hloop := G.noLoop e
  by_cases hfa : G.fst e = a <;> by_cases hfb : G.fst e = b <;>
    by_cases hsa : G.snd e = a <;> by_cases hsb : G.snd e = b <;>
      simp_all [Finset.mem_insert]

/-- Total pair costs incident with a vertex equal its indexed-edge
    incident cost, so the two density models have the same degree cap. -/
theorem subtwoPairCost_degree (cost : G.E → ℝ) (a : G.V) :
    SubtwoDenseTriangles.degree (G.subtwoPairCost cost) a =
      G.subtwoVertexCost cost a := by
  classical
  unfold SubtwoDenseTriangles.degree subtwoPairCost subtwoVertexCost
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have hloop := G.noLoop e
  by_cases hfa : G.fst e = a
  · have hsa : G.snd e ≠ a := by
      intro h
      exact hloop (hfa.trans h.symm)
    simp [hfa, hsa]
  · by_cases hsa : G.snd e = a
    · simp [hfa, hsa]
    · simp [hfa, hsa]

/-- The triangle's indexed-edge internal charge is exactly the sum
    of its three symmetric pair charges. -/
theorem subtwo_triangle_internal_eq_pair_sum (cost : G.E → ℝ)
    (a b c : G.V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.subtwoInternalCost cost {a, b, c} =
      SubtwoDenseTriangles.triangleCost (G.subtwoPairCost cost) a b c := by
  classical
  unfold subtwoInternalCost SubtwoDenseTriangles.triangleCost subtwoPairCost
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hloop := G.noLoop e
  by_cases hfa : G.fst e = a <;> by_cases hfb : G.fst e = b <;>
    by_cases hfc : G.fst e = c <;> by_cases hsa : G.snd e = a <;>
      by_cases hsb : G.snd e = b <;> by_cases hsc : G.snd e = c <;>
        simp_all [Finset.mem_insert]

/-- The original pair cap implies the symmetric matrix pair cap. -/
theorem subtwoPairCost_le_one (cost : G.E → ℝ)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1) (a b : G.V) :
    G.subtwoPairCost cost a b ≤ 1 := by
  by_cases hab : a = b
  · subst b
    rw [G.subtwoPairCost_self]
    norm_num
  · rw [G.subtwoPairCost_eq_two_internal cost a b hab]
    exact hpair {a, b} (by simp [hab])

/-- Indexed-edge density implies density in the symmetric pair-cost
    model for a three-element set. -/
theorem subtwo_isDenseTriangle_of_internal (cost : G.E → ℝ)
    (κ : ℝ) (S : Finset G.V)
    (hcard : S.card = 3)
    (hdense : κ < G.subtwoInternalCost cost S) :
    SubtwoDenseTriangles.IsDenseTriangle (G.subtwoPairCost cost) κ S := by
  classical
  rcases Finset.card_eq_three.mp hcard with ⟨a, b, c, hab, hac, hbc, rfl⟩
  refine ⟨a, b, c, hab, hac, hbc, rfl, ?_⟩
  simpa only [G.subtwo_triangle_internal_eq_pair_sum cost a b c hab hac hbc]
    using hdense

/-- The finite family of every original `κ`-dense triangle. -/
noncomputable def subtwoDenseTriangles (cost : G.E → ℝ) (κ : ℝ) :
    Finset (Finset G.V) :=
  Finset.univ.filter fun S =>
    S.card = 3 ∧ κ < G.subtwoInternalCost cost S

theorem mem_subtwoDenseTriangles (cost : G.E → ℝ) (κ : ℝ)
    (S : Finset G.V) :
    S ∈ G.subtwoDenseTriangles cost κ ↔
      S.card = 3 ∧ κ < G.subtwoInternalCost cost S := by
  classical
  simp [subtwoDenseTriangles]

/-- The first selection stage is canonical: all original dense triangles
    can be selected simultaneously because they are pairwise disjoint. -/
theorem subtwoDenseTriangles_pairwise_disjoint (cost : G.E → ℝ)
    (M κ : ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ M)
    (hone : M + 2 ≤ 2 * κ) (hedge : M ≤ κ) :
    ∀ S ∈ G.subtwoDenseTriangles cost κ,
      ∀ T ∈ G.subtwoDenseTriangles cost κ,
        S ≠ T → Disjoint S T := by
  intro S hS T hT hne
  have hS' := (G.mem_subtwoDenseTriangles cost κ S).mp hS
  have hT' := (G.mem_subtwoDenseTriangles cost κ T).mp hT
  apply SubtwoDenseTriangles.dense_triangles_disjoint
    (G.subtwoPairCost cost)
    (G.subtwoPairCost_nonneg cost hcost)
    (G.subtwoPairCost_le_one cost hpair)
    (G.subtwoPairCost_symm cost) M κ
  · intro v
    rw [G.subtwoPairCost_degree cost v]
    exact hdegree v
  · exact hone
  · exact hedge
  · exact G.subtwo_isDenseTriangle_of_internal cost κ S hS'.1 hS'.2
  · exact G.subtwo_isDenseTriangle_of_internal cost κ T hT'.1 hT'.2
  · exact hne

/-- Vertices occupied by the first-stage triangle blocks. -/
noncomputable def subtwoTriangleVertices (cost : G.E → ℝ) (κ : ℝ) :
    Finset G.V :=
  (G.subtwoDenseTriangles cost κ).biUnion id

/-- No unused original triangle remains dense after first-stage
    selection. -/
theorem subtwo_unused_triangle_not_dense (cost : G.E → ℝ)
    (κ : ℝ) (S : Finset G.V) (hcard : S.card = 3)
    (hunused : S ⊆ Finset.univ \ G.subtwoTriangleVertices cost κ) :
    G.subtwoInternalCost cost S ≤ κ := by
  by_contra h
  have hdense : κ < G.subtwoInternalCost cost S := lt_of_not_ge h
  have hS : S ∈ G.subtwoDenseTriangles cost κ :=
    (G.mem_subtwoDenseTriangles cost κ S).mpr ⟨hcard, hdense⟩
  have hpos : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hpos
  have hvOcc : v ∈ G.subtwoTriangleVertices cost κ := by
    exact Finset.mem_biUnion.mpr ⟨S, hS, hv⟩
  have hvUnused := hunused hv
  exact (Finset.mem_sdiff.mp hvUnused).2 hvOcc

/-- The ordinary vertices left after the first triangle selection. -/
noncomputable def subtwoOrdinaryAfterTriangles (cost : G.E → ℝ) (κ : ℝ) :
    Finset G.V :=
  Finset.univ \ G.subtwoTriangleVertices cost κ

/-- All dense original five-sets entirely among the unused vertices. -/
noncomputable def subtwoDenseOrdinaryFives (cost : G.E → ℝ) (κ : ℝ) :
    Finset (Finset G.V) :=
  Finset.univ.filter fun S =>
    S.card = 5 ∧ S ⊆ G.subtwoOrdinaryAfterTriangles cost κ ∧
      2 * κ < G.subtwoInternalCost cost S

theorem mem_subtwoDenseOrdinaryFives (cost : G.E → ℝ) (κ : ℝ)
    (S : Finset G.V) :
    S ∈ G.subtwoDenseOrdinaryFives cost κ ↔
      S.card = 5 ∧ S ⊆ G.subtwoOrdinaryAfterTriangles cost κ ∧
        2 * κ < G.subtwoInternalCost cost S := by
  classical
  simp [subtwoDenseOrdinaryFives]

/-- Dense five-sets in a region with no dense triangles are disjoint.
    The only triangle bound used is on the intersection of the two sets. -/
theorem subtwo_dense_fives_disjoint_in_region
    (cost : G.E → ℝ) (U S T : Finset G.V)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (htriangle : ∀ C : Finset G.V, C ⊆ U → C.card = 3 →
      G.subtwoInternalCost cost C ≤ subtwoKappa)
    (hS : S.card = 5) (hT : T.card = 5)
    (hSU : S ⊆ U)
    (hdenseS : 2 * subtwoKappa < G.subtwoInternalCost cost S)
    (hdenseT : 2 * subtwoKappa < G.subtwoInternalCost cost T)
    (hne : S ≠ T) : Disjoint S T := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvS hvT
  have hpos : 1 ≤ (S ∩ T).card :=
    Finset.one_le_card.mpr ⟨v, Finset.mem_inter.mpr ⟨hvS, hvT⟩⟩
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
  · exact G.subtwo_dense_fives_overlap_four_impossible cost S T
      subtwoM subtwoKappa hcost hdegree hS hT hfour hdenseS
      hdenseT subtwo_constant_inequalities.2.1
  · have hcases : (S ∩ T).card = 1 ∨ (S ∩ T).card = 2 ∨
        (S ∩ T).card = 3 := by omega
    have hval := G.subtwo_internal_supermodular cost hcost S T
    have hU := G.subtwo_internal_le_card_mul cost (S ∪ T) subtwoM
      hcost (by intro w _; exact hdegree w)
    have hcard := Finset.card_union_add_card_inter S T
    have hc := subtwo_overlap_constant_inequalities
    rcases hcases with hcase | hcase | hcase
    · have hUcard : (S ∪ T).card = 9 := by omega
      rcases Finset.card_eq_one.mp hcase with ⟨w, hw⟩
      rw [hUcard] at hU
      rw [hw, G.subtwo_internal_singleton] at hval
      norm_num at hU
      linarith only [hval, hU, hdenseS, hdenseT, hc.2.1]
    · have hUcard : (S ∪ T).card = 8 := by omega
      have hI := hpair (S ∩ T) hcase
      rw [hUcard] at hU
      norm_num at hU
      linarith only [hval, hU, hI, hdenseS, hdenseT, hc.2.2.1]
    · have hUcard : (S ∪ T).card = 7 := by omega
      have hI := htriangle (S ∩ T)
        ((Finset.inter_subset_left).trans hSU) hcase
      rw [hUcard] at hU
      norm_num at hU
      linarith only [hval, hU, hI, hdenseS, hdenseT, hc.2.2.2.1]

/-- The dense ordinary five-sets left after selecting all dense
    triangles are pairwise disjoint. -/
theorem subtwoDenseOrdinaryFives_pairwise_disjoint
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1) :
    ∀ S ∈ G.subtwoDenseOrdinaryFives cost subtwoKappa,
      ∀ T ∈ G.subtwoDenseOrdinaryFives cost subtwoKappa,
        S ≠ T → Disjoint S T := by
  intro S hS T hT hne
  have hS' := (G.mem_subtwoDenseOrdinaryFives cost subtwoKappa S).mp hS
  have hT' := (G.mem_subtwoDenseOrdinaryFives cost subtwoKappa T).mp hT
  apply G.subtwo_dense_fives_disjoint_in_region cost
    (G.subtwoOrdinaryAfterTriangles cost subtwoKappa)
    S T hcost hdegree hpair
  · intro C hCU hcard
    exact G.subtwo_unused_triangle_not_dense cost subtwoKappa C hcard hCU
  · exact hS'.1
  · exact hT'.1
  · exact hS'.2.1
  · exact hS'.2.2
  · exact hT'.2.2
  · exact hne

/-- First-stage triangle blocks and later ordinary five-blocks have
    disjoint vertex sets by construction. -/
theorem subtwo_triangle_five_disjoint (cost : G.E → ℝ)
    (S T : Finset G.V)
    (hS : S ∈ G.subtwoDenseTriangles cost subtwoKappa)
    (hT : T ∈ G.subtwoDenseOrdinaryFives cost subtwoKappa) :
    Disjoint S T := by
  apply Finset.disjoint_left.mpr
  intro v hvS hvT
  have hvOcc : v ∈ G.subtwoTriangleVertices cost subtwoKappa :=
    Finset.mem_biUnion.mpr ⟨S, hS, hvS⟩
  have hTordinary := (G.mem_subtwoDenseOrdinaryFives cost subtwoKappa T).mp hT
  have hvOrd := hTordinary.2.1 hvT
  exact (Finset.mem_sdiff.mp hvOrd).2 hvOcc

/-- Vertices occupied by third-stage ordinary dense five-blocks. -/
noncomputable def subtwoFiveVertices (cost : G.E → ℝ) : Finset G.V :=
  (G.subtwoDenseOrdinaryFives cost subtwoKappa).biUnion id

/-- No dense ordinary five-set remains after selecting all such sets. -/
theorem subtwo_unused_five_not_dense (cost : G.E → ℝ)
    (S : Finset G.V) (hcard : S.card = 5)
    (hordinary : S ⊆ G.subtwoOrdinaryAfterTriangles cost subtwoKappa)
    (hunused : S ⊆ Finset.univ \ G.subtwoFiveVertices cost) :
    G.subtwoInternalCost cost S ≤ 2 * subtwoKappa := by
  by_contra h
  have hdense : 2 * subtwoKappa < G.subtwoInternalCost cost S :=
    lt_of_not_ge h
  have hS : S ∈ G.subtwoDenseOrdinaryFives cost subtwoKappa :=
    (G.mem_subtwoDenseOrdinaryFives cost subtwoKappa S).mpr
      ⟨hcard, hordinary, hdense⟩
  have hpos : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hpos
  have hvOcc : v ∈ G.subtwoFiveVertices cost :=
    Finset.mem_biUnion.mpr ⟨S, hS, hv⟩
  exact (Finset.mem_sdiff.mp (hunused hv)).2 hvOcc

end WeightedMultigraph
end WeightedEdgeColoring
