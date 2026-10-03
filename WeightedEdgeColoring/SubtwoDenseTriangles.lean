import WeightedEdgeColoring.SubtwoBlockBounds
import Mathlib.Tactic

/-!
# Disjointness of dense triangles

A symmetric nonnegative pair-charge matrix models the pair costs in the
contraction lemma. The proofs below apply to arbitrary finite vertex types.
-/

namespace WeightedEdgeColoring
namespace SubtwoDenseTriangles

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Cost incident with a vertex in a finite pair-charge matrix. -/
def degree (t : V → V → ℝ) (a : V) : ℝ := ∑ x : V, t a x

/-- Cost of the three unordered pairs of a triangle. -/
def triangleCost (t : V → V → ℝ) (a b c : V) : ℝ :=
  t a b + t a c + t b c

/-- A dense triangle is a three-element vertex set with cost above `κ`. -/
def IsDenseTriangle (t : V → V → ℝ) (κ : ℝ) (S : Finset V) : Prop :=
  ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    S = {a, b, c} ∧ κ < triangleCost t a b c

omit [DecidableEq V] in
theorem sum_subset_le_degree (t : V → V → ℝ)
    (hcost : ∀ a b, 0 ≤ t a b) (a : V) (T : Finset V) :
    (∑ x ∈ T, t a x) ≤ degree t a := by
  unfold degree
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (by intro x _ _; exact hcost a x)

omit [Fintype V] [DecidableEq V] in
theorem triangleCost_swap_first (t : V → V → ℝ)
    (hsym : ∀ a b, t a b = t b a) (a b c : V) :
    triangleCost t a b c = triangleCost t b a c := by
  simp [triangleCost, hsym a b, hsym a c, hsym b c]
  ring

omit [Fintype V] [DecidableEq V] in
theorem triangleCost_swap_last (t : V → V → ℝ)
    (hsym : ∀ a b, t a b = t b a) (a b c : V) :
    triangleCost t a b c = triangleCost t a c b := by
  simp [triangleCost, hsym b c]
  ring

/-- Four distinct neighbors contribute at most the full degree. -/
theorem four_pair_costs_le_degree (t : V → V → ℝ)
    (hcost : ∀ x y, 0 ≤ t x y) (a b c d e : V)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    t a b + t a c + t a d + t a e ≤ degree t a := by
  have h := sum_subset_le_degree t hcost a ({b, c, d, e} : Finset V)
  have hsum : t a b + (t a c + (t a d + t a e)) ≤ degree t a := by
    simpa [Finset.sum_insert, hbc, hbd, hbe, hcd, hce, hde] using h
  linarith

/-- Three distinct neighbors contribute at most the full degree. -/
theorem three_pair_costs_le_degree (t : V → V → ℝ)
    (hcost : ∀ x y, 0 ≤ t x y) (a b c d : V)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    t a b + t a c + t a d ≤ degree t a := by
  have h := sum_subset_le_degree t hcost a ({b, c, d} : Finset V)
  have hsum : t a b + (t a c + t a d) ≤ degree t a := by
    simpa [Finset.sum_insert, hbc, hbd, hcd] using h
  linarith

/-- Two dense triangles cannot have exactly one common vertex. -/
theorem dense_triangles_one_shared_vertex (t : V → V → ℝ)
    (hcost : ∀ x y, 0 ≤ t x y)
    (hpair : ∀ x y, t x y ≤ 1)
    (a b c d e : V)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (M κ : ℝ) (hdegree : degree t a ≤ M)
    (hconstant : M + 2 ≤ 2 * κ)
    (hfirst : κ < triangleCost t a b c)
    (hsecond : κ < triangleCost t a d e) : False := by
  have hstar := four_pair_costs_le_degree t hcost a b c d e
    hbc hbd hbe hcd hce hde
  have hbcost := hpair b c
  have hdecost := hpair d e
  unfold triangleCost at hfirst hsecond
  linarith

/-- Two dense triangles cannot share an edge without being identical. -/
theorem dense_triangles_shared_edge (t : V → V → ℝ)
    (hcost : ∀ x y, 0 ≤ t x y)
    (hsym : ∀ x y, t x y = t y x)
    (a b c d : V) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (M κ : ℝ) (hdegreeA : degree t a ≤ M)
    (hdegreeB : degree t b ≤ M) (hconstant : M ≤ κ)
    (hfirst : κ < triangleCost t a b c)
    (hsecond : κ < triangleCost t a b d) : False := by
  have ha := three_pair_costs_le_degree t hcost a b c d
    hbc hbd hcd
  have hb := three_pair_costs_le_degree t hcost b a c d hac had hcd
  unfold triangleCost at hfirst hsecond
  rw [hsym b a] at hb
  linarith

/-- If two dense triangles contain the same named vertex, all their
    other vertices agree as a set. The proof separates one-vertex from
    shared-edge overlap. -/
theorem dense_triangles_same_first (t : V → V → ℝ)
    (hcost : ∀ x y, 0 ≤ t x y) (hpair : ∀ x y, t x y ≤ 1)
    (hsym : ∀ x y, t x y = t y x)
    (a b c d e : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hae : a ≠ e) (hde : d ≠ e)
    (M κ : ℝ) (hdegree : ∀ x, degree t x ≤ M)
    (hone : M + 2 ≤ 2 * κ) (hedge : M ≤ κ)
    (hfirst : κ < triangleCost t a b c)
    (hsecond : κ < triangleCost t a d e) :
    ({a, b, c} : Finset V) = {a, d, e} := by
  by_cases hbd : b = d
  · subst d
    by_cases hce : c = e
    · subst e
      rfl
    · exact False.elim (dense_triangles_shared_edge t hcost hsym
        a b c e hac hae hbc hde hce M κ (hdegree a) (hdegree b)
        hedge hfirst hsecond)
  by_cases hbe : b = e
  · subst e
    by_cases hcd : c = d
    · subst d
      ext x
      simp [or_comm]
    · have hsecond' : κ < triangleCost t a b d := by
        rwa [triangleCost_swap_last t hsym] at hsecond
      exact False.elim (dense_triangles_shared_edge t hcost hsym
        a b c d hac had hbc hde.symm hcd M κ (hdegree a) (hdegree b)
        hedge hfirst hsecond')
  by_cases hcd : c = d
  · subst d
    have hfirst' : κ < triangleCost t a c b := by
      rwa [triangleCost_swap_last t hsym] at hfirst
    by_cases hbe' : b = e
    · exact False.elim (hbe hbe')
    · exact False.elim (dense_triangles_shared_edge t hcost hsym
        a c b e hab hae hbc.symm hde hbe' M κ (hdegree a) (hdegree c)
        hedge hfirst' hsecond)
  by_cases hce : c = e
  · subst e
    have hfirst' : κ < triangleCost t a c b := by
      rwa [triangleCost_swap_last t hsym] at hfirst
    have hsecond' : κ < triangleCost t a c d := by
      rwa [triangleCost_swap_last t hsym] at hsecond
    exact False.elim (dense_triangles_shared_edge t hcost hsym
      a c b d hab had hbc.symm hde.symm hbd M κ (hdegree a) (hdegree c)
      hedge hfirst' hsecond')
  exact False.elim (dense_triangles_one_shared_vertex t hcost hpair
    a b c d e hbc hbd hbe hcd hce hde M κ (hdegree a) hone
    hfirst hsecond)

/-- Recenter a dense triangle at any of its vertices. -/
theorem dense_triangle_recenter (t : V → V → ℝ) (κ : ℝ)
    (hsym : ∀ x y, t x y = t y x)
    {S : Finset V} (hS : IsDenseTriangle t κ S)
    {x : V} (hx : x ∈ S) :
    ∃ b c, x ≠ b ∧ x ≠ c ∧ b ≠ c ∧
      S = {x, b, c} ∧ κ < triangleCost t x b c := by
  rcases hS with ⟨a, b, c, hab, hac, hbc, rfl, hd⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨b, c, hab, hac, hbc, rfl, hd⟩
  · refine ⟨a, c, hab.symm, hbc, hac, ?_, ?_⟩
    · ext y; simp [or_left_comm]
    · rw [triangleCost_swap_first t hsym] at hd
      exact hd
  · refine ⟨a, b, hac.symm, hbc.symm, hab, ?_, ?_⟩
    · ext y; simp [or_comm, or_left_comm]
    · rw [triangleCost_swap_last t hsym,
        triangleCost_swap_first t hsym] at hd
      exact hd

/-- All distinct `κ`-dense triangles are disjoint. -/
theorem dense_triangles_disjoint (t : V → V → ℝ)
    (hcost : ∀ x y, 0 ≤ t x y) (hpair : ∀ x y, t x y ≤ 1)
    (hsym : ∀ x y, t x y = t y x)
    (M κ : ℝ) (hdegree : ∀ x, degree t x ≤ M)
    (hone : M + 2 ≤ 2 * κ) (hedge : M ≤ κ)
    {S T : Finset V} (hS : IsDenseTriangle t κ S)
    (hT : IsDenseTriangle t κ T) (hne : S ≠ T) :
    Disjoint S T := by
  apply Finset.disjoint_left.mpr
  intro x hxS hxT
  rcases dense_triangle_recenter t κ hsym hS hxS with
    ⟨b, c, hxb, hxc, hbc, hSeq, hSdense⟩
  rcases dense_triangle_recenter t κ hsym hT hxT with
    ⟨d, e, hxd, hxe, hde, hTeq, hTdense⟩
  apply hne
  calc
    S = {x, b, c} := hSeq
    _ = {x, d, e} := dense_triangles_same_first t hcost hpair hsym
      x b c d e hxb hxc hbc hxd hxe hde M κ hdegree hone hedge
      hSdense hTdense
    _ = T := hTeq.symm

/-- The dense-triangle disjointness claim at the manuscript's exact
    rational constants `M = 1.691031` and `κ = 1.999`. -/
theorem manuscript_dense_triangles_disjoint (t : V → V → ℝ)
    (hcost : ∀ x y, 0 ≤ t x y) (hpair : ∀ x y, t x y ≤ 1)
    (hsym : ∀ x y, t x y = t y x)
    (hdegree : ∀ x, degree t x ≤ WeightedMultigraph.subtwoM)
    {S T : Finset V}
    (hS : IsDenseTriangle t WeightedMultigraph.subtwoKappa S)
    (hT : IsDenseTriangle t WeightedMultigraph.subtwoKappa T)
    (hne : S ≠ T) : Disjoint S T := by
  apply dense_triangles_disjoint t hcost hpair hsym
    WeightedMultigraph.subtwoM WeightedMultigraph.subtwoKappa
    hdegree
  · unfold WeightedMultigraph.subtwoM WeightedMultigraph.subtwoKappa
    norm_num
  · exact WeightedMultigraph.subtwo_constant_inequalities.2.1.le
  · exact hS
  · exact hT
  · exact hne

end SubtwoDenseTriangles
end WeightedEdgeColoring
