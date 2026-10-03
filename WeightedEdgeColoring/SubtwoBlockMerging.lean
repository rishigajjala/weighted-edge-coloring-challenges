import WeightedEdgeColoring.SubtwoContraction
import WeightedEdgeColoring.SubtwoDenseFiveSets
import Mathlib.Tactic

/-!
# Second-stage dense quotient triangles

After dense original triangles are contracted, a new dense quotient
triangle can contain one old triangle block and two ordinary vertices.
The lemmas here begin the overlap audit in the actual quotient graph.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Two dense triangles cannot share a quotient edge under the
    `M < κ` degree cap. This does not require a one-pair cap. -/
theorem subtwo_dense_triangles_shared_edge_impossible
    (cost : G.E → ℝ) (S T : Finset G.V) (M κ : ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ M)
    (hS : S.card = 3) (hT : T.card = 3)
    (hinter : (S ∩ T).card = 2)
    (hdenseS : κ < G.subtwoInternalCost cost S)
    (hdenseT : κ < G.subtwoInternalCost cost T)
    (hMk : M ≤ κ) : False := by
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
  have hsum : (∑ v ∈ S ∩ T, G.subtwoVertexCost cost v) ≤ 2 * M := by
    calc
      _ ≤ ∑ _v ∈ S ∩ T, M := Finset.sum_le_sum fun v hv => hdegree v
      _ = 2 * M := by simp [hinter]
  linarith

/-- Nonnegative original edge charges give nonnegative internal
    charge in every contraction fiber. -/
theorem subtwo_fiber_internal_nonneg {Q : Type u} [Fintype Q]
    [DecidableEq Q] (block : G.V → Q) (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e) (q : Q) :
    0 ≤ G.subtwoInternalCost cost (G.subtwoFiber block q) := by
  unfold subtwoInternalCost
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> first | exact hcost e | exact le_refl _

/-- A dense quotient triangle with exactly one old three-block expands
    to a dense five-set in the original indexed graph. -/
theorem subtwo_dense_quotient_triangle_lifts_to_five
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (block : G.V → Q) (rank : Q → ℕ) (cost : G.E → ℝ)
    (S : Finset Q) (κ : ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hsize : ∀ q ∈ S,
      (G.subtwoFiber block q).card = 1 + 2 * rank q)
    (hDenseFiber : ∀ q ∈ S, rank q = 1 →
      κ < G.subtwoInternalCost cost (G.subtwoFiber block q))
    (hScard : S.card = 3)
    (hRank : (∑ q ∈ S, rank q) = 1)
    (hDenseQuot : κ <
      (G.subtwoQuotient block).subtwoInternalCost
        (fun e => cost e.1) S) :
    (G.subtwoExpand block S).card = 5 ∧
      2 * κ < G.subtwoInternalCost cost (G.subtwoExpand block S) := by
  classical
  have hcard := G.subtwo_expand_card_of_fiber_sizes block S rank hsize
  have hcard5 : (G.subtwoExpand block S).card = 5 := by
    rw [hScard, hRank] at hcard
    omega
  have hpos : 0 < ∑ q ∈ S, rank q := by omega
  obtain ⟨q, hqS, hqPos⟩ := Finset.sum_pos_iff.mp hpos
  have hqLe : rank q ≤ 1 := by
    have h := Finset.single_le_sum (fun q _ => Nat.zero_le (rank q)) hqS
    omega
  have hqRank : rank q = 1 := by omega
  have hFiberDense := hDenseFiber q hqS hqRank
  have hFiberSum : G.subtwoInternalCost cost (G.subtwoFiber block q) ≤
      ∑ r ∈ S, G.subtwoInternalCost cost (G.subtwoFiber block r) := by
    exact Finset.single_le_sum
      (fun r _ => G.subtwo_fiber_internal_nonneg block cost hcost r) hqS
  have hidentity := G.subtwo_contraction_internal_identity block cost S
  constructor
  · exact hcard5
  · linarith

/-- Two dense quotient triangles cannot meet only at an ordinary
    quotient vertex: their original five-set lifts would overlap in one
    vertex and force more than `4κ` cost on nine original vertices. -/
theorem subtwo_dense_quotient_triangles_shared_ordinary_impossible
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (block : G.V → Q) (rank : Q → ℕ) (cost : G.E → ℝ)
    (S T : Finset Q) (q : Q)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (hsize : ∀ r ∈ S ∪ T,
      (G.subtwoFiber block r).card = 1 + 2 * rank r)
    (hDenseFiber : ∀ r ∈ S ∪ T, rank r = 1 →
      subtwoKappa < G.subtwoInternalCost cost (G.subtwoFiber block r))
    (hScard : S.card = 3) (hTcard : T.card = 3)
    (hSrank : (∑ r ∈ S, rank r) = 1)
    (hTrank : (∑ r ∈ T, rank r) = 1)
    (hinter : S ∩ T = {q}) (hqrank : rank q = 0)
    (hdenseS : subtwoKappa <
      (G.subtwoQuotient block).subtwoInternalCost
        (fun e => cost e.1) S)
    (hdenseT : subtwoKappa <
      (G.subtwoQuotient block).subtwoInternalCost
        (fun e => cost e.1) T) : False := by
  classical
  have hqS : q ∈ S := (Finset.mem_inter.mp (by rw [hinter]; simp)).1
  have hqT : q ∈ T := (Finset.mem_inter.mp (by rw [hinter]; simp)).2
  have hSsize : ∀ r ∈ S,
      (G.subtwoFiber block r).card = 1 + 2 * rank r := by
    intro r hr
    exact hsize r (Finset.mem_union.mpr (Or.inl hr))
  have hTsize : ∀ r ∈ T,
      (G.subtwoFiber block r).card = 1 + 2 * rank r := by
    intro r hr
    exact hsize r (Finset.mem_union.mpr (Or.inr hr))
  have hSdenseFiber : ∀ r ∈ S, rank r = 1 →
      subtwoKappa < G.subtwoInternalCost cost (G.subtwoFiber block r) := by
    intro r hr hRank
    exact hDenseFiber r (Finset.mem_union.mpr (Or.inl hr)) hRank
  have hTdenseFiber : ∀ r ∈ T, rank r = 1 →
      subtwoKappa < G.subtwoInternalCost cost (G.subtwoFiber block r) := by
    intro r hr hRank
    exact hDenseFiber r (Finset.mem_union.mpr (Or.inr hr)) hRank
  have hLiftS := G.subtwo_dense_quotient_triangle_lifts_to_five block rank
    cost S subtwoKappa hcost hSsize hSdenseFiber hScard hSrank hdenseS
  have hLiftT := G.subtwo_dense_quotient_triangle_lifts_to_five block rank
    cost T subtwoKappa hcost hTsize hTdenseFiber hTcard hTrank hdenseT
  have hqcard : (S ∩ T).card = 1 := by rw [hinter]; simp
  have hcardUnionQ : (S ∪ T).card = 5 := by
    have h := Finset.card_union_add_card_inter S T
    omega
  have hsumRank : (∑ r ∈ S ∪ T, rank r) = 2 := by
    have h := Finset.sum_union_inter (s₁ := S) (s₂ := T) (f := rank)
    rw [hinter] at h
    simp [hqrank, hSrank, hTrank] at h
    omega
  have hcardUnion := G.subtwo_expand_card_of_fiber_sizes block
    (S ∪ T) rank hsize
  have hExpUnionCard : (G.subtwoExpand block (S ∪ T)).card = 9 := by
    rw [hcardUnionQ, hsumRank] at hcardUnion
    omega
  have hExpInterCard : (G.subtwoExpand block (S ∩ T)).card = 1 := by
    rw [hinter]
    have hcard := G.subtwo_expand_card block ({q} : Finset Q)
    simpa [G.mem_subtwoFiber, hsize q
      (Finset.mem_union.mpr (Or.inl hqS)), hqrank] using hcard
  have hExpUnion : G.subtwoExpand block S ∪ G.subtwoExpand block T =
      G.subtwoExpand block (S ∪ T) := by
    ext v
    simp [Finset.mem_union]
  have hExpInter : G.subtwoExpand block S ∩ G.subtwoExpand block T =
      G.subtwoExpand block (S ∩ T) := by
    ext v
    simp [Finset.mem_inter]
  have hVal := G.subtwo_internal_supermodular cost hcost
    (G.subtwoExpand block S) (G.subtwoExpand block T)
  rw [hExpUnion, hExpInter] at hVal
  rcases Finset.card_eq_one.mp hExpInterCard with ⟨v, hv⟩
  rw [hv, G.subtwo_internal_singleton] at hVal
  have hUnionBound := G.subtwo_internal_le_card_mul cost
    (G.subtwoExpand block (S ∪ T)) subtwoM hcost
    (by intro v _; exact hdegree v)
  rw [hExpUnionCard] at hUnionBound
  have hconstant := subtwo_overlap_constant_inequalities.2.1
  norm_num at hUnionBound
  linarith only [hVal, hUnionBound, hLiftS.2, hLiftT.2, hconstant]

/-- Two dense quotient triangles cannot meet only at the same old
    three-block: their seven original vertices would carry more than
    `3κ` internal cost. -/
theorem subtwo_dense_quotient_triangles_shared_block_impossible
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (block : G.V → Q) (rank : Q → ℕ) (cost : G.E → ℝ)
    (S T : Finset Q) (q : Q)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (hsize : ∀ r ∈ S ∪ T,
      (G.subtwoFiber block r).card = 1 + 2 * rank r)
    (hDenseFiber : ∀ r ∈ S ∪ T, rank r = 1 →
      subtwoKappa < G.subtwoInternalCost cost (G.subtwoFiber block r))
    (hScard : S.card = 3) (hTcard : T.card = 3)
    (hSrank : (∑ r ∈ S, rank r) = 1)
    (hTrank : (∑ r ∈ T, rank r) = 1)
    (hinter : S ∩ T = {q}) (hqrank : rank q = 1)
    (hdenseS : subtwoKappa <
      (G.subtwoQuotient block).subtwoInternalCost
        (fun e => cost e.1) S)
    (hdenseT : subtwoKappa <
      (G.subtwoQuotient block).subtwoInternalCost
        (fun e => cost e.1) T) : False := by
  classical
  have hqS : q ∈ S := (Finset.mem_inter.mp (by rw [hinter]; simp)).1
  have hqUnion : q ∈ S ∪ T := Finset.mem_union.mpr (Or.inl hqS)
  have hqcard : (S ∩ T).card = 1 := by rw [hinter]; simp
  have hcardUnionQ : (S ∪ T).card = 5 := by
    have h := Finset.card_union_add_card_inter S T
    omega
  have hsumRank : (∑ r ∈ S ∪ T, rank r) = 1 := by
    have h := Finset.sum_union_inter (s₁ := S) (s₂ := T) (f := rank)
    rw [hinter] at h
    simp [hqrank, hSrank, hTrank] at h
    omega
  have hcardUnion := G.subtwo_expand_card_of_fiber_sizes block
    (S ∪ T) rank hsize
  have hExpUnionCard : (G.subtwoExpand block (S ∪ T)).card = 7 := by
    rw [hcardUnionQ, hsumRank] at hcardUnion
    omega
  have hQuotVal := (G.subtwoQuotient block).subtwo_internal_supermodular
    (fun e => cost e.1) (fun e => hcost e.1) S T
  rcases Finset.card_eq_one.mp hqcard with ⟨r, hr⟩
  have hqEq : r = q := by
    have : ({r} : Finset Q) = {q} := hr.symm.trans hinter
    simpa using this
  subst r
  rw [hinter, (G.subtwoQuotient block).subtwo_internal_singleton] at hQuotVal
  have hFiber := hDenseFiber q hqUnion hqrank
  have hFiberSum : G.subtwoInternalCost cost (G.subtwoFiber block q) ≤
      ∑ r ∈ S ∪ T, G.subtwoInternalCost cost (G.subtwoFiber block r) := by
    exact Finset.single_le_sum
      (fun r _ => G.subtwo_fiber_internal_nonneg block cost hcost r) hqUnion
  have hidentity := G.subtwo_contraction_internal_identity block cost (S ∪ T)
  have hUnionBound := G.subtwo_internal_le_card_mul cost
    (G.subtwoExpand block (S ∪ T)) subtwoM hcost
    (by intro v _; exact hdegree v)
  rw [hExpUnionCard] at hUnionBound
  have hconstant := subtwo_constant_inequalities.2.2.2
  norm_num at hUnionBound
  linarith only [hQuotVal, hFiber, hFiberSum, hidentity,
    hUnionBound, hconstant, hdenseS, hdenseT]

/-- After the original dense triangles are contracted, every quotient
    vertex still has degree at most `M`: singleton fibers inherit their
    original degree, and triangle fibers satisfy the strict boundary bound. -/
theorem subtwo_first_quotient_degree_le
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (block : G.V → Q) (rank : Q → ℕ) (cost : G.E → ℝ)
    (hsize : ∀ q, (G.subtwoFiber block q).card = 1 + 2 * rank q)
    (hrank : ∀ q, rank q ≤ 1)
    (hDenseFiber : ∀ q, rank q = 1 →
      subtwoKappa < G.subtwoInternalCost cost (G.subtwoFiber block q))
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM) :
    ∀ q, (G.subtwoQuotient block).subtwoVertexCost
      (fun e => cost e.1) q ≤ subtwoM := by
  intro q
  rw [G.subtwo_quotient_vertex_cost]
  by_cases hzero : rank q = 0
  · have hcard : (G.subtwoFiber block q).card = 1 := by
      simpa [hzero] using hsize q
    rcases Finset.card_eq_one.mp hcard with ⟨v, hv⟩
    rw [hv]
    have hsingle := G.subtwo_incidence_identity cost ({v} : Finset G.V)
    have hboundary : G.subtwoBoundaryCost cost {v} =
        G.subtwoVertexCost cost v := by
      simpa [G.subtwo_internal_singleton] using hsingle.symm
    rw [hboundary]
    exact hdegree v
  · have hone : rank q = 1 := by
      have hr := hrank q
      omega
    have hcard : (G.subtwoFiber block q).card = 3 := by
      simpa [hone] using hsize q
    have hb := G.subtwo_triangle_boundary_lt cost
      (G.subtwoFiber block q) subtwoM subtwoKappa
      hcard (by intro v _; exact hdegree v) (hDenseFiber q hone)
    have hMk := subtwo_constant_inequalities.2.1
    linarith

/-- All distinct second-stage dense quotient triangles, each with one
    old three-block, are disjoint. Shared edges are excluded by quotient
    degrees; a single shared ordinary vertex gives a nine-vertex
    contradiction, and a single shared block gives a seven-vertex one. -/
theorem subtwo_middle_dense_triangles_disjoint
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (block : G.V → Q) (rank : Q → ℕ) (cost : G.E → ℝ)
    (S T : Finset Q)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (hsize : ∀ q,
      (G.subtwoFiber block q).card = 1 + 2 * rank q)
    (hrank : ∀ q, rank q ≤ 1)
    (hDenseFiber : ∀ q, rank q = 1 →
      subtwoKappa < G.subtwoInternalCost cost (G.subtwoFiber block q))
    (hScard : S.card = 3) (hTcard : T.card = 3)
    (hSrank : (∑ q ∈ S, rank q) = 1)
    (hTrank : (∑ q ∈ T, rank q) = 1)
    (hdenseS : subtwoKappa <
      (G.subtwoQuotient block).subtwoInternalCost
        (fun e => cost e.1) S)
    (hdenseT : subtwoKappa <
      (G.subtwoQuotient block).subtwoInternalCost
        (fun e => cost e.1) T)
    (hne : S ≠ T) : Disjoint S T := by
  classical
  let H := G.subtwoQuotient block
  have hQdegree := G.subtwo_first_quotient_degree_le
    block rank cost hsize hrank hDenseFiber hdegree
  apply Finset.disjoint_left.mpr
  intro q hqS hqT
  have hpos : 1 ≤ (S ∩ T).card :=
    Finset.one_le_card.mpr ⟨q, Finset.mem_inter.mpr ⟨hqS, hqT⟩⟩
  have hle : (S ∩ T).card ≤ 3 := by
    calc
      _ ≤ S.card := Finset.card_le_card Finset.inter_subset_left
      _ = 3 := hScard
  have hnot3 : (S ∩ T).card ≠ 3 := by
    intro hthree
    have hEqS : S ∩ T = S :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hEqT : S ∩ T = T :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hne (hEqS.symm.trans hEqT)
  by_cases htwo : (S ∩ T).card = 2
  · exact H.subtwo_dense_triangles_shared_edge_impossible
      (fun e => cost e.1) S T subtwoM subtwoKappa
      (fun e => hcost e.1) hQdegree hScard hTcard htwo
      hdenseS hdenseT subtwo_constant_inequalities.2.1.le
  · have hone : (S ∩ T).card = 1 := by omega
    rcases Finset.card_eq_one.mp hone with ⟨r, hr⟩
    have hsizeUnion : ∀ p ∈ S ∪ T,
        (G.subtwoFiber block p).card = 1 + 2 * rank p := by
      intro p _
      exact hsize p
    have hDenseUnion : ∀ p ∈ S ∪ T, rank p = 1 →
        subtwoKappa < G.subtwoInternalCost cost (G.subtwoFiber block p) := by
      intro p _ hp
      exact hDenseFiber p hp
    by_cases hr0 : rank r = 0
    · exact G.subtwo_dense_quotient_triangles_shared_ordinary_impossible
        block rank cost S T r hcost hdegree hsizeUnion hDenseUnion
        hScard hTcard hSrank hTrank hr hr0 hdenseS hdenseT
    · have hr1 : rank r = 1 := by
        have hleRank := hrank r
        omega
      exact G.subtwo_dense_quotient_triangles_shared_block_impossible
        block rank cost S T r hcost hdegree hsizeUnion hDenseUnion
        hScard hTcard hSrank hTrank hr hr1 hdenseS hdenseT

/-- The canonical family of all dense quotient triangles containing
    exactly one previously contracted three-block. -/
noncomputable def subtwoMiddleDenseTriangles
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (block : G.V → Q) (rank : Q → ℕ) (cost : G.E → ℝ) :
    Finset (Finset Q) :=
  Finset.univ.filter fun S =>
    S.card = 3 ∧ (∑ q ∈ S, rank q) = 1 ∧
      subtwoKappa <
        (G.subtwoQuotient block).subtwoInternalCost
          (fun e => cost e.1) S

theorem mem_subtwoMiddleDenseTriangles
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (block : G.V → Q) (rank : Q → ℕ) (cost : G.E → ℝ)
    (S : Finset Q) :
    S ∈ G.subtwoMiddleDenseTriangles block rank cost ↔
      S.card = 3 ∧ (∑ q ∈ S, rank q) = 1 ∧
        subtwoKappa <
          (G.subtwoQuotient block).subtwoInternalCost
            (fun e => cost e.1) S := by
  classical
  simp [subtwoMiddleDenseTriangles]

/-- The entire finite middle-stage family can be contracted at once. -/
theorem subtwoMiddleDenseTriangles_pairwise_disjoint
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (block : G.V → Q) (rank : Q → ℕ) (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (hsize : ∀ q,
      (G.subtwoFiber block q).card = 1 + 2 * rank q)
    (hrank : ∀ q, rank q ≤ 1)
    (hDenseFiber : ∀ q, rank q = 1 →
      subtwoKappa < G.subtwoInternalCost cost (G.subtwoFiber block q)) :
    ∀ S ∈ G.subtwoMiddleDenseTriangles block rank cost,
      ∀ T ∈ G.subtwoMiddleDenseTriangles block rank cost,
        S ≠ T → Disjoint S T := by
  intro S hS T hT hne
  have hS' := (G.mem_subtwoMiddleDenseTriangles block rank cost S).mp hS
  have hT' := (G.mem_subtwoMiddleDenseTriangles block rank cost T).mp hT
  exact G.subtwo_middle_dense_triangles_disjoint block rank cost S T
    hcost hdegree hsize hrank hDenseFiber hS'.1 hT'.1
    hS'.2.1 hT'.2.1 hS'.2.2 hT'.2.2 hne

/-- Every selected middle-stage quotient triangle becomes a dense
    five-vertex block in the original graph. -/
theorem subtwoMiddleDenseTriangles_lift
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (block : G.V → Q) (rank : Q → ℕ) (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hsize : ∀ q,
      (G.subtwoFiber block q).card = 1 + 2 * rank q)
    (hDenseFiber : ∀ q, rank q = 1 →
      subtwoKappa < G.subtwoInternalCost cost (G.subtwoFiber block q))
    (S : Finset Q) (hS : S ∈ G.subtwoMiddleDenseTriangles block rank cost) :
    (G.subtwoExpand block S).card = 5 ∧
      2 * subtwoKappa <
        G.subtwoInternalCost cost (G.subtwoExpand block S) := by
  have h := (G.mem_subtwoMiddleDenseTriangles block rank cost S).mp hS
  exact G.subtwo_dense_quotient_triangle_lifts_to_five block rank cost S
    subtwoKappa hcost (by intro q _; exact hsize q)
    (by intro q _ hr; exact hDenseFiber q hr)
    h.1 h.2.1 h.2.2

/-- Disjoint selected quotient triangles expand to disjoint original
    five-blocks. -/
theorem subtwoMiddleDenseTriangles_expansions_disjoint
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (block : G.V → Q) (rank : Q → ℕ) (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (hsize : ∀ q,
      (G.subtwoFiber block q).card = 1 + 2 * rank q)
    (hrank : ∀ q, rank q ≤ 1)
    (hDenseFiber : ∀ q, rank q = 1 →
      subtwoKappa < G.subtwoInternalCost cost (G.subtwoFiber block q))
    (S T : Finset Q)
    (hS : S ∈ G.subtwoMiddleDenseTriangles block rank cost)
    (hT : T ∈ G.subtwoMiddleDenseTriangles block rank cost)
    (hne : S ≠ T) :
    Disjoint (G.subtwoExpand block S) (G.subtwoExpand block T) := by
  have hdis := G.subtwoMiddleDenseTriangles_pairwise_disjoint
    block rank cost hcost hdegree hsize hrank hDenseFiber
    S hS T hT hne
  apply Finset.disjoint_left.mpr
  intro v hvS hvT
  have hbs : block v ∈ S := (G.mem_subtwoExpand block S v).mp hvS
  have hbt : block v ∈ T := (G.mem_subtwoExpand block T v).mp hvT
  exact (Finset.disjoint_left.mp hdis) hbs hbt

end WeightedMultigraph
end WeightedEdgeColoring
