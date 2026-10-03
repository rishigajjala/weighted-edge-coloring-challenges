import WeightedEdgeColoring.SubtwoBlockBounds

/-!
# Actual loopless multigraph contraction and exact cost accounting

Contracting a vertex map deletes the edges within its fibers. Every other
edge retains its original index and weight, including parallel edges.
The identities below connect this graph construction to dense-block costs.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- The quotient multigraph, with all internal edges removed. -/
def subtwoQuotient (block : G.V → Q) : WeightedMultigraph.{u} where
  V := Q
  E := {e : G.E // block (G.fst e) ≠ block (G.snd e)}
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := inferInstance
  fst := fun e ↦ block (G.fst e.1)
  snd := fun e ↦ block (G.snd e.1)
  noLoop := fun e ↦ e.2
  weight := fun e ↦ G.weight e.1
  weight_pos := fun e ↦ G.weight_pos e.1
  weight_le_one := fun e ↦ G.weight_le_one e.1

def subtwoFiber (block : G.V → Q) (q : Q) : Finset G.V :=
  Finset.univ.filter fun v ↦ block v = q

def subtwoExpand (block : G.V → Q) (S : Finset Q) : Finset G.V :=
  Finset.univ.filter fun v ↦ block v ∈ S

@[simp] theorem mem_subtwoFiber (block : G.V → Q) (q : Q) (v : G.V) :
    v ∈ G.subtwoFiber block q ↔ block v = q := by simp [subtwoFiber]

@[simp] theorem mem_subtwoExpand (block : G.V → Q) (S : Finset Q) (v : G.V) :
    v ∈ G.subtwoExpand block S ↔ block v ∈ S := by simp [subtwoExpand]

/-- Any sum on retained quotient edges is exactly the corresponding
filtered sum over the original indexed edges. -/
theorem subtwo_sum_quotient_edges (block : G.V → Q) (f : G.E → ℝ) :
    (∑ e : (G.subtwoQuotient block).E, f e.1) =
      ∑ e : G.E, if block (G.fst e) ≠ block (G.snd e) then f e else 0 := by
  classical
  change (∑ e : {e : G.E // block (G.fst e) ≠ block (G.snd e)}, f e.1) = _
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by intro e; simp) f).symm

/-- The quotient degree at a block is precisely the original boundary
cost. Edges within the block do not remain as loops. -/
theorem subtwo_quotient_vertex_cost (block : G.V → Q) (cost : G.E → ℝ) (q : Q) :
    (G.subtwoQuotient block).subtwoVertexCost (fun e ↦ cost e.1) q =
      G.subtwoBoundaryCost cost (G.subtwoFiber block q) := by
  classical
  change (∑ e : (G.subtwoQuotient block).E,
    ((if block (G.fst e.1) = q then cost e.1 else 0) +
      if block (G.snd e.1) = q then cost e.1 else 0)) = _
  rw [G.subtwo_sum_quotient_edges block (fun e ↦
    (if block (G.fst e) = q then cost e else 0) +
      if block (G.snd e) = q then cost e else 0)]
  unfold subtwoBoundaryCost
  apply Finset.sum_congr rfl
  intro e _
  simp only [mem_subtwoFiber]
  by_cases hf : block (G.fst e) = q <;>
    by_cases hs : block (G.snd e) = q
  · simp [hf, hs]
  · have hne : block (G.fst e) ≠ block (G.snd e) := by
      intro heq
      exact hs (heq.symm.trans hf)
    simp [hf, hs, Ne.symm hs]
  · have hne : block (G.fst e) ≠ block (G.snd e) := by
      intro heq
      exact hf (heq.trans hs)
    simp [hf, hs]
  · simp [hf, hs]

/-- Internal quotient cost retains exactly the original crossing pairs. -/
theorem subtwo_quotient_internal_cost (block : G.V → Q)
    (cost : G.E → ℝ) (S : Finset Q) :
    (G.subtwoQuotient block).subtwoInternalCost (fun e ↦ cost e.1) S =
      ∑ e : G.E, if block (G.fst e) ≠ block (G.snd e) ∧
        block (G.fst e) ∈ S ∧ block (G.snd e) ∈ S then cost e else 0 := by
  classical
  change (∑ e : (G.subtwoQuotient block).E,
      if block (G.fst e.1) ∈ S ∧ block (G.snd e.1) ∈ S then cost e.1 else 0) = _
  rw [G.subtwo_sum_quotient_edges block (fun e ↦
    if block (G.fst e) ∈ S ∧ block (G.snd e) ∈ S then cost e else 0)]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp_all

/-- Each collapsed edge is counted in exactly one fiber. -/
theorem subtwo_sum_fiber_internal_cost (block : G.V → Q)
    (cost : G.E → ℝ) (S : Finset Q) :
    (∑ q ∈ S, G.subtwoInternalCost cost (G.subtwoFiber block q)) =
      ∑ e : G.E, if block (G.fst e) = block (G.snd e) ∧
        block (G.fst e) ∈ S then cost e else 0 := by
  classical
  unfold subtwoInternalCost
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp only [mem_subtwoFiber]
  by_cases he : block (G.fst e) = block (G.snd e)
  · simp [← he]
  · have heq (q : Q) : ¬ (block (G.fst e) = q ∧ block (G.snd e) = q) := by
      rintro ⟨hf, hs⟩
      exact he (hf.trans hs.symm)
    simp [he, heq]

/-- Exact expansion identity for any quotient vertex set. -/
theorem subtwo_contraction_internal_identity (block : G.V → Q)
    (cost : G.E → ℝ) (S : Finset Q) :
    G.subtwoInternalCost cost (G.subtwoExpand block S) =
      (G.subtwoQuotient block).subtwoInternalCost (fun e ↦ cost e.1) S +
        ∑ q ∈ S, G.subtwoInternalCost cost (G.subtwoFiber block q) := by
  classical
  rw [G.subtwo_quotient_internal_cost, G.subtwo_sum_fiber_internal_cost]
  unfold subtwoInternalCost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [mem_subtwoExpand]
  by_cases he : block (G.fst e) = block (G.snd e)
  · simp [← he]
  · by_cases hf : block (G.fst e) ∈ S <;>
      by_cases hs : block (G.snd e) ∈ S <;> simp [he, hf, hs]

/-- Expanding a quotient set counts each original vertex in exactly one fiber. -/
theorem subtwo_expand_card (block : G.V → Q) (S : Finset Q) :
    (G.subtwoExpand block S).card =
      ∑ q ∈ S, (G.subtwoFiber block q).card := by
  classical
  have hf (q : Q) : (G.subtwoFiber block q).card =
      ∑ v : G.V, if block v = q then (1 : ℕ) else 0 := by
    simp [subtwoFiber]
  rw [show (∑ q ∈ S, (G.subtwoFiber block q).card) =
      ∑ q ∈ S, ∑ v : G.V, if block v = q then (1 : ℕ) else 0 by
        apply Finset.sum_congr rfl; intro q _; exact hf q]
  rw [Finset.sum_comm]
  simp [subtwoExpand]

/-- If each fiber has size `1+2r`, expansion adds twice the total `r`.
The cases `r=0,1,2` are ordinary vertices, triangles, and five-blocks. -/
theorem subtwo_expand_card_of_fiber_sizes (block : G.V → Q)
    (S : Finset Q) (rank : Q → ℕ)
    (hsize : ∀ q ∈ S, (G.subtwoFiber block q).card = 1 + 2 * rank q) :
    (G.subtwoExpand block S).card = S.card + 2 * ∑ q ∈ S, rank q := by
  rw [G.subtwo_expand_card]
  calc
    (∑ q ∈ S, (G.subtwoFiber block q).card) =
        ∑ q ∈ S, (1 + 2 * rank q) := Finset.sum_congr rfl hsize
    _ = S.card + 2 * ∑ q ∈ S, rank q := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp

/-- Actual quotient degrees inherit any common upper bound on fiber boundaries. -/
theorem subtwo_quotient_degree_le (block : G.V → Q) (cost : G.E → ℝ)
    (M : ℝ) (hboundary : ∀ q, G.subtwoBoundaryCost cost (G.subtwoFiber block q) ≤ M) :
    ∀ q, (G.subtwoQuotient block).subtwoVertexCost (fun e ↦ cost e.1) q ≤ M := by
  intro q
  rw [G.subtwo_quotient_vertex_cost]
  exact hboundary q

end WeightedEdgeColoring.WeightedMultigraph
