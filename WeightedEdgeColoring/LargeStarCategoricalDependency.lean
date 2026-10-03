import WeightedEdgeColoring.TinyEdgeRounding
import WeightedEdgeColoring.FiniteCategoricalSelection

/-!
# Large-star bounds and local categorical dependencies

After edges below a fixed threshold are reserved for deterministic rounding,
only the remaining large edges enter profile synchronization.  This file
records the elementary bound on their number and the generic support-overlap
count used by an ordinary categorical local lemma.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})

/-- Edges at a vertex whose weight is at least `beta`. -/
def largeStarEdges (beta : ℝ) (v : G.V) : Finset (G.StarEdge v) :=
  Finset.univ.filter fun e ↦ beta ≤ G.weight e.1

@[simp] theorem mem_largeStarEdges {beta : ℝ} {v : G.V} {e : G.StarEdge v} :
    e ∈ G.largeStarEdges beta v ↔ beta ≤ G.weight e.1 := by
  simp [largeStarEdges]

/-- The number of `beta`-large edges times `beta` is at most the star load. -/
theorem largeStarEdges_card_mul_beta_le_starWeight
    (beta : ℝ) (v : G.V) :
    ((G.largeStarEdges beta v).card : ℝ) * beta ≤ G.starWeight v := by
  calc
    ((G.largeStarEdges beta v).card : ℝ) * beta =
        ∑ _e ∈ G.largeStarEdges beta v, beta := by simp
    _ ≤ ∑ e ∈ G.largeStarEdges beta v, G.weight e.1 := by
      apply Finset.sum_le_sum
      intro e he
      exact (G.mem_largeStarEdges).mp he
    _ ≤ ∑ e : G.StarEdge v, G.weight e.1 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun _ _ ↦ Finset.mem_univ _)
        (fun e _ _ ↦ G.weight_nonneg e.1)
    _ = G.starWeight v := rfl

/-- Under an `n`-bin local packing, a star has weighted large-edge count at
most `n / beta`. -/
theorem largeStarEdges_card_le_div_of_locallyPacksInto
    {n : ℕ} (hlocal : G.LocallyPacksInto n)
    {beta : ℝ} (hbeta : 0 < beta) (v : G.V) :
    ((G.largeStarEdges beta v).card : ℝ) ≤ (n : ℝ) / beta := by
  apply (le_div_iff₀ hbeta).2
  exact (G.largeStarEdges_card_mul_beta_le_starWeight beta v).trans
    (G.starWeight_le_of_locallyPacksInto hlocal v)

/-- Natural-number form: any `K` with `n < (K+1) beta` bounds the number of
large edges at every star by `K`. -/
theorem largeStarEdges_card_le_of_locallyPacksInto
    {n K : ℕ} (hlocal : G.LocallyPacksInto n)
    {beta : ℝ} (hbeta : 0 < beta)
    (hK : (n : ℝ) < ((K + 1 : ℕ) : ℝ) * beta)
    (v : G.V) :
    (G.largeStarEdges beta v).card ≤ K := by
  by_contra hnot
  have hKcard : K + 1 ≤ (G.largeStarEdges beta v).card := by omega
  have hcast : ((K + 1 : ℕ) : ℝ) ≤
      ((G.largeStarEdges beta v).card : ℝ) := by
    exact_mod_cast hKcard
  have hmul : ((K + 1 : ℕ) : ℝ) * beta ≤
      ((G.largeStarEdges beta v).card : ℝ) * beta :=
    mul_le_mul_of_nonneg_right hcast hbeta.le
  have hstar := G.largeStarEdges_card_mul_beta_le_starWeight beta v
  have hn := G.starWeight_le_of_locallyPacksInto hlocal v
  linarith

end WeightedSimpleGraph

namespace FiniteCategoricalSelection

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- Rows whose bad events can read a given categorical source. -/
def rowSupportIncidence
    (use : Source → State → Row → ℝ) (s : Source) : Finset Row :=
  Finset.univ.filter fun r ↦ s ∈ rowSupport use r

/-- The loopless intersection graph of categorical row supports. -/
def rowSupportOverlapNeighbor
    (use : Source → State → Row → ℝ) (r : Row) : Finset Row :=
  Finset.univ.filter fun t ↦
    t ≠ r ∧ ¬Disjoint (rowSupport use r) (rowSupport use t)

/-- Every non-neighbor row reads a disjoint set of categorical sources. -/
theorem rowSupportOverlapNeighbor_nonneighbor_disjoint
    (use : Source → State → Row → ℝ) (r t : Row)
    (ht : t ∉ insert r (rowSupportOverlapNeighbor use r)) :
    Disjoint (rowSupport use r) (rowSupport use t) := by
  by_contra hdisj
  have htr : t ≠ r := by
    intro h
    subst t
    exact ht (Finset.mem_insert_self r _)
  apply ht
  apply Finset.mem_insert_of_mem
  simp [rowSupportOverlapNeighbor, htr, hdisj]

/-- If a row reads at most `A` sources and one source is read by at most `B`
rows, then the row-support dependency degree is at most `A * B`. -/
theorem rowSupportOverlapNeighbor_card_le
    (use : Source → State → Row → ℝ) (A B : ℕ)
    (hrow : ∀ r, (rowSupport use r).card ≤ A)
    (hsource : ∀ s, (rowSupportIncidence use s).card ≤ B)
    (r : Row) :
    (rowSupportOverlapNeighbor use r).card ≤ A * B := by
  have hsub : rowSupportOverlapNeighbor use r ⊆
      (rowSupport use r).biUnion (rowSupportIncidence use) := by
    intro t ht
    have hnotDisj : ¬Disjoint (rowSupport use r) (rowSupport use t) :=
      (Finset.mem_filter.mp ht).2.2
    rw [Finset.not_disjoint_iff] at hnotDisj
    rcases hnotDisj with ⟨s, hsr, hst⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨s, hsr,
      Finset.mem_filter.mpr ⟨Finset.mem_univ t, hst⟩⟩
  calc
    (rowSupportOverlapNeighbor use r).card ≤
        ((rowSupport use r).biUnion (rowSupportIncidence use)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ s ∈ rowSupport use r, (rowSupportIncidence use s).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ rowSupport use r, B := by
      exact Finset.sum_le_sum fun s _ ↦ hsource s
    _ = (rowSupport use r).card * B := by simp
    _ ≤ A * B := Nat.mul_le_mul_right B (hrow r)

/-- A directly usable polynomial dependency estimate.  If row support and
source incidence are each affine in a locality parameter `K`, the overlap
degree is bounded by their quadratic product. -/
theorem rowSupportOverlapNeighbor_card_le_polynomial
    (use : Source → State → Row → ℝ)
    (A0 A1 B0 B1 K : ℕ)
    (hrow : ∀ r, (rowSupport use r).card ≤ A0 + A1 * K)
    (hsource : ∀ s,
      (rowSupportIncidence use s).card ≤ B0 + B1 * K)
    (r : Row) :
    (rowSupportOverlapNeighbor use r).card ≤
      (A0 + A1 * K) * (B0 + B1 * K) := by
  exact rowSupportOverlapNeighbor_card_le use
    (A0 + A1 * K) (B0 + B1 * K) hrow hsource r

end FiniteCategoricalSelection

end

end WeightedEdgeColoring
