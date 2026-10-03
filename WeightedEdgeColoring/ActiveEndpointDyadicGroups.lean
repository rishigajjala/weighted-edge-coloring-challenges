import WeightedEdgeColoring.ActiveEndpointBlockGroups
import WeightedEdgeColoring.DyadicWeightBuckets

/-!
# Dyadic endpoint blocks on an active edge set

At every vertex, split the active star into dyadic weight classes and then
into blocks of size between `K` and `2 * K - 1`, apart from at most one small
block in each class.  The small blocks are discarded.  The remaining endpoint
blocks have comparable weights and every edge belongs to at most two of them.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})

/-- The data and guarantees obtained by applying dyadic block grouping
separately to every active star. -/
structure ActiveEndpointDyadicGrouping
    (active : Finset G.E) (β : ℝ) (L K : ℕ) where
  partition : ∀ v, Finpartition (G.activeStarEdgeSet active v)
  block_spec : ∀ v T, T ∈ (partition v).parts →
    ((K ≤ T.card ∧ T.card ≤ 2 * K - 1) ∨ T.card < K) ∧
    (∃ i : Fin (L + 1),
      T ⊆ WeightedEdgeColoring.weightClass (G.activeStarEdgeSet active v)
        (WeightedEdgeColoring.dyadicBucket β L G.weight) i) ∧
    (∀ e ∈ T, ∀ f ∈ T, G.weight e ≤ 2 * G.weight f)
  small_block_is_bucket : ∀ v i T,
    T ∈ (partition v).parts → T.card < K →
    T ⊆ WeightedEdgeColoring.weightClass (G.activeStarEdgeSet active v)
      (WeightedEdgeColoring.dyadicBucket β L G.weight) i →
    T = WeightedEdgeColoring.weightClass (G.activeStarEdgeSet active v)
      (WeightedEdgeColoring.dyadicBucket β L G.weight) i
  discarded_weight_le : ∀ v,
    (∑ T ∈ (partition v).parts.filter (fun T ↦ T.card < K),
      ∑ e ∈ T, G.weight e) ≤ (((L + 1) * (K - 1) : ℕ) : ℝ)

/-- Dyadic grouping can be chosen simultaneously at every vertex. -/
theorem exists_activeEndpointDyadicGrouping
    (active : Finset G.E) (β : ℝ) (L K : ℕ)
    (hβ : 0 < β) (hcover : 1 ≤ WeightedEdgeColoring.dyadicScale β L)
    (hwlower : ∀ e ∈ active, β ≤ G.weight e) (hK : 0 < K) :
    Nonempty (G.ActiveEndpointDyadicGrouping active β L K) := by
  classical
  have hexists : ∀ v, ∃ P : Finpartition (G.activeStarEdgeSet active v),
      (∀ T ∈ P.parts,
        ((K ≤ T.card ∧ T.card ≤ 2 * K - 1) ∨ T.card < K) ∧
        (∃ i : Fin (L + 1),
          T ⊆ WeightedEdgeColoring.weightClass (G.activeStarEdgeSet active v)
            (WeightedEdgeColoring.dyadicBucket β L G.weight) i) ∧
        (∀ e ∈ T, ∀ f ∈ T, G.weight e ≤ 2 * G.weight f)) ∧
      (∀ i T, T ∈ P.parts → T.card < K →
        T ⊆ WeightedEdgeColoring.weightClass (G.activeStarEdgeSet active v)
          (WeightedEdgeColoring.dyadicBucket β L G.weight) i →
        T = WeightedEdgeColoring.weightClass (G.activeStarEdgeSet active v)
          (WeightedEdgeColoring.dyadicBucket β L G.weight) i) ∧
      (∑ T ∈ P.parts.filter (fun T ↦ T.card < K),
        ∑ e ∈ T, G.weight e) ≤ (((L + 1) * (K - 1) : ℕ) : ℝ) := by
    intro v
    apply WeightedEdgeColoring.exists_dyadic_block_finpartition_small_weight_bound
    · exact hβ
    · exact hcover
    · intro e he
      exact hwlower e (G.mem_activeStarEdgeSet active v e |>.mp he).1
    · intro e _he
      exact G.weight_le_one e
    · exact hK
  let P : ∀ v, Finpartition (G.activeStarEdgeSet active v) :=
    fun v ↦ Classical.choose (hexists v)
  have hP (v) := Classical.choose_spec (hexists v)
  exact ⟨{
    partition := P
    block_spec := fun v ↦ (hP v).1
    small_block_is_bucket := fun v ↦ (hP v).2.1
    discarded_weight_le := fun v ↦ (hP v).2.2
  }⟩

/-- The endpoint blocks retained after discarding all parts of size below
`K`. -/
abbrev ActiveEndpointDyadicLargeGroup
    {active : Finset G.E} {β : ℝ} {L K : ℕ}
    (D : G.ActiveEndpointDyadicGrouping active β L K) :=
  G.ActiveEndpointLargeBlockGroup active D.partition K

/-- The active edges in a retained dyadic endpoint block. -/
def activeEndpointDyadicLargeMembers
    {active : Finset G.E} {β : ℝ} {L K : ℕ}
    {D : G.ActiveEndpointDyadicGrouping active β L K} :
    G.ActiveEndpointDyadicLargeGroup D → Finset G.E :=
  fun g ↦ G.activeEndpointLargeBlockMembers g

/-- Every retained block has between `K` and `2*K-1` edges. -/
theorem activeEndpointDyadicLarge_card_between
    {active : Finset G.E} {β : ℝ} {L K : ℕ}
    {D : G.ActiveEndpointDyadicGrouping active β L K}
    (g : G.ActiveEndpointDyadicLargeGroup D) :
    K ≤ (G.activeEndpointDyadicLargeMembers g).card ∧
      (G.activeEndpointDyadicLargeMembers g).card ≤ 2 * K - 1 := by
  have hlower : K ≤ (G.activeEndpointDyadicLargeMembers g).card := g.2
  have hsize :
      ((K ≤ (G.activeEndpointDyadicLargeMembers g).card ∧
          (G.activeEndpointDyadicLargeMembers g).card ≤ 2 * K - 1) ∨
        (G.activeEndpointDyadicLargeMembers g).card < K) := by
    simpa [activeEndpointDyadicLargeMembers,
      activeEndpointLargeBlockMembers, activeEndpointBlockMembers] using
      (D.block_spec g.1.1 g.1.2.1 g.1.2.2).1
  refine ⟨hlower, ?_⟩
  rcases hsize with hlarge | hsmall
  · exact hlarge.2
  · omega

/-- Weights in one retained dyadic endpoint block differ by at most a factor
two. -/
theorem activeEndpointDyadicLarge_weight_le_two_mul
    {active : Finset G.E} {β : ℝ} {L K : ℕ}
    {D : G.ActiveEndpointDyadicGrouping active β L K}
    (g : G.ActiveEndpointDyadicLargeGroup D)
    {e f : G.E} (he : e ∈ G.activeEndpointDyadicLargeMembers g)
    (hf : f ∈ G.activeEndpointDyadicLargeMembers g) :
    G.weight e ≤ 2 * G.weight f := by
  exact (D.block_spec g.1.1 g.1.2.1 g.1.2.2).2.2 e he f hf

/-- An edge occurs in at most one retained block at each endpoint, hence in
at most two retained blocks altogether. -/
theorem activeEndpointDyadicLarge_incidence_card_le_two
    {active : Finset G.E} {β : ℝ} {L K : ℕ}
    {D : G.ActiveEndpointDyadicGrouping active β L K} (e : G.E) :
    ((Finset.univ : Finset (G.ActiveEndpointDyadicLargeGroup D)).filter
      (fun g ↦ e ∈ G.activeEndpointDyadicLargeMembers g)).card ≤ 2 := by
  exact G.activeEndpointLargeBlock_incidence_card_le_two e

/-- At one vertex, all discarded small blocks together have weight at most
`(L+1)(K-1)`. -/
theorem activeEndpointDyadic_discarded_weight_le
    {active : Finset G.E} {β : ℝ} {L K : ℕ}
    (D : G.ActiveEndpointDyadicGrouping active β L K) (v : G.V) :
    (∑ T ∈ (D.partition v).parts.filter (fun T ↦ T.card < K),
      ∑ e ∈ T, G.weight e) ≤ (((L + 1) * (K - 1) : ℕ) : ℝ) :=
  D.discarded_weight_le v

end WeightedEdgeColoring.WeightedSimpleGraph
