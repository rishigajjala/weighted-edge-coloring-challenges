import WeightedEdgeColoring.RankThreeActiveJobs
import WeightedEdgeColoring.BoundedMultiplicityEndpointGroups
import WeightedEdgeColoring.RankThreeWeightedGroupCoverage

/-!
# Endpoint dyadic groups as coverage rows

This file joins the active-job invariant to the endpoint dyadic partition.
The retained blocks are legal coverage groups: they contain only active jobs,
have controlled size, and each job occurs in at most two groups.  A uniform
count guarantee on those groups is then converted into a weighted gain at
every vertex.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace RankThreeOptionSystem

universe u v w

variable (G : WeightedMultigraph.{u})
  {Slot : Type v} {Option : Type w}
  [Fintype Slot] [Fintype Option]
  [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem G.E Slot Option)

/-! ## Structural facts -/

/-- Every member of a retained endpoint block is an active job. -/
theorem multigraphEndpointDyadicLargeMembers_subset_activeJobs
    {β : ℝ} {L K : ℕ}
    {D : G.ActiveEndpointDyadicGrouping H.activeJobs β L K}
    (g : G.ActiveEndpointDyadicLargeGroup D) :
    G.activeEndpointDyadicLargeMembers g ⊆ H.activeJobs := by
  intro e he
  have hstar := G.activeEndpointBlockMembers_subset_star g.1 he
  exact (G.mem_activeStarEdgeSet H.activeJobs g.1.1 e).mp hstar |>.1

/-- The retained blocks give coverage rows with support at least `K*d`. -/
theorem multigraphEndpointDyadicLarge_support_card_ge
    {β : ℝ} {L K d : ℕ}
    {D : G.ActiveEndpointDyadicGrouping H.activeJobs β L K}
    (hlower : ∀ o, d ≤ (H.fiber (H.owner o)).card)
    (g : G.ActiveEndpointDyadicLargeGroup D) :
    K * d ≤
      (linearRowSupport
        (H.jobGroupCoverageWeight G.activeEndpointDyadicLargeMembers) g).card := by
  apply H.jobGroupCoverage_support_card_ge_of_active
    G.activeEndpointDyadicLargeMembers g K d hlower
  · exact (G.activeEndpointDyadicLarge_card_between g).1
  · exact H.multigraphEndpointDyadicLargeMembers_subset_activeJobs G g

/-- All structural hypotheses needed for endpoint-block coverage rows, in one
bundle.  The harmless upper bound `2*K` is convenient in later estimates. -/
theorem multigraphEndpointDyadicLarge_structural
    {β : ℝ} {L K d : ℕ}
    {D : G.ActiveEndpointDyadicGrouping H.activeJobs β L K}
    (hlower : ∀ o, d ≤ (H.fiber (H.owner o)).card) :
    (∀ g : G.ActiveEndpointDyadicLargeGroup D,
      G.activeEndpointDyadicLargeMembers g ⊆ H.activeJobs) ∧
    (∀ g : G.ActiveEndpointDyadicLargeGroup D,
      K ≤ (G.activeEndpointDyadicLargeMembers g).card ∧
      (G.activeEndpointDyadicLargeMembers g).card ≤ 2 * K - 1 ∧
      (G.activeEndpointDyadicLargeMembers g).card ≤ 2 * K) ∧
    (∀ g : G.ActiveEndpointDyadicLargeGroup D,
      K * d ≤ (linearRowSupport
        (H.jobGroupCoverageWeight G.activeEndpointDyadicLargeMembers) g).card) ∧
    (∀ e : G.E,
      ((Finset.univ : Finset (G.ActiveEndpointDyadicLargeGroup D)).filter
        (fun g ↦ e ∈ G.activeEndpointDyadicLargeMembers g)).card ≤ 2) := by
  refine ⟨H.multigraphEndpointDyadicLargeMembers_subset_activeJobs G,
    ?_, H.multigraphEndpointDyadicLarge_support_card_ge G hlower,
    G.activeEndpointDyadicLarge_incidence_card_le_two⟩
  intro g
  have h := G.activeEndpointDyadicLarge_card_between g
  exact ⟨h.1, h.2, h.2.trans (by omega)⟩

/-! ## Count-to-weight conversion inside one retained block -/

/-- An arbitrary member of a retained block.  Using an arbitrary member,
rather than a minimum-weight member, costs only one extra factor two. -/
noncomputable def multigraphEndpointDyadicRepresentative
    {β : ℝ} {L K : ℕ}
    {D : G.ActiveEndpointDyadicGrouping H.activeJobs β L K}
    (hK : 0 < K) (g : G.ActiveEndpointDyadicLargeGroup D) : G.E :=
  Classical.choose (by
    have hpos : 0 < (G.activeEndpointDyadicLargeMembers g).card :=
      hK.trans_le (G.activeEndpointDyadicLarge_card_between g).1
    exact Finset.card_pos.mp hpos)

theorem multigraphEndpointDyadicRepresentative_mem
    {β : ℝ} {L K : ℕ}
    {D : G.ActiveEndpointDyadicGrouping H.activeJobs β L K}
    (hK : 0 < K) (g : G.ActiveEndpointDyadicLargeGroup D) :
    H.multigraphEndpointDyadicRepresentative G hK g ∈
      G.activeEndpointDyadicLargeMembers g := by
  exact Classical.choose_spec (by
    have hpos : 0 < (G.activeEndpointDyadicLargeMembers g).card :=
      hK.trans_le (G.activeEndpointDyadicLarge_card_between g).1
    exact Finset.card_pos.mp hpos)

/-- More than `c` covered jobs in every retained block covers more than the
`c/(8K)` fraction of the weight of each block. -/
theorem multigraphEndpointDyadicLarge_coveredWeight_gt
    {β c : ℝ} {L K : ℕ}
    {D : G.ActiveEndpointDyadicGrouping H.activeJobs β L K}
    (hK : 0 < K) (hc : 0 ≤ c) (S : Finset Option)
    (hcount : ∀ g : G.ActiveEndpointDyadicLargeGroup D,
      c < (H.coveredGroupJobs G.activeEndpointDyadicLargeMembers g S).card) :
    ∀ g : G.ActiveEndpointDyadicLargeGroup D,
      (c / (8 * (K : ℝ))) *
          (∑ e ∈ G.activeEndpointDyadicLargeMembers g, G.weight e) <
        ∑ e ∈ H.coveredGroupJobs
          G.activeEndpointDyadicLargeMembers g S, G.weight e := by
  let a : G.ActiveEndpointDyadicLargeGroup D → ℝ := fun g ↦
    G.weight (H.multigraphEndpointDyadicRepresentative G hK g) / 2
  have hraw := H.coveredGroupWeight_gt_of_count_gt_generic
    G.activeEndpointDyadicLargeMembers G.weight a S (2 * K) c 4
    (by omega) hc (by norm_num)
    (fun g ↦ by
      dsimp [a]
      exact div_pos (G.weight_pos _) (by norm_num))
    (fun g ↦ (G.activeEndpointDyadicLarge_card_between g).2.trans (by omega))
    (fun g e he ↦ by
      dsimp [a]
      have hcompare := G.activeEndpointDyadicLarge_weight_le_two_mul g
        (H.multigraphEndpointDyadicRepresentative_mem G hK g) he
      linarith)
    (fun g e he ↦ by
      dsimp [a]
      have hcompare := G.activeEndpointDyadicLarge_weight_le_two_mul g he
        (H.multigraphEndpointDyadicRepresentative_mem G hK g)
      linarith)
    hcount
  intro g
  have hg := hraw g
  have hKreal : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  convert hg using 1
  field_simp [hKreal]
  norm_num [Nat.cast_mul]
  ring

/-! ## Summing the retained blocks at a vertex -/

/-- The retained parts at one endpoint. -/
def multigraphEndpointDyadicLargeParts
    {β : ℝ} {L K : ℕ}
    (D : G.ActiveEndpointDyadicGrouping H.activeJobs β L K) (vtx : G.V) :
    Finset (Finset G.E) :=
  (D.partition vtx).parts.filter fun T ↦ K ≤ T.card

/-- The discarded parts at one endpoint. -/
def multigraphEndpointDyadicSmallParts
    {β : ℝ} {L K : ℕ}
    (D : G.ActiveEndpointDyadicGrouping H.activeJobs β L K) (vtx : G.V) :
    Finset (Finset G.E) :=
  (D.partition vtx).parts.filter fun T ↦ T.card < K

/-- Large and small parts account exactly for the active incident weight. -/
theorem multigraphEndpointDyadicLarge_add_small_weight
    {β : ℝ} {L K : ℕ}
    (D : G.ActiveEndpointDyadicGrouping H.activeJobs β L K) (vtx : G.V) :
    (∑ T ∈ H.multigraphEndpointDyadicLargeParts G D vtx, ∑ e ∈ T, G.weight e) +
      (∑ T ∈ H.multigraphEndpointDyadicSmallParts G D vtx, ∑ e ∈ T, G.weight e) =
    ∑ e ∈ G.activeStarEdgeSet H.activeJobs vtx, G.weight e := by
  classical
  rw [multigraphEndpointDyadicLargeParts, multigraphEndpointDyadicSmallParts]
  have hsmall :
      (D.partition vtx).parts.filter (fun T ↦ T.card < K) =
        (D.partition vtx).parts.filter (fun T ↦ ¬ K ≤ T.card) := by
    ext T
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hT, hlt⟩
      exact ⟨hT, Nat.not_le_of_lt hlt⟩
    · rintro ⟨hT, hnle⟩
      exact ⟨hT, Nat.lt_of_not_ge hnle⟩
  rw [hsmall, Finset.sum_filter_add_sum_filter_not]
  calc
    (∑ T ∈ (D.partition vtx).parts, ∑ e ∈ T, G.weight e) =
        ∑ e ∈ (D.partition vtx).parts.biUnion id, G.weight e :=
      (Finset.sum_biUnion (D.partition vtx).disjoint).symm
    _ = ∑ e ∈ G.activeStarEdgeSet H.activeJobs vtx, G.weight e := by
      rw [(D.partition vtx).biUnion_parts]

/-- Summing the block guarantees at one endpoint gives a gain on all active
incident weight except for the explicitly bounded discarded floor. -/
theorem multigraphEndpointDyadic_coveredActiveIncidentWeight_ge
    {β c floor : ℝ} {L K : ℕ}
    {D : G.ActiveEndpointDyadicGrouping H.activeJobs β L K}
    (hK : 0 < K) (hc : 0 ≤ c) (S : Finset Option)
    (hcount : ∀ g : G.ActiveEndpointDyadicLargeGroup D,
      c < (H.coveredGroupJobs G.activeEndpointDyadicLargeMembers g S).card)
    (hfloor : ∀ vtx,
      (∑ T ∈ H.multigraphEndpointDyadicSmallParts G D vtx,
        ∑ e ∈ T, G.weight e) ≤ floor) :
    ∀ vtx,
      (c / (8 * (K : ℝ))) *
          ((∑ e ∈ G.activeStarEdgeSet H.activeJobs vtx, G.weight e) - floor) ≤
        ∑ e ∈ (G.activeStarEdgeSet H.activeJobs vtx).filter (H.Covers S),
          G.weight e := by
  classical
  intro vtx
  let theta : ℝ := c / (8 * (K : ℝ))
  let large := H.multigraphEndpointDyadicLargeParts G D vtx
  let small := H.multigraphEndpointDyadicSmallParts G D vtx
  have htheta : 0 ≤ theta := by
    dsimp [theta]
    positivity
  have haccount := H.multigraphEndpointDyadicLarge_add_small_weight G D vtx
  have hretained :
      (∑ e ∈ G.activeStarEdgeSet H.activeJobs vtx, G.weight e) - floor ≤
        ∑ T ∈ large, ∑ e ∈ T, G.weight e := by
    have hf := hfloor vtx
    dsimp [large]
    linarith [haccount, hf]
  calc
    theta *
        ((∑ e ∈ G.activeStarEdgeSet H.activeJobs vtx, G.weight e) - floor) ≤
        theta * (∑ T ∈ large, ∑ e ∈ T, G.weight e) :=
      mul_le_mul_of_nonneg_left hretained htheta
    _ = ∑ T ∈ large, theta * (∑ e ∈ T, G.weight e) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ T ∈ large,
        ∑ e ∈ T.filter (H.Covers S), G.weight e := by
      apply Finset.sum_le_sum
      intro T hT
      have hTparts : T ∈ (D.partition vtx).parts :=
        (Finset.mem_filter.mp hT).1
      have hTlarge : K ≤ T.card := (Finset.mem_filter.mp hT).2
      let g : G.ActiveEndpointDyadicLargeGroup D :=
        ⟨⟨vtx, ⟨T, hTparts⟩⟩, hTlarge⟩
      have hg := H.multigraphEndpointDyadicLarge_coveredWeight_gt G hK hc S hcount g
      have hmembers : G.activeEndpointDyadicLargeMembers g = T := rfl
      have hcovered :
          H.coveredGroupJobs G.activeEndpointDyadicLargeMembers g S =
            T.filter (H.Covers S) := by
        simp [coveredGroupJobs, hmembers]
      simpa [theta, hmembers, hcovered] using hg.le
    _ ≤ ∑ e ∈ (G.activeStarEdgeSet H.activeJobs vtx).filter (H.Covers S),
          G.weight e := by
      have hpair : Set.PairwiseDisjoint (large : Set (Finset G.E))
          (fun T ↦ T.filter (H.Covers S)) := by
        intro T hT U hU hne
        apply Finset.disjoint_filter_filter
        exact (D.partition vtx).disjoint
          (Finset.mem_filter.mp hT).1 (Finset.mem_filter.mp hU).1 hne
      have hsub : large.biUnion (fun T ↦ T.filter (H.Covers S)) ⊆
          (G.activeStarEdgeSet H.activeJobs vtx).filter (H.Covers S) := by
        intro e he
        rcases Finset.mem_biUnion.mp he with ⟨T, hT, heT⟩
        have hpart : T ∈ (D.partition vtx).parts :=
          (Finset.mem_filter.mp hT).1
        have hstar : T ⊆ G.activeStarEdgeSet H.activeJobs vtx :=
          (D.partition vtx).le hpart
        exact Finset.mem_filter.mpr
          ⟨hstar (Finset.mem_filter.mp heT).1, (Finset.mem_filter.mp heT).2⟩
      rw [← Finset.sum_biUnion hpair]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun e _he _hout ↦ G.weight_nonneg e)

/-- The canonical dyadic discarded-weight estimate discharges the abstract
floor assumption in the preceding theorem. -/
theorem multigraphEndpointDyadic_coveredActiveIncidentWeight_ge_defaultFloor
    {β c : ℝ} {L K : ℕ}
    {D : G.ActiveEndpointDyadicGrouping H.activeJobs β L K}
    (hK : 0 < K) (hc : 0 ≤ c) (S : Finset Option)
    (hcount : ∀ g : G.ActiveEndpointDyadicLargeGroup D,
      c < (H.coveredGroupJobs G.activeEndpointDyadicLargeMembers g S).card) :
    ∀ vtx,
      (c / (8 * (K : ℝ))) *
          ((∑ e ∈ G.activeStarEdgeSet H.activeJobs vtx, G.weight e) -
            (((L + 1) * (K - 1) : ℕ) : ℝ)) ≤
        ∑ e ∈ (G.activeStarEdgeSet H.activeJobs vtx).filter (H.Covers S),
          G.weight e := by
  apply H.multigraphEndpointDyadic_coveredActiveIncidentWeight_ge G hK hc S hcount
  intro vtx
  exact D.discarded_weight_le vtx

end RankThreeOptionSystem
end WeightedEdgeColoring
