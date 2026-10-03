import WeightedEdgeColoring.RankThreeOriginalTypeNaturalIteration
import WeightedEdgeColoring.BoundedMultiplicityEndpointGroupRound
import WeightedEdgeColoring.RankThreeResidualActiveIteration
import WeightedEdgeColoring.RankThreeFinalCategoricalLLL
import WeightedEdgeColoring.WeightedInsertion

/-!
# Endpoint-block accounting for original-type sharp traces

The option set retained by the sharp iteration can be a proper subset of the
full residual option set.  We therefore measure the active star of the
current original-type state directly.  Once active-job persistence is known,
the usual endpoint-block gain gives exactly the same affine recurrence as in
`RankThreeActiveResidualWeight`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace RankThreeOptionSystem

universe u v w

variable (G : WeightedMultigraph.{u})
  {Slot : Type v} {Option : Type w}
  [Fintype Slot] [Fintype Option]
  [DecidableEq Slot] [DecidableEq Option]
  {H : RankThreeOptionSystem G.E Slot Option}

namespace OriginalIterationState

namespace Multigraph

/-- Weight of the current state's active incident jobs at a vertex. -/
noncomputable def stateActiveStarWeight
    (X : OriginalIterationState H) (vtx : G.V) : ℝ :=
  ∑ e ∈ G.activeStarEdgeSet X.activeJobs vtx, G.weight e

/-- Original jobs already represented by the accumulated matching. -/
def coveredJobSet (X : OriginalIterationState H) : Finset G.E :=
  Finset.univ.filter (H.Covers X.matching)

theorem full_activeJobs : (full H).activeJobs = H.activeJobs := by
  ext e
  rw [(full H).mem_activeJobs, H.mem_activeJobs]
  constructor
  · rintro ⟨o, ho⟩
    exact ⟨o.1, H.mem_fiber.mpr
      ((full H).system.mem_fiber.mp ho)⟩
  · rintro ⟨o, ho⟩
    let q : KeptOption (full H).keep := ⟨o, by simp [full, empty]⟩
    exact ⟨q, (full H).system.mem_fiber.mpr (H.mem_fiber.mp ho)⟩

@[simp] theorem full_system_fiber_card (j : G.E) :
    (((full H).system.fiber j).card) = (H.fiber j).card := by
  change ((H.inducedOnOptions Finset.univ).fiber j).card = (H.fiber j).card
  rw [H.inducedOnOptions_fiber_card]
  simp [fiber]

@[simp] theorem full_system_slotDegree (s : Slot) :
    (full H).system.slotDegree s = H.slotDegree s := by
  change (H.inducedOnOptions Finset.univ).slotDegree s = H.slotDegree s
  simp only [slotDegree, inducedOnOptions]
  apply Finset.card_bij (fun o _ho ↦ o.1)
  · intro o ho
    simpa using ho
  · intro o₁ _ho₁ o₂ _ho₂ heq
    exact Subtype.ext heq
  · intro o ho
    refine ⟨⟨o, Finset.mem_univ o⟩, ?_, rfl⟩
    simpa using ho

/-- For the canonical initial state this is precisely the initial active
(large-edge) star weight. -/
theorem stateActiveStarWeight_full (vtx : G.V) :
    stateActiveStarWeight G (full H) vtx =
      ∑ e ∈ G.activeStarEdgeSet H.activeJobs vtx, G.weight e := by
  rw [stateActiveStarWeight, full_activeJobs]

/-- If every edge has an option, the canonical initial active star is the
whole weighted star. -/
theorem stateActiveStarWeight_full_eq_total
    (hactive0 : ∀ j, j ∈ H.activeJobs) (vtx : G.V) :
    stateActiveStarWeight G (full H) vtx =
      ∑ e ∈ Finset.univ,
        if G.Inc vtx e then G.weight e else 0 := by
  rw [stateActiveStarWeight_full]
  have hall : H.activeJobs = (Finset.univ : Finset G.E) := by
    ext e
    simp [hactive0 e]
  rw [hall]
  unfold WeightedMultigraph.activeStarEdgeSet
  rw [Finset.sum_filter]

/-- Retained endpoint-block members, viewed in the current active-job type. -/
def activeEndpointMembers
    {β : ℝ} {L K : ℕ} (X : OriginalIterationState H)
    (D : G.ActiveEndpointDyadicGrouping X.activeJobs β L K) :
    G.ActiveEndpointDyadicLargeGroup D → Finset (ActiveJob X.activeJobs) :=
  fun g ↦ (Finset.univ : Finset (ActiveJob X.activeJobs)).filter
    (fun e ↦ e.1 ∈ G.activeEndpointDyadicLargeMembers g)

/-- Passing to the active-job subtype does not change an endpoint block's
cardinality. -/
theorem activeEndpointMembers_card
    {β : ℝ} {L K : ℕ} (X : OriginalIterationState H)
    (D : G.ActiveEndpointDyadicGrouping X.activeJobs β L K)
    (g : G.ActiveEndpointDyadicLargeGroup D) :
    (activeEndpointMembers G X D g).card =
      (G.activeEndpointDyadicLargeMembers g).card := by
  let valEmb : ActiveJob X.activeJobs ↪ G.E :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hmap :
      (activeEndpointMembers G X D g).map valEmb =
        G.activeEndpointDyadicLargeMembers g := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_map.mp he with ⟨j, hj, rfl⟩
      exact (Finset.mem_filter.mp hj).2
    · intro he
      have hactive : e ∈ X.activeJobs :=
        X.system.multigraphEndpointDyadicLargeMembers_subset_activeJobs G g he
      exact Finset.mem_map.mpr
        ⟨⟨e, hactive⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
  rw [← hmap, Finset.card_map]

/-- Endpoint incidence remains at most two after passing to active jobs. -/
theorem activeEndpointMembers_incidence_le_two
    {β : ℝ} {L K : ℕ} (X : OriginalIterationState H)
    (D : G.ActiveEndpointDyadicGrouping X.activeJobs β L K)
    (j : ActiveJob X.activeJobs) :
    ((Finset.univ : Finset (G.ActiveEndpointDyadicLargeGroup D)).filter
      (fun g ↦ j ∈ activeEndpointMembers G X D g)).card ≤ 2 := by
  simpa [activeEndpointMembers] using
    (G.activeEndpointDyadicLarge_incidence_card_le_two
      (D := D) j.1)

/-- Covered active subtype jobs map exactly to the covered original jobs in
the endpoint block. -/
theorem covered_activeEndpointMembers_card
    {β : ℝ} {L K d : ℕ} (X : OriginalIterationState H)
    (D : G.ActiveEndpointDyadicGrouping X.activeJobs β L K)
    (W : ActiveRegularizedProjectedRound X d)
    (g : G.ActiveEndpointDyadicLargeGroup D) :
    ((((X.activeSystem).inducedOnOptions W.trim).coveredGroupJobs
      (activeEndpointMembers G X D) g W.selected).card) =
      (X.system.coveredGroupJobs
        G.activeEndpointDyadicLargeMembers g W.currentSelection).card := by
  let valEmb : ActiveJob X.activeJobs ↪ G.E :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hmap :
      (((X.activeSystem).inducedOnOptions W.trim).coveredGroupJobs
        (activeEndpointMembers G X D) g W.selected).map valEmb =
      X.system.coveredGroupJobs
        G.activeEndpointDyadicLargeMembers g W.currentSelection := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_map.mp he with ⟨j, hj, rfl⟩
      have hj' := Finset.mem_filter.mp hj
      have hmember := (Finset.mem_filter.mp hj'.1).2
      apply Finset.mem_filter.mpr
      refine ⟨hmember, ?_⟩
      exact (X.system.covers_liftActiveKeptOptionSet_iff
        X.activeJobs W.trim W.selected j).mpr hj'.2
    · intro he
      have he' := Finset.mem_filter.mp he
      have heactive : e ∈ X.activeJobs :=
        X.system.multigraphEndpointDyadicLargeMembers_subset_activeJobs G g he'.1
      let j : ActiveJob X.activeJobs := ⟨e, heactive⟩
      apply Finset.mem_map.mpr
      refine ⟨j, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he'.1⟩
      · exact (X.system.covers_liftActiveKeptOptionSet_iff
          X.activeJobs W.trim W.selected j).mp he'.2
  rw [← hmap, Finset.card_map]

/-- The sharp group row with `m=K*d` yields the endpoint-block count used by
the weight conversion. -/
theorem SharpActiveRoundGood.endpointBlock_count
    {β a gamma etaJob etaLoad etaCollision delta : ℝ}
    {L K d : ℕ} (X : OriginalIterationState H)
    (D : G.ActiveEndpointDyadicGrouping X.activeJobs β L K)
    (W : ActiveRegularizedProjectedRound X d)
    (hd : 0 < d)
    (hgood : SharpActiveRoundGood (activeEndpointMembers G X D) (K * d) d
      a gamma etaJob etaLoad etaCollision delta W) :
    ∀ g : G.ActiveEndpointDyadicLargeGroup D,
      (1 - delta) * a * K <
        (X.system.coveredGroupJobs
          G.activeEndpointDyadicLargeMembers g W.currentSelection).card := by
  intro g
  have hrow := hgood.1 g
  have hcount :=
    ((X.activeSystem).inducedOnOptions W.trim).coveredGroupJobs_count_gt_of_row_gt
        (activeEndpointMembers G X D) g W.selected W.selected_isPartial
        ((1 - delta) * (a / (d : ℝ)) * ((K * d : ℕ) : ℝ)) hrow
  rw [covered_activeEndpointMembers_card G X D W g] at hcount
  have hdreal : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  convert hcount using 1
  field_simp [hdreal]
  push_cast <;> ring

/-- Exact active-star accounting when the next active set is obtained by
removing the jobs covered in the current round. -/
theorem stateActiveStarWeight_add_covered
    (X Y : OriginalIterationState H)
    (A : Finset (KeptOption X.keep))
    (hactive : Y.activeJobs =
      X.activeJobs.filter fun e ↦ ¬ X.system.Covers A e)
    (vtx : G.V) :
    stateActiveStarWeight G Y vtx +
        (∑ e ∈ (G.activeStarEdgeSet X.activeJobs vtx).filter
          (X.system.Covers A), G.weight e) =
      stateActiveStarWeight G X vtx := by
  classical
  unfold stateActiveStarWeight
  rw [hactive]
  have hset :
      G.activeStarEdgeSet
          (X.activeJobs.filter fun e ↦ ¬ X.system.Covers A e) vtx =
        (G.activeStarEdgeSet X.activeJobs vtx).filter
          (fun e ↦ ¬ X.system.Covers A e) := by
    ext e
    simp only [G.mem_activeStarEdgeSet, Finset.mem_filter]
    tauto
  rw [hset]
  simpa [add_comm] using
    (Finset.sum_filter_add_sum_filter_not
      (s := G.activeStarEdgeSet X.activeJobs vtx)
      (p := fun e ↦ X.system.Covers A e)
      (f := G.weight))

/-- One endpoint-block round gives the affine active-star recurrence. -/
theorem stateActiveStarWeight_step_le
    {β c : ℝ} {L K : ℕ}
    (X Y : OriginalIterationState H)
    (D : G.ActiveEndpointDyadicGrouping X.activeJobs β L K)
    (A : Finset (KeptOption X.keep))
    (hK : 0 < K) (hc : 0 ≤ c)
    (hactive : Y.activeJobs =
      X.activeJobs.filter fun e ↦ ¬ X.system.Covers A e)
    (hcount : ∀ g : G.ActiveEndpointDyadicLargeGroup D,
      c < (X.system.coveredGroupJobs
        G.activeEndpointDyadicLargeMembers g A).card) :
    ∀ vtx,
      stateActiveStarWeight G Y vtx ≤
        (1 - c / (8 * (K : ℝ))) * stateActiveStarWeight G X vtx +
          (c / (8 * (K : ℝ))) * (((L + 1) * (K - 1) : ℕ) : ℝ) := by
  intro vtx
  have hgain := X.system.multigraphEndpointDyadic_coveredActiveIncidentWeight_ge_defaultFloor
    G hK hc A hcount vtx
  have haccount := stateActiveStarWeight_add_covered G X Y A hactive vtx
  unfold stateActiveStarWeight at hgain haccount ⊢
  change c / (8 * (K : ℝ)) *
      ((∑ e ∈ G.activeStarEdgeSet X.activeJobs vtx, G.weight e) -
        (((L + 1) * (K - 1) : ℕ) : ℝ)) ≤
    ∑ e ∈ (G.activeStarEdgeSet X.activeJobs vtx).filter
      (X.system.Covers A), G.weight e at hgain
  nlinarith

/-- A dependent endpoint trace.  Its group type is rebuilt from the current
active-job set at every successor, so no padded empty groups are introduced. -/
inductive EndpointSharpTrace
    (β a delta : ℝ) (L K : ℕ) :
    ℕ → OriginalIterationState H → OriginalIterationState H → Prop
  | zero (X) : EndpointSharpTrace β a delta L K 0 X X
  | succ {n d : ℕ} {X Y Z : OriginalIterationState H}
      (hprev : EndpointSharpTrace β a delta L K n X Y)
      (D : G.ActiveEndpointDyadicGrouping Y.activeJobs β L K)
      (W : ActiveRegularizedProjectedRound Y d)
      (hactive : W.result.activeJobs =
        Y.activeJobs.filter fun e ↦ ¬ Y.system.Covers W.currentSelection e)
      (hcount : ∀ g : G.ActiveEndpointDyadicLargeGroup D,
        (1 - delta) * a * K <
          (Y.system.coveredGroupJobs
            G.activeEndpointDyadicLargeMembers g W.currentSelection).card)
      (hZ : Z = W.result) :
      EndpointSharpTrace β a delta L K (n + 1) X Z

/-- Extend an endpoint trace directly from the concrete sharp-round output. -/
theorem EndpointSharpTrace.succ_of_good
    {β a gamma etaJob etaLoad etaCollision delta : ℝ}
    {L K n d : ℕ} {X Y : OriginalIterationState H}
    (T : EndpointSharpTrace G β a delta L K n X Y)
    (D : G.ActiveEndpointDyadicGrouping Y.activeJobs β L K)
    (W : ActiveRegularizedProjectedRound Y d)
    (hd : 0 < d)
    (hgood : SharpActiveRoundGood (activeEndpointMembers G Y D) (K * d) d
      a gamma etaJob etaLoad etaCollision delta W)
    (hnextPositive : 0 <
      (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d) :
    EndpointSharpTrace G β a delta L K (n + 1) X W.result := by
  exact EndpointSharpTrace.succ T D W
    (hgood.result_activeJobs hnextPositive)
    (Multigraph.SharpActiveRoundGood.endpointBlock_count G Y D W hd hgood) rfl

/-- Geometric endpoint conclusion.  The block-boundary error is paid once. -/
theorem EndpointSharpTrace.stateActiveStarWeight_le
    {β a delta : ℝ} {L K n : ℕ}
    {X Y : OriginalIterationState H}
    (T : EndpointSharpTrace G β a delta L K n X Y)
    (hK : 0 < K) (hdelta1 : delta ≤ 1) (ha0 : 0 ≤ a)
    (htheta1 : (1 - delta) * a / 8 ≤ 1) :
    ∀ vtx,
      stateActiveStarWeight G Y vtx ≤
        (1 - (1 - delta) * a / 8) ^ n *
            stateActiveStarWeight G X vtx +
          (((L + 1) * (K - 1) : ℕ) : ℝ) := by
  have hdeltaFactor : 0 ≤ 1 - delta := by linarith
  have htheta0 : 0 ≤ (1 - delta) * a / 8 := by positivity
  intro vtx
  induction T with
  | zero X =>
      simp only [pow_zero, one_mul]
      have hfloor0 : (0 : ℝ) ≤ (((L + 1) * (K - 1) : ℕ) : ℝ) := by
        positivity
      linarith
  | @succ n d X Y Z hprev D W hactive hcount hZ ih =>
      subst Z
      have hc0 : 0 ≤ (1 - delta) * a * K := by positivity
      have hstep := stateActiveStarWeight_step_le G Y W.result D
        W.currentSelection hK hc0 hactive hcount vtx
      have hKreal : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
      have htheta :
          ((1 - delta) * a * K) / (8 * (K : ℝ)) =
            (1 - delta) * a / 8 := by
        field_simp [hKreal]
      rw [htheta] at hstep
      have hfactor : 0 ≤ 1 - (1 - delta) * a / 8 :=
        sub_nonneg.mpr htheta1
      calc
        stateActiveStarWeight G W.result vtx ≤
            (1 - (1 - delta) * a / 8) *
                stateActiveStarWeight G Y vtx +
              ((1 - delta) * a / 8) *
                (((L + 1) * (K - 1) : ℕ) : ℝ) := hstep
        _ ≤ (1 - (1 - delta) * a / 8) *
                ((1 - (1 - delta) * a / 8) ^ n *
                    stateActiveStarWeight G X vtx +
                  (((L + 1) * (K - 1) : ℕ) : ℝ)) +
              ((1 - delta) * a / 8) *
                (((L + 1) * (K - 1) : ℕ) : ℝ) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left ih hfactor) le_rfl
        _ = (1 - (1 - delta) * a / 8) ^ (n + 1) *
                stateActiveStarWeight G X vtx +
              (((L + 1) * (K - 1) : ℕ) : ℝ) := by
          rw [pow_succ]
          ring

/-- Along an endpoint trace, the active jobs are precisely the initially
active jobs which have not been covered by the accumulated matching.  The
statement is written with the initial matching included, so it also applies
to traces started after an earlier phase. -/
theorem EndpointSharpTrace.activeJobs_eq_uncovered
    {β a delta : ℝ} {L K n : ℕ}
    {X Y : OriginalIterationState H}
    (T : EndpointSharpTrace G β a delta L K n X Y)
    (hX : X.activeJobs = (Finset.univ : Finset G.E).filter
      (fun j ↦ ¬ H.Covers X.matching j)) :
    Y.activeJobs = (Finset.univ : Finset G.E).filter
      (fun j ↦ ¬ H.Covers Y.matching j) := by
  induction T with
  | zero X => exact hX
  | @succ n d X Y Z hprev D W hactive hcount hZ ih =>
      subst Z
      rw [hactive, ih hX]
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hprevUncovered, hcurrentUncovered⟩ hcovered
        rcases hcovered with ⟨o, ho, howner⟩
        rcases Finset.mem_union.mp ho with ho | ho
        · exact hprevUncovered ⟨o, ho, howner⟩
        · apply hcurrentUncovered
          apply (H.covers_liftKeptOptionSet_iff
            Y.keep W.currentSelection j).mp
          exact ⟨o, by simpa [ActiveRegularizedProjectedRound.originalSelection]
            using ho, howner⟩
      · intro hunion
        constructor
        · rintro ⟨o, ho, howner⟩
          exact hunion ⟨o, Finset.mem_union_left _ ho, howner⟩
        · intro hcurrent
          have horiginal : H.Covers W.originalSelection j := by
            exact (H.covers_liftKeptOptionSet_iff
              Y.keep W.currentSelection j).mpr hcurrent
          rcases horiginal with ⟨o, ho, howner⟩
          exact hunion ⟨o, Finset.mem_union_right _ ho, howner⟩

/-- For a trace satisfying the uncovered-job invariant, the weight outside
the accumulated covered-job set is exactly the state's active star weight. -/
theorem EndpointSharpTrace.uncoveredStar_eq_stateActiveStarWeight
    {β a delta : ℝ} {L K n : ℕ}
    {X Y : OriginalIterationState H}
    (T : EndpointSharpTrace G β a delta L K n X Y)
    (hX : X.activeJobs = (Finset.univ : Finset G.E).filter
      (fun j ↦ ¬ H.Covers X.matching j)) (vtx : G.V) :
    (∑ e ∈ Finset.univ \ coveredJobSet G Y,
      if G.Inc vtx e then G.weight e else 0) =
        stateActiveStarWeight G Y vtx := by
  have hactive := T.activeJobs_eq_uncovered G hX
  have hset : Finset.univ \ coveredJobSet G Y = Y.activeJobs := by
    rw [hactive]
    ext e
    simp [coveredJobSet]
  rw [hset]
  unfold stateActiveStarWeight WeightedMultigraph.activeStarEdgeSet
  rw [Finset.sum_filter]

/-- The full initial state satisfies the uncovered-job invariant whenever
every original job has at least one option. -/
theorem full_activeJobs_eq_uncovered
    (hactive0 : ∀ j, j ∈ H.activeJobs) :
    (full H).activeJobs = (Finset.univ : Finset G.E).filter
      (fun j ↦ ¬ H.Covers (full H).matching j) := by
  rw [full_activeJobs]
  ext j
  simp [hactive0 j, full, empty, Covers]

/-- Finish an original-type state once its retained active system reaches
the categorical-LLL range.  The final selector is lifted through the active
job subtype and the retained-option subtype, and then united with the
accumulated matching. -/
theorem exists_coveringPartialMatching_of_state_finalLLL
    (X : OriginalIterationState H)
    (b : ℕ) (hb : 0 < b)
    (hactive : ∀ j, ¬ H.Covers X.matching j → j ∈ X.activeJobs)
    (hfiber : ∀ j, (X.system.fiber j).Nonempty →
      900 * b ≤ (X.system.fiber j).card)
    (hslot : ∀ s, X.system.slotDegree s ≤ b) :
    ∃ Mfinal : Finset Option,
      H.IsPartialMatching Mfinal ∧ ∀ j, H.Covers Mfinal j := by
  let AJob := X.activeJobs
  let Q := X.system.inducedOnJobs AJob
  have hQfiber : ∀ j, 900 * b ≤ (Q.fiber j).card := by
    intro j
    rw [X.system.inducedOnJobs_fiber_card AJob j]
    exact hfiber j.1 ((X.mem_activeJobs j.1).mp j.2)
  have hQslot : ∀ s, Q.slotDegree s ≤ b := by
    intro s
    exact (X.system.inducedOnJobs_slotDegree_le AJob s).trans (hslot s)
  obtain ⟨A, hA, hcoverA⟩ :=
    Q.exists_covering_partialMatching_finalLLL_of_fiber_ge
      b hb hQfiber hQslot
  let Akeep : Finset (KeptOption X.keep) :=
    X.system.liftActiveJobSet AJob A
  have hAkeep : X.system.IsPartialMatching Akeep := by
    exact X.system.liftActiveJobSet_isPartialMatching AJob hA
  let Alift : Finset Option := H.liftKeptOptionSet X.keep Akeep
  have hfinal : H.IsPartialMatching (X.matching ∪ Alift) := by
    exact X.matching_isPartial.union_liftKeptOptionSet_of_subset_residual H
      X.keep_subset_residual hAkeep
  refine ⟨X.matching ∪ Alift, hfinal, ?_⟩
  intro j
  by_cases hj : H.Covers X.matching j
  · rcases hj with ⟨o, ho, howner⟩
    exact ⟨o, Finset.mem_union_left _ ho, howner⟩
  · have hjactive : j ∈ AJob := hactive j hj
    let ja : ActiveJob AJob := ⟨j, hjactive⟩
    have hQcover : Q.Covers A ja := hcoverA ja
    have hXcover : X.system.Covers Akeep j :=
      (X.system.covers_liftActiveJobSet_iff AJob A ja).mpr hQcover
    have hHcover : H.Covers Alift j :=
      (H.covers_liftKeptOptionSet_iff X.keep Akeep j).mpr hXcover
    rcases hHcover with ⟨o, ho, howner⟩
    exact ⟨o, Finset.mem_union_right _ ho, howner⟩

/-- Terminal cleanup for a concrete endpoint trace. -/
theorem EndpointSharpTrace.exists_finalCompletion
    {β a delta : ℝ} {L K n b : ℕ}
    {X Y : OriginalIterationState H}
    (T : EndpointSharpTrace G β a delta L K n X Y)
    (hX : X.activeJobs = (Finset.univ : Finset G.E).filter
      (fun j ↦ ¬ H.Covers X.matching j))
    (hb : 0 < b)
    (hfiber : ∀ j, (Y.system.fiber j).Nonempty →
      900 * b ≤ (Y.system.fiber j).card)
    (hslot : ∀ s, Y.system.slotDegree s ≤ b) :
    ∃ Mfinal : Finset Option,
      H.IsPartialMatching Mfinal ∧ ∀ j, H.Covers Mfinal j := by
  have hactiveEq := T.activeJobs_eq_uncovered G hX
  have hactive : ∀ j, ¬ H.Covers Y.matching j → j ∈ Y.activeJobs := by
    intro j hj
    rw [hactiveEq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  exact exists_coveringPartialMatching_of_state_finalLLL G Y b hb
    hactive hfiber hslot

/-! ## Constructing the dependent endpoint trace -/

/-- The only per-round input not supplied by the graph bookkeeping is the
explicit scalar package for the uniform sharp theorem.  The endpoint group
type is allowed to depend on the current state and on the grouping chosen in
that round. -/
structure EndpointNaturalSharpStepData
    {β : ℝ} {L K : ℕ}
    (X : OriginalIterationState H)
    (D : G.ActiveEndpointDyadicGrouping X.activeJobs β L K)
    (d S lambda k : ℕ)
    (a gamma etaJob etaLoad etaCollision z delta : ℝ)
    (hd : 0 < d) (hSd : S ≤ d) where
  numeric : ∀
    (trim : Finset (X.system.ActiveJobOption X.activeJobs))
    (htrim : ∀ j,
      ((((X.activeSystem).inducedOnOptions trim).fiber j).card) = d)
    (htwo : ∀ o : KeptOption trim,
      ((((X.activeSystem).inducedOnOptions trim).slots o).card) = 2)
    (hslot : ∀ s,
      ((X.activeSystem).inducedOnOptions trim).slotDegree s ≤ S)
    (hjobSlot : ∀ j s,
      ((X.activeSystem).inducedOnOptions trim).jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t →
      ((X.activeSystem).inducedOnOptions trim).slotPairCodegree s t ≤ lambda),
    UniformSharpScalarData
      (((X.activeSystem).inducedOnOptions trim).cyclicRegularization
        hSd htwo)
      ((CyclicRegularization.regularExtension hd hSd htwo htrim hslot
        hjobSlot hslotPair).liftedOldMembers
          (activeEndpointMembers G X D))
      (max lambda 1) d d 2 (2 * K) (K * d) k
      (a / (d : ℝ)) a gamma etaJob etaLoad etaCollision z delta

/-- Natural sharp iteration with endpoint blocks rebuilt at every round.

Unlike `NaturalSharpTrace`, this theorem does not fix a group type.  It
chooses the dyadic grouping from the current active set, derives all group
cardinality, support, and incidence bounds, and asks only for the explicit
scalar package consumed by the sharp one-round theorem. -/
theorem exists_endpointNaturalSharpIteration
    {β : ℝ}
    (initial : OriginalIterationState H)
    (steps d0 S0 lambda L K : ℕ) (k : ℕ → ℕ)
    (a gamma etaJob etaLoad etaCollision : ℝ) (z : ℕ → ℝ) (delta : ℝ)
    (hβ : 0 < β)
    (hdyadicCover : 1 ≤ dyadicScale β L)
    (hweightLower : ∀ e, β ≤ G.weight e)
    (hK : 0 < K) (hlambda : 0 < lambda)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hdelta1 : delta ≤ 1) (ha0 : 0 ≤ a)
    (htheta1 : (1 - delta) * a / 8 ≤ 1)
    (hjobRate0 : 0 ≤ WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob)
    (hslotRate0 : 0 ≤
      WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
        etaLoad + etaCollision)
    (herror : (1 - gamma) * etaJob + etaLoad + etaCollision ≤
      a * gamma * (1 - gamma))
    (hgap0 : (S0 : ℝ) ≤ (1 - gamma) * d0)
    (hmargin : ∀ n, 1 - gamma ≤
      (a * gamma * (1 - gamma) -
        ((1 - gamma) * etaJob + etaLoad + etaCollision)) *
          naturalSharpJobScale d0 a gamma etaJob n)
    (hpositive : ∀ n < steps,
      0 < naturalSharpJobScale d0 a gamma etaJob n)
    (hnextPositive : ∀ n < steps,
      0 < (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) *
        naturalSharpJobScale d0 a gamma etaJob n)
    (htwo : ∀ o, (H.slots o).card = 2)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hdegree0 : ∀ j, (initial.system.fiber j).Nonempty →
      d0 ≤ (initial.system.fiber j).card)
    (hslot0 : ∀ s, initial.system.slotDegree s ≤ S0)
    (data : ∀ n (hn : n < steps) (X : OriginalIterationState H)
      (D : G.ActiveEndpointDyadicGrouping X.activeJobs β L K),
      EndpointNaturalSharpStepData G X D
        (naturalSharpJobScale d0 a gamma etaJob n)
        (fixedSlackPaddedSlotTarget gamma
          (naturalSharpJobScale d0 a gamma etaJob n))
        lambda (k n) a gamma etaJob etaLoad etaCollision (z n) delta
        (hpositive n hn)
        (fixedSlackPaddedSlotTarget_le gamma
          (naturalSharpJobScale d0 a gamma etaJob n) hgamma0 hgamma1)) :
    ∃ final : OriginalIterationState H,
      EndpointSharpTrace G β a delta L K steps initial final ∧
      (∀ j, (final.system.fiber j).Nonempty →
        naturalSharpJobScale d0 a gamma etaJob steps ≤
          (final.system.fiber j).card) ∧
      (∀ s, final.system.slotDegree s ≤
        naturalSharpSlotCap S0 d0 a gamma etaJob etaLoad etaCollision steps) ∧
      ∀ vtx,
        stateActiveStarWeight G final vtx ≤
          (1 - (1 - delta) * a / 8) ^ steps *
              stateActiveStarWeight G initial vtx +
            (((L + 1) * (K - 1) : ℕ) : ℝ) := by
  let d : ℕ → ℕ := naturalSharpJobScale d0 a gamma etaJob
  let cap : ℕ → ℕ :=
    naturalSharpSlotCap S0 d0 a gamma etaJob etaLoad etaCollision
  have hgap : ∀ n, (cap n : ℝ) ≤ (1 - gamma) * d n := by
    exact naturalSharpSlotCap_le_gap S0 d0 a gamma etaJob etaLoad
      etaCollision hgamma0 hgamma1 hjobRate0 hslotRate0 hgap0 hmargin
  have hiter : ∀ n, n ≤ steps →
      ∃ X : OriginalIterationState H,
        EndpointSharpTrace G β a delta L K n initial X ∧
        (∀ j, (X.system.fiber j).Nonempty →
          d n ≤ (X.system.fiber j).card) ∧
        (∀ s, X.system.slotDegree s ≤ cap n) := by
    intro n hn
    induction n with
    | zero =>
        exact ⟨initial, EndpointSharpTrace.zero initial, hdegree0, hslot0⟩
    | succ n ih =>
        have hnlt : n < steps := Nat.lt_of_succ_le hn
        rcases ih (Nat.le_of_succ_le hn) with
          ⟨X, htrace, hdegreeX, hslotX⟩
        let D : G.ActiveEndpointDyadicGrouping X.activeJobs β L K :=
          Classical.choice (G.exists_activeEndpointDyadicGrouping
            X.activeJobs β L K hβ hdyadicCover
            (fun e _he ↦ hweightLower e) hK)
        let members := activeEndpointMembers G X D
        have hmembers : ∀ g, (members g).card ≤ 2 * K := by
          intro g
          rw [show (members g).card =
            (G.activeEndpointDyadicLargeMembers g).card by
              exact activeEndpointMembers_card G X D g]
          exact (G.activeEndpointDyadicLarge_card_between g).2.trans (by omega)
        have hgroupSize : ∀ g, K * d n ≤ (members g).card * d n := by
          intro g
          apply Nat.mul_le_mul_right (d n)
          rw [show (members g).card =
            (G.activeEndpointDyadicLargeMembers g).card by
              exact activeEndpointMembers_card G X D g]
          exact (G.activeEndpointDyadicLarge_card_between g).1
        have hincidence : ∀ j,
            ((Finset.univ : Finset (G.ActiveEndpointDyadicLargeGroup D)).filter
              (fun g ↦ j ∈ members g)).card ≤ 2 := by
          intro j
          exact activeEndpointMembers_incidence_le_two G X D j
        have htwoX : ∀ o : KeptOption X.keep,
            (X.system.slots o).card = 2 := by
          intro o
          exact htwo o.1
        have hjobSlotX : ∀ j s,
            X.system.jobSlotCodegree j s ≤ lambda := by
          intro j s
          exact (H.inducedOnOptions_jobSlotCodegree_le X.keep j s).trans
            (hjobSlot j s)
        have hslotPairX : ∀ s t, s ≠ t →
            X.system.slotPairCodegree s t ≤ lambda := by
          intro s t hst
          exact (H.inducedOnOptions_slotPairCodegree_le X.keep s t).trans
            (hslotPair s t hst)
        have hslotCap0 : 0 ≤
            (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
              etaLoad + etaCollision) * d n :=
          mul_nonneg hslotRate0 (Nat.cast_nonneg _)
        have hcapPad : cap n ≤ fixedSlackPaddedSlotTarget gamma (d n) := by
          exact nat_le_fixedSlackPaddedSlotTarget gamma (d n) (cap n)
            hgamma1 (hgap n)
        have hslotPad : ∀ s,
            X.system.slotDegree s ≤ fixedSlackPaddedSlotTarget gamma (d n) := by
          intro s
          exact (hslotX s).trans hcapPad
        let stepData := data n hnlt X D
        have hfloorNonneg : 0 ≤ (1 - gamma) * (d n : ℝ) :=
          mul_nonneg (sub_nonneg.mpr hgamma1) (by positivity)
        rcases exists_activeSharpRound X (d n)
            (fixedSlackPaddedSlotTarget gamma (d n)) lambda 2 (2 * K)
            (K * d n) (k n) (a / (d n : ℝ)) a gamma etaJob etaLoad
            etaCollision (z n) delta (hpositive n hnlt) hlambda
            (fixedSlackPaddedSlotTarget_le gamma (d n) hgamma0 hgamma1)
            hdegreeX htwoX hslotPad hjobSlotX hslotPairX
            (Nat.floor_le hfloorNonneg) hgamma1
            herror hslotCap0 members hmembers hgroupSize hincidence
            stepData.numeric with
          ⟨W, hgood⟩
        let Y := W.result
        have hdegreeY : ∀ j, (Y.system.fiber j).Nonempty →
            d (n + 1) ≤ (Y.system.fiber j).card := by
          intro j hj
          have hlower := hgood.originalKeep_nonempty_fiber_lower j (by
            simpa [Y, OriginalIterationState.system] using hj)
          have harg : 0 ≤
              (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d n :=
            mul_nonneg hjobRate0 (Nat.cast_nonneg _)
          have hfloor := Nat.floor_le harg
          have hreal : ((d (n + 1) : ℕ) : ℝ) ≤
              ((H.inducedOnOptions W.originalKeep).fiber j).card :=
            hfloor.trans hlower
          have hnat : d (n + 1) ≤
              ((H.inducedOnOptions W.originalKeep).fiber j).card := by
            exact_mod_cast hreal
          simpa [Y, OriginalIterationState.system] using hnat
        have hslotY : ∀ s, Y.system.slotDegree s ≤ cap (n + 1) := by
          intro s
          have hreal := hgood.originalKeep_slotDegree s
          have harg : 0 ≤
              (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
                etaLoad + etaCollision) * d n :=
            mul_nonneg hslotRate0 (Nat.cast_nonneg _)
          have hnat :
              (H.inducedOnOptions W.originalKeep).slotDegree s ≤
                ⌊(WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
                    etaLoad + etaCollision) * d n⌋₊ :=
            (Nat.le_floor_iff harg).mpr hreal
          simpa [Y, OriginalIterationState.system, cap, d,
            naturalSharpSlotCap] using hnat
        have htraceY : EndpointSharpTrace G β a delta L K (n + 1)
            initial Y := by
          exact EndpointSharpTrace.succ htrace D W
            (hgood.result_activeJobs (hnextPositive n hnlt))
            (Multigraph.SharpActiveRoundGood.endpointBlock_count
              G X D W (hpositive n hnlt) hgood) rfl
        exact ⟨Y, htraceY, hdegreeY, hslotY⟩
  rcases hiter steps le_rfl with ⟨final, htrace, hdegree, hslot⟩
  have hweight := htrace.stateActiveStarWeight_le G hK
    hdelta1 ha0 htheta1
  exact ⟨final, htrace, hdegree, hslot, hweight⟩

/-- Apply terminal cleanup to the quantitative output of the natural
endpoint iteration.  This isolates the two exact stopping inequalities:
the final job floor must be at least `900*b`, and the final slot cap at most
`b`. -/
theorem EndpointSharpTrace.exists_finalCompletion_of_naturalBounds
    {β a delta : ℝ} {L K steps d0 S0 b : ℕ}
    {gamma etaJob etaLoad etaCollision : ℝ}
    {initial final : OriginalIterationState H}
    (T : EndpointSharpTrace G β a delta L K steps initial final)
    (hinitial : initial.activeJobs = (Finset.univ : Finset G.E).filter
      (fun j ↦ ¬ H.Covers initial.matching j))
    (hb : 0 < b)
    (hterminalJob : 900 * b ≤
      naturalSharpJobScale d0 a gamma etaJob steps)
    (hterminalSlot :
      naturalSharpSlotCap S0 d0 a gamma etaJob etaLoad etaCollision steps ≤ b)
    (hdegree : ∀ j, (final.system.fiber j).Nonempty →
      naturalSharpJobScale d0 a gamma etaJob steps ≤
        (final.system.fiber j).card)
    (hslot : ∀ s, final.system.slotDegree s ≤
      naturalSharpSlotCap S0 d0 a gamma etaJob etaLoad etaCollision steps) :
    ∃ Mfinal : Finset Option,
      H.IsPartialMatching Mfinal ∧ ∀ j, H.Covers Mfinal j := by
  apply T.exists_finalCompletion G hinitial hb
  · intro j hj
    exact hterminalJob.trans (hdegree j hj)
  · intro s
    exact (hslot s).trans hterminalSlot

/-! ## Outer partial-coloring interface -/

/-- Extract a feasible partial coloring from the accumulated matching and
combine it with the endpoint recurrence.  The option-construction input is
stated pointwise: every partial matching of the concrete option system must
decode to a feasible coloring of exactly its covered jobs. -/
theorem EndpointSharpTrace.exists_partialColoring_with_residualStar
    {β a delta : ℝ} {L K steps q : ℕ}
    {final : OriginalIterationState H}
    (T : EndpointSharpTrace G β a delta L K steps (full H) final)
    (hactive0 : ∀ j, j ∈ H.activeJobs)
    (hK : 0 < K) (hdelta1 : delta ≤ 1) (ha0 : 0 ≤ a)
    (htheta1 : (1 - delta) * a / 8 ≤ 1)
    (hextract : ∀ M : Finset Option, H.IsPartialMatching M →
      ∃ color : G.E → Fin q,
        G.IsFeasibleOn
          (Finset.univ.filter (H.Covers M)) color) :
    ∃ (P : Finset G.E) (color : G.E → Fin q),
      G.IsFeasibleOn P color ∧
      P = coveredJobSet G final ∧
      ∀ vtx,
        (∑ e ∈ Finset.univ \ P,
          if G.Inc vtx e then G.weight e else 0) ≤
            (1 - (1 - delta) * a / 8) ^ steps *
                (∑ e ∈ Finset.univ,
                  if G.Inc vtx e then G.weight e else 0) +
              (((L + 1) * (K - 1) : ℕ) : ℝ) := by
  obtain ⟨color, hcolor⟩ := hextract final.matching final.matching_isPartial
  refine ⟨coveredJobSet G final, color, ?_, rfl, ?_⟩
  · simpa [coveredJobSet] using hcolor
  · intro vtx
    rw [Multigraph.EndpointSharpTrace.uncoveredStar_eq_stateActiveStarWeight
      G T
      (full_activeJobs_eq_uncovered G hactive0) vtx]
    simpa [stateActiveStarWeight_full_eq_total G hactive0 vtx] using
      (T.stateActiveStarWeight_le G hK hdelta1 ha0 htheta1 vtx)

end Multigraph

end OriginalIterationState
end RankThreeOptionSystem
end WeightedEdgeColoring
