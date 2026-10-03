import WeightedEdgeColoring.SubtwoLabelConditionalLaw

/-!
# Exact graph-star transport under endpoint-label conditioning

At a fixed original vertex, every endpoint label receives a conditional
bounded-profile realization.  Weighting its large-slot and tiny-reservoir
assignments by the original label mass restores the unconditioned edge
marginal exactly.  Positive assignments remain on the matching endpoint
label.  These are the local graph identities needed by a labelled completion
argument.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- Conditional star proposal, defined as zero when the chosen label has
zero original probability. -/
def conditionalEndpointProposal
    {v : G.V} {Label : Type*} [DecidableEq Label]
    (edgeLabel : G.StarEdge v → Label)
    (x : G.StarEdge v → ℝ)
    (q : Finset (G.StarEdge v) → ℝ)
    (label : Label) (e : G.StarEdge v) : ℝ :=
  if 0 < subsetLabelMass edgeLabel q label then
    (if edgeLabel e = label then
      x e / subsetLabelMass edgeLabel q label else 0)
  else 0

/-- All labels, including zero-mass labels, have a conditional profile
realization; zero-mass labels use the empty star law. -/
theorem exists_allConditionalEndpointRealizations
    {v : G.V} {Label : Type*} [Fintype Label] [DecidableEq Label]
    (edgeLabel : G.StarEdge v → Label)
    (x : G.StarEdge v → ℝ)
    (q : Finset (G.StarEdge v) → ℝ)
    (hq0 : ∀ S, 0 ≤ q S)
    (hqfeasible : ∀ S, q S ≠ 0 → G.StarFeasible v S)
    (hqmarg : ∀ e, (∑ S, if e ∈ S then q S else 0) = x e)
    (hqsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ a : Label, ∀ e ∈ S, edgeLabel e = a)
    {s β qstep r : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hqstep : 0 < qstep) (hr : 0 < r) :
    ∃ R : ∀ label : Label,
      G.BoundedProfileRealization
        (G.conditionalEndpointProposal edgeLabel x q label)
        s β qstep r hβ hr,
      (∀ label e j, 0 < (R label).largeAssign e j →
        edgeLabel e = label) ∧
      (∀ label e P, 0 < (R label).tinyAssign e P →
        edgeLabel e = label) := by
  classical
  have hlocal : ∀ label : Label,
      G.IsAverageOfStarFeasibleSets v
        (G.conditionalEndpointProposal edgeLabel x q label) := by
    intro label
    by_cases hmass : 0 < subsetLabelMass edgeLabel q label
    · obtain ⟨conditional, hc0, hctotal, hcfeasible, hcmarg⟩ :=
        condition_singleLabelSubsetDistribution edgeLabel label
          (fun e : G.StarEdge v ↦ G.weight e.1) x q hq0
          (fun S hS ↦ hqfeasible S hS) hqmarg hqsingle hmass
      apply G.isAverageOfStarFeasibleSets_of_subsetAverage
      refine ⟨conditional, hc0, hctotal, hcfeasible, ?_⟩
      intro e
      simpa [conditionalEndpointProposal, hmass] using hcmarg e
    · have hzero : G.IsAverageOfStarFeasibleSets v
          (fun _ : G.StarEdge v ↦ 0) := by
        refine ⟨1, (fun _ ↦ 1), (fun _ ↦ ∅), ?_, ?_, ?_, ?_⟩
        · intro i; norm_num
        · simp
        · intro i; simp [StarFeasible]
        · intro e; simp
      have heq : G.conditionalEndpointProposal edgeLabel x q label =
          (fun _ : G.StarEdge v ↦ 0) := by
        funext e
        simp [conditionalEndpointProposal, hmass]
      rw [heq]
      exact hzero
  have hR : ∀ label : Label,
      Nonempty (G.BoundedProfileRealization
        (G.conditionalEndpointProposal edgeLabel x q label)
        s β qstep r hβ hr) := by
    intro label
    exact G.exists_boundedProfileRealization (hlocal label)
      hs hs1 hβ hqstep hr
  let R := fun label ↦ Classical.choice (hR label)
  refine ⟨R, ?_, ?_⟩
  · intro label e j hpos
    exact BoundedProfileRealization.positive_largeAssign_respects_support
      G (R label) hs (fun e ↦ edgeLabel e = label)
      (fun e he ↦ by
        by_cases h : edgeLabel e = label
        · exact h
        · simp [conditionalEndpointProposal, h] at he)
      e j hpos
  · intro label e P hpos
    exact BoundedProfileRealization.positive_tinyAssign_respects_support
      G (R label) hs (fun e ↦ edgeLabel e = label)
      (fun e he ↦ by
        by_cases h : edgeLabel e = label
        · exact h
        · simp [conditionalEndpointProposal, h] at he)
      e P hpos


/-- The label-weighted ordinary-slot assignment equals the original large
edge demand, while every positive entry has the correct endpoint label. -/
theorem conditionalEndpoint_largeAssign_exact
    {v : G.V} {Label : Type*} [Fintype Label] [DecidableEq Label]
    (edgeLabel : G.StarEdge v → Label)
    (x : G.StarEdge v → ℝ)
    (q : Finset (G.StarEdge v) → ℝ)
    (hq0 : ∀ S, 0 ≤ q S)
    (hqmarg : ∀ e, (∑ S, if e ∈ S then q S else 0) = x e)
    (hqsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ a : Label, ∀ e ∈ S, edgeLabel e = a)
    {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
    (R : ∀ label : Label,
      G.BoundedProfileRealization
        (G.conditionalEndpointProposal edgeLabel x q label)
        s β qstep r hβ hr)
    (e : G.StarEdge v) :
    (∑ label : Label,
      subsetLabelMass edgeLabel q label *
        (∑ j : G.ExplicitLargeSlot (R label).law hβ hr,
          (R label).largeAssign e j)) =
      if β ≤ G.weight e.1 then s * x e else 0 := by
  classical
  have hmix :
      (∑ label : Label,
        subsetLabelMass edgeLabel q label *
          G.conditionalEndpointProposal edgeLabel x q label e) = x e := by
    simpa only [conditionalEndpointProposal] using
      (sum_labelMass_mul_conditionalMarginal
        edgeLabel x q hq0 hqmarg hqsingle e)
  calc
    (∑ label : Label,
      subsetLabelMass edgeLabel q label *
        (∑ j : G.ExplicitLargeSlot (R label).law hβ hr,
          (R label).largeAssign e j)) =
      ∑ label : Label,
        subsetLabelMass edgeLabel q label *
          (if β ≤ G.weight e.1 then
            s * G.conditionalEndpointProposal edgeLabel x q label e
            else 0) := by
      apply Finset.sum_congr rfl
      intro label _
      rw [(R label).largeAssign_marginal e]
    _ = if β ≤ G.weight e.1 then
          s * (∑ label : Label,
            subsetLabelMass edgeLabel q label *
              G.conditionalEndpointProposal edgeLabel x q label e)
        else 0 := by
      by_cases he : β ≤ G.weight e.1
      · simp only [he, ite_true, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro label _
        ring
      · simp [he]
    _ = if β ≤ G.weight e.1 then s * x e else 0 := by rw [hmix]

/-- The label-weighted rounded-reservoir assignment equals the original
tiny-edge demand.  Together with the large identity it preserves all
original edge mass across the label-separated transports. -/
theorem conditionalEndpoint_tinyAssign_exact
    {v : G.V} {Label : Type*} [Fintype Label] [DecidableEq Label]
    (edgeLabel : G.StarEdge v → Label)
    (x : G.StarEdge v → ℝ)
    (q : Finset (G.StarEdge v) → ℝ)
    (hq0 : ∀ S, 0 ≤ q S)
    (hqmarg : ∀ e, (∑ S, if e ∈ S then q S else 0) = x e)
    (hqsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ a : Label, ∀ e ∈ S, edgeLabel e = a)
    {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
    (R : ∀ label : Label,
      G.BoundedProfileRealization
        (G.conditionalEndpointProposal edgeLabel x q label)
        s β qstep r hβ hr)
    (e : G.StarEdge v) :
    (∑ label : Label,
      subsetLabelMass edgeLabel q label *
        (∑ P : G.RoundedProfileIndex (R label).law hβ hr,
          (R label).tinyAssign e P)) =
      if G.weight e.1 < β then s * x e else 0 := by
  classical
  have hmix :
      (∑ label : Label,
        subsetLabelMass edgeLabel q label *
          G.conditionalEndpointProposal edgeLabel x q label e) = x e := by
    simpa only [conditionalEndpointProposal] using
      (sum_labelMass_mul_conditionalMarginal
        edgeLabel x q hq0 hqmarg hqsingle e)
  calc
    (∑ label : Label,
      subsetLabelMass edgeLabel q label *
        (∑ P : G.RoundedProfileIndex (R label).law hβ hr,
          (R label).tinyAssign e P)) =
      ∑ label : Label,
        subsetLabelMass edgeLabel q label *
          (if G.weight e.1 < β then
            s * G.conditionalEndpointProposal edgeLabel x q label e
            else 0) := by
      apply Finset.sum_congr rfl
      intro label _
      rw [(R label).tinyAssign_marginal e]
      rfl
    _ = if G.weight e.1 < β then
          s * (∑ label : Label,
            subsetLabelMass edgeLabel q label *
              G.conditionalEndpointProposal edgeLabel x q label e)
        else 0 := by
      by_cases he : G.weight e.1 < β
      · simp only [he, ite_true, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro label _
        ring
      · simp [he]
    _ = if G.weight e.1 < β then s * x e else 0 := by rw [hmix]


/-- Full label-separated graph-star profile package.  Every positive
transport entry has the correct endpoint label, and the weighted total of
large plus tiny assignments is exactly the original retained edge mass. -/
theorem exists_labelSeparatedGraphStarTransport
    {v : G.V} {Label : Type*} [Fintype Label] [DecidableEq Label]
    (edgeLabel : G.StarEdge v → Label)
    (x : G.StarEdge v → ℝ)
    (q : Finset (G.StarEdge v) → ℝ)
    (hq0 : ∀ S, 0 ≤ q S)
    (hqfeasible : ∀ S, q S ≠ 0 → G.StarFeasible v S)
    (hqmarg : ∀ e, (∑ S, if e ∈ S then q S else 0) = x e)
    (hqsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ a : Label, ∀ e ∈ S, edgeLabel e = a)
    {s β qstep r : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hqstep : 0 < qstep) (hr : 0 < r) :
    ∃ R : ∀ label : Label,
      G.BoundedProfileRealization
        (G.conditionalEndpointProposal edgeLabel x q label)
        s β qstep r hβ hr,
      (∀ label e j, 0 < (R label).largeAssign e j →
        edgeLabel e = label) ∧
      (∀ label e P, 0 < (R label).tinyAssign e P →
        edgeLabel e = label) ∧
      (∀ e : G.StarEdge v,
        (∑ label : Label,
          subsetLabelMass edgeLabel q label *
            (∑ j : G.ExplicitLargeSlot (R label).law hβ hr,
              (R label).largeAssign e j)) +
        (∑ label : Label,
          subsetLabelMass edgeLabel q label *
            (∑ P : G.RoundedProfileIndex (R label).law hβ hr,
              (R label).tinyAssign e P)) = s * x e) := by
  obtain ⟨R, hlargeSupport, htinySupport⟩ :=
    G.exists_allConditionalEndpointRealizations edgeLabel x q
      hq0 hqfeasible hqmarg hqsingle hs hs1 hβ hqstep hr
  refine ⟨R, hlargeSupport, htinySupport, ?_⟩
  intro e
  rw [G.conditionalEndpoint_largeAssign_exact edgeLabel x q
    hq0 hqmarg hqsingle R e]
  rw [G.conditionalEndpoint_tinyAssign_exact edgeLabel x q
    hq0 hqmarg hqsingle R e]
  by_cases he : β ≤ G.weight e.1
  · have hnot : ¬G.weight e.1 < β := not_lt_of_ge he
    simp [he, hnot]
  · have ht : G.weight e.1 < β := lt_of_not_ge he
    simp [he, ht]

end WeightedMultigraph

end

end WeightedEdgeColoring
