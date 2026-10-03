import WeightedEdgeColoring.SubtwoLabelGraphTransport
import WeightedEdgeColoring.SubtwoSingleClassLocalPolytope

/-! A graph-level factory for diffuse proposal rows with one original endpoint
label per sampled star set. The charge inequality is stated at every vertex
and candidate color; the construction preserves exact edge marginals. -/

namespace WeightedEdgeColoring

open scoped BigOperators
noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {Color Label K : Type*}
variable [Fintype Color] [DecidableEq Color]
variable [Fintype Label] [DecidableEq Label]
variable [Fintype K] [DecidableEq K]

/-- A diffuse charge bound produces a one-label feasible local law at every
vertex and candidate color, with exact original edge marginals. -/
theorem exists_diffuseSingleLabelGraphLaw
    (proposal : G.E → Color → ℝ)
    (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
    (sizeClass : G.E → K) (capacity : K → ℕ)
    (M : ℝ)
    (hcapacity : ∀ a, 0 < capacity a)
    (hweight : ∀ e, G.weight e ≤ (1 : ℝ) / capacity (sizeClass e))
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hM0 : 0 ≤ M)
    (hproposalM : ∀ e c, proposal e c ≤ M)
    (hcharge : ∀ v c,
      (∑ f : G.StarEdge v,
        proposal f.1 c / (capacity (sizeClass f.1) : ℝ)) +
        (Fintype.card (Label × K) : ℝ) * M ≤ 1) :
    ∃ qLaw : ∀ v : G.V, Color → Finset (G.StarEdge v) → ℝ,
      (∀ v c S, 0 ≤ qLaw v c S) ∧
      (∀ v c, ∑ S, qLaw v c S = 1) ∧
      (∀ v c S, qLaw v c S ≠ 0 → G.StarFeasible v S) ∧
      (∀ v c (f : G.StarEdge v),
        (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c) ∧
      (∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
        ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label) ∧
      (∀ (v : G.V) (c : Color) (label : Label),
        subsetLabelMass (edgeLabel v) (qLaw v c) label ≤
          ∑ a : K,
            ((∑ f : G.StarEdge v,
              if edgeLabel v f = label ∧ sizeClass f.1 = a
              then proposal f.1 c else 0) / (capacity a : ℝ) + M)) := by
  classical
  have hlocal (v : G.V) (c : Color) :
      ∃ q : Finset (G.StarEdge v) → ℝ,
        (∀ S, 0 ≤ q S) ∧ (∑ S, q S = 1) ∧
        (∀ S, q S ≠ 0 → G.StarFeasible v S) ∧
        (∀ f, (∑ S, if f ∈ S then q S else 0) = proposal f.1 c) ∧
        (∀ S, q S ≠ 0 → S ≠ ∅ →
          ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label) ∧
        (∀ label : Label, subsetLabelMass (edgeLabel v) q label ≤
          ∑ a : K,
            ((∑ f : G.StarEdge v,
              if edgeLabel v f = label ∧ sizeClass f.1 = a
              then proposal f.1 c else 0) / (capacity a : ℝ) + M)) := by
    obtain ⟨q, hq0, hqsum, hqfeas, hqmarg, hqsingle, hqlabel⟩ :=
      sizeClasses_singleLabelDistribution_of_charge capacity hcapacity
        (edgeLabel v) (fun f : G.StarEdge v => sizeClass f.1)
        (fun f : G.StarEdge v => G.weight f.1)
        (fun f : G.StarEdge v => proposal f.1 c) M
        (fun f => (G.weight_pos f.1).le)
        (fun f => hweight f.1)
        (fun f => hproposal0 f.1 c) hM0
        (fun f => hproposalM f.1 c) (hcharge v c)
    exact ⟨q, hq0, hqsum,
      (fun S hS => by simpa [StarFeasible] using hqfeas S hS),
      hqmarg, hqsingle, hqlabel⟩
  let qLaw : ∀ v : G.V, Color → Finset (G.StarEdge v) → ℝ :=
    fun v c => Classical.choose (hlocal v c)
  refine ⟨qLaw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v c S; exact (Classical.choose_spec (hlocal v c)).1 S
  · intro v c; exact (Classical.choose_spec (hlocal v c)).2.1
  · intro v c S hS; exact (Classical.choose_spec (hlocal v c)).2.2.1 S hS
  · intro v c f; exact (Classical.choose_spec (hlocal v c)).2.2.2.1 f
  · intro v c S hS hSne; exact (Classical.choose_spec (hlocal v c)).2.2.2.2.1 S hS hSne
  · intro v c label; exact (Classical.choose_spec (hlocal v c)).2.2.2.2.2 label

/-- All local conditional endpoint realizations may be chosen at once.  The
label-weighted slot and reservoir assignments recover each original proposal
coordinate exactly. -/
theorem exists_allDiffuseLabelEndpointRealizations
    (proposal : G.E → Color → ℝ)
    (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
    (qLaw : ∀ v : G.V, Color → Finset (G.StarEdge v) → ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqfeasible : ∀ v c S, qLaw v c S ≠ 0 → G.StarFeasible v S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    {s β qstep r : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hqstep : 0 < qstep) (hr : 0 < r) :
    ∃ R : ∀ v c label,
      G.BoundedProfileRealization
        (G.conditionalEndpointProposal (edgeLabel v)
          (fun f : G.StarEdge v => proposal f.1 c) (qLaw v c) label)
        s β qstep r hβ hr,
      (∀ v c label (f : G.StarEdge v) j,
        0 < (R v c label).largeAssign f j → edgeLabel v f = label) ∧
      (∀ v c label (f : G.StarEdge v) P,
        0 < (R v c label).tinyAssign f P → edgeLabel v f = label) ∧
      (∀ v c (f : G.StarEdge v),
        (∑ label : Label,
          subsetLabelMass (edgeLabel v) (qLaw v c) label *
            (∑ j : G.ExplicitLargeSlot (R v c label).law hβ hr,
              (R v c label).largeAssign f j)) +
        (∑ label : Label,
          subsetLabelMass (edgeLabel v) (qLaw v c) label *
            (∑ P : G.RoundedProfileIndex (R v c label).law hβ hr,
              (R v c label).tinyAssign f P)) = s * proposal f.1 c) := by
  classical
  have hlocal (v : G.V) (c : Color) :
      ∃ R : ∀ label : Label,
        G.BoundedProfileRealization
          (G.conditionalEndpointProposal (edgeLabel v)
            (fun f : G.StarEdge v => proposal f.1 c) (qLaw v c) label)
          s β qstep r hβ hr,
        (∀ label (f : G.StarEdge v) j,
          0 < (R label).largeAssign f j → edgeLabel v f = label) ∧
        (∀ label (f : G.StarEdge v) P,
          0 < (R label).tinyAssign f P → edgeLabel v f = label) ∧
        (∀ (f : G.StarEdge v),
          (∑ label : Label,
            subsetLabelMass (edgeLabel v) (qLaw v c) label *
              (∑ j : G.ExplicitLargeSlot (R label).law hβ hr,
                (R label).largeAssign f j)) +
          (∑ label : Label,
            subsetLabelMass (edgeLabel v) (qLaw v c) label *
              (∑ P : G.RoundedProfileIndex (R label).law hβ hr,
                (R label).tinyAssign f P)) = s * proposal f.1 c) := by
    exact G.exists_labelSeparatedGraphStarTransport (edgeLabel v)
      (fun f : G.StarEdge v => proposal f.1 c) (qLaw v c)
      (hq0 v c) (hqfeasible v c) (hqmarg v c) (hqsingle v c)
      hs hs1 hβ hqstep hr
  let R : ∀ v c label,
      G.BoundedProfileRealization
        (G.conditionalEndpointProposal (edgeLabel v)
          (fun f : G.StarEdge v => proposal f.1 c) (qLaw v c) label)
        s β qstep r hβ hr :=
    fun v c => Classical.choose (hlocal v c)
  refine ⟨R, ?_, ?_, ?_⟩
  · intro v c label f j hpos
    exact (Classical.choose_spec (hlocal v c)).1 label f j hpos
  · intro v c label f P hpos
    exact (Classical.choose_spec (hlocal v c)).2.1 label f P hpos
  · intro v c f
    exact (Classical.choose_spec (hlocal v c)).2.2 f

end WeightedMultigraph
end
end WeightedEdgeColoring
