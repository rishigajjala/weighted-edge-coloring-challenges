import WeightedEdgeColoring.SubtwoSingleClassLocalPolytope

/-!
# Conditioning a coupled one-label local law

A distribution on feasible subsets that uses a single endpoint label per
nonempty outcome may be disintegrated by that label.  The conditional law
has exact label-restricted marginals divided by the original label mass.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

section ConditionalLabelLaw

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Probability mass of nonempty outcomes using one label. -/
noncomputable def subsetLabelMass {Label : Type*} [DecidableEq Label]
    (edgeLabel : I → Label) (q : Finset I → ℝ) (label : Label) : ℝ :=
  ∑ S : Finset I,
    if S ≠ ∅ ∧ (∀ i ∈ S, edgeLabel i = label) then q S else 0

/-- A positive label mass admits a normalized conditional law whose
marginals are the original label marginals divided by that mass. -/
theorem condition_singleLabelSubsetDistribution
    {Label : Type*} [DecidableEq Label]
    (edgeLabel : I → Label) (label : Label)
    (w x : I → ℝ) (q : Finset I → ℝ)
    (hq0 : ∀ S, 0 ≤ q S)
    (hqfeasible : ∀ S, q S ≠ 0 → ∑ i ∈ S, w i ≤ 1)
    (hqmarg : ∀ i, (∑ S, if i ∈ S then q S else 0) = x i)
    (hqsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ a : Label, ∀ i ∈ S, edgeLabel i = a)
    (hlabel : 0 < subsetLabelMass edgeLabel q label) :
    ∃ conditional : Finset I → ℝ,
      (∀ S, 0 ≤ conditional S) ∧
      (∑ S, conditional S = 1) ∧
      (∀ S, conditional S ≠ 0 → ∑ i ∈ S, w i ≤ 1) ∧
      (∀ i, (∑ S, if i ∈ S then conditional S else 0) =
        if edgeLabel i = label then
          x i / subsetLabelMass edgeLabel q label else 0) := by
  classical
  let mass := subsetLabelMass edgeLabel q label
  let eligible : Finset I → Prop := fun S ↦
    S ≠ ∅ ∧ ∀ i ∈ S, edgeLabel i = label
  let conditional : Finset I → ℝ := fun S ↦
    if eligible S then q S / mass else 0
  refine ⟨conditional, ?_, ?_, ?_, ?_⟩
  · intro S
    by_cases hS : eligible S
    · exact (by simpa [conditional, hS] using div_nonneg (hq0 S) hlabel.le)
    · simp [conditional, hS]
  · calc
      (∑ S, conditional S) =
          (∑ S : Finset I, if eligible S then q S else 0) / mass := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro S _
        by_cases hS : eligible S <;> simp [conditional, hS]
      _ = 1 := by
        change subsetLabelMass edgeLabel q label /
          subsetLabelMass edgeLabel q label = 1
        exact div_self hlabel.ne'
  · intro S hS
    have hq : q S ≠ 0 := by
      by_contra hz
      simp [conditional, hz] at hS
    exact hqfeasible S hq
  · intro i
    by_cases hi : edgeLabel i = label
    · have hterm : ∀ S : Finset I,
          (if i ∈ S then conditional S else 0) =
            (if i ∈ S then q S / mass else 0) := by
        intro S
        by_cases hiS : i ∈ S
        · by_cases hqS : q S = 0
          · simp [conditional, hqS, hiS]
          · have hSne : S ≠ ∅ := by
              intro hz
              rw [hz] at hiS
              simpa using hiS
            obtain ⟨a, ha⟩ := hqsingle S hqS hSne
            have halabel : a = label := by
              rw [← ha i hiS]
              exact hi
            have heligible : eligible S := by
              refine ⟨hSne, ?_⟩
              intro j hj
              rw [ha j hj, halabel]
            simp [conditional, hiS, heligible]
        · simp [hiS]
      calc
        (∑ S, if i ∈ S then conditional S else 0) =
            ∑ S : Finset I, if i ∈ S then q S / mass else 0 := by
          apply Finset.sum_congr rfl
          intro S _
          exact hterm S
        _ = (∑ S : Finset I, if i ∈ S then q S else 0) / mass := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro S _
          by_cases hiS : i ∈ S <;> simp [hiS]
        _ = (if edgeLabel i = label then
              x i / subsetLabelMass edgeLabel q label else 0) := by
          simp [hqmarg i, hi, mass]
    · have hzero : ∀ S : Finset I,
          (if i ∈ S then conditional S else 0) = 0 := by
        intro S
        by_cases hiS : i ∈ S
        · have hnot : ¬eligible S := by
            intro hS
            exact hi (hS.2 i hiS)
          simp [conditional, hiS, hnot]
        · simp [hiS]
      simp [hzero, hi]

end ConditionalLabelLaw
end WeightedEdgeColoring

namespace WeightedEdgeColoring

section ConditionalLabelBudget

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Nonempty outcome masses partition by their unique endpoint label;
empty outcomes account for the remaining probability. -/
theorem sum_subsetLabelMass_le_one
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (edgeLabel : I → Label) (q : Finset I → ℝ)
    (hq0 : ∀ S, 0 ≤ q S) (hqsum : ∑ S, q S = 1)
    (hqsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ a : Label, ∀ i ∈ S, edgeLabel i = a) :
    (∑ label : Label, subsetLabelMass edgeLabel q label) ≤ 1 := by
  classical
  have hpoint : ∀ S : Finset I,
      (∑ label : Label,
        if S ≠ ∅ ∧ (∀ i ∈ S, edgeLabel i = label) then q S else 0) ≤
          q S := by
    intro S
    by_cases hS : S = ∅
    · subst S
      simpa [subsetLabelMass] using hq0 ∅
    · by_cases hq : q S = 0
      · simp [hq]
      · obtain ⟨a, ha⟩ := hqsingle S hq hS
        have hunique : ∀ label : Label, label ≠ a →
            ¬(∀ i ∈ S, edgeLabel i = label) := by
          intro label hne hall
          obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
          exact hne ((hall i hi).symm.trans (ha i hi))
        rw [Finset.sum_eq_single a]
        · rw [if_pos ⟨hS, ha⟩]
        · intro label _hmem hne
          simp [hunique label hne]
        · intro hnot
          exact (hnot (Finset.mem_univ a)).elim
  calc
    (∑ label : Label, subsetLabelMass edgeLabel q label) =
        ∑ S : Finset I, ∑ label : Label,
          if S ≠ ∅ ∧ (∀ i ∈ S, edgeLabel i = label) then q S else 0 := by
      simp only [subsetLabelMass]
      rw [Finset.sum_comm]
    _ ≤ ∑ S : Finset I, q S :=
      Finset.sum_le_sum fun S _ ↦ hpoint S
    _ = 1 := hqsum

/-- If a label has zero nonempty outcome mass, every edge bearing that label
has zero original marginal. -/
theorem zero_subsetLabelMass_zero_marginal
    {Label : Type*} [DecidableEq Label]
    (edgeLabel : I → Label) (label : Label)
    (x : I → ℝ) (q : Finset I → ℝ)
    (hq0 : ∀ S, 0 ≤ q S)
    (hqmarg : ∀ i, (∑ S, if i ∈ S then q S else 0) = x i)
    (hqsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ a : Label, ∀ i ∈ S, edgeLabel i = a)
    (hzero : subsetLabelMass edgeLabel q label = 0)
    (i : I) (hi : edgeLabel i = label) : x i = 0 := by
  classical
  have htermZero : ∀ S : Finset I,
      (S ≠ ∅ ∧ (∀ j ∈ S, edgeLabel j = label)) → q S = 0 := by
    intro S hS
    have htermNonneg : ∀ T : Finset I,
        0 ≤ if T ≠ ∅ ∧ (∀ j ∈ T, edgeLabel j = label) then q T else 0 := by
      intro T
      split
      · exact hq0 T
      · exact le_rfl
    have hsingle := Finset.single_le_sum
      (fun T _ ↦ htermNonneg T) (Finset.mem_univ S)
    rw [if_pos hS] at hsingle
    change q S ≤ subsetLabelMass edgeLabel q label at hsingle
    rw [hzero] at hsingle
    exact le_antisymm hsingle (hq0 S)
  rw [← hqmarg i]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hiS : i ∈ S
  · by_cases hqS : q S = 0
    · simp [hqS]
    · have hSne : S ≠ ∅ := by
        intro h
        rw [h] at hiS
        simpa using hiS
      obtain ⟨a, ha⟩ := hqsingle S hqS hSne
      have halabel : a = label := by
        rw [← ha i hiS]
        exact hi
      have hAll : ∀ j ∈ S, edgeLabel j = label := by
        intro j hj
        rw [ha j hj, halabel]
      simp [htermZero S ⟨hSne, hAll⟩]
  · simp [hiS]

end ConditionalLabelBudget
end WeightedEdgeColoring

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- Condition a single-label feasible-subset distribution on a positive
endpoint label mass, then run the existing bounded profile and transport
construction for that conditional law.  Both transports retain the label. -/
theorem exists_conditionalLabelProfileRealization
    {v : G.V} {Label : Type*} [DecidableEq Label]
    (edgeLabel : G.StarEdge v → Label) (label : Label)
    (x : G.StarEdge v → ℝ)
    (q : Finset (G.StarEdge v) → ℝ)
    (hq0 : ∀ S, 0 ≤ q S)
    (hqfeasible : ∀ S, q S ≠ 0 → G.StarFeasible v S)
    (hqmarg : ∀ e, (∑ S, if e ∈ S then q S else 0) = x e)
    (hqsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ a : Label, ∀ e ∈ S, edgeLabel e = a)
    (hlabel : 0 < subsetLabelMass edgeLabel q label)
    {s β qstep r : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hqstep : 0 < qstep) (hr : 0 < r) :
    ∃ R : G.BoundedProfileRealization
      (fun e ↦ if edgeLabel e = label then
        x e / subsetLabelMass edgeLabel q label else 0)
      s β qstep r hβ hr,
      (∀ e j, 0 < R.largeAssign e j → edgeLabel e = label) ∧
      (∀ e P, 0 < R.tinyAssign e P → edgeLabel e = label) := by
  classical
  obtain ⟨conditional, hc0, hctotal, hcfeasible, hcmarg⟩ :=
    condition_singleLabelSubsetDistribution edgeLabel label
      (fun e : G.StarEdge v ↦ G.weight e.1) x q hq0
      (fun S hS ↦ hqfeasible S hS) hqmarg hqsingle hlabel
  have hlocal : G.IsAverageOfStarFeasibleSets v
      (fun e ↦ if edgeLabel e = label then
        x e / subsetLabelMass edgeLabel q label else 0) :=
    G.isAverageOfStarFeasibleSets_of_subsetAverage
      ⟨conditional, hc0, hctotal, hcfeasible, hcmarg⟩
  obtain ⟨R⟩ := G.exists_boundedProfileRealization hlocal
    hs hs1 hβ hqstep hr
  refine ⟨R, ?_, ?_⟩
  · intro e j hpos
    exact BoundedProfileRealization.positive_largeAssign_respects_support
      G R hs (fun e ↦ edgeLabel e = label)
      (fun e he ↦ by
        by_cases h : edgeLabel e = label
        · exact h
        · simp [h] at he)
      e j hpos
  · intro e P hpos
    exact BoundedProfileRealization.positive_tinyAssign_respects_support
      G R hs (fun e ↦ edgeLabel e = label)
      (fun e he ↦ by
        by_cases h : edgeLabel e = label
        · exact h
        · simp [h] at he)
      e P hpos

end WeightedMultigraph
end WeightedEdgeColoring

namespace WeightedEdgeColoring

section ConditionalMixtureMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Mixing the conditional label marginals with their original masses
recovers every original edge marginal exactly.  A zero-mass label contributes
zero by the preceding zero-marginal lemma. -/
theorem sum_labelMass_mul_conditionalMarginal
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (edgeLabel : I → Label)
    (x : I → ℝ) (q : Finset I → ℝ)
    (hq0 : ∀ S, 0 ≤ q S)
    (hqmarg : ∀ i, (∑ S, if i ∈ S then q S else 0) = x i)
    (hqsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ a : Label, ∀ i ∈ S, edgeLabel i = a)
    (i : I) :
    (∑ label : Label,
      subsetLabelMass edgeLabel q label *
        (if 0 < subsetLabelMass edgeLabel q label then
          (if edgeLabel i = label then
            x i / subsetLabelMass edgeLabel q label else 0)
          else 0)) = x i := by
  classical
  let mass := subsetLabelMass edgeLabel q
  have hsingle :
      (∑ label : Label,
        mass label *
          (if 0 < mass label then
            (if edgeLabel i = label then x i / mass label else 0)
            else 0)) =
        mass (edgeLabel i) *
          (if 0 < mass (edgeLabel i) then
            x i / mass (edgeLabel i) else 0) := by
    calc
      (∑ label : Label,
        mass label *
          (if 0 < mass label then
            (if edgeLabel i = label then x i / mass label else 0)
            else 0)) =
          mass (edgeLabel i) *
            (if 0 < mass (edgeLabel i) then
              (if edgeLabel i = edgeLabel i then
                x i / mass (edgeLabel i) else 0) else 0) := by
        apply Finset.sum_eq_single (edgeLabel i)
        · intro label _hlabel hne
          simp [hne.symm]
        · intro hnot
          exact (hnot (Finset.mem_univ (edgeLabel i))).elim
      _ = _ := by simp
  change (∑ label : Label,
      mass label *
        (if 0 < mass label then
          (if edgeLabel i = label then x i / mass label else 0)
          else 0)) = x i
  rw [hsingle]
  by_cases hm : 0 < mass (edgeLabel i)
  · simp [hm, mul_div_cancel₀, ne_of_gt hm]
  · have hm0 : mass (edgeLabel i) = 0 := by
      have hnonneg : 0 ≤ mass (edgeLabel i) := by
        unfold mass subsetLabelMass
        apply Finset.sum_nonneg
        intro S _
        split
        · exact hq0 S
        · exact le_rfl
      exact le_antisymm (le_of_not_gt hm) hnonneg
    have hxzero : x i = 0 :=
      zero_subsetLabelMass_zero_marginal edgeLabel (edgeLabel i)
        x q hq0 hqmarg hqsingle hm0 i rfl
    simp [hm, hxzero]

end ConditionalMixtureMarginal
end WeightedEdgeColoring

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- Quantitative endpoint-label local profile package from harmonic charge.
The original color first chooses a label with its true probability mass;
conditional on that label, the existing bounded-profile transport is used.
The displayed mixture identity guarantees that this normalization preserves
all original edge marginals exactly. -/
theorem exists_chargeControlledConditionalLabelProfiles
    {v : G.V} {Label K : Type*}
    [Fintype Label] [DecidableEq Label]
    [Fintype K] [DecidableEq K]
    (capacity : K → ℕ) (hcapacity : ∀ a, 0 < capacity a)
    (edgeLabel : G.StarEdge v → Label)
    (sizeClass : G.StarEdge v → K)
    (x : G.StarEdge v → ℝ) (M : ℝ)
    (hw : ∀ e, G.weight e.1 ≤ (1 : ℝ) / capacity (sizeClass e))
    (hx0 : ∀ e, 0 ≤ x e) (hM0 : 0 ≤ M)
    (hxM : ∀ e, x e ≤ M)
    (hbudget :
      (∑ e, x e / (capacity (sizeClass e) : ℝ)) +
          (Fintype.card (Label × K) : ℝ) * M ≤ 1)
    {s β qstep r : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hqstep : 0 < qstep) (hr : 0 < r) :
    ∃ q : Finset (G.StarEdge v) → ℝ,
      (∀ S, 0 ≤ q S) ∧
      (∑ S, q S = 1) ∧
      (∀ S, q S ≠ 0 → G.StarFeasible v S) ∧
      (∀ e, (∑ S, if e ∈ S then q S else 0) = x e) ∧
      (∀ S, q S ≠ 0 → S ≠ ∅ →
        ∃ label : Label, ∀ e ∈ S, edgeLabel e = label) ∧
      (∀ label : Label,
        subsetLabelMass edgeLabel q label ≤
          ∑ a : K,
            ((∑ e, if edgeLabel e = label ∧ sizeClass e = a
              then x e else 0) / (capacity a : ℝ) + M)) ∧
      ((∑ label : Label, subsetLabelMass edgeLabel q label) ≤ 1) ∧
      (∀ label : Label, 0 < subsetLabelMass edgeLabel q label →
        ∃ R : G.BoundedProfileRealization
          (fun e ↦ if edgeLabel e = label then
            x e / subsetLabelMass edgeLabel q label else 0)
          s β qstep r hβ hr,
          (∀ e j, 0 < R.largeAssign e j → edgeLabel e = label) ∧
          (∀ e P, 0 < R.tinyAssign e P → edgeLabel e = label)) ∧
      (∀ e,
        (∑ label : Label,
          subsetLabelMass edgeLabel q label *
            (if 0 < subsetLabelMass edgeLabel q label then
              (if edgeLabel e = label then
                x e / subsetLabelMass edgeLabel q label else 0)
              else 0)) = x e) := by
  classical
  obtain ⟨q, hq0, hqsum, hqfeasible, hqmarg, hqsingle, hqbudget⟩ :=
    sizeClasses_singleLabelDistribution_of_charge capacity hcapacity
      edgeLabel sizeClass (fun e : G.StarEdge v ↦ G.weight e.1)
      x M (fun e ↦ (G.weight_pos e.1).le) hw hx0 hM0 hxM hbudget
  refine ⟨q, hq0, hqsum, hqfeasible, hqmarg, hqsingle,
    hqbudget, ?_, ?_, ?_⟩
  · exact sum_subsetLabelMass_le_one edgeLabel q
      hq0 hqsum hqsingle
  · intro label hlabel
    exact G.exists_conditionalLabelProfileRealization
      edgeLabel label x q hq0 hqfeasible hqmarg hqsingle
      hlabel hs hs1 hβ hqstep hr
  · intro e
    exact sum_labelMass_mul_conditionalMarginal
      edgeLabel x q hq0 hqmarg hqsingle e

end WeightedMultigraph
end WeightedEdgeColoring
