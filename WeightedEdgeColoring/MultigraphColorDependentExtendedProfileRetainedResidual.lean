import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileSelectedNormalizedOptions
import WeightedEdgeColoring.MultigraphProposalTrimTinyRounding

/-!
# Clipping loss on the retained macroscopic core

On a retained edge the proposal mass is at least `1-gamma`.  Therefore the
edge-dependent profile target `rho*s*proposalMass` leaves only the explicit
gap `1-rho*s*(1-gamma)`.  This file combines that observation with the
weighted quadratic block estimate.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

@[simp] theorem colorDependentTotalTarget_eq_proposalMass
    (rho s : ℝ) (e : G.E) :
    G.colorDependentTotalTarget proposal rho s e =
      rho * s * G.proposalMass proposal e := by
  rfl

/-- The private option is used only on retained macroscopic edges. -/
def selectedColorDependentRetainedMacroscopicResidual
    (gamma tau rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) : ℝ :=
  if e ∈ G.retainedMacroscopicEdges proposal gamma tau then
    G.selectedColorDependentResidualOptionMass
      proposal R rho omega choice e
  else 0

/-- The private option restricted to the full high-proposal-mass core. -/
def selectedColorDependentRetainedCoreResidual
    (gamma rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) : ℝ :=
  if e ∈ (Finset.univ \ G.lowProposalMassEdges proposal gamma) then
    G.selectedColorDependentResidualOptionMass
      proposal R rho omega choice e
  else 0

@[simp] theorem selectedColorDependentRetainedMacroscopicResidual_eq_of_mem
    (gamma tau rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (he : e ∈ G.retainedMacroscopicEdges proposal gamma tau) :
    G.selectedColorDependentRetainedMacroscopicResidual
      proposal R gamma tau rho omega choice e =
    G.selectedColorDependentResidualOptionMass
      proposal R rho omega choice e := by
  simp [selectedColorDependentRetainedMacroscopicResidual, he]

@[simp] theorem selectedColorDependentRetainedMacroscopicResidual_eq_zero_of_not_mem
    (gamma tau rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (he : e ∉ G.retainedMacroscopicEdges proposal gamma tau) :
    G.selectedColorDependentRetainedMacroscopicResidual
      proposal R gamma tau rho omega choice e = 0 := by
  simp [selectedColorDependentRetainedMacroscopicResidual, he]

/-- On a retained edge, the clipping loss is the retained-mass target gap
plus the absolute option-mass error. -/
theorem selectedColorDependentRetainedMacroscopicResidual_le_gap_add_abs
    (gamma tau rho omega : ℝ)
    (hgamma0 : 0 ≤ gamma) (hrhos0 : 0 ≤ rho * s)
    (hrhos1 : rho * s ≤ 1)
    (hmass : ∀ e, G.proposalMass proposal e ≤ 1)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) :
    G.selectedColorDependentRetainedMacroscopicResidual
        proposal R gamma tau rho omega choice e ≤
      (1 - rho * s * (1 - gamma)) +
        |G.selectedColorDependentAllOptionMass
            proposal R rho omega choice e -
          G.colorDependentTotalTarget proposal rho s e| := by
  classical
  by_cases he : e ∈ G.retainedMacroscopicEdges proposal gamma tau
  · rw [G.selectedColorDependentRetainedMacroscopicResidual_eq_of_mem
      proposal R gamma tau rho omega choice e he]
    have hhigh : 1 - gamma ≤ G.proposalMass proposal e :=
      (G.mem_retainedMacroscopicEdges proposal gamma tau e).mp he |>.1
    have htarget : G.colorDependentTotalTarget proposal rho s e ≤ 1 := by
      rw [G.colorDependentTotalTarget_eq_proposalMass]
      calc
        rho * s * G.proposalMass proposal e ≤ rho * s * 1 :=
          mul_le_mul_of_nonneg_left (hmass e) hrhos0
        _ = rho * s := by ring
        _ ≤ 1 := hrhos1
    have hbase :=
      G.selectedColorDependentResidualOptionMass_le_target_add_abs
        proposal R rho omega
          (G.colorDependentTotalTarget proposal rho s e)
          choice htarget e
    have hgap :
        1 - G.colorDependentTotalTarget proposal rho s e ≤
          1 - rho * s * (1 - gamma) := by
      rw [G.colorDependentTotalTarget_eq_proposalMass]
      have := mul_le_mul_of_nonneg_left hhigh hrhos0
      linarith
    exact hbase.trans (add_le_add hgap le_rfl)
  · rw [G.selectedColorDependentRetainedMacroscopicResidual_eq_zero_of_not_mem
      proposal R gamma tau rho omega choice e he]
    have habs : 0 ≤ |G.selectedColorDependentAllOptionMass
          proposal R rho omega choice e -
        G.colorDependentTotalTarget proposal rho s e| := abs_nonneg _
    have hfactor : 1 - gamma ≤ 1 := by linarith
    have hprod : rho * s * (1 - gamma) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hfactor hrhos0).trans
        (by simpa using hrhos1)
    linarith

/-- The retained-core private residual has a uniform star bound.  The
quadratic error may be estimated on the whole star, so no extra dependence
on the retained set enters the Cauchy term. -/
theorem weightedResidualStar_selectedColorDependentRetained_le_sqrt
    (gamma tau rho omega : ℝ)
    (hgamma0 : 0 ≤ gamma) (hrhos0 : 0 ≤ rho * s)
    (hrhos1 : rho * s ≤ 1)
    (hmass : ∀ e, G.proposalMass proposal e ≤ 1)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (v : G.V) (sigma : ℝ) (hsigma0 : 0 ≤ sigma)
    (hquad :
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedColorDependentAllOptionMass
            proposal R rho omega choice e.1 -
          G.colorDependentTotalTarget proposal rho s e.1) ^ 2) ≤ sigma) :
    G.weightedResidualStar
        (G.selectedColorDependentRetainedMacroscopicResidual
          proposal R gamma tau rho omega choice) v ≤
      (1 - rho * s * (1 - gamma)) * G.starWeight v +
        Real.sqrt (G.starWeight v * sigma) := by
  classical
  let gap := 1 - rho * s * (1 - gamma)
  have hpoint (e : G.E) :
      (if G.Inc v e then
          G.selectedColorDependentRetainedMacroscopicResidual
              proposal R gamma tau rho omega choice e * G.weight e
        else 0) ≤
      (if G.Inc v e then
          (gap +
            |G.selectedColorDependentAllOptionMass
                proposal R rho omega choice e -
              G.colorDependentTotalTarget proposal rho s e|) * G.weight e
        else 0) := by
    by_cases hinc : G.Inc v e
    · simp only [if_pos hinc]
      exact mul_le_mul_of_nonneg_right
        (G.selectedColorDependentRetainedMacroscopicResidual_le_gap_add_abs
          proposal R gamma tau rho omega hgamma0 hrhos0 hrhos1 hmass choice e)
        (G.weight_nonneg e)
    · simp [hinc]
  have habs := G.selectedColorDependentAbsoluteError_le_sqrt
    proposal R rho omega choice
      (G.colorDependentTotalTarget proposal rho s) v sigma hsigma0 hquad
  unfold weightedResidualStar
  calc
    (∑ e, if G.Inc v e then
        G.selectedColorDependentRetainedMacroscopicResidual
          proposal R gamma tau rho omega choice e * G.weight e else 0) ≤
      ∑ e, if G.Inc v e then
        (gap +
          |G.selectedColorDependentAllOptionMass
              proposal R rho omega choice e -
            G.colorDependentTotalTarget proposal rho s e|) * G.weight e
        else 0 := Finset.sum_le_sum fun e _ ↦ hpoint e
    _ = gap * G.starWeight v +
        ∑ e : G.StarEdge v, G.weight e.1 *
          |G.selectedColorDependentAllOptionMass
              proposal R rho omega choice e.1 -
            G.colorDependentTotalTarget proposal rho s e.1| := by
      calc
        (∑ e : G.E, if G.Inc v e then
            (gap + |G.selectedColorDependentAllOptionMass
                proposal R rho omega choice e -
              G.colorDependentTotalTarget proposal rho s e|) * G.weight e
            else 0) =
            ∑ e ∈ (Finset.univ : Finset G.E).filter (G.Inc v),
              (gap + |G.selectedColorDependentAllOptionMass
                  proposal R rho omega choice e -
                G.colorDependentTotalTarget proposal rho s e|) * G.weight e := by
          rw [Finset.sum_filter]
        _ = ∑ e : G.StarEdge v,
              (gap + |G.selectedColorDependentAllOptionMass
                  proposal R rho omega choice e.1 -
                G.colorDependentTotalTarget proposal rho s e.1|) *
                G.weight e.1 := by
          exact Finset.sum_subtype
            ((Finset.univ : Finset G.E).filter (G.Inc v))
            (by intro e; simp)
            (fun e ↦ (gap + |G.selectedColorDependentAllOptionMass
              proposal R rho omega choice e -
              G.colorDependentTotalTarget proposal rho s e|) * G.weight e)
        _ = _ := by
          unfold starWeight
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro e _he
          ring
    _ ≤ gap * G.starWeight v + Real.sqrt (G.starWeight v * sigma) :=
      add_le_add le_rfl habs

/-- The residual-star estimate for the full retained proposal core, with no
weight-threshold restriction. -/
theorem weightedResidualStar_selectedColorDependentRetainedCore_le_sqrt
    (gamma rho omega : ℝ)
    (hgamma0 : 0 ≤ gamma) (hrhos0 : 0 ≤ rho * s)
    (hrhos1 : rho * s ≤ 1)
    (hmass : ∀ e, G.proposalMass proposal e ≤ 1)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (v : G.V) (sigma : ℝ) (hsigma0 : 0 ≤ sigma)
    (hquad :
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedColorDependentAllOptionMass
            proposal R rho omega choice e.1 -
          G.colorDependentTotalTarget proposal rho s e.1) ^ 2) ≤ sigma) :
    G.weightedResidualStar
        (G.selectedColorDependentRetainedCoreResidual
          proposal R gamma rho omega choice) v ≤
      (1 - rho * s * (1 - gamma)) * G.starWeight v +
        Real.sqrt (G.starWeight v * sigma) := by
  classical
  let gap := 1 - rho * s * (1 - gamma)
  have hgap0 : 0 ≤ gap := by
    have hfactor : 1 - gamma ≤ 1 := by linarith
    have hprod : rho * s * (1 - gamma) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hfactor hrhos0).trans
        (by simpa using hrhos1)
    dsimp [gap]
    linarith
  have hpoint (e : G.E) :
      G.selectedColorDependentRetainedCoreResidual
          proposal R gamma rho omega choice e ≤
        gap + |G.selectedColorDependentAllOptionMass
            proposal R rho omega choice e -
          G.colorDependentTotalTarget proposal rho s e| := by
    by_cases he : e ∈ (Finset.univ \ G.lowProposalMassEdges proposal gamma)
    · have hhigh : 1 - gamma ≤ G.proposalMass proposal e := by
        have hnlow : ¬ G.proposalMass proposal e < 1 - gamma := by
          have heNot := (Finset.mem_sdiff.mp he).2
          simpa [lowProposalMassEdges] using heNot
        exact le_of_not_gt hnlow
      have htarget : G.colorDependentTotalTarget proposal rho s e ≤ 1 := by
        rw [G.colorDependentTotalTarget_eq_proposalMass]
        calc
          rho * s * G.proposalMass proposal e ≤ rho * s * 1 :=
            mul_le_mul_of_nonneg_left (hmass e) hrhos0
          _ = rho * s := by ring
          _ ≤ 1 := hrhos1
      have hbase :=
        G.selectedColorDependentResidualOptionMass_le_target_add_abs
          proposal R rho omega
            (G.colorDependentTotalTarget proposal rho s e)
            choice htarget e
      have htargetLower : rho * s * (1 - gamma) ≤
          G.colorDependentTotalTarget proposal rho s e := by
        rw [G.colorDependentTotalTarget_eq_proposalMass]
        exact mul_le_mul_of_nonneg_left hhigh hrhos0
      simp only [selectedColorDependentRetainedCoreResidual, he, if_true]
      exact hbase.trans (by dsimp [gap]; gcongr)
    · simp only [selectedColorDependentRetainedCoreResidual, he, if_false]
      exact add_nonneg hgap0 (abs_nonneg _)
  have habs := G.selectedColorDependentAbsoluteError_le_sqrt
    proposal R rho omega choice
      (G.colorDependentTotalTarget proposal rho s) v sigma hsigma0 hquad
  unfold weightedResidualStar
  calc
    (∑ e, if G.Inc v e then
      G.selectedColorDependentRetainedCoreResidual
          proposal R gamma rho omega choice e * G.weight e else 0) ≤
      ∑ e, if G.Inc v e then
        (gap + |G.selectedColorDependentAllOptionMass
            proposal R rho omega choice e -
          G.colorDependentTotalTarget proposal rho s e|) * G.weight e else 0 := by
      apply Finset.sum_le_sum
      intro e _he
      by_cases hinc : G.Inc v e
      · simp only [hinc, if_true]
        exact mul_le_mul_of_nonneg_right (hpoint e) (G.weight_nonneg e)
      · simp [hinc]
    _ = gap * G.starWeight v +
        ∑ e : G.StarEdge v, G.weight e.1 *
          |G.selectedColorDependentAllOptionMass
              proposal R rho omega choice e.1 -
            G.colorDependentTotalTarget proposal rho s e.1| := by
      calc
        (∑ e : G.E, if G.Inc v e then
            (gap + |G.selectedColorDependentAllOptionMass
                proposal R rho omega choice e -
              G.colorDependentTotalTarget proposal rho s e|) * G.weight e
            else 0) =
            ∑ e ∈ (Finset.univ : Finset G.E).filter (G.Inc v),
              (gap + |G.selectedColorDependentAllOptionMass
                  proposal R rho omega choice e -
                G.colorDependentTotalTarget proposal rho s e|) * G.weight e := by
          rw [Finset.sum_filter]
        _ = ∑ e : G.StarEdge v,
              (gap + |G.selectedColorDependentAllOptionMass
                  proposal R rho omega choice e.1 -
                G.colorDependentTotalTarget proposal rho s e.1|) *
                G.weight e.1 := by
          exact Finset.sum_subtype
            ((Finset.univ : Finset G.E).filter (G.Inc v))
            (by intro e; simp)
            (fun e ↦ (gap + |G.selectedColorDependentAllOptionMass
              proposal R rho omega choice e -
              G.colorDependentTotalTarget proposal rho s e|) * G.weight e)
        _ = _ := by
          unfold starWeight
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro e _he
          ring
    _ ≤ gap * G.starWeight v + Real.sqrt (G.starWeight v * sigma) :=
      add_le_add le_rfl habs

end WeightedMultigraph

end

end WeightedEdgeColoring
