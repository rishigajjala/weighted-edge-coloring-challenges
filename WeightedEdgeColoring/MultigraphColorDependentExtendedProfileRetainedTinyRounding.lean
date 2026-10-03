import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileSelectedCapacityOptionBridge
import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileRetainedResidual
import WeightedEdgeColoring.MultigraphTinyEdgeResidualRounding

/-!
# Rounding retained color-dependent tiny options

The high-proposal-mass edges below the profile threshold are rounded from
the selected normalized tiny array itself.  Colors are flattened only at
the call to the generic finite tiny-edge rounding theorem.
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

/-- High-proposal-mass edges handled by the profile-tiny rounding step. -/
def retainedColorDependentTinyEdges (gamma β : ℝ) : Finset G.E :=
  (Finset.univ \ G.lowProposalMassEdges proposal gamma).filter
    fun e ↦ G.weight e < β

@[simp] theorem mem_retainedColorDependentTinyEdges
    (gamma β : ℝ) (e : G.E) :
    e ∈ G.retainedColorDependentTinyEdges proposal gamma β ↔
      1 - gamma ≤ G.proposalMass proposal e ∧ G.weight e < β := by
  simp [retainedColorDependentTinyEdges, lowProposalMassEdges]

/-- Flatten the selected tiny option array to `Fin (B*k)`. -/
def flattenedSelectedColorDependentNormalizedTiny
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin (B * k)) : ℝ :=
  G.selectedColorDependentNormalizedTinyOptionMass
    proposal R rho omega choice e (finProdFinEquiv.symm c)

/-- A retained tiny fractional row is bounded by the selected reservoir
load on the corresponding product color. -/
theorem tinyResidualColorLoad_flattenedSelectedTiny_le
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (gamma : ℝ)
    (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k) :
    G.tinyResidualColorLoad
        (G.retainedColorDependentTinyEdges proposal gamma β)
        (fun e d ↦ G.flattenedSelectedColorDependentNormalizedTiny
          proposal R rho omega
            (G.encodedColorDependentSelectedBlock proposal R selected)
            e.1 d) v (finProdFinEquiv c) ≤
      G.selectedColorDependentNormalizedTinyReservoirLoad
        proposal R rho omega selected v c := by
  classical
  let T := G.retainedColorDependentTinyEdges proposal gamma β
  let f : G.E → ℝ := fun e ↦ if G.Inc v e then
    G.weight e * G.selectedColorDependentNormalizedTinyOptionMass
      proposal R rho omega
        (G.encodedColorDependentSelectedBlock proposal R selected) e c else 0
  have hf0 : ∀ e, 0 ≤ f e := by
    intro e
    by_cases hinc : G.Inc v e
    · simp only [f, hinc, if_true]
      exact mul_nonneg (G.weight_nonneg e)
        (G.selectedColorDependentNormalizedTinyOptionMass_nonneg proposal R
          hs hq hr0 hleft homega0 homega1 hrho
          (G.encodedColorDependentSelectedBlock proposal R selected) e c)
    · simp [f, hinc]
  calc
    G.tinyResidualColorLoad T
        (fun e d ↦ G.flattenedSelectedColorDependentNormalizedTiny
          proposal R rho omega
            (G.encodedColorDependentSelectedBlock proposal R selected)
            e.1 d) v (finProdFinEquiv c) =
      ∑ e ∈ T, f e := by
        unfold tinyResidualColorLoad
        rw [Finset.sum_subtype (p := fun e : G.E ↦ e ∈ T) T
          (by intro e; simp)]
        apply Finset.sum_congr rfl
        intro e _he
        by_cases hinc : G.Inc v e
        · simp [f, hinc, flattenedSelectedColorDependentNormalizedTiny,
            mul_comm]
        · simp [f, hinc]
    _ ≤ ∑ e, f e := Finset.sum_le_univ_sum_of_nonneg hf0
    _ = G.selectedColorDependentNormalizedTinyReservoirLoad
        proposal R rho omega selected v c := by
      unfold selectedColorDependentNormalizedTinyReservoirLoad
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hinc : G.Inc v e <;> simp [f, hinc, mul_comm]

/-- The fractional uncolored loss on retained tiny edges is a sub-sum of
the retained-core residual star. -/
theorem tinyResidualLossLoad_retainedColorDependentTiny_le
    (gamma rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (v : G.V) :
    G.tinyResidualLossLoad
        (G.retainedColorDependentTinyEdges proposal gamma β)
        (fun e ↦ G.selectedColorDependentResidualOptionMass
          proposal R rho omega choice e.1) v ≤
      G.weightedResidualStar
        (G.selectedColorDependentRetainedCoreResidual
          proposal R gamma rho omega choice) v := by
  classical
  let T := G.retainedColorDependentTinyEdges proposal gamma β
  let f : G.E → ℝ := fun e ↦ if G.Inc v e then
    G.selectedColorDependentResidualOptionMass
      proposal R rho omega choice e * G.weight e else 0
  have hf0 : ∀ e, 0 ≤ f e := by
    intro e
    by_cases hinc : G.Inc v e
    · simp only [f, hinc, if_true]
      exact mul_nonneg
        (G.selectedColorDependentResidualOptionMass_nonneg
          proposal R rho omega choice e)
        (G.weight_nonneg e)
    · simp [f, hinc]
  calc
    G.tinyResidualLossLoad T
        (fun e ↦ G.selectedColorDependentResidualOptionMass
          proposal R rho omega choice e.1) v =
      ∑ e ∈ T, f e := by
        unfold tinyResidualLossLoad
        rw [Finset.sum_subtype (p := fun e : G.E ↦ e ∈ T) T
          (by intro e; simp)]
    _ = ∑ e, if e ∈ T then f e else 0 := by
      classical
      simp
    _ ≤ ∑ e, if G.Inc v e then
        G.selectedColorDependentRetainedCoreResidual
          proposal R gamma rho omega choice e * G.weight e else 0 := by
      apply Finset.sum_le_sum
      intro e _he
      by_cases he : e ∈ T
      · have hhigh : e ∈
            (Finset.univ \ G.lowProposalMassEdges proposal gamma) := by
          apply Finset.mem_sdiff.mpr
          refine ⟨Finset.mem_univ e, ?_⟩
          have hp := (G.mem_retainedColorDependentTinyEdges
            proposal gamma β e).mp he |>.1
          simpa [lowProposalMassEdges] using (not_lt_of_ge hp)
        simp [f, he, hhigh,
          selectedColorDependentRetainedCoreResidual]
      · have hres0 : 0 ≤
            G.selectedColorDependentRetainedCoreResidual
              proposal R gamma rho omega choice e := by
          unfold selectedColorDependentRetainedCoreResidual
          split
          · exact G.selectedColorDependentResidualOptionMass_nonneg
              proposal R rho omega choice e
          · exact le_rfl
        by_cases hinc : G.Inc v e
        · simp only [he, if_false, hinc, if_true]
          exact mul_nonneg hres0 (G.weight_nonneg e)
        · simp [he, hinc]
    _ = G.weightedResidualStar
        (G.selectedColorDependentRetainedCoreResidual
          proposal R gamma rho omega choice) v := by
      rfl

/-- Unconditional color-or-residual rounding on retained profile-tiny edges.
The selected color has positive original proposal support, and both integral
color load and uncolored weight retain the generic additive `2*β` error. -/
theorem exists_retainedColorDependentTinyDecision
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (gamma : ℝ)
    (selected : G.ColorDependentSelectedStates proposal R) :
    ∃ decision : {e : G.E // e ∈
        G.retainedColorDependentTinyEdges proposal gamma β} →
          Option (Fin (B * k)),
      (∀ e c, decision e = some c →
        0 < proposal e.1 (finProdFinEquiv.symm c) ∧
        0 < G.colorDependentExtendedProfileReservoirSize R
          (G.fst e.1) (finProdFinEquiv.symm c)
          (selected (G.fst e.1) (finProdFinEquiv.symm c).1
            (finProdFinEquiv.symm c).2) ∧
        0 < G.colorDependentExtendedProfileReservoirSize R
          (G.snd e.1) (finProdFinEquiv.symm c)
          (selected (G.snd e.1) (finProdFinEquiv.symm c).1
            (finProdFinEquiv.symm c).2)) ∧
      (∀ e, decision e = none →
        0 < G.selectedColorDependentResidualOptionMass proposal R rho omega
          (G.encodedColorDependentSelectedBlock proposal R selected) e.1) ∧
      (∀ v c,
        G.tinyResidualIntegralColorLoad decision v (finProdFinEquiv c) ≤
          G.selectedColorDependentNormalizedTinyReservoirLoad
            proposal R rho omega selected v c + 2 * β) ∧
      ∀ v,
        G.tinyResidualIntegralLossLoad decision v ≤
          G.tinyResidualLossLoad
            (G.retainedColorDependentTinyEdges proposal gamma β)
            (fun e ↦ G.selectedColorDependentResidualOptionMass
              proposal R rho omega
                (G.encodedColorDependentSelectedBlock proposal R selected) e.1) v +
            2 * β := by
  let T := G.retainedColorDependentTinyEdges proposal gamma β
  let choice := G.encodedColorDependentSelectedBlock proposal R selected
  let x : {e : G.E // e ∈ T} → Fin (B * k) → ℝ := fun e c ↦
    G.flattenedSelectedColorDependentNormalizedTiny
      proposal R rho omega choice e.1 c
  let residual : {e : G.E // e ∈ T} → ℝ := fun e ↦
    G.selectedColorDependentResidualOptionMass
      proposal R rho omega choice e.1
  have hx0 : ∀ e c, 0 ≤ x e c := by
    intro e c
    exact G.selectedColorDependentNormalizedTinyOptionMass_nonneg proposal R
      hs hq hr0 hleft homega0 homega1 hrho choice e.1
        (finProdFinEquiv.symm c)
  have hres0 : ∀ e, 0 ≤ residual e := fun e ↦
    G.selectedColorDependentResidualOptionMass_nonneg
      proposal R rho omega choice e.1
  have htotal : ∀ e, (∑ c, x e c) + residual e = 1 := by
    intro e
    have htiny : G.weight e.1 < β :=
      (G.mem_retainedColorDependentTinyEdges proposal gamma β e.1).mp e.2 |>.2
    have hbase :=
      G.sum_selectedColorDependentNormalizedTiny_add_residual_of_tiny
        proposal R hs hq hr0 hleft homega0 homega1 hrho choice e.1 htiny
    have hreindex : (∑ c : Fin (B * k), x e c) =
        ∑ c : Fin B × Fin k,
          G.selectedColorDependentNormalizedTinyOptionMass
            proposal R rho omega choice e.1 c := by
      simpa [x, flattenedSelectedColorDependentNormalizedTiny] using
        (Equiv.sum_comp finProdFinEquiv.symm
          (fun c : Fin B × Fin k ↦
            G.selectedColorDependentNormalizedTinyOptionMass
              proposal R rho omega choice e.1 c))
    simpa [residual, hreindex] using hbase
  have hweight : ∀ e ∈ T, G.weight e ≤ β := by
    intro e he
    exact ((G.mem_retainedColorDependentTinyEdges proposal gamma β e).mp he).2.le
  obtain ⟨decision, hpos, hres, hcolor, hloss⟩ :=
    G.exists_tinyColorDecision T β hβ x residual hx0 hres0 htotal hweight
  refine ⟨decision, ?_, ?_, ?_, hloss⟩
  · intro e c hec
    have hp : 0 < G.selectedColorDependentNormalizedTinyOptionMass
        proposal R rho omega choice e.1 (finProdFinEquiv.symm c) := by
      simpa [x, flattenedSelectedColorDependentNormalizedTiny] using
        hpos e c hec
    have hproposal :=
      G.proposal_pos_of_selectedColorDependentNormalizedTiny_pos
        proposal R hproposal0 rho omega choice e.1
          (finProdFinEquiv.symm c) hp
    have hraw :=
      (G.selectedColorDependentNormalizedTinyOptionMass_pos_iff
        proposal R rho omega choice e.1 (finProdFinEquiv.symm c)).mp hp
    have hreservoir :=
      G.colorDependentExtendedProfileTinyProductMass_pos_reservoirs
        proposal R hs hq hr0 hleft homega0 homega1 hrho e.1
          (finProdFinEquiv.symm c)
          (selected (G.fst e.1) (finProdFinEquiv.symm c).1
            (finProdFinEquiv.symm c).2)
          (selected (G.snd e.1) (finProdFinEquiv.symm c).1
            (finProdFinEquiv.symm c).2) (by
              simpa [choice, selectedColorDependentTinyOptionMass,
                G.decode_encodedColorDependentSelectedBlock] using hraw)
    exact ⟨hproposal, hreservoir⟩
  · intro e he
    simpa [residual] using hres e he
  · intro v c
    have htiny :=
      G.tinyResidualColorLoad_flattenedSelectedTiny_le proposal R
        hs hq hr0 hleft homega0 homega1 hrho gamma selected v c
    exact (hcolor v (finProdFinEquiv c)).trans
      (by simpa [add_comm] using add_le_add_right htiny (2 * β))

end WeightedMultigraph

end

end WeightedEdgeColoring
