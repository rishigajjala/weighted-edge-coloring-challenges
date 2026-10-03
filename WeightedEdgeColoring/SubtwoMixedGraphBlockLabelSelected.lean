import WeightedEdgeColoring.SubtwoMixedGraphBlockSharpResidual

/-! Endpoint-label charges retained by the mixed block joint selector. -/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {B k : ℕ} {Label : Type*} [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
variable (qLaw : ∀ v : G.V, (Fin B × Fin k) →
  Finset (G.StarEdge v) → ℝ)
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : ∀ v c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel v)
      (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
    s β qstep r hβ hr)

def selectedMixedBlockLabelCount
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (v : G.V) (label : Label) : ℝ :=
  ∑ b : Fin B, ∑ i : Fin k,
    if G.decodeMixedGraphLabel
      (G.mixedBlockProposal proposal b) edgeLabel
      (G.mixedBlockLaw qLaw b)
      (G.mixedBlockRealization proposal edgeLabel qLaw R b)
      v (choice v b) i = some label then 1 else 0

theorem selectedMixedBlockLabel_rowLoad_eq
    (n : ℕ) (candidateScale rho omega pairScale selfScale : ℝ)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (v : G.V) (label : Label) :
    FiniteCategoricalSelection.rowLoad
      (G.mixedBlockJointUse proposal edgeLabel qLaw R
        n candidateScale rho omega pairScale selfScale)
      (Sum.inr (v, some label))
      (fun source ↦ choice source.1 source.2) =
    G.selectedMixedBlockLabelCount proposal edgeLabel qLaw R
      choice v label / (k : ℝ) := by
  classical
  unfold FiniteCategoricalSelection.rowLoad
    selectedMixedBlockLabelCount
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single v]
  · simp [mixedBlockJointUse, mixedBlockLabelUse, Finset.sum_div]
  · intro v' _ hv
    simp [mixedBlockJointUse, mixedBlockLabelUse, hv, Ne.symm hv]
  · simp

theorem mixedBlockLabel_rowMean_le_charge
    (hk : 0 < k) (omega : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (homega0 : 0 ≤ omega) (homega1 : omega ≤ 1)
    (v : G.V) (label : Label) :
    FiniteCategoricalSelection.rowMean
      (fun source : G.V × Fin B ↦
        G.mixedBlockProbability proposal edgeLabel qLaw R
          omega source.1 source.2)
      (G.mixedBlockLabelUse proposal edgeLabel qLaw R)
      (v, some label) ≤
    ((∑ c : Fin B × Fin k,
      subsetLabelMass (edgeLabel v) (qLaw v c) label) +
      ((B : ℝ) * k) * omega) / (k : ℝ) := by
  classical
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  unfold FiniteCategoricalSelection.rowMean
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    (∑ b : Fin B, ∑ source : G.V,
      ∑ state : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b,
      G.mixedBlockProbability proposal edgeLabel qLaw R
        omega source b state *
      G.mixedBlockLabelUse proposal edgeLabel qLaw R
        (source, b) state (v, some label)) =
      ∑ b : Fin B,
        (∑ state : G.MixedGraphPackedBlockState
          proposal edgeLabel qLaw R b,
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega v b state *
          (∑ i : Fin k,
            if G.decodeMixedGraphLabel
              (G.mixedBlockProposal proposal b) edgeLabel
              (G.mixedBlockLaw qLaw b)
              (G.mixedBlockRealization proposal edgeLabel qLaw R b)
              v state i = some label then (1 : ℝ) else 0)) /
            (k : ℝ) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_eq_single v]
      · rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro state _
        simp [mixedBlockLabelUse, mul_div_assoc]
      · intro v' _ hv
        simp [mixedBlockLabelUse, hv, Ne.symm hv]
      · simp
    _ ≤ ∑ b : Fin B,
        ((∑ i : Fin k,
          subsetLabelMass (edgeLabel v) (qLaw v (b, i)) label) +
          (k : ℝ) * omega) / (k : ℝ) := by
      apply Finset.sum_le_sum
      intro b _
      apply div_le_div_of_nonneg_right _ hkreal.le
      simpa [mixedBlockProbability, mixedBlockLaw] using
        (G.sum_paddedMixedGraphProbability_mul_labelCount_le
          (G.mixedBlockProposal proposal b) edgeLabel
          (G.mixedBlockLaw qLaw b)
          (G.mixedBlockRealization proposal edgeLabel qLaw R b)
          (fun v i S ↦ hq0 v (b, i) S)
          homega0 homega1 v label)
    _ = _ := by
      rw [← Finset.sum_div]
      rw [Fintype.sum_prod_type]
      simp [Finset.sum_add_distrib, Finset.sum_mul]
      ring

theorem selectedMixedBlockLabelCount_lt_charge
    (hk : 0 < k) (n : ℕ)
    (candidateScale rho omega pairScale selfScale deviation : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (homega0 : 0 ≤ omega) (homega1 : omega ≤ 1)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (v : G.V) (label : Label)
    (hrow :
      FiniteCategoricalSelection.rowLoad
        (G.mixedBlockJointUse proposal edgeLabel qLaw R
          n candidateScale rho omega pairScale selfScale)
        (Sum.inr (v, some label))
        (fun source ↦ choice source.1 source.2) <
      FiniteCategoricalSelection.rowMean
        (fun source : G.V × Fin B ↦
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega source.1 source.2)
        (G.mixedBlockJointUse proposal edgeLabel qLaw R
          n candidateScale rho omega pairScale selfScale)
        (Sum.inr (v, some label)) + deviation) :
    G.selectedMixedBlockLabelCount proposal edgeLabel qLaw R
      choice v label <
      (∑ c : Fin B × Fin k,
        subsetLabelMass (edgeLabel v) (qLaw v c) label) +
      ((B : ℝ) * k) * omega + (k : ℝ) * deviation := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  rw [G.selectedMixedBlockLabel_rowLoad_eq
    proposal edgeLabel qLaw R n candidateScale rho omega
    pairScale selfScale choice v label] at hrow
  change G.selectedMixedBlockLabelCount proposal edgeLabel qLaw R
      choice v label / (k : ℝ) <
    FiniteCategoricalSelection.rowMean
      (fun source : G.V × Fin B ↦
        G.mixedBlockProbability proposal edgeLabel qLaw R
          omega source.1 source.2)
      (G.mixedBlockLabelUse proposal edgeLabel qLaw R)
      (v, some label) + deviation at hrow
  have hmean := G.mixedBlockLabel_rowMean_le_charge
    proposal edgeLabel qLaw R hk omega hq0 homega0 homega1 v label
  have hbound := lt_of_lt_of_le hrow (add_le_add hmean le_rfl)
  have hscaled := (div_lt_iff₀ hkreal).mp hbound
  calc
    G.selectedMixedBlockLabelCount proposal edgeLabel qLaw R
        choice v label <
      (((∑ c : Fin B × Fin k,
          subsetLabelMass (edgeLabel v) (qLaw v c) label) +
        ((B : ℝ) * k) * omega) / (k : ℝ) + deviation) * k := hscaled
    _ = _ := by field_simp [ne_of_gt hkreal]

end WeightedMultigraph

end
end WeightedEdgeColoring
