import WeightedEdgeColoring.SubtwoMixedGraphBlockVariance
import WeightedEdgeColoring.SubtwoSelectedResidualVarianceBridge

/-!
# From selected block squares to the clipped residual

This deterministic bridge is where the block-variance rows control the
normalization loss.  It does not presume that the raw whole-edge option mass
is at most one.
-/

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

def selectedMixedBlockTotalOptionMass
    (rho omega : ℝ)
    (choice : (v : G.V) → (b : Fin B) →
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (e : G.E) : ℝ :=
  ∑ b : Fin B,
    G.mixedBlockOptionMass proposal edgeLabel qLaw R
      rho omega e b (choice (G.fst e) b) (choice (G.snd e) b)

def mixedBlockTotalTarget (rho s : ℝ) (e : G.E) : ℝ :=
  ∑ b : Fin B, G.mixedBlockTarget proposal rho s e b

theorem selectedMixedBlockTotalOptionMass_weightedSquare_le
    (rho omega : ℝ)
    (choice : (v : G.V) → (b : Fin B) →
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (e : G.E) :
    G.weight e *
      (G.selectedMixedBlockTotalOptionMass
        proposal edgeLabel qLaw R rho omega choice e -
        G.mixedBlockTotalTarget proposal rho s e) ^ 2 ≤
      (B : ℝ) * ∑ b : Fin B,
        G.mixedBlockVariance proposal edgeLabel qLaw R rho omega e b
          (choice (G.fst e) b) (choice (G.snd e) b) := by
  have hsum :
      G.selectedMixedBlockTotalOptionMass
          proposal edgeLabel qLaw R rho omega choice e -
        G.mixedBlockTotalTarget proposal rho s e =
      ∑ b : Fin B,
        (G.mixedBlockOptionMass proposal edgeLabel qLaw R
          rho omega e b (choice (G.fst e) b) (choice (G.snd e) b) -
          G.mixedBlockTarget proposal rho s e b) := by
    unfold selectedMixedBlockTotalOptionMass mixedBlockTotalTarget
    rw [Finset.sum_sub_distrib]
  rw [hsum]
  have hsquare := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ)
    (f := fun b : Fin B ↦
      G.mixedBlockOptionMass proposal edgeLabel qLaw R
        rho omega e b (choice (G.fst e) b) (choice (G.snd e) b) -
      G.mixedBlockTarget proposal rho s e b)
  calc
    G.weight e * (∑ b : Fin B,
      (G.mixedBlockOptionMass proposal edgeLabel qLaw R
        rho omega e b (choice (G.fst e) b) (choice (G.snd e) b) -
      G.mixedBlockTarget proposal rho s e b)) ^ 2 ≤
        G.weight e * ((B : ℝ) * ∑ b : Fin B,
          (G.mixedBlockOptionMass proposal edgeLabel qLaw R
            rho omega e b (choice (G.fst e) b) (choice (G.snd e) b) -
          G.mixedBlockTarget proposal rho s e b) ^ 2) :=
      mul_le_mul_of_nonneg_left (by simpa using hsquare)
        (G.weight_pos e).le
    _ = (B : ℝ) * ∑ b : Fin B,
        G.mixedBlockVariance proposal edgeLabel qLaw R rho omega e b
          (choice (G.fst e) b) (choice (G.snd e) b) := by
      simp only [mixedBlockVariance, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

theorem sum_selectedMixedBlockTotalOptionMass_weightedSquare_le
    (rho omega : ℝ)
    (choice : (v : G.V) → (b : Fin B) →
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b) :
    (∑ e : G.E, G.weight e *
      (G.selectedMixedBlockTotalOptionMass
        proposal edgeLabel qLaw R rho omega choice e -
        G.mixedBlockTotalTarget proposal rho s e) ^ 2) ≤
      (B : ℝ) * ∑ e : G.E, ∑ b : Fin B,
        G.mixedBlockVariance proposal edgeLabel qLaw R rho omega e b
          (choice (G.fst e) b) (choice (G.snd e) b) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  exact G.selectedMixedBlockTotalOptionMass_weightedSquare_le
    proposal edgeLabel qLaw R rho omega choice e

theorem selectedMixedBlockClippedResidual_le
    (rho omega t : ℝ) (ht : 0 < t)
    (choice : (v : G.V) → (b : Fin B) →
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b) :
    (∑ e : G.E, G.weight e *
      (1 - min 1 (G.selectedMixedBlockTotalOptionMass
        proposal edgeLabel qLaw R rho omega choice e))) ≤
      (∑ e : G.E, G.weight e *
        max 0 (1 - G.mixedBlockTotalTarget proposal rho s e)) +
      t * (∑ e : G.E, G.weight e) +
      ((B : ℝ) * ∑ e : G.E, ∑ b : Fin B,
        G.mixedBlockVariance proposal edgeLabel qLaw R rho omega e b
          (choice (G.fst e) b) (choice (G.snd e) b)) / (4 * t) := by
  have ht4 : 0 ≤ 4 * t := by positivity
  have hvar := G.sum_selectedMixedBlockTotalOptionMass_weightedSquare_le
    proposal edgeLabel qLaw R rho omega choice
  have hdiv := div_le_div_of_nonneg_right hvar ht4
  have hclip := sum_clipped_residual_le_mean_deficit_add_variance
    G.weight
    (G.selectedMixedBlockTotalOptionMass
      proposal edgeLabel qLaw R rho omega choice)
    (G.mixedBlockTotalTarget proposal rho s)
    t ht (fun e ↦ (G.weight_pos e).le)
  exact hclip.trans (by
    simpa [add_comm, add_left_comm, add_assoc] using
      (add_le_add_left hdiv
        ((∑ e : G.E, G.weight e *
          max 0 (1 - G.mixedBlockTotalTarget proposal rho s e)) +
          t * (∑ e : G.E, G.weight e))))

end WeightedMultigraph

end
end WeightedEdgeColoring
