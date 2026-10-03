import WeightedEdgeColoring.MultigraphExtendedProfileBlockVarianceRows
import WeightedEdgeColoring.QuadraticNormalization
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# From block variance to whole-edge quadratic error

The selected option mass of an edge is the sum of its block masses.  The
square of its total error is therefore at most the number of blocks times
the sum of the squared block errors.  This file also identifies the direct
star sum with the candidate-row load used by the finite PRA.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- Selected unnormalised option mass in one block of one edge. -/
def selectedExtendedProfileBlockOptionMass
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (b : Fin B) : ℝ :=
  G.extendedProfileBlockOptionMass R0 rho omega e
    (choice (G.fst e, b)) (choice (G.snd e, b))

/-- Total unnormalised option mass of one edge after all blocks are joined. -/
def selectedExtendedProfileTotalOptionMass
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) : ℝ :=
  ∑ b, G.selectedExtendedProfileBlockOptionMass R0 rho omega choice e b

/-- The candidate-row load for one block is exactly the direct variance sum
over the star at its center. -/
theorem selectedRawExtendedProfileBlockVariance_eq_star_sum
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (v : G.V) (b : Fin B) :
    G.selectedRawExtendedProfileBlockVariance R0 rho omega choice v b =
      ∑ e : G.StarEdge v,
        G.extendedProfileBlockVariance R0 rho omega e.1
          (choice (G.fst e.1, b)) (choice (G.snd e.1, b)) := by
  classical
  unfold selectedRawExtendedProfileBlockVariance
    FiniteCategoricalSelection.rowLoad
    rawExtendedProfileBlockVarianceCandidateUse
  rw [Finset.sum_comm]
  calc
    (∑ e : G.E, ∑ source : G.V × Fin B,
        G.extendedProfileBlockVarianceCandidateEdgeUse R0 rho omega
          source (choice source) e (v, b, choice (v, b))) =
        ∑ e : G.E, if G.Inc v e then
          G.extendedProfileBlockVariance R0 rho omega e
            (choice (G.fst e, b)) (choice (G.snd e, b)) else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [Fintype.sum_prod_type]
      by_cases hfst : v = G.fst e
      · subst v
        have hne : G.fst e ≠ G.snd e := G.noLoop e
        simp [extendedProfileBlockVarianceCandidateEdgeUse,
          WeightedMultigraph.Inc, hne]
      · by_cases hsnd : v = G.snd e
        · subst v
          have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
          simp [extendedProfileBlockVarianceCandidateEdgeUse,
            WeightedMultigraph.Inc, hne, hfst]
        · have hfst' : G.fst e ≠ v := Ne.symm hfst
          have hsnd' : G.snd e ≠ v := Ne.symm hsnd
          simp [extendedProfileBlockVarianceCandidateEdgeUse,
            WeightedMultigraph.Inc, hfst, hsnd, hfst', hsnd']
    _ = ∑ e ∈ Finset.univ.filter (G.Inc v),
          G.extendedProfileBlockVariance R0 rho omega e
            (choice (G.fst e, b)) (choice (G.snd e, b)) := by
      rw [Finset.sum_filter]
    _ = ∑ e : G.StarEdge v,
        G.extendedProfileBlockVariance R0 rho omega e.1
          (choice (G.fst e.1, b)) (choice (G.snd e.1, b)) := by
      exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
        (by intro e; simp)
        (fun e ↦ G.extendedProfileBlockVariance R0 rho omega e
          (choice (G.fst e, b)) (choice (G.snd e, b)))

theorem selectedTotalRawExtendedProfileBlockVariance_eq_star_sum
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (v : G.V) :
    G.selectedTotalRawExtendedProfileBlockVariance R0 rho omega choice v =
      ∑ b : Fin B, ∑ e : G.StarEdge v,
        G.extendedProfileBlockVariance R0 rho omega e.1
          (choice (G.fst e.1, b)) (choice (G.snd e.1, b)) := by
  unfold selectedTotalRawExtendedProfileBlockVariance
  apply Finset.sum_congr rfl
  intro b _hb
  exact G.selectedRawExtendedProfileBlockVariance_eq_star_sum
    R0 rho omega choice v b

/-- Pointwise Cauchy--Schwarz: joining `B` blocks costs only a factor `B`
in the squared error. -/
theorem selectedExtendedProfileTotalOptionMass_sq_le_blocks
    (hB : 0 < B) (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) :
    (G.selectedExtendedProfileTotalOptionMass R0 rho omega choice e -
        rho * s) ^ 2 ≤
      B * ∑ b : Fin B,
        (G.selectedExtendedProfileBlockOptionMass R0 rho omega choice e b -
          extendedProfileBlockTarget rho s B) ^ 2 := by
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have htarget :
      (∑ _b : Fin B, extendedProfileBlockTarget rho s B) = rho * s := by
    simp [extendedProfileBlockTarget]
    field_simp [hB0]
  have hsplit :
      G.selectedExtendedProfileTotalOptionMass R0 rho omega choice e -
          rho * s =
        ∑ b : Fin B,
          (G.selectedExtendedProfileBlockOptionMass R0 rho omega choice e b -
            extendedProfileBlockTarget rho s B) := by
    unfold selectedExtendedProfileTotalOptionMass
    rw [Finset.sum_sub_distrib, htarget]
  rw [hsplit]
  simpa using
    (sq_sum_le_card_mul_sum_sq
      (s := Finset.univ)
      (f := fun b : Fin B ↦
        G.selectedExtendedProfileBlockOptionMass R0 rho omega choice e b -
          extendedProfileBlockTarget rho s B))

/-- At a vertex, the whole-edge quadratic error is bounded by `B` times
the selected block-variance row total. -/
theorem selectedStarTotalOptionMass_quadratic_le
    (hB : 0 < B) (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (v : G.V) :
    (∑ e : G.StarEdge v,
      G.weight e.1 *
        (G.selectedExtendedProfileTotalOptionMass R0 rho omega choice e.1 -
          rho * s) ^ 2) ≤
      B * G.selectedTotalRawExtendedProfileBlockVariance
        R0 rho omega choice v := by
  calc
    (∑ e : G.StarEdge v,
      G.weight e.1 *
        (G.selectedExtendedProfileTotalOptionMass R0 rho omega choice e.1 -
          rho * s) ^ 2) ≤
        ∑ e : G.StarEdge v, G.weight e.1 *
          (B * ∑ b : Fin B,
            (G.selectedExtendedProfileBlockOptionMass R0 rho omega
                choice e.1 b - extendedProfileBlockTarget rho s B) ^ 2) := by
      apply Finset.sum_le_sum
      intro e _he
      exact mul_le_mul_of_nonneg_left
        (G.selectedExtendedProfileTotalOptionMass_sq_le_blocks
          R0 hB rho omega choice e.1) (G.weight_nonneg e.1)
    _ = B * (∑ b : Fin B, ∑ e : G.StarEdge v,
        G.extendedProfileBlockVariance R0 rho omega e.1
          (choice (G.fst e.1, b)) (choice (G.snd e.1, b))) := by
      simp_rw [extendedProfileBlockVariance,
        selectedExtendedProfileBlockOptionMass]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ = B * G.selectedTotalRawExtendedProfileBlockVariance
        R0 rho omega choice v := by
      rw [G.selectedTotalRawExtendedProfileBlockVariance_eq_star_sum
        R0 rho omega choice v]

/-- Weighted Cauchy--Schwarz in the form needed for the signed first-moment
deficit.  Squaring avoids any square-root side conditions. -/
theorem weightedSignedDeficit_sq_le
    {I : Type*} [Fintype I]
    (weight error : I → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    (∑ i, weight i * error i) ^ 2 ≤
      (∑ i, weight i) * ∑ i, weight i * (error i) ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    (s := Finset.univ)
    (r := fun i ↦ weight i * error i)
    (f := weight)
    (g := fun i ↦ weight i * (error i) ^ 2)
  · intro i _hi
    exact hweight i
  · intro i _hi
    exact mul_nonneg (hweight i) (sq_nonneg _)
  · intro i _hi
    ring_nf

/-- The block quadratic estimate also controls the signed loss of the
uncut first moment. -/
theorem selectedStarTotalOptionMass_signedDeficit_sq_le
    (hB : 0 < B) (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (v : G.V) :
    (∑ e : G.StarEdge v, G.weight e.1 *
      (rho * s -
        G.selectedExtendedProfileTotalOptionMass R0 rho omega choice e.1)) ^ 2 ≤
      G.starWeight v *
        (B * G.selectedTotalRawExtendedProfileBlockVariance
          R0 rho omega choice v) := by
  have hcauchy := weightedSignedDeficit_sq_le
    (fun e : G.StarEdge v ↦ G.weight e.1)
    (fun e : G.StarEdge v ↦ rho * s -
      G.selectedExtendedProfileTotalOptionMass R0 rho omega choice e.1)
    (fun e ↦ G.weight_nonneg e.1)
  have hquad := G.selectedStarTotalOptionMass_quadratic_le
    R0 hB rho omega choice v
  calc
    (∑ e : G.StarEdge v, G.weight e.1 *
      (rho * s -
        G.selectedExtendedProfileTotalOptionMass R0 rho omega choice e.1)) ^ 2 ≤
        G.starWeight v *
          (∑ e : G.StarEdge v, G.weight e.1 *
            (rho * s -
              G.selectedExtendedProfileTotalOptionMass
                R0 rho omega choice e.1) ^ 2) := by
      simpa [starWeight] using hcauchy
    _ ≤ G.starWeight v *
        (B * G.selectedTotalRawExtendedProfileBlockVariance
          R0 rho omega choice v) := by
      apply mul_le_mul_of_nonneg_left _
        (Finset.sum_nonneg fun e _he ↦ G.weight_nonneg e.1)
      calc
        (∑ e : G.StarEdge v, G.weight e.1 *
          (rho * s -
            G.selectedExtendedProfileTotalOptionMass
              R0 rho omega choice e.1) ^ 2) =
            ∑ e : G.StarEdge v, G.weight e.1 *
              (G.selectedExtendedProfileTotalOptionMass
                R0 rho omega choice e.1 - rho * s) ^ 2 := by
          apply Finset.sum_congr rfl
          intro e _he
          congr 1
          ring
        _ ≤ B * G.selectedTotalRawExtendedProfileBlockVariance
            R0 rho omega choice v := hquad

end WeightedMultigraph

end

end WeightedEdgeColoring
