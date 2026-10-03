import WeightedEdgeColoring.SubtwoMixedGraphBlockFullSharpSelection
import WeightedEdgeColoring.BoundedMultiplicityJointProfileParameters

/-! Exact proposal coverage controls the deterministic part of the block residual. -/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {B k : ℕ} {Label : Type*} [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → (Fin B × Fin k) → ℝ)

theorem mixedBlockTotalTarget_eq_totalProposal
    (rho s : ℝ) (e : G.E) :
    G.mixedBlockTotalTarget proposal rho s e =
      rho * s * ∑ c : Fin B × Fin k, proposal e c := by
  unfold mixedBlockTotalTarget mixedBlockTarget
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]

/-- The deterministic block deficit is controlled by the actual weighted
proposal deficit, without a pointwise fill assumption. -/
theorem mixedBlockTargetDeficit_le_proposalDeficit
    {rho s : ℝ} (hrhos : 0 ≤ rho * s) (hrhos1 : rho * s ≤ 1)
    (hmass : ∀ e, ∑ c : Fin B × Fin k, proposal e c ≤ 1)
    (v : G.V) :
    (∑ e : G.StarEdge v, G.weight e.1 *
      max 0 (1 - G.mixedBlockTotalTarget proposal rho s e.1)) ≤
      (1 - rho * s) * G.starWeight v +
        rho * s * G.proposalDeficit
          (fun e c ↦ proposal e (finProdFinEquiv.symm c)) v := by
  classical
  have hstar :
      (∑ e : G.StarEdge v, G.weight e.1 *
        (1 - ∑ c : Fin B × Fin k, proposal e.1 c)) =
        G.proposalDeficit
          (fun e c ↦ proposal e (finProdFinEquiv.symm c)) v := by
    unfold proposalDeficit
    simp_rw [show ∀ e : G.E,
        (∑ c : Fin (B * k), proposal e (finProdFinEquiv.symm c)) =
          ∑ c : Fin B × Fin k, proposal e c from
      fun e ↦ Equiv.sum_comp finProdFinEquiv.symm (proposal e)]
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (G.Inc v))
      (by intro e; simp)
      (fun e : G.E ↦ G.weight e *
        (1 - ∑ c : Fin B × Fin k, proposal e c))).symm
  have htarget (e : G.E) :
      0 ≤ 1 - G.mixedBlockTotalTarget proposal rho s e := by
    rw [G.mixedBlockTotalTarget_eq_totalProposal proposal rho s e]
    have hm := hmass e
    nlinarith [mul_le_mul_of_nonneg_left hm hrhos]
  calc
    _ = ∑ e : G.StarEdge v,
        G.weight e.1 * (1 - G.mixedBlockTotalTarget proposal rho s e.1) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [max_eq_right (htarget e.1)]
    _ = ∑ e : G.StarEdge v,
        G.weight e.1 * ((1 - rho * s) + rho * s *
          (1 - ∑ c : Fin B × Fin k, proposal e.1 c)) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [G.mixedBlockTotalTarget_eq_totalProposal proposal rho s e.1]
      ring
    _ = (1 - rho * s) * G.starWeight v +
        rho * s * G.proposalDeficit
          (fun e c ↦ proposal e (finProdFinEquiv.symm c)) v := by
      rw [← hstar]
      unfold starWeight
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hfirst :
          (∑ e : G.StarEdge v, G.weight e.1 * (1 - rho * s)) =
            (1 - rho * s) * ∑ e : G.StarEdge v, G.weight e.1 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring
      have hsecond :
          (∑ e : G.StarEdge v,
            G.weight e.1 * (rho * s *
              (1 - ∑ c : Fin B × Fin k, proposal e.1 c))) =
            rho * s * ∑ e : G.StarEdge v,
              G.weight e.1 *
                (1 - ∑ c : Fin B × Fin k, proposal e.1 c) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring
      rw [hfirst, hsecond]
    _ ≤ _ := le_refl _

theorem mixedBlockTargetDeficit_le_jointProfile_of_proposalDeficit
    {tau : ℝ} (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1 / 4)
    (hmass : ∀ e, ∑ c : Fin B × Fin k, proposal e c ≤ 1)
    (v : G.V) :
    (∑ e : G.StarEdge v, G.weight e.1 *
      max 0 (1 - G.mixedBlockTotalTarget proposal
        (jointProfileRho tau) (jointProfileS tau) e.1)) ≤
      4 * tau * G.starWeight v + G.proposalDeficit
        (fun e c ↦ proposal e (finProdFinEquiv.symm c)) v := by
  have hprod0 : 0 ≤ jointProfileRho tau * jointProfileS tau := by
    unfold jointProfileRho jointProfileS
    have h : 0 ≤ 1 - 2 * tau := by linarith
    positivity
  have hprod1 : jointProfileRho tau * jointProfileS tau ≤ 1 := by
    unfold jointProfileRho jointProfileS
    nlinarith [sq_nonneg tau]
  have hcoef : 1 - jointProfileRho tau * jointProfileS tau ≤ 4 * tau := by
    unfold jointProfileRho jointProfileS
    nlinarith [sq_nonneg tau]
  have hstar0 : 0 ≤ G.starWeight v := by
    unfold starWeight
    exact Finset.sum_nonneg (fun e _ ↦ G.weight_nonneg e.1)
  have hflatmass : ∀ e,
      (∑ c : Fin (B * k), proposal e (finProdFinEquiv.symm c)) ≤ 1 := by
    intro e
    rw [Equiv.sum_comp finProdFinEquiv.symm (proposal e)]
    exact hmass e
  have hdef0 := G.proposalDeficit_nonneg
    (fun e c ↦ proposal e (finProdFinEquiv.symm c)) hflatmass v
  calc
    _ ≤ (1 - jointProfileRho tau * jointProfileS tau) * G.starWeight v +
        (jointProfileRho tau * jointProfileS tau) * G.proposalDeficit
          (fun e c ↦ proposal e (finProdFinEquiv.symm c)) v :=
      G.mixedBlockTargetDeficit_le_proposalDeficit proposal hprod0 hprod1 hmass v
    _ ≤ 4 * tau * G.starWeight v + G.proposalDeficit
        (fun e c ↦ proposal e (finProdFinEquiv.symm c)) v := by
      nlinarith [mul_le_mul_of_nonneg_right hcoef hstar0,
        mul_le_mul_of_nonneg_right hprod1 hdef0]

theorem mixedBlockTargetDeficit_le_of_proposalFill
    {rho s eps : ℝ} (hrhos : 0 ≤ rho * s)
    (hrhos1 : rho * s ≤ 1) (heps : 0 ≤ eps)
    (hfill : ∀ e, 1 - eps ≤ ∑ c : Fin B × Fin k, proposal e c)
    (v : G.V) :
    (∑ e : G.StarEdge v, G.weight e.1 *
      max 0 (1 - G.mixedBlockTotalTarget proposal rho s e.1)) ≤
      (1 - rho * s + rho * s * eps) * G.starWeight v := by
  classical
  have hco : 0 ≤ 1 - rho * s + rho * s * eps := by
    nlinarith
  calc
    (∑ e : G.StarEdge v, G.weight e.1 *
      max 0 (1 - G.mixedBlockTotalTarget proposal rho s e.1)) ≤
      ∑ e : G.StarEdge v,
        G.weight e.1 * (1 - rho * s + rho * s * eps) := by
      apply Finset.sum_le_sum
      intro e _
      apply mul_le_mul_of_nonneg_left _ (G.weight_nonneg e.1)
      rw [G.mixedBlockTotalTarget_eq_totalProposal proposal rho s e.1]
      apply max_le
      · exact hco
      · nlinarith [mul_le_mul_of_nonneg_left (hfill e.1) hrhos]
    _ = (1 - rho * s + rho * s * eps) * G.starWeight v := by
      unfold starWeight
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring

theorem mixedBlockTargetDeficit_le_jointProfile
    {tau eps : ℝ} (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1 / 4)
    (heps0 : 0 ≤ eps)
    (hfill : ∀ e, 1 - eps ≤ ∑ c : Fin B × Fin k, proposal e c)
    (v : G.V) :
    (∑ e : G.StarEdge v, G.weight e.1 *
      max 0 (1 - G.mixedBlockTotalTarget proposal
        (jointProfileRho tau) (jointProfileS tau) e.1)) ≤
      (4 * tau + eps) * G.starWeight v := by
  have hprod0 : 0 ≤ jointProfileRho tau * jointProfileS tau := by
    unfold jointProfileRho jointProfileS
    have h : 0 ≤ 1 - 2 * tau := by linarith
    positivity
  have hprod1 : jointProfileRho tau * jointProfileS tau ≤ 1 := by
    unfold jointProfileRho jointProfileS
    nlinarith [sq_nonneg tau]
  have hcoef : 1 - jointProfileRho tau * jointProfileS tau +
      jointProfileRho tau * jointProfileS tau * eps ≤ 4 * tau + eps := by
    have h1 : 1 - jointProfileRho tau * jointProfileS tau ≤
        4 * tau := by
      unfold jointProfileRho jointProfileS
      nlinarith [sq_nonneg tau]
    have h2 := mul_le_mul_of_nonneg_right hprod1 heps0
    nlinarith
  have hstar0 : 0 ≤ G.starWeight v := by
    unfold starWeight
    apply Finset.sum_nonneg
    intro e _
    exact G.weight_nonneg e.1
  calc
    _ ≤ (1 - jointProfileRho tau * jointProfileS tau +
        jointProfileRho tau * jointProfileS tau * eps) *
        G.starWeight v :=
      G.mixedBlockTargetDeficit_le_of_proposalFill proposal
        hprod0 hprod1 heps0 hfill v
    _ ≤ (4 * tau + eps) * G.starWeight v :=
      mul_le_mul_of_nonneg_right hcoef hstar0

end WeightedMultigraph

end
end WeightedEdgeColoring
