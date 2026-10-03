import WeightedEdgeColoring.GeneralFiniteTinyHybrid
import WeightedEdgeColoring.FiniteClassesTinyProposalLocalPolytope
import WeightedEdgeColoring.TinyThresholdMixedObjects

/-!
# Artificial charge and local proposals for the general finite/tiny hybrid

The finite core residual is charged by its harmonic class and the tiny
residual by `w / (1 - tau)`.  These lemmas translate a moment-mixing output
on the hybrid graph into a locally feasible proposal on the physical joint
residual.  They only assume a direct pair-multiplicity bound; no bipartition
is used.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option linter.constructorNameAsVariable false

universe u

namespace GeneralColoredPacketBase

variable {G : WeightedMultigraph.{u}} {tau : ℝ}
variable {P : G.GeneralTinyThresholdPacketization tau}
variable {T K : ℕ}
variable {classOf : P.coreObjectGraph.E → Fin T}
variable (C : P.coreObjectGraph.GeneralColoredPacketBase K)

def jointFiniteClassAt (vertex : G.V)
    (e : {e : C.jointResidualGraph.StarEdge vertex //
      C.isFiniteCoreResidual e.1}) : Fin T :=
  classOf (C.jointFiniteCoreEdge ⟨e.1.1, e.2⟩)

/-- Artificial charge on the joint residual: harmonic charge on the finite
core residual and weighted-slack charge `w/(1-tau)` on the tiny tail. -/
def jointResidualCharge (e : C.jointResidualGraph.E) : ℝ :=
  if C.isFiniteCoreResidual e then
    harmonicCharge (C.jointResidualGraph.weight e)
  else C.jointResidualGraph.weight e / (1 - tau)

/-- Artificial charge incident with a joint-residual vertex. -/
def jointResidualStarCharge (v : G.V) : ℝ :=
  ∑ e : C.jointResidualGraph.StarEdge v, C.jointResidualCharge e.1

/-- Extend the joint residual charge by zero to the packet summand. -/
def finiteTinyHybridResidualCharge : C.finiteTinyHybridGraph.E → ℝ
  | Sum.inl _ => 0
  | Sum.inr e => C.jointResidualCharge e

@[simp] theorem finiteTinyHybridResidualCharge_inr_finite
    (e : C.jointResidualGraph.E) (he : C.isFiniteCoreResidual e) :
    C.finiteTinyHybridResidualCharge (Sum.inr e) =
      harmonicCharge (C.jointResidualGraph.weight e) := by
  simp [finiteTinyHybridResidualCharge, jointResidualCharge, he]

@[simp] theorem finiteTinyHybridResidualCharge_inr_tiny
    (e : C.jointResidualGraph.E) (he : ¬ C.isFiniteCoreResidual e) :
    C.finiteTinyHybridResidualCharge (Sum.inr e) =
      C.jointResidualGraph.weight e / (1 - tau) := by
  simp [finiteTinyHybridResidualCharge, jointResidualCharge, he]

theorem jointResidual_weight_le_charge
    (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (e : C.jointResidualGraph.E) :
    C.jointResidualGraph.weight e ≤ C.jointResidualCharge e := by
  by_cases he : C.isFiniteCoreResidual e
  · simp only [jointResidualCharge, he, if_true]
    exact TinyThresholdPacketization.weight_le_harmonicCharge e
  · simp only [jointResidualCharge, he, if_false]
    rw [le_div_iff₀ (sub_pos.mpr htau1)]
    have hw := C.jointResidualGraph.weight_nonneg e
    nlinarith

theorem jointResidualCharge_nonneg
    (htau1 : tau < 1) (e : C.jointResidualGraph.E) :
    0 ≤ C.jointResidualCharge e := by
  by_cases he : C.isFiniteCoreResidual e
  · simp [jointResidualCharge, he, harmonicCharge_nonneg]
  · simp only [jointResidualCharge, he, if_false]
    exact div_nonneg (C.jointResidualGraph.weight_nonneg e)
      (sub_pos.mpr htau1).le

theorem jointResidualCharge_le_one
    (htau0 : 0 ≤ tau) (htauHalf : tau ≤ (1 : ℝ) / 2)
    (e : C.jointResidualGraph.E) :
    C.jointResidualCharge e ≤ 1 := by
  have htau1 : tau < 1 := by linarith
  by_cases he : C.isFiniteCoreResidual e
  · simp only [jointResidualCharge, he, if_true]
    exact harmonicCharge_le_one (C.jointResidualGraph.weight_pos e)
      (C.jointResidualGraph.weight_le_one e)
  · simp only [jointResidualCharge, he, if_false]
    apply (div_le_one (sub_pos.mpr htau1)).2
    have hsmall := C.jointResidual_mem_small_of_not_finite e he
    have hw : C.jointResidualGraph.weight e ≤ tau := by
      simpa [jointResidualGraph] using P.smallObject_weight_le hsmall
    linarith

/-- Uncovered artificial charge controls the physical proposal deficit on
the joint residual. -/
theorem jointResidual_proposalDeficit_le_uncoveredCharge
    {q : ℕ} (x : C.jointResidualGraph.E → Fin q → ℝ)
    (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (hmass : ∀ e, ∑ c, x e c ≤ 1) (v : G.V) :
    C.jointResidualGraph.proposalDeficit x v ≤
      ∑ e : C.jointResidualGraph.E,
        if C.jointResidualGraph.Inc v e then
          C.jointResidualCharge e * (1 - ∑ c, x e c) else 0 := by
  unfold proposalDeficit
  apply Finset.sum_le_sum
  intro e _he
  by_cases hinc : C.jointResidualGraph.Inc v e
  · simp only [hinc, if_true]
    exact mul_le_mul_of_nonneg_right
      (C.jointResidual_weight_le_charge htau0 htau1 e)
      (sub_nonneg.mpr (hmass e))
  · simp [hinc]

/-- The mixed finite-plus-tiny local polytope theorem in the exact joint
residual edge type. -/
theorem jointResidual_isAverageOfStarFeasibleSets
    (hT : 0 < T) {vertex : G.V}
    (x : C.jointResidualGraph.StarEdge vertex → ℝ) (M : ℝ)
    (hM : 0 < M) (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (hfiniteWeight : ∀ e : P.coreObjectGraph.E,
      P.coreObjectGraph.weight e ≤
        (1 : ℝ) / finiteClassSize (classOf e))
    (hx0 : ∀ e, 0 ≤ x e) (hxM : ∀ e, x e ≤ M)
    (hbudget :
      (∑ e : {e : C.jointResidualGraph.StarEdge vertex //
          C.isFiniteCoreResidual e.1},
          x e.1 / (finiteClassSize
            (C.jointFiniteClassAt (classOf := classOf) vertex e) : ℝ)) +
        (T : ℝ) * M +
        (∑ e : {e : C.jointResidualGraph.StarEdge vertex //
          ¬ C.isFiniteCoreResidual e.1},
          C.jointResidualGraph.weight e.1.1 * x e.1) / (1 - tau) + M ≤ 1) :
    C.jointResidualGraph.IsAverageOfStarFeasibleSets vertex x := by
  letI : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
  apply C.jointResidualGraph.finiteClassesTinyProposal_isAverageOfStarFeasibleSets
    (fun e => C.isFiniteCoreResidual e.1)
    (fun a : Fin T => finiteClassSize a)
    (fun a : Fin T => by simp [finiteClassSize])
    (C.jointFiniteClassAt (classOf := classOf) vertex) x M tau hM htau0 htau1
  · intro e
    simpa [jointFiniteClassAt, jointFiniteCoreEdge, jointResidualGraph] using
      hfiniteWeight (C.jointFiniteCoreEdge ⟨e.1.1, e.2⟩)
  · intro e
    have hsmall := C.jointResidual_mem_small_of_not_finite e.1.1 e.2
    simpa [jointResidualGraph] using P.smallObject_weight_le hsmall
  · exact hx0
  · exact hxM
  · simpa using hbudget

/-- The artificial proposal-charge row is exactly the finite reciprocal
class row plus the tiny weighted-slack row consumed by the local-polytope
wrapper. -/
theorem jointResidual_chargeLoad_eq_finite_add_tiny
    {vertex : G.V} (x : C.jointResidualGraph.StarEdge vertex → ℝ)
    (hcharge : ∀ e : P.coreObjectGraph.E,
      harmonicCharge (P.coreObjectGraph.weight e) =
        (1 : ℝ) / finiteClassSize (classOf e)) :
    (∑ e : C.jointResidualGraph.StarEdge vertex,
        C.jointResidualCharge e.1 * x e) =
      (∑ e : {e : C.jointResidualGraph.StarEdge vertex //
          C.isFiniteCoreResidual e.1},
          x e.1 / (finiteClassSize
            (C.jointFiniteClassAt (classOf := classOf) vertex e) : ℝ)) +
        (∑ e : {e : C.jointResidualGraph.StarEdge vertex //
          ¬ C.isFiniteCoreResidual e.1},
          C.jointResidualGraph.weight e.1.1 * x e.1) / (1 - tau) := by
  classical
  let pred : C.jointResidualGraph.StarEdge vertex → Prop :=
    fun e => C.isFiniteCoreResidual e.1
  let A := (Finset.univ : Finset (C.jointResidualGraph.StarEdge vertex)).filter pred
  let B := (Finset.univ : Finset (C.jointResidualGraph.StarEdge vertex)).filter
    (fun e => ¬ pred e)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    exact (Finset.mem_filter.mp heB).2 (Finset.mem_filter.mp heA).2
  have hunion : A ∪ B = Finset.univ := by
    ext e
    by_cases he : C.isFiniteCoreResidual e.1 <;>
      simp [A, B, pred, he]
  calc
    (∑ e : C.jointResidualGraph.StarEdge vertex,
        C.jointResidualCharge e.1 * x e) =
        (∑ e ∈ A, C.jointResidualCharge e.1 * x e) +
          ∑ e ∈ B, C.jointResidualCharge e.1 * x e := by
      rw [← Finset.sum_union hdisj, hunion]
    _ = (∑ e : {e : C.jointResidualGraph.StarEdge vertex // pred e},
          C.jointResidualCharge e.1.1 * x e.1) +
        ∑ e : {e : C.jointResidualGraph.StarEdge vertex // ¬ pred e},
          C.jointResidualCharge e.1.1 * x e.1 := by
      exact congrArg₂ (fun a b : ℝ => a + b)
        (Finset.sum_subtype A (by simp [A])
          (fun e => C.jointResidualCharge e.1 * x e))
        (Finset.sum_subtype B (by simp [B])
          (fun e => C.jointResidualCharge e.1 * x e))
    _ = (∑ e : {e : C.jointResidualGraph.StarEdge vertex //
          C.isFiniteCoreResidual e.1},
          x e.1 / (finiteClassSize
            (C.jointFiniteClassAt (classOf := classOf) vertex e) : ℝ)) +
        ∑ e : {e : C.jointResidualGraph.StarEdge vertex //
          ¬ C.isFiniteCoreResidual e.1},
          (C.jointResidualGraph.weight e.1.1 / (1 - tau)) * x e.1 := by
      dsimp [pred]
      apply congrArg₂ (fun a b : ℝ => a + b)
      · apply Finset.sum_congr rfl
        intro e _he
        rw [jointResidualCharge, if_pos e.2]
        have hc := hcharge (C.jointFiniteCoreEdge ⟨e.1.1, e.2⟩)
        have hc' : harmonicCharge (C.jointResidualGraph.weight e.1.1) =
            (1 : ℝ) / finiteClassSize
              (C.jointFiniteClassAt (classOf := classOf) vertex e) := by
          simpa only [jointFiniteCoreEdge_weight, jointFiniteClassAt] using hc
        rw [hc']
        ring
      · apply Finset.sum_congr rfl
        intro e _he
        rw [jointResidualCharge, if_neg e.2]
    _ = _ := by
      apply congrArg (fun z : ℝ =>
        (∑ e : {e : C.jointResidualGraph.StarEdge vertex //
          C.isFiniteCoreResidual e.1},
          x e.1 / (finiteClassSize
            (C.jointFiniteClassAt (classOf := classOf) vertex e) : ℝ)) + z)
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e _he
      ring

/-- The local-polytope conclusion directly from a row bound in artificial
charge units. -/
theorem jointResidual_isAverageOfStarFeasibleSets_of_chargeBudget
    (hT : 0 < T) {vertex : G.V}
    (x : C.jointResidualGraph.StarEdge vertex → ℝ) (M : ℝ)
    (hM : 0 < M) (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (hfiniteWeight : ∀ e : P.coreObjectGraph.E,
      P.coreObjectGraph.weight e ≤
        (1 : ℝ) / finiteClassSize (classOf e))
    (hcharge : ∀ e : P.coreObjectGraph.E,
      harmonicCharge (P.coreObjectGraph.weight e) =
        (1 : ℝ) / finiteClassSize (classOf e))
    (hx0 : ∀ e, 0 ≤ x e) (hxM : ∀ e, x e ≤ M)
    (hbudget :
      (∑ e : C.jointResidualGraph.StarEdge vertex,
        C.jointResidualCharge e.1 * x e) + (T + 1 : ℝ) * M ≤ 1) :
    C.jointResidualGraph.IsAverageOfStarFeasibleSets vertex x := by
  apply C.jointResidual_isAverageOfStarFeasibleSets hT x M hM htau0 htau1
    hfiniteWeight hx0 hxM
  have heq := C.jointResidual_chargeLoad_eq_finite_add_tiny x hcharge
  push_cast at hbudget ⊢
  linarith

theorem sum_finiteTinyHybridResidualEdges
    (f : C.finiteTinyHybridGraph.E → ℝ) :
    (∑ e ∈ C.finiteTinyHybridResidualEdges, f e) =
      ∑ e : C.jointResidualGraph.E, f (Sum.inr e) := by
  classical
  symm
  apply Finset.sum_bij (fun e _ => Sum.inr e)
  · intro e _he
    exact C.mem_finiteTinyHybridResidualEdges_inr e
  · intro e₁ _ e₂ _ h
    exact Sum.inr_injective h
  · intro e he
    rcases e with p | e
    · exact (C.not_mem_finiteTinyHybridResidualEdges_inl p he).elim
    · exact ⟨e, Finset.mem_univ _, rfl⟩
  · intro e _he
    rfl

/-- Restricted hybrid charge is exactly joint-residual artificial star
charge. -/
theorem finiteTinyHybrid_restrictedCharge_eq_jointStarCharge (v : G.V) :
    C.finiteTinyHybridGraph.restrictedCharge
        C.finiteTinyHybridResidualEdges
        C.finiteTinyHybridResidualCharge v =
      C.jointResidualStarCharge v := by
  classical
  unfold restrictedCharge jointResidualStarCharge
  rw [show
      (∑ e : C.jointResidualGraph.StarEdge v,
        C.jointResidualCharge e.1) =
      ∑ e : C.jointResidualGraph.E,
        if C.jointResidualGraph.Inc v e then
          C.jointResidualCharge e else 0 by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype
      (p := fun e : C.jointResidualGraph.E =>
        C.jointResidualGraph.Inc v e)
      ((Finset.univ : Finset C.jointResidualGraph.E).filter
        (C.jointResidualGraph.Inc v)) (by
          intro e
          rw [Finset.mem_filter]
          simp only [Finset.mem_univ, true_and])
      (fun e => C.jointResidualCharge e)).symm]
  rw [C.sum_finiteTinyHybridResidualEdges]
  rfl

/-- Hybrid proposal charge load is the joint-residual star sum. -/
theorem finiteTinyHybrid_proposalChargeLoad_eq_joint
    {q : ℕ} (x : C.finiteTinyHybridGraph.E → Fin q → ℝ)
    (v : G.V) (c : Fin q) :
    C.finiteTinyHybridGraph.proposalChargeLoad
        C.finiteTinyHybridResidualEdges C.finiteTinyHybridResidualCharge
        x v c =
      ∑ e : C.jointResidualGraph.StarEdge v,
        C.jointResidualCharge e.1 * x (Sum.inr e.1) c := by
  classical
  unfold proposalChargeLoad
  rw [show
      (∑ e : C.jointResidualGraph.StarEdge v,
        C.jointResidualCharge e.1 * x (Sum.inr e.1) c) =
      ∑ e : C.jointResidualGraph.E,
        if C.jointResidualGraph.Inc v e then
          C.jointResidualCharge e * x (Sum.inr e) c else 0 by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype
      (p := fun e : C.jointResidualGraph.E =>
        C.jointResidualGraph.Inc v e)
      ((Finset.univ : Finset C.jointResidualGraph.E).filter
        (C.jointResidualGraph.Inc v)) (by
          intro e
          rw [Finset.mem_filter]
          simp only [Finset.mem_univ, true_and])
      (fun e => C.jointResidualCharge e * x (Sum.inr e) c)).symm]
  rw [C.sum_finiteTinyHybridResidualEdges]
  rfl

/-- Hybrid uncovered charge is the joint-residual uncovered star sum. -/
theorem finiteTinyHybrid_uncoveredCharge_eq_joint
    {q : ℕ} (x : C.finiteTinyHybridGraph.E → Fin q → ℝ)
    (v : G.V) :
    C.finiteTinyHybridGraph.uncoveredProposalCharge
        C.finiteTinyHybridResidualEdges C.finiteTinyHybridResidualCharge
        x v =
      ∑ e : C.jointResidualGraph.E,
        if C.jointResidualGraph.Inc v e then
          C.jointResidualCharge e *
            (1 - ∑ c, x (Sum.inr e) c) else 0 := by
  classical
  unfold uncoveredProposalCharge
  rw [C.sum_finiteTinyHybridResidualEdges]
  rfl

/-- A joint endpoint-multiplicity bound controls the hybrid pair charge,
because every finite or tiny artificial edge charge is at most one. -/
theorem finiteTinyHybrid_pairCharge_le_of_pairMultiplicity
    {L : ℕ} (htau0 : 0 ≤ tau) (htauHalf : tau ≤ (1 : ℝ) / 2)
    (hmult : C.jointResidualGraph.PairMultiplicityAtMost L)
    (u v : G.V) :
    C.finiteTinyHybridGraph.pairCharge
        C.finiteTinyHybridResidualEdges C.finiteTinyHybridResidualCharge
          u v ≤ L := by
  have hsum := C.jointResidualGraph.sum_le_mul_of_pairMultiplicityAtMost
    hmult u v
    (fun e => if C.jointResidualGraph.EndpointPairMatches u v e then
      C.jointResidualCharge e else 0) 1
    (by norm_num)
    (fun e _he => by
      simp only [if_pos _he]
      exact C.jointResidualCharge_le_one htau0 htauHalf e)
    (fun e he => by simp [he])
  calc
    C.finiteTinyHybridGraph.pairCharge
        C.finiteTinyHybridResidualEdges C.finiteTinyHybridResidualCharge
          u v =
        ∑ e : C.jointResidualGraph.E,
          if C.jointResidualGraph.EndpointPairMatches u v e then
            C.jointResidualCharge e else 0 := by
      classical
      unfold pairCharge
      rw [C.sum_finiteTinyHybridResidualEdges]
      apply Finset.sum_congr rfl
      intro e _he
      have hcond :
          (C.finiteTinyHybridGraph.fst (Sum.inr e) = u ∧
              C.finiteTinyHybridGraph.snd (Sum.inr e) = v) ∨
            (C.finiteTinyHybridGraph.fst (Sum.inr e) = v ∧
              C.finiteTinyHybridGraph.snd (Sum.inr e) = u) ↔
          C.jointResidualGraph.EndpointPairMatches u v e := by
        simp only [EndpointPairMatches, finiteTinyHybridGraph]
        constructor
        · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
          · exact Or.inl ⟨h₁.symm, h₂.symm⟩
          · exact Or.inr ⟨h₂.symm, h₁.symm⟩
        · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
          · exact Or.inl ⟨h₁.symm, h₂.symm⟩
          · exact Or.inr ⟨h₂.symm, h₁.symm⟩
      rw [if_congr hcond rfl rfl]
      rfl
    _ ≤ (L : ℝ) * 1 := hsum
    _ = L := by ring

end GeneralColoredPacketBase

end

end WeightedMultigraph
end WeightedEdgeColoring

#print axioms WeightedEdgeColoring.WeightedMultigraph.GeneralColoredPacketBase.finiteTinyHybrid_pairCharge_le_of_pairMultiplicity
