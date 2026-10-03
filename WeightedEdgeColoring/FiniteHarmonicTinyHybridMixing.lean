import WeightedEdgeColoring.TinyThresholdJointResidual
import WeightedEdgeColoring.FiniteClassesTinyProposalLocalPolytope
import WeightedEdgeColoring.FiniteHarmonicRoundingAssembly
import WeightedEdgeColoring.WeightedMomentPaletteMixingProof

/-!
# A packet/core-residual/tiny hybrid graph

The finite harmonic certificate lives on the non-tiny core restriction.  Its
proper packet skeleton must be mixed against one residual graph containing
both the finite-class packet residual and the endpoint-simple tiny objects.
This file supplies that three-part graph.  Keeping the two residual pieces in
one edge restriction is essential: the whole-edge rounder then coordinates
their use of the common missing palette at every vertex.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option linter.constructorNameAsVariable false

universe u

variable {G : WeightedMultigraph.{u}}

namespace FiniteHarmonicPacketColoringCertificate

variable {b : G.Bipartition} {tau : ℝ}
variable {P : G.TinyThresholdPacketization b tau}
variable {T K : ℕ}
variable {classOf : P.coreObjectGraph.E → Fin T}
variable (C : P.coreObjectGraph.FiniteHarmonicPacketColoringCertificate
  P.coreBipartition classOf K)

/-- The one residual graph used by moment mixing and whole-edge rounding. -/
abbrev jointResidualGraph : WeightedMultigraph.{u} :=
  P.mixedObjectGraph.edgeRestriction C.jointResidualObjects

/-- The proper finite-core packet skeleton. -/
abbrev corePacketGraph : WeightedMultigraph.{u} :=
  (C.decomposition.fullPacketization C.packetWeight_le).groupedGraph

/-- Disjoint union of the proper packet skeleton and the joint physical
residual.  The right summand itself contains the core residual and tiny tail. -/
def finiteTinyHybridGraph : WeightedMultigraph.{u} where
  V := G.V
  E := C.decomposition.Packet ⊕ C.jointResidualGraph.E
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := inferInstance
  fst
    | Sum.inl p => C.corePacketGraph.fst p
    | Sum.inr e => C.jointResidualGraph.fst e
  snd
    | Sum.inl p => C.corePacketGraph.snd p
    | Sum.inr e => C.jointResidualGraph.snd e
  noLoop
    | Sum.inl p => C.corePacketGraph.noLoop p
    | Sum.inr e => C.jointResidualGraph.noLoop e
  weight
    | Sum.inl p => C.corePacketGraph.weight p
    | Sum.inr e => C.jointResidualGraph.weight e
  weight_pos
    | Sum.inl p => C.corePacketGraph.weight_pos p
    | Sum.inr e => C.jointResidualGraph.weight_pos e
  weight_le_one
    | Sum.inl p => C.corePacketGraph.weight_le_one p
    | Sum.inr e => C.jointResidualGraph.weight_le_one e

/-- Left (proper packet) side of the three-part hybrid. -/
def finiteTinyHybridPacketEdges : Finset C.finiteTinyHybridGraph.E :=
  by
    classical
    exact Finset.univ.filter fun e => match e with
      | Sum.inl _ => True
      | Sum.inr _ => False

/-- Right (core residual plus tiny) side of the three-part hybrid. -/
def finiteTinyHybridResidualEdges : Finset C.finiteTinyHybridGraph.E :=
  by
    classical
    exact Finset.univ.filter fun e => match e with
      | Sum.inl _ => False
      | Sum.inr _ => True

@[simp] theorem mem_finiteTinyHybridPacketEdges_inl
    (p : C.decomposition.Packet) :
    Sum.inl p ∈ C.finiteTinyHybridPacketEdges := by
  simp [finiteTinyHybridPacketEdges]

@[simp] theorem not_mem_finiteTinyHybridPacketEdges_inr
    (e : C.jointResidualGraph.E) :
    Sum.inr e ∉ C.finiteTinyHybridPacketEdges := by
  simp [finiteTinyHybridPacketEdges]

@[simp] theorem not_mem_finiteTinyHybridResidualEdges_inl
    (p : C.decomposition.Packet) :
    Sum.inl p ∉ C.finiteTinyHybridResidualEdges := by
  simp [finiteTinyHybridResidualEdges]

@[simp] theorem mem_finiteTinyHybridResidualEdges_inr
    (e : C.jointResidualGraph.E) :
    Sum.inr e ∈ C.finiteTinyHybridResidualEdges := by
  simp [finiteTinyHybridResidualEdges]

theorem finiteTinyHybridPacketEdges_disjoint_residualEdges :
    Disjoint C.finiteTinyHybridPacketEdges
      C.finiteTinyHybridResidualEdges := by
  rw [Finset.disjoint_left]
  intro e heF heR
  rcases e with p | e
  · exact C.not_mem_finiteTinyHybridResidualEdges_inl p heR
  · exact C.not_mem_finiteTinyHybridPacketEdges_inr e heF

/-- The predicate separating the finite harmonic residual from the tiny
tail inside the joint residual graph. -/
def isFiniteCoreResidual (e : C.jointResidualGraph.E) : Prop :=
  e.1 ∈ C.residualCoreObjects

instance instDecidableIsFiniteCoreResidual :
    DecidablePred C.isFiniteCoreResidual := by
  intro e
  exact Finset.decidableMem e.1 C.residualCoreObjects

/-- Recover the core-restriction edge represented by a finite edge of the
joint residual. -/
def jointFiniteCoreEdge
    (e : {e : C.jointResidualGraph.E // C.isFiniteCoreResidual e}) :
    P.coreObjectGraph.E :=
  ⟨e.1.1, (P.mixedObjectGraph.mem_liftRestrictionFinset_iff
    P.coreObjects C.residualEdges e.1.1).mp e.2 |>.choose⟩

theorem jointFiniteCoreEdge_mem_residual
    (e : {e : C.jointResidualGraph.E // C.isFiniteCoreResidual e}) :
    C.jointFiniteCoreEdge e ∈ C.residualEdges := by
  exact (P.mixedObjectGraph.mem_liftRestrictionFinset_iff
    P.coreObjects C.residualEdges e.1.1).mp e.2 |>.choose_spec

@[simp] theorem jointFiniteCoreEdge_weight
    (e : {e : C.jointResidualGraph.E // C.isFiniteCoreResidual e}) :
    P.coreObjectGraph.weight (C.jointFiniteCoreEdge e) =
      C.jointResidualGraph.weight e.1 := rfl

/-- A joint-residual edge outside the finite part is a tiny object. -/
theorem jointResidual_mem_small_of_not_finite
    (e : C.jointResidualGraph.E) (he : ¬ C.isFiniteCoreResidual e) :
    e.1 ∈ P.smallObjects := by
  rcases Finset.mem_union.mp e.2 with hfinite | htiny
  · exact (he hfinite).elim
  · exact htiny

/-- The joint residual has the finite-class multiplicity bound plus one tiny
edge for each unordered endpoint pair. -/
theorem jointResidualGraph_pairMultiplicityAtMost :
    C.jointResidualGraph.PairMultiplicityAtMost
      (T * (T - 1) / 2 + 1) := by
  intro u v
  let L : ℕ := T * (T - 1) / 2
  let H := C.jointResidualGraph
  let HF := C.residualGraph
  let HS := P.smallObjectGraph.asMultigraph
  let source := {e : H.E // e ∈ H.endpointPairCell u v}
  let leftTarget := {e : HF.E // e ∈ HF.endpointPairCell u v}
  let rightTarget := {e : HS.E // e ∈ HS.endpointPairCell u v}
  let f : source → leftTarget ⊕ rightTarget := fun e =>
    if heF : C.isFiniteCoreResidual e.1 then
      let core := C.jointFiniteCoreEdge ⟨e.1, heF⟩
      let residual : HF.E := ⟨core,
        C.jointFiniteCoreEdge_mem_residual ⟨e.1, heF⟩⟩
      Sum.inl ⟨residual, by
        apply (HF.mem_endpointPairCell_iff u v residual).mpr
        have he := (H.mem_endpointPairCell_iff u v e.1).mp e.2
        change P.mixedObjectGraph.endpoints e.1.1 = s(u, v) at he
        change P.mixedObjectGraph.endpoints e.1.1 = s(u, v)
        exact he⟩
    else
      let small : HS.E := ⟨e.1.1,
        C.jointResidual_mem_small_of_not_finite e.1 heF⟩
      Sum.inr ⟨small, by
        apply (HS.mem_endpointPairCell_iff u v small).mpr
        have he := (H.mem_endpointPairCell_iff u v e.1).mp e.2
        change P.mixedObjectGraph.endpoints e.1.1 = s(u, v) at he
        change P.mixedObjectGraph.endpoints e.1.1 = s(u, v)
        exact he⟩
  have hf : Function.Injective f := by
    intro e d hed
    by_cases he : C.isFiniteCoreResidual e.1 <;>
      by_cases hd : C.isFiniteCoreResidual d.1
    · dsimp only [f] at hed
      rw [dif_pos he, dif_pos hd] at hed
      have h := Sum.inl.inj hed
      have hval : e.1.1 = d.1.1 :=
        congrArg (fun z : leftTarget => z.1.1.1) h
      exact Subtype.ext (Subtype.ext hval)
    · have : False := by
        dsimp only [f] at hed
        rw [dif_pos he, dif_neg hd] at hed
        cases hed
      contradiction
    · have : False := by
        dsimp only [f] at hed
        rw [dif_neg he, dif_pos hd] at hed
        cases hed
      contradiction
    · dsimp only [f] at hed
      rw [dif_neg he, dif_neg hd] at hed
      have h := Sum.inr.inj hed
      have hval : e.1.1 = d.1.1 :=
        congrArg (fun z : rightTarget => z.1.1) h
      exact Subtype.ext (Subtype.ext hval)
  have hcard : Fintype.card source ≤ Fintype.card (leftTarget ⊕ rightTarget) :=
    Fintype.card_le_of_injective f hf
  have hleft : Fintype.card leftTarget ≤ L := by
    simpa only [leftTarget, Fintype.card_coe, HF] using
      C.residualGraph_pairMultiplicityAtMost u v
  have hright : Fintype.card rightTarget ≤ 1 := by
    simpa only [rightTarget, Fintype.card_coe, HS] using
      P.smallObjectGraph_pairMultiplicityAtMost u v
  have htarget : Fintype.card (leftTarget ⊕ rightTarget) ≤ L + 1 := by
    rw [Fintype.card_sum]
    exact Nat.add_le_add hleft hright
  have htotal := hcard.trans htarget
  simpa only [source, Fintype.card_coe, H] using htotal

/-- Harmonic class of a finite edge in a joint-residual star. -/
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
          x e.1 / (finiteClassSize (C.jointFiniteClassAt vertex e) : ℝ)) +
        (T : ℝ) * M +
        (∑ e : {e : C.jointResidualGraph.StarEdge vertex //
          ¬ C.isFiniteCoreResidual e.1},
          C.jointResidualGraph.weight e.1.1 * x e.1) / (1 - tau) + M ≤ 1) :
    C.jointResidualGraph.IsAverageOfStarFeasibleSets vertex x := by
  letI : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
  apply C.jointResidualGraph.finiteClassesTinyProposal_isAverageOfStarFeasibleSets
    (fun e => C.isFiniteCoreResidual e.1)
    finiteClassSize (fun a => by simp [finiteClassSize])
    (C.jointFiniteClassAt vertex) x M tau hM htau0 htau1
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
          x e.1 / (finiteClassSize (C.jointFiniteClassAt vertex e) : ℝ)) +
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
          x e.1 / (finiteClassSize (C.jointFiniteClassAt vertex e) : ℝ)) +
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
            (1 : ℝ) / finiteClassSize (C.jointFiniteClassAt vertex e) := by
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
          x e.1 / (finiteClassSize (C.jointFiniteClassAt vertex e) : ℝ)) + z)
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

/-- Extend the packet coloring arbitrarily across the residual summand. -/
def finiteTinyHybridBaseColor (hK : 0 < K) :
    C.finiteTinyHybridGraph.E → Fin K
  | Sum.inl p => C.packetColor p
  | Sum.inr _ => ⟨0, hK⟩

theorem finiteTinyHybridBaseColor_isProperOn (hK : 0 < K) :
    C.finiteTinyHybridGraph.IsProperOn
      C.finiteTinyHybridPacketEdges (C.finiteTinyHybridBaseColor hK) := by
  intro v e he f hf hef
  rcases e with p | e
  · rcases f with q | f
    · apply congrArg Sum.inl
      apply C.packetProper v
      · have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
        simpa [finiteTinyHybridGraph, corePacketGraph] using he'.2
      · have hf' := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
        simpa [finiteTinyHybridGraph, corePacketGraph] using hf'.2
      · simpa [finiteTinyHybridBaseColor] using hef
    · have hf' := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
      exact (C.not_mem_finiteTinyHybridPacketEdges_inr f hf'.1).elim
  · have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
    exact (C.not_mem_finiteTinyHybridPacketEdges_inr e he'.1).elim

/-- Sums over the right summand are sums over the joint residual graph. -/
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

/-- Missing colors on the hybrid packet side depend only on the packet
coloring. -/
theorem finiteTinyHybrid_missingColorsAt_eq_corePacketGraph
    {q : ℕ} (color : C.finiteTinyHybridGraph.E → Fin q) (v : G.V) :
    C.finiteTinyHybridGraph.missingColorsAt
        C.finiteTinyHybridPacketEdges color v =
      C.corePacketGraph.missingColorsAt Finset.univ
        (fun p => color (Sum.inl p)) v := by
  classical
  unfold missingColorsAt
  congr 1
  ext c
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨e, he, rfl⟩
    rcases e with p | e
    · apply Finset.mem_image.mpr
      refine ⟨p, ?_, rfl⟩
      have he' := Finset.mem_filter.mp he
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change C.corePacketGraph.Inc v p
      exact he'.2
    · exact (C.not_mem_finiteTinyHybridPacketEdges_inr e
        (Finset.mem_filter.mp he).1).elim
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨p, hp, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨Sum.inl p, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨C.mem_finiteTinyHybridPacketEdges_inl p, ?_⟩
    change C.corePacketGraph.Inc v p
    exact (Finset.mem_filter.mp hp).2

/-- Lifting both a core edge set and its coloring to the mixed-object graph
does not change the missing palette. -/
theorem ambient_missingColorsAt_eq_core (hK : 0 < K) (v : G.V) :
    P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
        (C.ambientBaseColor hK) v =
      P.coreObjectGraph.missingColorsAt C.fullEdges (C.baseColor hK) v := by
  classical
  unfold missingColorsAt
  congr 1
  ext c
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨e, he, hcolor⟩
    have he' := Finset.mem_filter.mp he
    rcases (P.mixedObjectGraph.mem_liftRestrictionFinset_iff
      P.coreObjects C.fullEdges e).mp he'.1 with ⟨heCore, heFull⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨e, heCore⟩, Finset.mem_filter.mpr ⟨heFull, ?_⟩, ?_⟩
    · exact he'.2
    · simpa [ambientBaseColor, liftRestrictedColor, heCore] using hcolor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨e, he, hcolor⟩
    have he' := Finset.mem_filter.mp he
    apply Finset.mem_image.mpr
    refine ⟨e.1, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (P.mixedObjectGraph.mem_liftRestrictionFinset_iff
        P.coreObjects C.fullEdges e.1).mpr ⟨e.2, he'.1⟩
    · exact he'.2
    · simpa [ambientBaseColor, liftRestrictedColor, e.2] using hcolor

/-- The initial hybrid missing palette is exactly the ambient missing palette
of the expanded full core packets. -/
theorem finiteTinyHybrid_missingColorsAt_eq_ambientBase
    (hK : 0 < K) (v : G.V) :
    C.finiteTinyHybridGraph.missingColorsAt
        C.finiteTinyHybridPacketEdges (C.finiteTinyHybridBaseColor hK) v =
      P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
        (C.ambientBaseColor hK) v := by
  calc
    _ = C.corePacketGraph.missingColorsAt Finset.univ C.packetColor v := by
      simpa [finiteTinyHybridBaseColor] using
        C.finiteTinyHybrid_missingColorsAt_eq_corePacketGraph
          (C.finiteTinyHybridBaseColor hK) v
    _ = P.coreObjectGraph.missingColorsAt C.fullEdges
        (C.baseColor hK) v := by
      exact (C.decomposition.missingColorsAt_expandedFullColor
        C.packetWeight_le hK C.packetColor v).symm
    _ = _ := (C.ambient_missingColorsAt_eq_core hK v).symm

/-- Repackage a mixed proper packet coloring as a recolored core
certificate.  The decomposition, hence both ambient residual pieces, is
unchanged. -/
def finiteTinyRecoloredCertificate (hK : 0 < K)
    (mixed : C.finiteTinyHybridGraph.E → Fin K)
    (hmixed : C.finiteTinyHybridGraph.IsProperOn
      C.finiteTinyHybridPacketEdges mixed) :
    P.coreObjectGraph.FiniteHarmonicPacketColoringCertificate
      P.coreBipartition classOf K where
  decomposition := C.decomposition
  packetWeight_le := C.packetWeight_le
  packetColor := fun p => mixed (Sum.inl p)
  packetProper := by
    intro v p hp q hq heq
    apply Sum.inl_injective
    apply hmixed v
    · apply Finset.mem_filter.mpr
      exact ⟨C.mem_finiteTinyHybridPacketEdges_inl p,
        (Finset.mem_filter.mp hp).2⟩
    · apply Finset.mem_filter.mpr
      exact ⟨C.mem_finiteTinyHybridPacketEdges_inl q,
        (Finset.mem_filter.mp hq).2⟩
    · exact heq

@[simp] theorem finiteTinyRecoloredCertificate_decomposition
    (hK : 0 < K) (mixed : C.finiteTinyHybridGraph.E → Fin K)
    (hmixed : C.finiteTinyHybridGraph.IsProperOn
      C.finiteTinyHybridPacketEdges mixed) :
    (C.finiteTinyRecoloredCertificate hK mixed hmixed).decomposition =
      C.decomposition := rfl

/-- After moment mixing, the ambient missing palette of the recolored full
core is the hybrid missing palette of the mixed packet coloring. -/
theorem finiteTinyRecolored_missingColorsAt_eq_hybrid
    (hK : 0 < K) (mixed : C.finiteTinyHybridGraph.E → Fin K)
    (hmixed : C.finiteTinyHybridGraph.IsProperOn
      C.finiteTinyHybridPacketEdges mixed) (v : G.V) :
    P.mixedObjectGraph.missingColorsAt
        (C.finiteTinyRecoloredCertificate hK mixed hmixed).fullCoreObjects
        ((C.finiteTinyRecoloredCertificate hK mixed hmixed).ambientBaseColor hK)
        v =
      C.finiteTinyHybridGraph.missingColorsAt
        C.finiteTinyHybridPacketEdges mixed v := by
  let C' := C.finiteTinyRecoloredCertificate hK mixed hmixed
  calc
    P.mixedObjectGraph.missingColorsAt C'.fullCoreObjects
        (C'.ambientBaseColor hK) v =
        P.coreObjectGraph.missingColorsAt C'.fullEdges
          (C'.baseColor hK) v := C'.ambient_missingColorsAt_eq_core hK v
    _ = C.corePacketGraph.missingColorsAt Finset.univ
        (fun p => mixed (Sum.inl p)) v := by
      simpa [C', corePacketGraph, finiteTinyRecoloredCertificate] using
        C.decomposition.missingColorsAt_expandedFullColor C.packetWeight_le hK
          (fun p => mixed (Sum.inl p)) v
    _ = _ :=
      (C.finiteTinyHybrid_missingColorsAt_eq_corePacketGraph mixed v).symm

/-- Weighted-moment mixing on the proper packet skeleton produces one joint
proposal for the finite core residual and the tiny tail.  The mixed local
polytope theorem discharges the rounder's exact star-distribution hypothesis. -/
theorem exists_finiteTinyHybridProposal
    (alpha Cbound L eps : ℝ)
    (halpha : 0 < alpha) (hCbound : 0 < Cbound)
    (hL : 0 < L) (heps : 0 < eps) (hT : 0 < T)
    (htau0 : 0 ≤ tau) (htau1 : tau < 1) :
    ∃ N : ℕ, ∀ (n : ℕ)
      (C : P.coreObjectGraph.FiniteHarmonicPacketColoringCertificate
        P.coreBipartition classOf K) (hK : 0 < K),
      N ≤ n → 0 < n → Even K → 4 ≤ K →
      (∀ v, alpha * n ≤
        (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
          (C.ambientBaseColor hK) v).card) →
      (K : ℝ) ≤ Cbound * n →
      (∀ v, C.jointResidualStarCharge v ≤ n) →
      (∀ u v, C.finiteTinyHybridGraph.pairCharge
        C.finiteTinyHybridResidualEdges C.finiteTinyHybridResidualCharge
          u v ≤ L) →
      (∀ v,
        C.jointResidualStarCharge v /
            (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
              (C.ambientBaseColor hK) v).card + eps +
          (T + 1 : ℝ) * (Cbound / (alpha ^ 2 * n)) ≤ 1) →
      (∀ e : P.coreObjectGraph.E,
        P.coreObjectGraph.weight e ≤
          (1 : ℝ) / finiteClassSize (classOf e)) →
      (∀ e : P.coreObjectGraph.E,
        harmonicCharge (P.coreObjectGraph.weight e) =
          (1 : ℝ) / finiteClassSize (classOf e)) →
      ∃ (C' : P.coreObjectGraph.FiniteHarmonicPacketColoringCertificate
          P.coreBipartition classOf K)
        (x : C'.jointResidualGraph.E → Fin K → ℝ),
        C'.decomposition = C.decomposition ∧
        (∀ e c, 0 ≤ x e c ∧
          x e c ≤ Cbound / (alpha ^ 2 * n)) ∧
        (∀ e, ∑ c, x e c ≤ 1) ∧
        (∀ v c, C'.jointResidualGraph.IsAverageOfStarFeasibleSets v
          (fun se ↦ x se.1 c)) ∧
        (∀ e c, 0 < x e c →
          c ∈ P.mixedObjectGraph.missingColorsAt C'.fullCoreObjects
              (C'.ambientBaseColor hK) (P.mixedObjectGraph.fst e.1) ∧
            c ∈ P.mixedObjectGraph.missingColorsAt C'.fullCoreObjects
              (C'.ambientBaseColor hK) (P.mixedObjectGraph.snd e.1)) ∧
        ∀ v, C'.jointResidualGraph.proposalDeficit x v ≤ eps * n := by
  rcases weightedMomentPaletteMixing_proved alpha Cbound L eps halpha
      hCbound hL heps with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n C hK hn hnpos heven hfour hmissing hpalette hchargeStar hpair
    hlocal hfiniteWeight hcharge
  have hcharge0 : ∀ e ∈ C.finiteTinyHybridResidualEdges,
      0 ≤ C.finiteTinyHybridResidualCharge e := by
    intro e he
    rcases e with p | e
    · exact (C.not_mem_finiteTinyHybridResidualEdges_inl p he).elim
    · exact C.jointResidualCharge_nonneg htau1 e
  have hrestricted : ∀ v,
      C.finiteTinyHybridGraph.restrictedCharge
        C.finiteTinyHybridResidualEdges C.finiteTinyHybridResidualCharge v ≤ n := by
    intro v
    rw [C.finiteTinyHybrid_restrictedCharge_eq_jointStarCharge]
    exact hchargeStar v
  have hmissingHybrid : ∀ v, alpha * n ≤
      (C.finiteTinyHybridGraph.missingColorsAt
        C.finiteTinyHybridPacketEdges (C.finiteTinyHybridBaseColor hK) v).card := by
    intro v
    rw [C.finiteTinyHybrid_missingColorsAt_eq_ambientBase hK v]
    exact hmissing v
  rcases hN C.finiteTinyHybridGraph n K C.finiteTinyHybridPacketEdges
      C.finiteTinyHybridResidualEdges (C.finiteTinyHybridBaseColor hK)
      C.finiteTinyHybridResidualCharge hn hnpos heven hfour
      C.finiteTinyHybridPacketEdges_disjoint_residualEdges
      (C.finiteTinyHybridBaseColor_isProperOn hK) hmissingHybrid hpalette
      hcharge0 hrestricted hpair with
    ⟨mixed, xHybrid, hmixed, hsupport, hx, hmass, hrow, huncovered⟩
  let C' := C.finiteTinyRecoloredCertificate hK mixed hmixed
  let x : C'.jointResidualGraph.E → Fin K → ℝ :=
    fun e c => xHybrid (Sum.inr e) c
  refine ⟨C', x, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro e c
    exact hx (Sum.inr e) (C.mem_finiteTinyHybridResidualEdges_inr e) c
  · intro e
    exact hmass (Sum.inr e) (C.mem_finiteTinyHybridResidualEdges_inr e)
  · intro v c
    have hr := hrow v c
    rw [C.finiteTinyHybrid_proposalChargeLoad_eq_joint] at hr
    rw [C.finiteTinyHybrid_restrictedCharge_eq_jointStarCharge] at hr
    have hcard :
        ((C.finiteTinyHybridGraph.missingColorsAt
          C.finiteTinyHybridPacketEdges mixed v).card : ℝ) =
        ((P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
          (C.ambientBaseColor hK) v).card : ℝ) := by
      congr 1
      calc
        (C.finiteTinyHybridGraph.missingColorsAt
            C.finiteTinyHybridPacketEdges mixed v).card =
          (C.finiteTinyHybridGraph.missingColorsAt
            C.finiteTinyHybridPacketEdges
              (C.finiteTinyHybridBaseColor hK) v).card :=
          C.finiteTinyHybridGraph.card_missingColorsAt_eq_of_isProperOn
            C.finiteTinyHybridPacketEdges mixed
            (C.finiteTinyHybridBaseColor hK) hmixed
            (C.finiteTinyHybridBaseColor_isProperOn hK) v
        _ = _ := by
          rw [C.finiteTinyHybrid_missingColorsAt_eq_ambientBase hK v]
    rw [hcard] at hr
    apply C'.jointResidual_isAverageOfStarFeasibleSets_of_chargeBudget
      hT (fun se => x se.1 c) (Cbound / (alpha ^ 2 * n))
      (by positivity) htau0 htau1 hfiniteWeight hcharge
    · intro e
      exact (hx (Sum.inr e.1)
        (C.mem_finiteTinyHybridResidualEdges_inr e.1) c).1
    · intro e
      exact (hx (Sum.inr e.1)
        (C.mem_finiteTinyHybridResidualEdges_inr e.1) c).2
    · have hl := hlocal v
      change
        (∑ e : C.jointResidualGraph.StarEdge v,
          C.jointResidualCharge e.1 * xHybrid (Sum.inr e.1) c) +
            (T + 1 : ℝ) * (Cbound / (alpha ^ 2 * n)) ≤ 1
      linarith
  · intro e c hpos
    have hs := hsupport (Sum.inr e)
      (C.mem_finiteTinyHybridResidualEdges_inr e) c hpos
    simpa [C', x, finiteTinyRecolored_missingColorsAt_eq_hybrid] using hs
  · intro v
    have hu := huncovered v
    rw [C.finiteTinyHybrid_uncoveredCharge_eq_joint] at hu
    exact (C'.jointResidual_proposalDeficit_le_uncoveredCharge
      (fun e c => xHybrid (Sum.inr e) c) htau0 htau1
      (fun e => hmass (Sum.inr e)
        (C.mem_finiteTinyHybridResidualEdges_inr e)) v).trans hu

/-- Uniform form of `exists_finiteTinyHybridProposal`: the threshold is
chosen before the graph, bipartition, tiny cutoff, class encoding, and
certificate. -/
theorem exists_uniform_finiteTinyHybridProposal
    (T : ℕ) (alpha Cbound L eps : ℝ)
    (halpha : 0 < alpha) (hCbound : 0 < Cbound)
    (hL : 0 < L) (heps : 0 < eps) (hT : 0 < T) :
    ∃ N : ℕ, ∀ (H : WeightedMultigraph.{u}) (bH : H.Bipartition)
      (tauH : ℝ) (PH : H.TinyThresholdPacketization bH tauH)
      (K : ℕ) (classOfH : PH.coreObjectGraph.E → Fin T) (n : ℕ)
      (D : PH.coreObjectGraph.FiniteHarmonicPacketColoringCertificate
        PH.coreBipartition classOfH K) (hK : 0 < K),
      0 ≤ tauH → tauH < 1 →
      N ≤ n → 0 < n → Even K → 4 ≤ K →
      (∀ v, alpha * n ≤
        (PH.mixedObjectGraph.missingColorsAt D.fullCoreObjects
          (D.ambientBaseColor hK) v).card) →
      (K : ℝ) ≤ Cbound * n →
      (∀ v, D.jointResidualStarCharge v ≤ n) →
      (∀ u v, D.finiteTinyHybridGraph.pairCharge
        D.finiteTinyHybridResidualEdges D.finiteTinyHybridResidualCharge
          u v ≤ L) →
      (∀ v,
        D.jointResidualStarCharge v /
            (PH.mixedObjectGraph.missingColorsAt D.fullCoreObjects
              (D.ambientBaseColor hK) v).card + eps +
          (T + 1 : ℝ) * (Cbound / (alpha ^ 2 * n)) ≤ 1) →
      (∀ e : PH.coreObjectGraph.E,
        PH.coreObjectGraph.weight e ≤
          (1 : ℝ) / finiteClassSize (classOfH e)) →
      (∀ e : PH.coreObjectGraph.E,
        harmonicCharge (PH.coreObjectGraph.weight e) =
          (1 : ℝ) / finiteClassSize (classOfH e)) →
      ∃ (D' : PH.coreObjectGraph.FiniteHarmonicPacketColoringCertificate
          PH.coreBipartition classOfH K)
        (x : D'.jointResidualGraph.E → Fin K → ℝ),
        D'.decomposition = D.decomposition ∧
        (∀ e c, 0 ≤ x e c ∧
          x e c ≤ Cbound / (alpha ^ 2 * n)) ∧
        (∀ e, ∑ c, x e c ≤ 1) ∧
        (∀ v c, D'.jointResidualGraph.IsAverageOfStarFeasibleSets v
          (fun se ↦ x se.1 c)) ∧
        (∀ e c, 0 < x e c →
          c ∈ PH.mixedObjectGraph.missingColorsAt D'.fullCoreObjects
              (D'.ambientBaseColor hK) (PH.mixedObjectGraph.fst e.1) ∧
            c ∈ PH.mixedObjectGraph.missingColorsAt D'.fullCoreObjects
              (D'.ambientBaseColor hK) (PH.mixedObjectGraph.snd e.1)) ∧
        ∀ v, D'.jointResidualGraph.proposalDeficit x v ≤ eps * n := by
  rcases weightedMomentPaletteMixing_proved alpha Cbound L eps halpha
      hCbound hL heps with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro H bH tauH PH K classOfH n D hK htau0 htau1 hn hnpos heven
    hfour hmissing hpalette hchargeStar hpair hlocal hfiniteWeight hcharge
  have hcharge0 : ∀ e ∈ D.finiteTinyHybridResidualEdges,
      0 ≤ D.finiteTinyHybridResidualCharge e := by
    intro e he
    rcases e with p | e
    · exact (D.not_mem_finiteTinyHybridResidualEdges_inl p he).elim
    · exact D.jointResidualCharge_nonneg htau1 e
  have hrestricted : ∀ v,
      D.finiteTinyHybridGraph.restrictedCharge
        D.finiteTinyHybridResidualEdges D.finiteTinyHybridResidualCharge v ≤ n := by
    intro v
    rw [D.finiteTinyHybrid_restrictedCharge_eq_jointStarCharge]
    exact hchargeStar v
  have hmissingHybrid : ∀ v, alpha * n ≤
      (D.finiteTinyHybridGraph.missingColorsAt
        D.finiteTinyHybridPacketEdges (D.finiteTinyHybridBaseColor hK) v).card := by
    intro v
    rw [D.finiteTinyHybrid_missingColorsAt_eq_ambientBase hK v]
    exact hmissing v
  rcases hN D.finiteTinyHybridGraph n K D.finiteTinyHybridPacketEdges
      D.finiteTinyHybridResidualEdges (D.finiteTinyHybridBaseColor hK)
      D.finiteTinyHybridResidualCharge hn hnpos heven hfour
      D.finiteTinyHybridPacketEdges_disjoint_residualEdges
      (D.finiteTinyHybridBaseColor_isProperOn hK) hmissingHybrid hpalette
      hcharge0 hrestricted hpair with
    ⟨mixed, xHybrid, hmixed, hsupport, hx, hmass, hrow, huncovered⟩
  let D' := D.finiteTinyRecoloredCertificate hK mixed hmixed
  let x : D'.jointResidualGraph.E → Fin K → ℝ :=
    fun e c => xHybrid (Sum.inr e) c
  refine ⟨D', x, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro e c
    exact hx (Sum.inr e) (D.mem_finiteTinyHybridResidualEdges_inr e) c
  · intro e
    exact hmass (Sum.inr e) (D.mem_finiteTinyHybridResidualEdges_inr e)
  · intro v c
    have hr := hrow v c
    rw [D.finiteTinyHybrid_proposalChargeLoad_eq_joint] at hr
    rw [D.finiteTinyHybrid_restrictedCharge_eq_jointStarCharge] at hr
    have hcard :
        ((D.finiteTinyHybridGraph.missingColorsAt
          D.finiteTinyHybridPacketEdges mixed v).card : ℝ) =
        ((PH.mixedObjectGraph.missingColorsAt D.fullCoreObjects
          (D.ambientBaseColor hK) v).card : ℝ) := by
      congr 1
      calc
        (D.finiteTinyHybridGraph.missingColorsAt
            D.finiteTinyHybridPacketEdges mixed v).card =
          (D.finiteTinyHybridGraph.missingColorsAt
            D.finiteTinyHybridPacketEdges
              (D.finiteTinyHybridBaseColor hK) v).card :=
          D.finiteTinyHybridGraph.card_missingColorsAt_eq_of_isProperOn
            D.finiteTinyHybridPacketEdges mixed
            (D.finiteTinyHybridBaseColor hK) hmixed
            (D.finiteTinyHybridBaseColor_isProperOn hK) v
        _ = _ := by
          rw [D.finiteTinyHybrid_missingColorsAt_eq_ambientBase hK v]
    rw [hcard] at hr
    apply D'.jointResidual_isAverageOfStarFeasibleSets_of_chargeBudget
      hT (fun se => x se.1 c) (Cbound / (alpha ^ 2 * n))
      (by positivity) htau0 htau1 hfiniteWeight hcharge
    · intro e
      exact (hx (Sum.inr e.1)
        (D.mem_finiteTinyHybridResidualEdges_inr e.1) c).1
    · intro e
      exact (hx (Sum.inr e.1)
        (D.mem_finiteTinyHybridResidualEdges_inr e.1) c).2
    · have hl := hlocal v
      change
        (∑ e : D.jointResidualGraph.StarEdge v,
          D.jointResidualCharge e.1 * xHybrid (Sum.inr e.1) c) +
            (T + 1 : ℝ) * (Cbound / (alpha ^ 2 * n)) ≤ 1
      linarith
  · intro e c hpos
    have hs := hsupport (Sum.inr e)
      (D.mem_finiteTinyHybridResidualEdges_inr e) c hpos
    simpa [D', x, finiteTinyRecolored_missingColorsAt_eq_hybrid] using hs
  · intro v
    have hu := huncovered v
    rw [D.finiteTinyHybrid_uncoveredCharge_eq_joint] at hu
    exact (D'.jointResidual_proposalDeficit_le_uncoveredCharge
      (fun e c => xHybrid (Sum.inr e) c) htau0 htau1
      (fun e => hmass (Sum.inr e)
        (D.mem_finiteTinyHybridResidualEdges_inr e)) v).trans hu

end FiniteHarmonicPacketColoringCertificate

end

end WeightedMultigraph
end WeightedEdgeColoring
