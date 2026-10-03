import WeightedEdgeColoring.FiniteHarmonicResidualMultiplicity
import WeightedEdgeColoring.MultigraphLocalPolytope
import WeightedEdgeColoring.PartialCompletion

/-!
# Assembly of finite harmonic packets and coordinated residual rounding

This file records the deterministic endpoint of the finite-cutoff harmonic
argument.  Its substantive input is an explicit diffuse proposal on the
physical residual edges.  A harmonic row budget puts that proposal in every
local star packing polytope.  The bounded-multiplicity whole-edge theorem then
colors almost all residual weight in the packet palette, and descending-weight
cleanup colors the remainder in fresh colors.

The proposal is an explicit hypothesis.  The `WeightedMomentPaletteMixing`
interface requires its proper skeleton and residual to be edge sets of one
multigraph.  Here the skeleton consists of packet edges, while the residual
consists of physical edges.  Applying that interface therefore requires a
bridge between these two edge types.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable {G : WeightedMultigraph.{u}} {T K : ℕ}
variable {b : G.Bipartition} {classOf : G.E → Fin T}

/-- Harmonic row budgets are exactly the finite-size-class hypotheses for the
multigraph local star polytope on the packet residual. -/
theorem FiniteHarmonicPacketColoringCertificate.residualProposal_isAverageOfStarFeasibleSets
    (C : G.FiniteHarmonicPacketColoringCertificate b classOf K)
    (hweight : ∀ e, G.weight e ≤
      (1 : ℝ) / finiteClassSize (classOf e))
    (hcharge : ∀ e, harmonicCharge (G.weight e) =
      (1 : ℝ) / finiteClassSize (classOf e))
    {q : ℕ} (x : C.residualGraph.E → Fin q → ℝ) (M : ℝ)
    (hx0 : ∀ e c, 0 ≤ x e c) (hM0 : 0 ≤ M)
    (hxM : ∀ e c, x e c ≤ M)
    (hbudget : ∀ v c,
      (∑ e : C.residualGraph.StarEdge v,
        harmonicCharge (C.residualGraph.weight e.1) * x e.1 c) +
          (T : ℝ) * M ≤ 1) :
    ∀ v c,
      C.residualGraph.IsAverageOfStarFeasibleSets v (fun e ↦ x e.1 c) := by
  intro v c
  apply C.residualGraph.sizeClasses_isAverageOfStarFeasibleSets_of_charge
    finiteClassSize (fun a ↦ by simp [finiteClassSize])
    (fun e ↦ classOf e.1.1) (fun e ↦ x e.1 c) M
  · intro e
    simpa using hweight e.1.1
  · intro e
    exact hx0 e.1 c
  · exact hM0
  · intro e
    exact hxM e.1 c
  · calc
      (∑ e : C.residualGraph.StarEdge v,
          x e.1 c / (finiteClassSize (classOf e.1.1) : ℝ)) +
            (Fintype.card (Fin T) : ℝ) * M =
          (∑ e : C.residualGraph.StarEdge v,
            harmonicCharge (C.residualGraph.weight e.1) * x e.1 c) +
              (T : ℝ) * M := by
        rw [Fintype.card_fin]
        congr 1
        apply Finset.sum_congr rfl
        intro e _he
        rw [show harmonicCharge (C.residualGraph.weight e.1) =
            (1 : ℝ) / finiteClassSize (classOf e.1.1) by
          simpa using hcharge e.1.1]
        ring
      _ ≤ 1 := hbudget v c

/-- Merge two feasible colorings in disjoint palette blocks while retaining
the exact color used on each side.  The agreement clauses are what the
support-preserving packet completion needs. -/
theorem exists_merge_feasibleOn_with_agreement
    {q r : ℕ} (G : WeightedMultigraph.{u})
    (P R : Finset G.E) (hdisj : Disjoint P R)
    (left : G.E → Fin q) (hleft : G.IsFeasibleOn P left)
    (right : G.E → Fin r) (hright : G.IsFeasibleOn R right) :
    ∃ color : G.E → Fin (q + r),
      G.IsFeasibleOn (P ∪ R) color ∧
      (∀ e ∈ P, color e = Fin.castAdd r (left e)) ∧
      (∀ e ∈ R, color e = Fin.natAdd q (right e)) := by
  classical
  let color : G.E → Fin (q + r) := fun e ↦
    if e ∈ P then Fin.castAdd r (left e) else Fin.natAdd q (right e)
  have hcolor : G.IsFeasibleOn (P ∪ R) color := by
    intro v i
    refine Fin.addCases ?_ ?_ i
    · intro j
      have hload :
          G.colorLoadOn (P ∪ R) color v (Fin.castAdd r j) =
            G.colorLoadOn P left v j := by
        unfold colorLoadOn
        rw [Finset.sum_union hdisj]
        have hleftsum :
            (∑ e ∈ P, if G.Inc v e ∧ color e = Fin.castAdd r j
              then G.weight e else 0) =
            ∑ e ∈ P, if G.Inc v e ∧ left e = j then G.weight e else 0 := by
          apply Finset.sum_congr rfl
          intro e heP
          simp [color, heP]
        rw [hleftsum]
        have hrightzero :
            (∑ e ∈ R, if G.Inc v e ∧ color e = Fin.castAdd r j
              then G.weight e else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro e heR
          have heP : e ∉ P := fun heP ↦
            Finset.disjoint_left.mp hdisj heP heR
          have hne : Fin.natAdd q (right e) ≠ Fin.castAdd r j := by
            intro h
            have hv := congrArg Fin.val h
            simp at hv
            omega
          simp [color, heP, hne]
        rw [hrightzero, add_zero]
      rw [hload]
      exact hleft v j
    · intro j
      have hload :
          G.colorLoadOn (P ∪ R) color v (Fin.natAdd q j) =
            G.colorLoadOn R right v j := by
        unfold colorLoadOn
        rw [Finset.sum_union hdisj]
        have hleftzero :
            (∑ e ∈ P, if G.Inc v e ∧ color e = Fin.natAdd q j
              then G.weight e else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro e heP
          have hne : Fin.castAdd r (left e) ≠ Fin.natAdd q j := by
            intro h
            have hv := congrArg Fin.val h
            simp at hv
            omega
          simp [color, heP, hne]
        rw [hleftzero, zero_add]
        apply Finset.sum_congr rfl
        intro e heR
        have heP : e ∉ P := fun heP ↦
          Finset.disjoint_left.mp hdisj heP heR
        simp [color, heP]
      rw [hload]
      exact hright v j
  refine ⟨color, hcolor, ?_, ?_⟩
  · intro e heP
    simp [color, heP]
  · intro e heR
    have heP : e ∉ P := fun heP ↦ Finset.disjoint_left.mp hdisj heP heR
    simp [color, heP]

/-- Coordinated rounding plus fresh-palette cleanup produces precisely the
support-preserving residual coloring consumed by the packet certificate. -/
theorem exists_supportPreservingResidualColoring_of_boundedMultiplicityWholeEdge
    (hround : BoundedMultiplicityWholeEdgeUniformRounding.{u})
    (T : ℕ) (C0 C1 eta eps : ℝ)
    (hC0 : 0 < C0) (hC1 : 0 < C1)
    (heta : 0 < eta) (heps : 0 ≤ eps) :
    ∃ N : ℕ,
      ∀ (G : WeightedMultigraph.{u}) (b : G.Bipartition)
        (classOf : G.E → Fin T) (K n : ℕ)
        (C : G.FiniteHarmonicPacketColoringCertificate b classOf K)
        (x : C.residualGraph.E → Fin K → ℝ) (hK : 0 < K),
        N ≤ n →
        (∀ v, G.starWeight v ≤ n) →
        (K : ℝ) ≤ C1 * n →
        (∀ e, G.weight e ≤
          (1 : ℝ) / finiteClassSize (classOf e)) →
        (∀ e, harmonicCharge (G.weight e) =
          (1 : ℝ) / finiteClassSize (classOf e)) →
        (∀ e c, 0 ≤ x e c ∧ x e c ≤ C0 / n) →
        (∀ e, ∑ c, x e c ≤ 1) →
        (∀ v c,
          (∑ e : C.residualGraph.StarEdge v,
            harmonicCharge (C.residualGraph.weight e.1) * x e.1 c) +
              (T : ℝ) * (C0 / n) ≤ 1) →
        (∀ e c, 0 < x e c →
          c ∈ G.missingColorsAt C.fullEdges (C.baseColor hK)
              (G.fst e.1) ∧
            c ∈ G.missingColorsAt C.fullEdges (C.baseColor hK)
              (G.snd e.1)) →
        (∀ v, C.residualGraph.proposalDeficit x v ≤ eps * n) →
        C.HasSupportPreservingResidualColoring hK
          (4 * Nat.ceil ((eps + eta) * n) + 1) := by
  rcases exists_missingSupported_partialColoring_of_boundedMultiplicityWholeEdge
      hround (T * (T - 1) / 2) C0 C1 eta hC0 hC1 heta with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro G b classOf K n C x hK hn hstar hpalette hweight hcharge hx hmass
    hbudget hsupport hdeficit
  have havg : ∀ v c,
      C.residualGraph.IsAverageOfStarFeasibleSets v (fun e ↦ x e.1 c) :=
    C.residualProposal_isAverageOfStarFeasibleSets hweight hcharge x
      (C0 / n) (fun e c ↦ (hx e c).1)
      (div_nonneg hC0.le (Nat.cast_nonneg n))
      (fun e c ↦ (hx e c).2) hbudget
  let missing : C.residualGraph.V → Finset (Fin K) := fun v ↦
    G.missingColorsAt C.fullEdges (C.baseColor hK) v
  rcases hN C.residualGraph C.residualBipartition n K missing x hn hK
      C.residualGraph_orientedPairCell_card_le
      (fun v ↦ C.residualGraph_starWeight_le hstar v)
      hpalette hx hmass havg hsupport with
    ⟨P, left, hleft, hleftSupport, hresidual⟩
  let loss : ℝ := (eps + eta) * n
  have hloss0 : 0 ≤ loss :=
    mul_nonneg (add_nonneg heps heta.le) (Nat.cast_nonneg n)
  have hresidual' : ∀ v,
      (∑ e ∈ Finset.univ \ P,
        if C.residualGraph.Inc v e then C.residualGraph.weight e else 0) ≤
          loss := by
    intro v
    calc
      _ ≤ C.residualGraph.proposalDeficit x v + eta * n := hresidual v
      _ ≤ loss := by
        have hd := hdeficit v
        dsimp [loss]
        linarith
  let R : Finset C.residualGraph.E := Finset.univ \ P
  let H := C.residualGraph.edgeRestriction R
  let fresh : ℕ := 4 * Nat.ceil loss + 1
  have hfresh : 0 < fresh := by simp [fresh]
  have hdelta : H.deltaW ≤ Nat.ceil loss := by
    apply C.residualGraph.edgeRestriction_deltaW_le R (Nat.ceil loss)
    · exact_mod_cast Nat.zero_le (Nat.ceil loss)
    · intro v
      exact (hresidual' v).trans (Nat.le_ceil loss)
  rcases H.hasWeightedColoring_four_add_one (Nat.ceil loss) hdelta with
    ⟨rightSub, hrightSub⟩
  let right : C.residualGraph.E → Fin fresh :=
    C.residualGraph.liftRestrictedColor hfresh R rightSub
  have hright : C.residualGraph.IsFeasibleOn R right :=
    C.residualGraph.feasibleOn_liftRestrictedColor hfresh R rightSub hrightSub
  have hdisj : Disjoint P R := by
    simp [R, Finset.disjoint_left]
  rcases exists_merge_feasibleOn_with_agreement C.residualGraph P R hdisj
      left hleft right hright with
    ⟨residualColor, hcolor, hagreeLeft, hagreeRight⟩
  have hunion : P ∪ R = Finset.univ := by
    ext e
    simp [R]
  refine ⟨residualColor,
    (C.residualGraph.isWeightedColoring_iff_feasibleOn_univ residualColor).2
      (by simpa [hunion] using hcolor), ?_⟩
  intro e c heq
  by_cases heP : e ∈ P
  · have heq' : left e = c := by
      have h := (hagreeLeft e heP).symm.trans heq
      exact Fin.castAdd_inj.mp h
    simpa [missing, heq'] using hleftSupport e heP
  · have heR : e ∈ R := by simp [R, heP]
    have h := (hagreeRight e heR).symm.trans heq
    have hv := congrArg Fin.val h
    simp at hv
    omega

end

end WeightedMultigraph
end WeightedEdgeColoring
