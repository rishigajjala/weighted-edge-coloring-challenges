import WeightedEdgeColoring.BipartiteTinyChargeAccounting
import WeightedEdgeColoring.EdgeRestrictionPairMultiplicityUnion

/-!
# Completing the finite-plus-tiny bipartite construction

This is the structural composition step.  Moment mixing supplies one diffuse
proposal on the finite residual and the tiny tail together.  The
bounded-multiplicity whole-edge theorem rounds that proposal, inserts the
selected edges into the packet palette, and sends only the proposal deficit
and rounding loss to fresh colors.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {G : WeightedMultigraph.{u}}

namespace TinyThresholdPacketization

open FiniteHarmonicPacketColoringCertificate

variable {b : G.Bipartition} {tau : ℝ}
variable (P : G.TinyThresholdPacketization b tau)
variable {T K : ℕ}
variable {classOf : P.coreObjectGraph.E → Fin T}

/-- Joint moment mixing followed by proposal-relative whole-edge rounding.
All thresholds are uniform in the graph and in its edge weights. -/
theorem exists_hasWeightedColoring_of_finiteTinyHybrid
    (hround : BoundedMultiplicityWholeEdgeUniformRounding.{u})
    (alpha Cbound eps eta : ℝ)
    (halpha : 0 < alpha) (hCbound : 0 < Cbound)
    (heps : 0 < eps) (heta : 0 < eta)
    (hT : 0 < T) (htau0 : 0 ≤ tau)
    (htau1 : tau < 1) (htauHalf : tau ≤ (1 : ℝ) / 2) :
    ∃ N : ℕ, ∀ (n : ℕ)
      (C : P.coreObjectGraph.FiniteHarmonicPacketColoringCertificate
        P.coreBipartition classOf K) (hK : 0 < K),
      N ≤ n → 0 < n → Even K → 4 ≤ K →
      (∀ v, alpha * n ≤
        (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
          (C.ambientBaseColor hK) v).card) →
      (K : ℝ) ≤ Cbound * n →
      (∀ v, C.jointResidualStarCharge v ≤ n) →
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
      G.HasWeightedColoring
        (K + (4 * Nat.ceil ((eps + eta) * n) + 1)) := by
  let L : ℕ := T * (T - 1) / 2 + 1
  have hL : (0 : ℝ) < L := by positivity
  have hC0 : 0 < Cbound / alpha ^ 2 := by positivity
  rcases FiniteHarmonicPacketColoringCertificate.exists_finiteTinyHybridProposal
      (P := P) alpha Cbound (L : ℝ) eps
      halpha hCbound hL heps hT htau0 htau1 with ⟨Nmix, hmix⟩
  rcases hasWeightedColoring_add_fresh_of_jointResidualRounding
      hround L (Cbound / alpha ^ 2) Cbound eta eps
      hC0 hCbound heta heps.le with ⟨Nround, hround⟩
  refine ⟨max Nmix Nround, ?_⟩
  intro n C hK hn hnpos heven hfour hmissing hpalette hchargeStar hlocal
    hfiniteWeight hcharge
  have hnMix : Nmix ≤ n := (le_max_left _ _).trans hn
  have hnRound : Nround ≤ n := (le_max_right _ _).trans hn
  have hpair : ∀ u v,
      C.finiteTinyHybridGraph.pairCharge
        C.finiteTinyHybridResidualEdges C.finiteTinyHybridResidualCharge
          u v ≤ (L : ℝ) := by
    intro u v
    exact C.finiteTinyHybrid_pairCharge_le_of_pairMultiplicity
      htau0 htauHalf C.jointResidualGraph_pairMultiplicityAtMost u v
  rcases hmix n C hK hnMix hnpos heven hfour hmissing hpalette
      hchargeStar hpair hlocal hfiniteWeight hcharge with
    ⟨C', x, hdecomp, hx, hmass, havg, hsupport, hdeficit⟩
  have hchargeStar' : ∀ v, C'.jointResidualStarCharge v ≤ n := by
    intro v
    have h := hchargeStar v
    rw [C.jointResidualStarCharge_eq_residual_add_small] at h
    rw [C'.jointResidualStarCharge_eq_residual_add_small]
    have hres : C'.residualEdges = C.residualEdges := by
      change C'.decomposition.residualEdges = C.decomposition.residualEdges
      rw [hdecomp]
    have hR : C'.residualGraph.starCharge harmonicCharge v =
        C.residualGraph.starCharge harmonicCharge v := by
      change (P.coreObjectGraph.edgeRestriction C'.residualEdges).starCharge
          harmonicCharge v =
        (P.coreObjectGraph.edgeRestriction C.residualEdges).starCharge
          harmonicCharge v
      rw [hres]
    rw [hR]
    exact h
  have hstar : ∀ v, C'.jointResidualGraph.starWeight v ≤ n := by
    intro v
    calc
      C'.jointResidualGraph.starWeight v ≤
          C'.jointResidualStarCharge v := by
        unfold starWeight jointResidualStarCharge
        exact Finset.sum_le_sum fun e _he ↦
          C'.jointResidual_weight_le_charge htau0 htau1 e.1
      _ ≤ n := hchargeStar' v
  have hmult : ∀ k,
      ((Bipartition.edgeRestriction P.mixedObjectGraph
        P.mixedBipartition C'.jointResidualObjects).orientedPairCell k).card
        ≤ L := by
    intro k
    let bR := Bipartition.edgeRestriction P.mixedObjectGraph
      P.mixedBipartition C'.jointResidualObjects
    exact bR.orientedPairCell_card_le_of_pairMultiplicityAtMost
      C'.jointResidualGraph_pairMultiplicityAtMost k
  have hx' : ∀ e c,
      0 ≤ x e c ∧ x e c ≤ (Cbound / alpha ^ 2) / n := by
    intro e c
    refine ⟨(hx e c).1, ?_⟩
    calc
      x e c ≤ Cbound / (alpha ^ 2 * n) := (hx e c).2
      _ = (Cbound / alpha ^ 2) / n := by ring
  have hambient := hround P.mixedObjectGraph P.mixedBipartition
    C'.fullCoreObjects C'.jointResidualObjects n K
    (C'.ambientBaseColor hK) x hnRound hK
    C'.fullCoreObjects_disjoint_jointResidualObjects
    C'.fullCoreObjects_union_jointResidualObjects
    (C'.ambientBaseColor_feasibleOn hK) hmult hstar hpalette hx' hmass
    havg hsupport hdeficit
  exact P.hasWeightedColoring_of_mixedObjectGraph hambient

/-- Fully uniform finite-plus-tiny completion.  Its threshold is selected
before the graph, bipartition, tiny cutoff, class encoding, and certificate. -/
theorem exists_uniform_hasWeightedColoring_of_finiteTinyHybrid
    (hround : BoundedMultiplicityWholeEdgeUniformRounding.{u})
    (T : ℕ) (alpha Cbound eps eta : ℝ)
    (halpha : 0 < alpha) (hCbound : 0 < Cbound)
    (heps : 0 < eps) (heta : 0 < eta) (hT : 0 < T) :
    ∃ N : ℕ, ∀ (H : WeightedMultigraph.{u}) (bH : H.Bipartition)
      (tauH : ℝ) (PH : H.TinyThresholdPacketization bH tauH)
      (K : ℕ) (classOfH : PH.coreObjectGraph.E → Fin T) (n : ℕ)
      (D : PH.coreObjectGraph.FiniteHarmonicPacketColoringCertificate
        PH.coreBipartition classOfH K) (hK : 0 < K),
      0 ≤ tauH → tauH < 1 → tauH ≤ (1 : ℝ) / 2 →
      N ≤ n → 0 < n → Even K → 4 ≤ K →
      (∀ v, alpha * n ≤
        (PH.mixedObjectGraph.missingColorsAt D.fullCoreObjects
          (D.ambientBaseColor hK) v).card) →
      (K : ℝ) ≤ Cbound * n →
      (∀ v, D.jointResidualStarCharge v ≤ n) →
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
      H.HasWeightedColoring
        (K + (4 * Nat.ceil ((eps + eta) * n) + 1)) := by
  let L : ℕ := T * (T - 1) / 2 + 1
  have hL : (0 : ℝ) < L := by positivity
  have hC0 : 0 < Cbound / alpha ^ 2 := by positivity
  rcases FiniteHarmonicPacketColoringCertificate.exists_uniform_finiteTinyHybridProposal
      T alpha Cbound (L : ℝ) eps halpha hCbound hL heps hT with
    ⟨Nmix, hmix⟩
  rcases hasWeightedColoring_add_fresh_of_jointResidualRounding
      hround L (Cbound / alpha ^ 2) Cbound eta eps
      hC0 hCbound heta heps.le with ⟨Nround, hround⟩
  refine ⟨max Nmix Nround, ?_⟩
  intro H bH tauH PH K classOfH n D hK htau0 htau1 htauHalf hn hnpos
    heven hfour hmissing hpalette hchargeStar hlocal hfiniteWeight hcharge
  have hnMix : Nmix ≤ n := (le_max_left _ _).trans hn
  have hnRound : Nround ≤ n := (le_max_right _ _).trans hn
  have hpair : ∀ u v,
      D.finiteTinyHybridGraph.pairCharge
        D.finiteTinyHybridResidualEdges D.finiteTinyHybridResidualCharge
          u v ≤ (L : ℝ) := by
    intro u v
    exact D.finiteTinyHybrid_pairCharge_le_of_pairMultiplicity
      htau0 htauHalf D.jointResidualGraph_pairMultiplicityAtMost u v
  rcases hmix H bH tauH PH K classOfH n D hK htau0 htau1 hnMix hnpos
      heven hfour hmissing hpalette hchargeStar hpair hlocal hfiniteWeight
      hcharge with
    ⟨D', x, hdecomp, hx, hmass, havg, hsupport, hdeficit⟩
  have hchargeStar' : ∀ v, D'.jointResidualStarCharge v ≤ n := by
    intro v
    have h := hchargeStar v
    rw [D.jointResidualStarCharge_eq_residual_add_small] at h
    rw [D'.jointResidualStarCharge_eq_residual_add_small]
    have hres : D'.residualEdges = D.residualEdges := by
      change D'.decomposition.residualEdges = D.decomposition.residualEdges
      rw [hdecomp]
    have hR : D'.residualGraph.starCharge harmonicCharge v =
        D.residualGraph.starCharge harmonicCharge v := by
      change (PH.coreObjectGraph.edgeRestriction D'.residualEdges).starCharge
          harmonicCharge v =
        (PH.coreObjectGraph.edgeRestriction D.residualEdges).starCharge
          harmonicCharge v
      rw [hres]
    rw [hR]
    exact h
  have hstar : ∀ v, D'.jointResidualGraph.starWeight v ≤ n := by
    intro v
    calc
      D'.jointResidualGraph.starWeight v ≤
          D'.jointResidualStarCharge v := by
        unfold starWeight jointResidualStarCharge
        exact Finset.sum_le_sum fun e _he ↦
          D'.jointResidual_weight_le_charge htau0 htau1 e.1
      _ ≤ n := hchargeStar' v
  have hmult : ∀ k,
      ((Bipartition.edgeRestriction PH.mixedObjectGraph
        PH.mixedBipartition D'.jointResidualObjects).orientedPairCell k).card
        ≤ L := by
    intro k
    let bR := Bipartition.edgeRestriction PH.mixedObjectGraph
      PH.mixedBipartition D'.jointResidualObjects
    exact bR.orientedPairCell_card_le_of_pairMultiplicityAtMost
      D'.jointResidualGraph_pairMultiplicityAtMost k
  have hx' : ∀ e c,
      0 ≤ x e c ∧ x e c ≤ (Cbound / alpha ^ 2) / n := by
    intro e c
    refine ⟨(hx e c).1, ?_⟩
    calc
      x e c ≤ Cbound / (alpha ^ 2 * n) := (hx e c).2
      _ = (Cbound / alpha ^ 2) / n := by ring
  have hambient := hround PH.mixedObjectGraph PH.mixedBipartition
    D'.fullCoreObjects D'.jointResidualObjects n K
    (D'.ambientBaseColor hK) x hnRound hK
    D'.fullCoreObjects_disjoint_jointResidualObjects
    D'.fullCoreObjects_union_jointResidualObjects
    (D'.ambientBaseColor_feasibleOn hK) hmult hstar hpalette hx' hmass
    havg hsupport hdeficit
  exact PH.hasWeightedColoring_of_mixedObjectGraph hambient

/-- Uniform finite-plus-tiny completion through deficit-aware retained-core rounding. -/
theorem exists_uniform_hasWeightedColoring_of_finiteTinyHybrid_deficitAware
    (hround : DeficitAwareBoundedMultiplicityWholeEdgeUniformRounding.{u})
    (T : ℕ) (alpha Cbound trim eps eta : ℝ)
    (halpha : 0 < alpha) (hCbound : 0 < Cbound) (hCbound4 : Cbound < 4)
    (htrim0 : 0 < trim) (htrim1 : trim < 1)
    (htrimEta : 64 * trim < eta)
    (heps : 0 < eps) (heta : 0 < eta) (hT : 0 < T) :
    ∃ N : ℕ, ∀ (H : WeightedMultigraph.{u}) (bH : H.Bipartition)
      (tauH : ℝ) (PH : H.TinyThresholdPacketization bH tauH)
      (K : ℕ) (classOfH : PH.coreObjectGraph.E → Fin T) (n : ℕ)
      (D : PH.coreObjectGraph.FiniteHarmonicPacketColoringCertificate
        PH.coreBipartition classOfH K) (hK : 0 < K),
      0 ≤ tauH → tauH < 1 → tauH ≤ (1 : ℝ) / 2 →
      N ≤ n → 0 < n → Even K → 4 ≤ K →
      (∀ v, alpha * n ≤
        (PH.mixedObjectGraph.missingColorsAt D.fullCoreObjects
          (D.ambientBaseColor hK) v).card) →
      (K : ℝ) ≤ Cbound * n →
      (∀ v, D.jointResidualStarCharge v ≤ n) →
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
      H.HasWeightedColoring
        (K + (4 * Nat.ceil ((eps / trim + eta) * n) + 1)) := by
  let L : ℕ := T * (T - 1) / 2 + 1
  have hL : (0 : ℝ) < L := by positivity
  have hC0 : 0 < Cbound / alpha ^ 2 := by positivity
  rcases FiniteHarmonicPacketColoringCertificate.exists_uniform_finiteTinyHybridProposal
      T alpha Cbound (L : ℝ) eps halpha hCbound hL heps hT with
    ⟨Nmix, hmix⟩
  rcases hasWeightedColoring_add_fresh_of_jointResidualDeficitAwareRounding
      hround L (Cbound / alpha ^ 2) Cbound trim eta eps
      hC0 hCbound hCbound4 htrim0 htrim1 htrimEta heta heps.le with
    ⟨Nround, hround⟩
  refine ⟨max Nmix Nround, ?_⟩
  intro H bH tauH PH K classOfH n D hK htau0 htau1 htauHalf hn hnpos
    heven hfour hmissing hpalette hchargeStar hlocal hfiniteWeight hcharge
  have hnMix : Nmix ≤ n := (le_max_left _ _).trans hn
  have hnRound : Nround ≤ n := (le_max_right _ _).trans hn
  have hpair : ∀ u v,
      D.finiteTinyHybridGraph.pairCharge
        D.finiteTinyHybridResidualEdges D.finiteTinyHybridResidualCharge
          u v ≤ (L : ℝ) := by
    intro u v
    exact D.finiteTinyHybrid_pairCharge_le_of_pairMultiplicity
      htau0 htauHalf D.jointResidualGraph_pairMultiplicityAtMost u v
  rcases hmix H bH tauH PH K classOfH n D hK htau0 htau1 hnMix hnpos
      heven hfour hmissing hpalette hchargeStar hpair hlocal hfiniteWeight
      hcharge with
    ⟨D', x, hdecomp, hx, hmass, havg, hsupport, hdeficit⟩
  have hchargeStar' : ∀ v, D'.jointResidualStarCharge v ≤ n := by
    intro v
    have h := hchargeStar v
    rw [D.jointResidualStarCharge_eq_residual_add_small] at h
    rw [D'.jointResidualStarCharge_eq_residual_add_small]
    have hres : D'.residualEdges = D.residualEdges := by
      change D'.decomposition.residualEdges = D.decomposition.residualEdges
      rw [hdecomp]
    have hR : D'.residualGraph.starCharge harmonicCharge v =
        D.residualGraph.starCharge harmonicCharge v := by
      change (PH.coreObjectGraph.edgeRestriction D'.residualEdges).starCharge
          harmonicCharge v =
        (PH.coreObjectGraph.edgeRestriction D.residualEdges).starCharge
          harmonicCharge v
      rw [hres]
    rw [hR]
    exact h
  have hstar : ∀ v, D'.jointResidualGraph.starWeight v ≤ n := by
    intro v
    calc
      D'.jointResidualGraph.starWeight v ≤
          D'.jointResidualStarCharge v := by
        unfold starWeight jointResidualStarCharge
        exact Finset.sum_le_sum fun e _he ↦
          D'.jointResidual_weight_le_charge htau0 htau1 e.1
      _ ≤ n := hchargeStar' v
  have hmult : ∀ k,
      ((Bipartition.edgeRestriction PH.mixedObjectGraph
        PH.mixedBipartition D'.jointResidualObjects).orientedPairCell k).card
        ≤ L := by
    intro k
    let bR := Bipartition.edgeRestriction PH.mixedObjectGraph
      PH.mixedBipartition D'.jointResidualObjects
    exact bR.orientedPairCell_card_le_of_pairMultiplicityAtMost
      D'.jointResidualGraph_pairMultiplicityAtMost k
  have hx' : ∀ e c,
      0 ≤ x e c ∧ x e c ≤ (Cbound / alpha ^ 2) / n := by
    intro e c
    refine ⟨(hx e c).1, ?_⟩
    calc
      x e c ≤ Cbound / (alpha ^ 2 * n) := (hx e c).2
      _ = (Cbound / alpha ^ 2) / n := by ring
  have hambient := hround PH.mixedObjectGraph PH.mixedBipartition
    D'.fullCoreObjects D'.jointResidualObjects n K
    (D'.ambientBaseColor hK) x hnRound hK
    D'.fullCoreObjects_disjoint_jointResidualObjects
    D'.fullCoreObjects_union_jointResidualObjects
    (D'.ambientBaseColor_feasibleOn hK) hmult hstar hpalette hx' hmass
    havg hsupport hdeficit
  exact PH.hasWeightedColoring_of_mixedObjectGraph hambient

end TinyThresholdPacketization

end

end WeightedMultigraph
end WeightedEdgeColoring
