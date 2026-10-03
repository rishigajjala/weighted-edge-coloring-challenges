import WeightedEdgeColoring.SubtwoActualGroupedFloor
import WeightedEdgeColoring.SubtwoActualObjectGroupingRecovery
import WeightedEdgeColoring.SubtwoMixedObjectAsymptoticReduction

/-!
# Bounded weight menus suffice for the unrestricted theorem

The only premise here is the remaining uniform coloring construction on
the actual preprocessed finite/tiny graph. The preprocessing, both physical
color pullbacks, cutoff choice, and final weighted cleanup are proved.
This conditional reduction is not an inhabitant of `SubtwoBPAsymptotic`.
-/

set_option maxHeartbeats 4000000
open scoped BigOperators
namespace WeightedEdgeColoring
noncomputable section
universe u

theorem subtwoBPAsymptotic_of_uniform_boundedTypeMixedColorings
    (h : ∀ η : ℝ, 0 < η → ∃ S0 : ℕ, ∀ S : ℕ, max 40 S0 ≤ S →
      ∀ D : ℕ, ∃ N : ℕ,
      ∀ (G : WeightedMultigraph.{u})
        (P : G.GeneralTinyThresholdPacketization ((1 : ℝ)/S)) (n : ℕ),
        N ≤ n → P.mixedObjectGraph.LocallyPacksInto n →
        P.mixedObjectGraph.FloorBundleAtMostOneTiny D S →
        ∃ (F : Finset P.mixedObjectGraph.E) (q : ℕ)
          (color : P.mixedObjectGraph.E → Fin q),
          0 < q ∧ P.mixedObjectGraph.IsFeasibleOn F color ∧
          (q : ℝ) ≤ ((1999/1000 : ℝ)+η)*n ∧
          ∀ v, (∑ e ∈ Finset.univ \ F,
            if P.mixedObjectGraph.Inc v e then P.mixedObjectGraph.weight e else 0) ≤ η*n) :
    SubtwoBPAsymptotic.{u} := by
  apply subtwoBPAsymptotic_of_uniform_fineCutoffPartialColorings
  intro η hη
  have hhalf : 0 < η/2 := by positivity
  obtain ⟨S0,hfine⟩ := h (η/2) hhalf
  refine ⟨S0, ?_⟩
  intro S hSlarge
  have hS : 0 < S := by have hh := (le_max_left 40 S0).trans hSlarge; omega
  obtain ⟨M,hM,hwidth⟩ := WeightedMultigraph.SubtwoMixedCoreGrouping.exists_uniform_groupingWidth
    S (η/2) hhalf
  obtain ⟨N,hN⟩ := hfine S hSlarge (2*M)
  refine ⟨N,?_⟩
  intro G P n hn hlocal
  obtain ⟨F,q,color,hq,hfeas,hpalette,hleft⟩ := hN
    (P.coreGroupedGraph M) (P.coreGroupedPacketization M) n hn
    (P.coreGroupedPacketization_locallyPacksInto M hM hlocal)
    (P.coreGroupedPacketization_oneTinyFloor M hS)
  obtain ⟨A,lifted,hfeasible,hresidual⟩ := P.exists_recover_coreGroupedObjects_partialColor
    M hM hS hlocal F q hq color hfeas ((η/2)*n) hleft
  refine ⟨A,q,lifted,hfeasible,?_,?_⟩
  · exact hpalette.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n))
  · intro v
    have hw := mul_le_mul_of_nonneg_right hwidth (Nat.cast_nonneg n)
    have hh := hresidual v
    nlinarith

end
end WeightedEdgeColoring
