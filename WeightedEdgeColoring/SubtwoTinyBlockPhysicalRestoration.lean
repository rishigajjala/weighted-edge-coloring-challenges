import WeightedEdgeColoring.SubtwoTinyBlockPalette
import WeightedEdgeColoring.SubtwoLinearGroupedPhysicalRestoration
import WeightedEdgeColoring.SubtwoSmallBlockGroupingBounds

/-! Restore retained actual mixed objects inside a selected three- or
five-vertex block, with its original exterior endpoint reservations. -/

open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
noncomputable section
universe u
variable {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {Sbound : ℕ}
  (P : G.GeneralTinyThresholdPacketization ((1:ℝ)/Sbound))

theorem selectedBlock_card_le_five
    {n : ℕ} (hn : 0 < n) (hlocal : P.mixedObjectGraph.LocallyPacksInto n)
    (b : (P.mixedObjectGraph.subtwoFloorQuotient n).V)
    (hrank : P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFinalRank
      (P.mixedObjectGraph.subtwoFloorCost n) b = 1 ∨
      P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFinalRank
      (P.mixedObjectGraph.subtwoFloorCost n) b = 2) :
    (P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFiber
      (P.mixedObjectGraph.subtwoFloorBlock n) b).card ≤ 5 := by
  let H := P.mixedObjectGraph
  have hcard := H.floorPacketization.groupedGraph.subtwoFinalBlock_fiber_card
    (H.subtwoFloorCost n) (H.subtwoFloorCost_nonneg n)
    (H.subtwoFloorCost_pair_le hn hlocal) (H.subtwoFloorCost_degree_le hn hlocal) b
  change (H.floorPacketization.groupedGraph.subtwoFiber
    (H.subtwoFloorBlock n) b).card = 1 + 2 *
      H.floorPacketization.groupedGraph.subtwoFinalRank (H.subtwoFloorCost n) b at hcard
  dsimp [H] at hcard
  rcases hrank with h1 | h2
  · rw [h1] at hcard
    omega
  · rw [h2] at hcard
    omega

theorem retainedBlock_weight_ge
    (T : Finset G.V)
    (R : Finset (P.mixedObjectGraph.vertexRestriction T).E)
    (hR : ∀ e ∈ R, e.val ∈ P.coreObjects)
    (e : ((P.mixedObjectGraph.vertexRestriction T).edgeRestriction R).E) :
    (1:ℝ)/Sbound ≤
      ((P.mixedObjectGraph.vertexRestriction T).edgeRestriction R).weight e := by
  have he := P.coreObject_weight_ge (hR e.val e.2)
  exact he

theorem exists_retainedBlock_physical_restoration
    (hSbound : 0 < Sbound)
    {n : ℕ} (hn : 0 < n) (hlocal : P.mixedObjectGraph.LocallyPacksInto n)
    (b : (P.mixedObjectGraph.subtwoFloorQuotient n).V)
    (hrank : P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFinalRank
      (P.mixedObjectGraph.subtwoFloorCost n) b = 1 ∨
      P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFinalRank
      (P.mixedObjectGraph.subtwoFloorCost n) b = 2)
    (M D K : ℕ) (hM : 0 < M) (hK : 0 < K)
    (boundaryLabel : Fin K → Option
      (P.mixedObjectGraph.vertexRestriction
        (P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFiber
          (P.mixedObjectGraph.subtwoFloorBlock n) b)).V)
    (hlabel : ∀ v,
      (Fintype.card {c : Fin K // boundaryLabel c = some v} : ℝ) ≤
        n * (P.mixedObjectGraph.subtwoExteriorHarmonicCharge
          (P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFiber
            (P.mixedObjectGraph.subtwoFloorBlock n) b) v.val / n) + D)
    (hpalette : (n : ℝ)*(1999/1000:ℝ)+5*(D+1) ≤ K) :
    let H := P.mixedObjectGraph
    let T := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
    let R : Finset (H.vertexRestriction T).E :=
      Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
    let J := (H.vertexRestriction T).edgeRestriction R
    ∃ A : Finset J.E, ∃ color : J.E → Fin K,
      J.IsFeasibleOn A color ∧
      (∀ e ∈ A, ∀ v, J.Inc v e → boundaryLabel (color e) ≠ some v) ∧
      ∀ v : J.V,
        (∑ o ∈ P.smallInternalObjects T,
          if H.Inc v.val o.1 then H.weight o.1 else 0) +
        (∑ e ∈ Finset.univ \ A, if J.Inc v e then J.weight e else 0) ≤
          25 / (Sbound : ℝ) +
            2*(Fintype.card J.E : ℝ)/M + ((Fintype.card J.V)^2 : ℕ)*M +
            ((Fintype.card J.V)^2*M : ℕ)*((Fintype.card J.V : ℝ)+1)*
              ((Sbound+1)^((Fintype.card J.V)^2*M) : ℕ)*Sbound := by
  dsimp only
  let H := P.mixedObjectGraph
  let T := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
  let R : Finset (H.vertexRestriction T).E :=
    Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
  let J := (H.vertexRestriction T).edgeRestriction R
  have hT : T.card ≤ 5 := P.selectedBlock_card_le_five hn hlocal b hrank
  have hV : Fintype.card J.V ≤ 5 := by
    change Fintype.card (H.vertexRestriction T).V ≤ 5
    rw [H.vertexRestriction_card]
    exact hT
  have hlocalJ : J.LocallyPacksInto n :=
    (H.vertexRestriction T).edgeRestriction_locallyPacksInto R
      (H.vertexRestriction_locallyPacksInto T hlocal)
  have hlower : ∀ e : J.E, (1:ℝ)/Sbound ≤ J.weight e := by
    intro e
    exact P.retainedBlock_weight_ge T R
      (by intro x hx; exact (Finset.mem_filter.mp hx).2) e
  have hq : ∀ v : J.V,
      0 ≤ H.subtwoExteriorHarmonicCharge T v.val / (n:ℝ) := by
    intro v
    exact div_nonneg (H.subtwoExteriorHarmonicCharge_nonneg T v.val)
      (Nat.cast_nonneg _)
  have hsum : (∑ v : J.V,
      H.subtwoExteriorHarmonicCharge T v.val / (n:ℝ)) ≤
      (1999/1000:ℝ) := by
    have hb : (∑ v ∈ T,
        H.subtwoExteriorHarmonicCharge T v / (n:ℝ)) ≤
        (1999/1000:ℝ) := by
      rcases hrank with h1 | h2
      · simpa only [subtwoKappa] using
          H.subtwoFloorThree_exterior_budget hn hlocal b h1
      · simpa only [subtwoKappa] using
          H.subtwoFloorFive_exterior_budget hn hlocal b h2
    change (∑ v : (H.vertexRestriction T).V,
      H.subtwoExteriorHarmonicCharge T v.val / (n:ℝ)) ≤ _
    have heq : (∑ v : (H.vertexRestriction T).V,
        H.subtwoExteriorHarmonicCharge T v.val / (n:ℝ)) =
        ∑ v ∈ T, H.subtwoExteriorHarmonicCharge T v / (n:ℝ) := by
      exact (Finset.sum_subtype T (fun v => Iff.rfl)
        (fun v => H.subtwoExteriorHarmonicCharge T v / (n:ℝ))).symm
    rw [heq]
    exact hb
  have hd : (fun _ : J.E => (1:ℝ)/n) ∈
      WeightedEdgeColoring.Subtwo.PaletteAttainable
        (WeightedEdgeColoring.Subtwo.reservedPaletteBudget (1999/1000:ℝ)
          (fun v : J.V => H.subtwoExteriorHarmonicCharge T v.val / n))
        J.subtwoReservedColorPattern := by
    rcases hrank with h1 | h2
    · exact P.rankOneThree_retained_induced_palette_attainable hn hlocal b h1
    · exact P.rankTwoFive_retained_induced_palette_attainable hn hlocal b h2
  have hpaletteJ : (n : ℝ)*(1999/1000:ℝ)+
      (Fintype.card J.V : ℝ)*(D+1) ≤ K := by
    have hv : (Fintype.card J.V : ℝ) ≤ 5 := by exact_mod_cast hV
    have hd0 : (0:ℝ) ≤ D+1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hv hd0]
  obtain ⟨A,color,hfeas,havoid,herror⟩ :=
    WeightedEdgeColoring.WeightedMultigraph.SubtwoLinearGrouping.exists_physical_reserved_restoration J
      M Sbound hM hSbound hlower n D K hn hK
      (1999/1000:ℝ) (fun v : J.V => H.subtwoExteriorHarmonicCharge T v.val / n)
      hq hsum hd boundaryLabel hlabel hpaletteJ
  refine ⟨A,color,hfeas,havoid,?_⟩
  intro v
  have hsmall := P.smallInternalObjects_starWeight_le T hT
    (by positivity : (0:ℝ) ≤ (1:ℝ)/Sbound) v.val
  have herr := herror v
  have hτ : 25 * ((1:ℝ)/Sbound) = 25 / (Sbound:ℝ) := by ring
  linarith

theorem exists_uniform_retainedBlock_physical_restoration
    (hSbound : 0 < Sbound) (η : ℝ) (hη : 0 < η) :
    ∃ M N : ℕ, 0 < M ∧ 0 < N ∧
      ∀ (n : ℕ), N ≤ n →
      P.mixedObjectGraph.LocallyPacksInto n →
      ∀ (b : (P.mixedObjectGraph.subtwoFloorQuotient n).V),
      (P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFinalRank
        (P.mixedObjectGraph.subtwoFloorCost n) b = 1 ∨
       P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFinalRank
        (P.mixedObjectGraph.subtwoFloorCost n) b = 2) →
      ∀ (D K : ℕ), 0 < K →
      ∀ (boundaryLabel : Fin K → Option
        (P.mixedObjectGraph.vertexRestriction
          (P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFiber
            (P.mixedObjectGraph.subtwoFloorBlock n) b)).V),
      (∀ v,
        (Fintype.card {c : Fin K // boundaryLabel c = some v} : ℝ) ≤
          n * (P.mixedObjectGraph.subtwoExteriorHarmonicCharge
            (P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFiber
              (P.mixedObjectGraph.subtwoFloorBlock n) b) v.val / n) + D) →
      (n : ℝ)*(1999/1000:ℝ)+5*(D+1) ≤ K →
      let H := P.mixedObjectGraph
      let T := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
      let R : Finset (H.vertexRestriction T).E :=
        Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
      let J := (H.vertexRestriction T).edgeRestriction R
      ∃ A : Finset J.E, ∃ color : J.E → Fin K,
        J.IsFeasibleOn A color ∧
        (∀ e ∈ A, ∀ v, J.Inc v e → boundaryLabel (color e) ≠ some v) ∧
        ∀ v : J.V,
          (∑ o ∈ P.smallInternalObjects T,
            if H.Inc v.val o.1 then H.weight o.1 else 0) +
          (∑ e ∈ Finset.univ \ A, if J.Inc v e then J.weight e else 0) ≤
            25 / (Sbound : ℝ) + η*n := by
  obtain ⟨M,N,hM,hN,hparam⟩ :=
    WeightedEdgeColoring.WeightedMultigraph.SubtwoLinearGrouping.exists_uniform_smallBlockGroupingParameters
      Sbound η hη
  refine ⟨M,N,hM,hN,?_⟩
  intro n hnN hlocal b hrank D K hK boundaryLabel hlabel hpalette
  have hn : 0 < n := lt_of_lt_of_le hN hnN
  let H := P.mixedObjectGraph
  let T := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
  let R : Finset (H.vertexRestriction T).E :=
    Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
  let J := (H.vertexRestriction T).edgeRestriction R
  have hT : T.card ≤ 5 := P.selectedBlock_card_le_five hn hlocal b hrank
  have hV : Fintype.card J.V ≤ 5 := by
    change Fintype.card (H.vertexRestriction T).V ≤ 5
    rw [H.vertexRestriction_card]
    exact hT
  have hlocalJ : J.LocallyPacksInto n :=
    (H.vertexRestriction T).edgeRestriction_locallyPacksInto R
      (H.vertexRestriction_locallyPacksInto T hlocal)
  have hlower : ∀ e : J.E, (1:ℝ)/Sbound ≤ J.weight e := by
    intro e
    exact P.retainedBlock_weight_ge T R
      (by intro x hx; exact (Finset.mem_filter.mp hx).2) e
  have hcard := J.subtwo_card_edges_le_of_weight_floor Sbound hSbound hlower hlocalJ
  have herr := hparam J n hnN hV hcard
  obtain ⟨A,color,hfeas,havoid,hraw⟩ :=
    P.exists_retainedBlock_physical_restoration hSbound hn hlocal b
      hrank M D K hM hK boundaryLabel hlabel hpalette
  refine ⟨A,color,hfeas,havoid,?_⟩
  intro v
  have hv := hraw v
  linarith

end
end WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
