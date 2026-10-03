import WeightedEdgeColoring.SubtwoPhysicalPackets

/-!
# Fractional bundle costs behind the packet-count construction

Minimum exact-demand bundle costs dominate full packet counts and are
bounded by the harmonic charge of the original physical edges. Thus
selecting dense blocks from integer packet counts retains the fractional
internal cost needed for restoration.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

namespace BinPackingInstance.ExactDemandPatternCover

theorem subtwo_cost_le_harmonicCharge
    {B : BinPackingInstance} {demand : B.Item → ℕ}
    (C : B.ExactDemandPatternCover demand) (hmin : C.IsMinimumCost) :
    C.cost ≤ ∑ i : B.Item, (demand i : ℝ) * harmonicCharge (B.weight i) := by
  classical
  calc
    C.cost = ∑ p : B.Pattern, C.coeff p := C.sum_coeff_eq_cost.symm
    _ ≤ ∑ p : B.Pattern, C.coeff p * p.harmonicPatternCharge := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hz : C.coeff p = 0
      · simp [hz]
      · have hc : 1 ≤ p.harmonicPatternCharge := by
          by_contra h
          exact hz (C.coeff_eq_zero_of_harmonicPatternCharge_lt_one hmin p
            (lt_of_not_ge h))
        nlinarith [C.coeff_nonneg p]
    _ = ∑ i : B.Item, (demand i : ℝ) * harmonicCharge (B.weight i) := by
      unfold Pattern.harmonicPatternCharge
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul, C.sum_coeff_mul_multiplicity_eq]

end BinPackingInstance.ExactDemandPatternCover

namespace WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem subtwo_edgeSetWeightDemand_charge
    (F : Finset G.E) (charge : ℝ → ℝ) :
    (∑ x : G.EdgeSetWeightType F, (G.edgeSetWeightDemand F x : ℝ) * charge x.1) =
      ∑ e ∈ F, charge (G.weight e) := by
  classical
  calc
    _ = ∑ x : G.EdgeSetWeightType F,
        ∑ e ∈ F, if G.weight e = x.1 then charge x.1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_filter]
      simp [edgeSetWeightDemand]
    _ = ∑ e ∈ F, ∑ x : G.EdgeSetWeightType F,
        if G.weight e = x.1 then charge x.1 else 0 := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      let x : G.EdgeSetWeightType F :=
        ⟨G.weight e, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
      rw [Finset.sum_eq_single x]
      · simp [x]
      · intro y _ hy
        have hn : G.weight e ≠ y.1 := fun h ↦ hy (Subtype.ext h.symm)
        simp [hn]
      · simp

theorem subtwo_floorBundleCover_cost_le_harmonic (k : G.V × G.V) :
    (G.floorBundleCover k).cost ≤
      ∑ e ∈ G.floorBundle k, harmonicCharge (G.weight e) := by
  calc
    _ ≤ ∑ x : G.EdgeSetWeightType (G.floorBundle k),
        (G.edgeSetWeightDemand (G.floorBundle k) x : ℝ) * harmonicCharge x.1 :=
      (G.floorBundleCover k).subtwo_cost_le_harmonicCharge
        (G.floorBundleCover_minimum k)
    _ = _ := G.subtwo_edgeSetWeightDemand_charge (G.floorBundle k) harmonicCharge

/-- Sum of the true fractional costs of all bundles internal to `S`. The
fixed orientation ensures that each unordered pair contributes only once. -/
noncomputable def subtwoFractionalInternalBundleCost (S : Finset G.V) : ℝ :=
  ∑ k : G.V × G.V,
    if k.1 ∈ S ∧ k.2 ∈ S then (G.floorBundleCover k).cost else 0

theorem subtwoFractionalInternalBundleCost_nonneg (S : Finset G.V) :
    0 ≤ G.subtwoFractionalInternalBundleCost S := by
  apply Finset.sum_nonneg
  intro k _
  split
  · exact (G.floorBundleCover k).cost_nonneg
  · rfl

theorem subtwo_fullFloorPacket_internal_card_eq (S : Finset G.V) :
    ((G.floorPacketization.groupedGraph.internalEdges G.fullFloorPacketSet S).card : ℝ) =
      ∑ k : G.V × G.V,
        if k.1 ∈ S ∧ k.2 ∈ S then ((G.floorBundleCover k).floorPacketCount : ℝ) else 0 := by
  classical
  rw [← div_one ((G.floorPacketization.groupedGraph.internalEdges G.fullFloorPacketSet S).card : ℝ),
    ← subtwoSelectedCost_internal]
  unfold subtwoInternalCost
  change (∑ p : G.GlobalFloorPacket ⊕ G.GlobalResidualEdge,
    if G.globalFloorTail p ∈ S ∧ G.globalFloorHead p ∈ S then
      (if p ∈ G.fullFloorPacketSet then (1 : ℝ) / 1 else 0) else 0) = _
  rw [Fintype.sum_sum_type]
  simp only [fullFloorPacketSet, Finset.mem_filter, Finset.mem_univ, true_and,
    if_true, if_false, one_div_one, globalFloorTail, globalFloorHead,
    ite_self, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.1 ∈ S ∧ k.2 ∈ S
  · simp [hk, BinPackingInstance.ExactDemandPatternCover.floorPacketCount]
  · simp [hk]

theorem subtwo_fullFloorPacket_internal_le_fractional (S : Finset G.V) :
    ((G.floorPacketization.groupedGraph.internalEdges G.fullFloorPacketSet S).card : ℝ) ≤
      G.subtwoFractionalInternalBundleCost S := by
  rw [G.subtwo_fullFloorPacket_internal_card_eq]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k.1 ∈ S ∧ k.2 ∈ S
  · simpa [subtwoFractionalInternalBundleCost, hk] using
      (G.floorBundleCover k).floorPacketCount_cast_le_cost
  · simp [hk]

theorem subtwo_sum_floorBundles (f : (G.V × G.V) → G.E → ℝ) :
    (∑ k : G.V × G.V, ∑ e ∈ G.floorBundle k, f k e) =
      ∑ e : G.E, f (G.floorKey e) e := by
  classical
  simp only [floorBundle, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp

theorem subtwoFractionalInternalBundleCost_le_harmonic (S : Finset G.V) :
    G.subtwoFractionalInternalBundleCost S ≤
      G.subtwoInternalCost (fun e ↦ harmonicCharge (G.weight e)) S := by
  classical
  calc
    _ ≤ ∑ k : G.V × G.V,
        if k.1 ∈ S ∧ k.2 ∈ S then
          ∑ e ∈ G.floorBundle k, harmonicCharge (G.weight e) else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k.1 ∈ S ∧ k.2 ∈ S
      · simpa [hk] using G.subtwo_floorBundleCover_cost_le_harmonic k
      · simp [hk]
    _ = ∑ k : G.V × G.V, ∑ e ∈ G.floorBundle k,
        if k.1 ∈ S ∧ k.2 ∈ S then harmonicCharge (G.weight e) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k.1 ∈ S ∧ k.2 ∈ S <;> simp [hk]
    _ = ∑ e : G.E,
        if (G.floorKey e).1 ∈ S ∧ (G.floorKey e).2 ∈ S
        then harmonicCharge (G.weight e) else 0 := G.subtwo_sum_floorBundles _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      unfold floorKey floorTail floorHead
      split <;> simp [and_comm]

theorem subtwo_harmonicVertexCost_eq (v : G.V) :
    G.subtwoVertexCost (fun e ↦ harmonicCharge (G.weight e)) v =
      G.starCharge harmonicCharge v := by
  rw [G.subtwoVertexCost_eq_incidence, G.starCharge_eq_chargeOn_univ]
  rfl

theorem subtwo_floorBundleCost_sum_le_harmonic
    (keep : G.V × G.V → Prop) [DecidablePred keep] :
    (∑ k : G.V × G.V, if keep k then (G.floorBundleCover k).cost else 0) ≤
      ∑ e : G.E, if keep (G.floorKey e) then harmonicCharge (G.weight e) else 0 := by
  classical
  calc
    _ ≤ ∑ k : G.V × G.V,
        if keep k then ∑ e ∈ G.floorBundle k, harmonicCharge (G.weight e) else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : keep k
      · simpa [hk] using G.subtwo_floorBundleCover_cost_le_harmonic k
      · simp [hk]
    _ = ∑ k : G.V × G.V, ∑ e ∈ G.floorBundle k,
        if keep k then harmonicCharge (G.weight e) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : keep k <;> simp [hk]
    _ = _ := G.subtwo_sum_floorBundles _

theorem subtwo_floorKey_incidence (v : G.V) (e : G.E) :
    (G.floorKey e).1 = v ∨ (G.floorKey e).2 = v ↔ G.Inc v e := by
  unfold floorKey floorTail floorHead Inc
  split <;> simp [or_comm]

theorem subtwo_floorKey_internal (S : Finset G.V) (e : G.E) :
    (G.floorKey e).1 ∈ S ∧ (G.floorKey e).2 ∈ S ↔ G.fst e ∈ S ∧ G.snd e ∈ S := by
  unfold floorKey floorTail floorHead
  split <;> simp [and_comm]

/-- Fractional costs of internal bundles meeting one specified vertex. -/
noncomputable def subtwoFractionalIncidentBundleCost (S : Finset G.V) (v : G.V) : ℝ :=
  ∑ k : G.V × G.V,
    if (k.1 ∈ S ∧ k.2 ∈ S) ∧ (k.1 = v ∨ k.2 = v)
      then (G.floorBundleCover k).cost else 0

/-- Harmonic charge of the edges at `v` that are not internal to `S`. -/
noncomputable def subtwoExteriorHarmonicCharge (S : Finset G.V) (v : G.V) : ℝ :=
  ∑ e : G.E, if G.Inc v e ∧ ¬(G.fst e ∈ S ∧ G.snd e ∈ S)
    then harmonicCharge (G.weight e) else 0

theorem subtwo_exterior_add_fractionalIncident_le_star (S : Finset G.V) (v : G.V) :
    G.subtwoExteriorHarmonicCharge S v + G.subtwoFractionalIncidentBundleCost S v ≤
      G.starCharge harmonicCharge v := by
  classical
  have hint := G.subtwo_floorBundleCost_sum_le_harmonic
    (fun k ↦ (k.1 ∈ S ∧ k.2 ∈ S) ∧ (k.1 = v ∨ k.2 = v))
  simp only [G.subtwo_floorKey_internal, G.subtwo_floorKey_incidence] at hint
  change G.subtwoFractionalIncidentBundleCost S v ≤
    ∑ e : G.E, if (G.fst e ∈ S ∧ G.snd e ∈ S) ∧ G.Inc v e
      then harmonicCharge (G.weight e) else 0 at hint
  calc
    _ ≤ G.subtwoExteriorHarmonicCharge S v +
        ∑ e : G.E, if (G.fst e ∈ S ∧ G.snd e ∈ S) ∧ G.Inc v e
          then harmonicCharge (G.weight e) else 0 := add_le_add le_rfl hint
    _ = G.subtwoVertexCost (fun e ↦ harmonicCharge (G.weight e)) v := by
      rw [G.subtwoVertexCost_eq_incidence]
      unfold subtwoExteriorHarmonicCharge
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hi : G.Inc v e <;> by_cases hs : G.fst e ∈ S ∧ G.snd e ∈ S <;>
        simp [hi, hs]
    _ = _ := G.subtwo_harmonicVertexCost_eq v

theorem subtwo_harmonicVertexCost_le
    {n : ℕ} (hlocal : G.LocallyPacksInto n) (v : G.V) :
    G.subtwoVertexCost (fun e ↦ harmonicCharge (G.weight e)) v ≤ subtwoM * n := by
  rw [G.subtwo_harmonicVertexCost_eq]
  have h := G.harmonicStarCharge_le_of_packsStarInto (hlocal v)
  have hm : harmonicBinPackingConstant ≤ subtwoM := Subtwo.harmonic_lt_M.le
  nlinarith [mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem subtwo_exterior_add_fractionalIncident_le
    {n : ℕ} (hlocal : G.LocallyPacksInto n) (S : Finset G.V) (v : G.V) :
    G.subtwoExteriorHarmonicCharge S v + G.subtwoFractionalIncidentBundleCost S v ≤
      subtwoM * n := by
  have h := G.subtwo_harmonicVertexCost_le hlocal v
  rw [G.subtwo_harmonicVertexCost_eq] at h
  exact (G.subtwo_exterior_add_fractionalIncident_le_star S v).trans h

set_option maxHeartbeats 2000000 in
/-- Every actual block retains the required amount of fractional internal
bundle cost, even though it was selected from integer full-packet counts. -/
theorem subtwoFloorBlock_fractional_paid
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (q : (G.subtwoFloorQuotient n).V) :
    (G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q : ℝ) *
        subtwoKappa * n ≤
      G.subtwoFractionalInternalBundleCost
        (G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q) := by
  have hpaid := G.floorPacketization.groupedGraph.subtwoFinalBlock_fiber_paid
    (G.subtwoFloorCost n) (G.subtwoFloorCost_nonneg n)
    (G.subtwoFloorCost_pair_le hn hlocal) (G.subtwoFloorCost_degree_le hn hlocal) q
  let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q
  have heq := G.floorPacketization.groupedGraph.subtwoSelectedCost_internal
    G.fullFloorPacketSet (n : ℝ) S
  change G.floorPacketization.groupedGraph.subtwoInternalCost (G.subtwoFloorCost n) S =
    ((G.floorPacketization.groupedGraph.internalEdges G.fullFloorPacketSet S).card : ℝ) / n at heq
  change (G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q : ℝ) *
    subtwoKappa ≤ G.floorPacketization.groupedGraph.subtwoInternalCost (G.subtwoFloorCost n) S at hpaid
  rw [heq] at hpaid
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcount := (le_div_iff₀ hnR).1 hpaid
  exact hcount.trans (G.subtwo_fullFloorPacket_internal_le_fractional _)

/-- The exterior physical harmonic charge of a block is bounded using its
true fractional internal cost. No grouped-graph local packing is assumed. -/
theorem subtwoFloorBlock_boundary_harmonic_add_fractional_le
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (q : (G.subtwoFloorQuotient n).V) :
    let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q
    G.subtwoBoundaryCost (fun e ↦ harmonicCharge (G.weight e)) S +
        2 * G.subtwoFractionalInternalBundleCost S ≤
      (S.card : ℝ) * (subtwoM * n) := by
  dsimp only
  let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q
  have hid := G.subtwo_incidence_identity (fun e ↦ harmonicCharge (G.weight e)) S
  have hfrac := G.subtwoFractionalInternalBundleCost_le_harmonic S
  have htwo : (2 : ℝ) * G.subtwoFractionalInternalBundleCost S ≤
      2 * G.subtwoInternalCost (fun e ↦ harmonicCharge (G.weight e)) S :=
    mul_le_mul_of_nonneg_left hfrac (by norm_num)
  have hs : (∑ v ∈ S, G.subtwoVertexCost (fun e ↦ harmonicCharge (G.weight e)) v) ≤
      (S.card : ℝ) * (subtwoM * n) := by
    calc
      _ ≤ ∑ _v ∈ S, subtwoM * n :=
        Finset.sum_le_sum (fun v _ ↦ G.subtwo_harmonicVertexCost_le hlocal v)
      _ = _ := by simp
  change G.subtwoBoundaryCost (fun e ↦ harmonicCharge (G.weight e)) S +
    2 * G.subtwoFractionalInternalBundleCost S ≤ (S.card : ℝ) * (subtwoM * n)
  calc
    _ ≤ G.subtwoBoundaryCost (fun e ↦ harmonicCharge (G.weight e)) S +
        2 * G.subtwoInternalCost (fun e ↦ harmonicCharge (G.weight e)) S :=
      add_le_add le_rfl htwo
    _ = ∑ v ∈ S, G.subtwoVertexCost (fun e ↦ harmonicCharge (G.weight e)) v := by
      simpa [add_comm] using hid.symm
    _ ≤ _ := hs

theorem subtwoFloorBlock_boundary_harmonic_le
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (q : (G.subtwoFloorQuotient n).V) :
    let r := (G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q : ℝ)
    let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q
    G.subtwoBoundaryCost (fun e ↦ harmonicCharge (G.weight e)) S ≤
      ((1 + 2 * r) * subtwoM - 2 * r * subtwoKappa) * n := by
  dsimp only
  have hp := G.subtwoFloorBlock_fractional_paid hn hlocal q
  have hb := G.subtwoFloorBlock_boundary_harmonic_add_fractional_le hn hlocal q
  have hcard := G.floorPacketization.groupedGraph.subtwoFinalBlock_fiber_card
    (G.subtwoFloorCost n) (G.subtwoFloorCost_nonneg n)
    (G.subtwoFloorCost_pair_le hn hlocal) (G.subtwoFloorCost_degree_le hn hlocal) q
  dsimp only at hb
  change (G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q).card = _ at hcard
  rw [hcard] at hb
  push_cast at hb
  nlinarith

end WeightedMultigraph
end WeightedEdgeColoring
