import WeightedEdgeColoring.SubtwoMixedGraphWholePhysicalLoss

/-!
# Reservoir support for exact physical feasibility
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {v : G.V} {φ : G.StarEdge v → ℝ}
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : G.BoundedProfileRealization φ s β qstep r hβ hr)

private theorem natFloor_cast_eq_intFloor_cast (a : ℝ) (ha : 0 ≤ a) :
    ((⌊a⌋₊ : ℕ) : ℝ) = ((⌊a⌋ : ℤ) : ℝ) := by
  have hn := (Nat.floor_eq_iff (n := ⌊a⌋₊) ha).mp rfl
  have hi : (⌊a⌋ : ℤ) = (⌊a⌋₊ : ℕ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact_mod_cast hn.1
    · exact_mod_cast hn.2
  rw [hi]
  norm_num

theorem roundedProfileReservoirMass_eq_zero_of_code_zero
    (P : G.RoundedProfileCode R.law)
    (hP : P.2.val = 0) :
    G.roundedProfileReservoirMass R.law hβ hr P = 0 := by
  classical
  unfold roundedProfileReservoirMass fiberMass
  apply Finset.sum_eq_zero
  intro a ha
  have hcode : G.roundedProfileCode R.law hβ hr a = P :=
    (Finset.mem_filter.mp ha).2
  have hR : 0 ≤ (G.rawProfile β (R.law.outcome a)).reservoir :=
    G.rawProfile_reservoir_nonneg (R.law.feasible a)
  have hcast := natFloor_cast_eq_intFloor_cast
    ((G.rawProfile β (R.law.outcome a)).reservoir / r)
    (div_nonneg hR hr.le)
  have hsecond : (G.roundedProfileCode R.law hβ hr a).2 = P.2 :=
    congrArg Prod.snd hcode
  have hfloor : ⌊(G.rawProfile β (R.law.outcome a)).reservoir / r⌋₊ =
      P.2.val := by
    simpa [roundedProfileCode] using congrArg Fin.val hsecond
  have hround : roundReservoir r
      (G.rawProfile β (R.law.outcome a)).reservoir = 0 := by
    unfold roundReservoir
    rw [← hcast, hfloor, hP]
    ring
  rw [hround]
  ring

theorem localExtendedProfileTinyAssign_eq_zero_of_reservoir_zero
    (e : G.StarEdge v)
    (z : G.LocalExtendedProfileState R)
    (hzero : G.localMixedConcreteReservoirSize R z = 0) :
    G.localExtendedProfileTinyAssign R e z = 0 := by
  classical
  rcases z with P | k
  · have hcode : P.1.2.val = 0 := by
      have h : r * (P.1.2.val : ℝ) = 0 := by
        simpa [localMixedConcreteReservoirSize] using hzero
      have hcast : (P.1.2.val : ℝ) = 0 := (mul_eq_zero.mp h).resolve_left (ne_of_gt hr)
      exact_mod_cast hcast
    have hmass := G.roundedProfileReservoirMass_eq_zero_of_code_zero
      R P.1 hcode
    have hcap := R.tinyAssign_capacity (some P)
    have hcap0 : (∑ f : G.StarEdge v,
        G.weight f.1 * R.tinyAssign f (some P)) ≤ 0 := by
      simpa [explicitTinyProfileCapacity, hmass] using hcap
    have hsingle : G.weight e.1 * R.tinyAssign e (some P) ≤
        ∑ f : G.StarEdge v, G.weight f.1 * R.tinyAssign f (some P) := by
      exact Finset.single_le_sum (s := Finset.univ)
        (fun f _ ↦ mul_nonneg (G.weight_nonneg f.1)
          (R.tinyAssign_nonneg f (some P))) (Finset.mem_univ e)
    have hnonneg := R.tinyAssign_nonneg e (some P)
    have hprod : G.weight e.1 * R.tinyAssign e (some P) = 0 := by
      have hnonnegProd := mul_nonneg (G.weight_nonneg e.1) hnonneg
      linarith
    have htiny : R.tinyAssign e (some P) = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (G.weight_pos e.1))
    simpa [localExtendedProfileTinyAssign] using htiny
  · fin_cases k <;>
      simp [localExtendedProfileTinyAssign, localMixedConcreteReservoirSize]
        at hzero ⊢

variable {Color Label : Type*} [Fintype Color] [DecidableEq Color]
  [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → Color → ℝ)
variable (edgeLabel : ∀ w : G.V, G.StarEdge w → Label)
variable (qLaw : ∀ w : G.V, Color → Finset (G.StarEdge w) → ℝ)
variable (RG : ∀ w c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel w)
      (fun e : G.StarEdge w ↦ proposal e.1 c) (qLaw w c) label)
    s β qstep r hβ hr)

theorem mixedGraphTinyAssign_eq_zero_of_concreteReservoir_zero
    (w : G.V) (c : Color) (e : G.StarEdge w)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw RG w c)
    (hzero : G.mixedGraphConcreteReservoirSize
      proposal edgeLabel qLaw RG w c a = 0) :
    G.mixedGraphTinyAssign proposal edgeLabel qLaw RG w c e a = 0 := by
  rcases a with _ | ⟨label, z⟩
  · simp [mixedGraphTinyAssign, mixedLabelGraphTinyAssign]
  · have hz : G.localMixedConcreteReservoirSize (RG w c label) z = 0 := by
      simpa [mixedGraphConcreteReservoirSize] using hzero
    have htiny := G.localExtendedProfileTinyAssign_eq_zero_of_reservoir_zero
      (RG w c label) e z hz
    simp [mixedGraphTinyAssign, mixedLabelGraphTinyAssign, htiny]

theorem selectedMixedTinyOptionMass_eq_zero_of_left_reservoir_zero
    (rho omega : ℝ)
    (choice : ∀ w : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw RG)
    (e : G.E) (c : Color)
    (hzero : G.selectedMixedConcreteReservoirSize
      proposal edgeLabel qLaw RG choice (G.fst e) c = 0) :
    G.selectedMixedTinyOptionMass proposal edgeLabel qLaw RG
      rho omega choice e c = 0 := by
  have hassign := G.mixedGraphTinyAssign_eq_zero_of_concreteReservoir_zero
    proposal edgeLabel qLaw RG (G.fst e) c (G.fstStarEdge e)
      (G.decodeMixedGraphAtom proposal edgeLabel qLaw RG
        (G.fst e) (choice (G.fst e)) c) hzero
  unfold selectedMixedTinyOptionMass mixedGraphTinyProductMass pairedOption
  by_cases hy : G.mixedGraphTinyEdgeMass proposal s β e c = 0
  · simp [hy]
  · simp [hy, hassign]

theorem selectedMixedTinyOptionMass_eq_zero_of_right_reservoir_zero
    (rho omega : ℝ)
    (choice : ∀ w : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw RG)
    (e : G.E) (c : Color)
    (hzero : G.selectedMixedConcreteReservoirSize
      proposal edgeLabel qLaw RG choice (G.snd e) c = 0) :
    G.selectedMixedTinyOptionMass proposal edgeLabel qLaw RG
      rho omega choice e c = 0 := by
  have hassign := G.mixedGraphTinyAssign_eq_zero_of_concreteReservoir_zero
    proposal edgeLabel qLaw RG (G.snd e) c (G.sndStarEdge e)
      (G.decodeMixedGraphAtom proposal edgeLabel qLaw RG
        (G.snd e) (choice (G.snd e)) c) hzero
  unfold selectedMixedTinyOptionMass mixedGraphTinyProductMass pairedOption
  by_cases hy : G.mixedGraphTinyEdgeMass proposal s β e c = 0
  · simp [hy]
  · simp [hy, hassign]

theorem selectedMixedNormalizedTinyOptionMass_eq_zero_of_inc_reservoir_zero
    (rho omega : ℝ)
    (choice : ∀ w : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw RG)
    (e : G.E) (c : Color) (w : G.V)
    (hinc : G.Inc w e)
    (hzero : G.selectedMixedConcreteReservoirSize
      proposal edgeLabel qLaw RG choice w c = 0) :
    G.selectedMixedNormalizedTinyOptionMass proposal edgeLabel qLaw RG
      rho omega choice e c = 0 := by
  unfold selectedMixedNormalizedTinyOptionMass
  by_cases hfst : w = G.fst e
  · have hz := G.selectedMixedTinyOptionMass_eq_zero_of_left_reservoir_zero
      proposal edgeLabel qLaw RG rho omega choice e c (by simpa [hfst] using hzero)
    rw [hz]
    simp
  · have hsnd : w = G.snd e :=
      (hinc.resolve_left (fun h ↦ hfst h.symm)).symm
    have hz := G.selectedMixedTinyOptionMass_eq_zero_of_right_reservoir_zero
      proposal edgeLabel qLaw RG rho omega choice e c (by simpa [hsnd] using hzero)
    rw [hz]
    simp

theorem selectedMixedConcreteReservoirSize_zero_or_ge_r
    (hr1 : r ≤ 1)
    (choice : ∀ w : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw RG)
    (w : G.V) (c : Color) :
    G.selectedMixedConcreteReservoirSize proposal edgeLabel qLaw RG
      choice w c = 0 ∨
      r ≤ G.selectedMixedConcreteReservoirSize proposal edgeLabel qLaw RG
        choice w c := by
  unfold selectedMixedConcreteReservoirSize mixedGraphConcreteReservoirSize
  rcases G.decodeMixedGraphAtom proposal edgeLabel qLaw RG w (choice w) c with
    _ | ⟨label, z⟩
  · exact Or.inl rfl
  · rcases z with P | k
    · by_cases hcode : P.1.2.val = 0
      · left
        simp [localMixedConcreteReservoirSize, hcode]
      · right
        have hcode1 : 1 ≤ P.1.2.val := Nat.one_le_iff_ne_zero.mpr hcode
        have hcast : (1 : ℝ) ≤ P.1.2.val := by exact_mod_cast hcode1
        simpa [localMixedConcreteReservoirSize] using
          (mul_le_mul_of_nonneg_left hcast hr.le)
    · fin_cases k
      · exact Or.inl (by simp [localMixedConcreteReservoirSize])
      · exact Or.inr (by simpa [localMixedConcreteReservoirSize] using hr1)
      · exact Or.inl (by simp [localMixedConcreteReservoirSize])

theorem selectedMixedIntegralTinyColorLoad_eq_zero_of_reservoir_zero
    (rho omega : ℝ)
    (choice : ∀ w : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw RG)
    (decision : {e : G.E // e ∈ G.selectedMixedTinyEdges (β := β)} →
      Option (Fin (Fintype.card Color)))
    (hpositive : ∀ e d, decision e = some d →
      0 < G.selectedMixedNormalizedTinyOptionMass
        proposal edgeLabel qLaw RG rho omega choice e.1
          ((Fintype.equivFin Color).symm d))
    (w : G.V) (d : Fin (Fintype.card Color))
    (hzero : G.selectedMixedConcreteReservoirSize
      proposal edgeLabel qLaw RG choice w
        ((Fintype.equivFin Color).symm d) = 0) :
    G.tinyResidualIntegralColorLoad decision w d = 0 := by
  classical
  unfold tinyResidualIntegralColorLoad
  apply Finset.sum_eq_zero
  intro e _he
  by_cases huse : G.Inc w e.1 ∧ decision e = some d
  · have hz := G.selectedMixedNormalizedTinyOptionMass_eq_zero_of_inc_reservoir_zero
      proposal edgeLabel qLaw RG rho omega choice e.1
      ((Fintype.equivFin Color).symm d) w huse.1 hzero
    exact False.elim ((ne_of_gt (hpositive e d huse.2)) hz)
  · simp [huse]

/-- A genuine feasible physical assignment follows from the selector's tiny
row cap once it fits below one rounded reservoir level.  Empty reservoirs
have exactly zero tiny support, so the additive rounding error is never
charged to a full large slot. -/
theorem exists_selectedMixedAnyJointPhysicalColor_feasible
    (hColor : 0 < Fintype.card Color)
    (hq0 : ∀ w c S, 0 ≤ qLaw w c S)
    (hqsum : ∀ w c, ∑ S, qLaw w c S = 1)
    (hqsingle : ∀ w c S, qLaw w c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel w f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ w : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw RG)
    (hr1 : r ≤ 1) (bound : ℝ) (hslack : bound + 2 * β ≤ r)
    (hTinyCap : ∀ w c,
      G.selectedMixedCandidateCapacityLoad proposal edgeLabel qLaw RG
        rho omega choice c
        (Sum.inr (G.selectedMixedTinyCandidateRow
          proposal edgeLabel qLaw RG choice w c)) < bound)
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (gamma : ℝ) (reserve N : ℕ)
    (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual
        (G.selectedMixedNormalizedLargeOptionMass
          proposal edgeLabel qLaw RG rho omega choice))))
    (hM : ((G.dyadicLargeEdgeOptionSystem
      (Color := Color) (explicitLargeSlotBound β qstep r)
      bucket gamma reserve residual).quantized N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket gamma reserve residual
          (G.selectedMixedNormalizedLargeOptionMass
            proposal edgeLabel qLaw RG rho omega choice))).IsPartialMatching M) :
    let T := G.selectedMixedTinyEdges (β := β)
    let x := G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw RG rho omega choice
    let O := G.selectedDyadicOrdinaryBaseOptionsAny
      (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual x M
    let OFin := O.map
      (OrdinarySlotChoice.colorEquiv (Fintype.equivFin Color)).toEmbedding
    let hO := G.selectedDyadicOrdinaryBaseOptionsAny_isPartialMatching
      (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual x M hM
    let hOFin := ordinarySlotChoice_colorEquiv_isPartialMatching
      G.fst G.snd (explicitLargeSlotBound β qstep r)
      (Fintype.equivFin Color) O hO
    ∃ decision : {e : G.E // e ∈ T} →
        Option (Fin (Fintype.card Color)),
      G.IsFeasibleOn
        (G.ordinarySelectedEdges OFin ∪ G.tinyDecisionColoredEdges T decision)
        (G.ordinaryTinyJointColor hColor OFin hOFin T decision) ∧
      ∀ w,
        G.tinyResidualIntegralLossLoad decision w ≤
          G.tinyResidualLossLoad T
            (fun e ↦ G.selectedMixedResidualOptionMass
              proposal edgeLabel qLaw RG rho omega choice e.1) w + 2 * β := by
  classical
  obtain ⟨decision, hpositive, _hresidual, htiny, hloss⟩ :=
    G.exists_selectedMixedTinyColorDecision
      proposal edgeLabel qLaw RG hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice
  let T := G.selectedMixedTinyEdges (β := β)
  let x := G.selectedMixedNormalizedLargeOptionMass
    proposal edgeLabel qLaw RG rho omega choice
  let O := G.selectedDyadicOrdinaryBaseOptionsAny
    (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual x M
  let OFin := O.map
    (OrdinarySlotChoice.colorEquiv (Fintype.equivFin Color)).toEmbedding
  let hO := G.selectedDyadicOrdinaryBaseOptionsAny_isPartialMatching
    (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual x M hM
  let hOFin := ordinarySlotChoice_colorEquiv_isPartialMatching
    G.fst G.snd (explicitLargeSlotBound β qstep r)
    (Fintype.equivFin Color) O hO
  have hdisj : Disjoint (G.ordinarySelectedEdges OFin) T := by
    rw [Finset.disjoint_left]
    intro e heOrd heTiny
    rcases (G.mem_ordinarySelectedEdges_iff OFin e).mp heOrd with
      ⟨oFin, hoFin, rfl⟩
    rcases Finset.mem_map.mp hoFin with ⟨o, ho, rfl⟩
    have hpos := G.selectedDyadicOrdinaryBaseOptionsAny_mass_pos
      (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual
      x M ho
    have hzero := G.selectedMixedNormalizedLargeOptionMass_eq_zero_of_tiny
      proposal edgeLabel qLaw RG rho omega choice o.job o.color
      o.leftPlace o.rightPlace (G.mem_selectedMixedTinyEdges.mp heTiny)
    exact (ne_of_gt hpos) hzero
  refine ⟨decision, ?_, hloss⟩
  intro w d
  rw [G.colorLoadOn_ordinaryTinyJoint_eq hColor OFin hOFin T decision hdisj w d]
  have hlarge := G.selectedMixedAnyMatching_load_le_concreteSlotSum
    proposal edgeLabel qLaw RG hq0 hqsum hqsingle hs hqstep hr0
    hleft homega0 homega1 hrho hproposal0 choice
    bucket gamma reserve N residual M hM w d
  let c := (Fintype.equivFin Color).symm d
  have hsafe := G.sum_selectedMixedConcreteSlotSize_add_reservoir_le_one
    proposal edgeLabel qLaw RG choice w c
  have hsafe' :
      (∑ i, G.encodedSelectedMixedConcreteSlotSize
        proposal edgeLabel qLaw RG choice w d i) +
      G.selectedMixedConcreteReservoirSize proposal edgeLabel qLaw RG
        choice w c ≤ 1 := by
    simpa [encodedSelectedMixedConcreteSlotSize, c] using hsafe
  rcases G.selectedMixedConcreteReservoirSize_zero_or_ge_r
    proposal edgeLabel qLaw RG hr1 choice w c with hzero | hreserve
  · have htinyZero :=
      G.selectedMixedIntegralTinyColorLoad_eq_zero_of_reservoir_zero
        proposal edgeLabel qLaw RG rho omega choice decision
        (fun e d hed ↦ (hpositive e d hed).1) w d hzero
    rw [htinyZero]
    rw [hzero] at hsafe'
    linarith
  · have htinyBound := htiny w c
    have hcolor : (Fintype.equivFin Color) c = d :=
      Equiv.apply_symm_apply _ _
    rw [hcolor] at htinyBound
    have hnormal := G.selectedMixedNormalizedTinyReservoirLoad_le
      proposal edgeLabel qLaw RG hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice w c
    have hraw := G.selectedMixedTinyReservoirLoad_lt
      proposal edgeLabel qLaw RG rho omega bound choice w c (hTinyCap w c)
    linarith

end WeightedMultigraph

end

end WeightedEdgeColoring
