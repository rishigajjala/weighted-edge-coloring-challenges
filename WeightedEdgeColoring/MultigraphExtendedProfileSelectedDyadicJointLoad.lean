import WeightedEdgeColoring.BoundedMultiplicitySelectedDyadicInitialBounds
import WeightedEdgeColoring.MultigraphExtendedProfileSelectedJointLoad
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeMatchingExtraction
import WeightedEdgeColoring.MultigraphExtendedProfileBlockVarianceSelection

/-!
# Joint selected-profile completion for local dyadic extra options

The tiny-edge completion sees only the ordinary projection of the large-edge
matching.  Consequently its proof is unchanged by replacing the uniform
cyclic right summand with the locally dyadic one.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]
variable {B k N reserve : ℕ}
variable {s β q r gamma : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

@[simp] theorem decoded_encodeExtendedProfileBlockSelection_joint
    (selected : ∀ v (b : Fin B), Fin k → G.ExtendedProfileState R0 v)
    (v : G.V) (c : Fin (B * k)) :
    G.decodedExtendedProfileBlockSelection R0
        (G.encodeExtendedProfileBlockSelection R0 selected) v c =
      selected v (extendedProfileColorBlock c)
        (extendedProfileColorPosition c) := by
  simp [decodedExtendedProfileBlockSelection,
    encodeExtendedProfileBlockSelection]

theorem selectedDyadicNormalizedLargeMatching_load_le_concreteSlotSum
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleftParam : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockLargeResidual R0 omega rho choice)
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice))))
    (hM : ((G.dyadicLargeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r) bucket gamma
      reserve (G.selectedBlockLargeResidual R0 omega rho choice)).quantized N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
          reserve (G.selectedBlockLargeResidual R0 omega rho choice)
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice))).IsPartialMatching M)
    (v : G.V) (c : Fin (B * k)) :
    let O := G.selectedDyadicOrdinaryBaseOptions
      (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
      (G.selectedBlockLargeResidual R0 omega rho choice)
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) M
    let hO := G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
      (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
      (G.selectedBlockLargeResidual R0 omega rho choice)
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) M hM
    G.selectedOrdinaryIntegralColorLoad O hO v c ≤
      ∑ i, G.selectedBlockConcreteSlotSize R0 choice v c i := by
  dsimp only
  apply G.selectedOrdinaryIntegralColorLoad_le_slotSum
    (G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
      (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
      (G.selectedBlockLargeResidual R0 omega rho choice)
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) M hM)
    (G.selectedBlockConcreteSlotSize R0 choice)
    (G.selectedBlockConcreteSlotSize_nonneg R0 choice)
  · intro o ho
    apply G.weight_le_selectedBlockConcreteSlotSize_fst_of_large_pos R0
      hn hs hq hr0 hleftParam rho omega homega0 homega1 hrho choice
    exact G.selectedDyadicOrdinaryBaseOptions_mass_pos
      (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
      (G.selectedBlockLargeResidual R0 omega rho choice)
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) M ho
  · intro o ho
    apply G.weight_le_selectedBlockConcreteSlotSize_snd_of_large_pos R0
      hn hs hq hr0 hleftParam rho omega homega0 homega1 hrho choice
    exact G.selectedDyadicOrdinaryBaseOptions_mass_pos
      (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
      (G.selectedBlockLargeResidual R0 omega rho choice)
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) M ho

theorem selectedDyadicNormalizedLargeMatching_disjoint_tinyEdges
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockLargeResidual R0 omega rho choice)
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)))) :
    let O := G.selectedDyadicOrdinaryBaseOptions
      (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
      (G.selectedBlockLargeResidual R0 omega rho choice)
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) M
    Disjoint (G.ordinarySelectedEdges O) (G.selectedBlockTinyEdges β) := by
  dsimp only
  rw [Finset.disjoint_left]
  intro e heOrd heTiny
  rcases (G.mem_ordinarySelectedEdges_iff _ e).mp heOrd with ⟨o, ho, rfl⟩
  have hpos := G.selectedDyadicOrdinaryBaseOptions_mass_pos
    (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
    (G.selectedBlockLargeResidual R0 omega rho choice)
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) M ho
  have hzero := G.selectedBlockNormalizedLargeOptionMass_eq_zero_of_tiny
    R0 rho omega choice o.job o.color o.leftPlace o.rightPlace
      (G.mem_selectedBlockTinyEdges.mp heTiny)
  exact (ne_of_gt hpos) hzero

theorem exists_selectedBlockTinyColorDecision_dyadic_joint_isFeasibleOn
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hleftParam : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockLargeResidual R0 omega rho choice)
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice))))
    (hM : ((G.dyadicLargeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r) bucket gamma
      reserve (G.selectedBlockLargeResidual R0 omega rho choice)).quantized N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
          reserve (G.selectedBlockLargeResidual R0 omega rho choice)
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice))).IsPartialMatching M)
    (a delta : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (htinyFractional : ∀ v c,
      G.selectedBlockNormalizedTinyReservoirLoad R0 rho omega choice (v, c) ≤
        a * G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c) + delta)
    (herror : delta + 2 * β ≤ (1 - a) * r) :
    ∃ decision : {e : G.E // e ∈ G.selectedBlockTinyEdges β} →
        Option (Fin (B * k)),
      (let O := G.selectedDyadicOrdinaryBaseOptions
          (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
          (G.selectedBlockLargeResidual R0 omega rho choice)
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) M
       let hO := G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
          (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
          (G.selectedBlockLargeResidual R0 omega rho choice)
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) M hM
       G.IsFeasibleOn
         (G.ordinarySelectedEdges O ∪
           G.tinyDecisionColoredEdges (G.selectedBlockTinyEdges β) decision)
         (G.ordinaryTinyJointColor hn O hO
           (G.selectedBlockTinyEdges β) decision)) ∧
      ∀ v,
        G.tinyResidualIntegralLossLoad decision v ≤
          G.tinyResidualLossLoad (G.selectedBlockTinyEdges β)
            (fun e ↦ G.selectedBlockResidualOptionMass
              R0 rho omega choice e.1) v + 2 * β := by
  obtain ⟨decision, hpositive, _hresidual, htinyIntegral, hloss⟩ :=
    G.exists_selectedBlockTinyColorDecision R0
      hn hs hq hr0 hleftParam rho omega homega0 homega1 hrho choice
  let O := G.selectedDyadicOrdinaryBaseOptions
    (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
    (G.selectedBlockLargeResidual R0 omega rho choice)
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) M
  let hO := G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
    (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
    (G.selectedBlockLargeResidual R0 omega rho choice)
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) M hM
  have hload : ∀ v c,
      G.selectedOrdinaryIntegralColorLoad O hO v c +
        G.tinyResidualIntegralColorLoad decision v c ≤ 1 := by
    intro v c
    have hlarge := G.selectedDyadicNormalizedLargeMatching_load_le_concreteSlotSum
      R0 hn hs hq hr0 hleftParam rho omega homega0 homega1 hrho choice
      bucket M hM v c
    by_cases hex : ∃ e, G.Inc v e.1 ∧ decision e = some c
    · rcases hex with ⟨e, hinc, hdecision⟩
      have hsupport := (hpositive e c hdecision).2
      have hreservoirPos :
          0 < G.extendedProfileReservoirSize R0 v
            (G.decodedExtendedProfileBlockSelection R0 choice v c) := by
        rcases hinc with hfst | hsnd
        · subst v
          exact hsupport.1
        · subst v
          exact hsupport.2
      have hreservoirGe :=
        G.extendedProfileReservoirSize_ge_r_of_pos R0 hr1 v _ hreservoirPos
      have hcoef : 0 ≤ 1 - a := sub_nonneg.mpr ha1
      have htiny := (htinyIntegral v c).trans
        (add_le_add (htinyFractional v c) (le_refl (2 * β)))
      have hsafe := G.sum_selectedBlockConcreteSlotSize_add_reservoir_le_one
        R0 choice v c
      have hslack := herror.trans
        (mul_le_mul_of_nonneg_left hreservoirGe hcoef)
      dsimp only [O, hO] at hlarge ⊢
      nlinarith
    · have htinyZero : G.tinyResidualIntegralColorLoad decision v c = 0 := by
        unfold tinyResidualIntegralColorLoad
        apply Finset.sum_eq_zero
        intro e _he
        have hnot : ¬(G.Inc v e.1 ∧ decision e = some c) := by
          intro he
          exact hex ⟨e, he⟩
        simp [hnot]
      have hslot := G.sum_selectedBlockConcreteSlotSize_le_one R0 choice v c
      dsimp only [O, hO] at hlarge ⊢
      rw [htinyZero, add_zero]
      exact hlarge.trans hslot
  refine ⟨decision, ?_, hloss⟩
  dsimp only
  apply G.ordinaryTinyJoint_isFeasibleOn_of_load_le_one hn
  · exact G.selectedDyadicNormalizedLargeMatching_disjoint_tinyEdges
      R0 rho omega choice bucket M
  · exact hload

/-- Directly substitute the reservoir-capacity selector estimate into the
local-dyadic joint decoder. -/
theorem exists_jointColoring_of_selectedBlock_reservoirCapacity_dyadic
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hleftParam : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (selected : ∀ v (b : Fin B), Fin k → G.ExtendedProfileState R0 v)
    (deviation : ℝ)
    (htinyCapacity : ∀ tiny : G.ExtendedProfileTinyRow (n := B * k),
      G.selectedBlockCapacityLoad R0 rho omega
          (G.encodeExtendedProfileBlockSelection R0 selected)
          (Sum.inr tiny) / ((B * k : ℕ) : ℝ) <
        rho * G.extendedProfileReservoirSize R0 tiny.1
            (selected tiny.1 (extendedProfileColorBlock tiny.2)
              (extendedProfileColorPosition tiny.2)) /
            extendedProfileSmoothingKappa omega β q r +
          extendedProfileCandidateCapacityScale rho s omega β q r /
            ((B * k : ℕ) : ℝ) *
            deviation)
    (hrhoKappa : rho ≤ extendedProfileSmoothingKappa omega β q r)
    (hscalar :
      extendedProfileCandidateCapacityScale rho s omega β q r /
            ((B * k : ℕ) : ℝ) *
            deviation +
          2 * β ≤
        (1 - rho / extendedProfileSmoothingKappa omega β q r) * r)
    (bucket : G.E → Class)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve
        (G.selectedBlockLargeResidual R0 omega rho
          (G.encodeExtendedProfileBlockSelection R0 selected))
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega
          (G.encodeExtendedProfileBlockSelection R0 selected)))))
    (hM : ((G.dyadicLargeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r) bucket gamma
      reserve
      (G.selectedBlockLargeResidual R0 omega rho
        (G.encodeExtendedProfileBlockSelection R0 selected))).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve
        (G.selectedBlockLargeResidual R0 omega rho
          (G.encodeExtendedProfileBlockSelection R0 selected))
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega
          (G.encodeExtendedProfileBlockSelection R0 selected)))).IsPartialMatching M) :
    ∃ decision : {e : G.E // e ∈ G.selectedBlockTinyEdges β} →
        Option (Fin (B * k)),
      (let choice := G.encodeExtendedProfileBlockSelection R0 selected
       let O := G.selectedDyadicOrdinaryBaseOptions
          (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
          (G.selectedBlockLargeResidual R0 omega rho choice)
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) M
       let hO := G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
          (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
          (G.selectedBlockLargeResidual R0 omega rho choice)
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) M hM
       G.IsFeasibleOn
         (G.ordinarySelectedEdges O ∪
           G.tinyDecisionColoredEdges (G.selectedBlockTinyEdges β) decision)
         (G.ordinaryTinyJointColor hn O hO
           (G.selectedBlockTinyEdges β) decision)) ∧
      ∀ v,
        G.tinyResidualIntegralLossLoad decision v ≤
          G.tinyResidualLossLoad (G.selectedBlockTinyEdges β)
            (fun e ↦ G.selectedBlockResidualOptionMass R0 rho omega
              (G.encodeExtendedProfileBlockSelection R0 selected) e.1) v +
            2 * β := by
  let choice := G.encodeExtendedProfileBlockSelection R0 selected
  let kappa := extendedProfileSmoothingKappa omega β q r
  let scale := extendedProfileCandidateCapacityScale rho s omega β q r
  let a := rho / kappa
  let delta := scale / ((B * k : ℕ) : ℝ) * deviation
  have hkappa : 0 < kappa :=
    extendedProfileSmoothingKappa_pos homega0 homega1
  have ha0 : 0 ≤ a := div_nonneg hrho.le hkappa.le
  have ha1 : a ≤ 1 := (div_le_one hkappa).2 hrhoKappa
  have htinyFractional : ∀ v c,
      G.selectedBlockNormalizedTinyReservoirLoad R0 rho omega choice (v, c) ≤
        a * G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c) + delta := by
    intro v c
    apply le_of_lt
    apply G.selectedBlockNormalizedTinyReservoirLoad_lt_of_capacityRow R0
      hn hs hq hr0 hleftParam rho omega homega0 homega1 hrho.le choice
    have hrow := htinyCapacity (v, c)
    convert hrow using 1 <;>
      simp [choice, a, delta, scale, kappa] <;> ring
  have herror : delta + 2 * β ≤ (1 - a) * r := by
    simpa [delta, scale, a, kappa] using hscalar
  simpa [choice] using
    (G.exists_selectedBlockTinyColorDecision_dyadic_joint_isFeasibleOn R0
      hn hs hq hr0 hr1 hleftParam rho omega homega0 homega1 hrho.le choice
      bucket M hM a delta ha0 ha1 htinyFractional herror)

end WeightedMultigraph

end

end WeightedEdgeColoring
