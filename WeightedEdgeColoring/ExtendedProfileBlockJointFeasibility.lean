import WeightedEdgeColoring.ExtendedProfileBlockReservoirCapacitySelection
import WeightedEdgeColoring.ExtendedProfileBlockAsymptoticBounds
import WeightedEdgeColoring.ExtendedProfileSelectedJointLoad

/-!
# From block selection to a common-palette feasible partial coloring

The reservoir-sensitive block selector gives, for a selected tiny row,

`normalized load < (rho / kappa) * reservoir + (scale / n) * deviation`.

This file records the exact substitution into the support-sensitive joint
load theorem.  It also gives one explicit family of profile parameters for
which the required scalar slack holds once the packing deviation is small
enough.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u w

variable (G : WeightedSimpleGraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]
variable {B k N : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- The direct composition bridge.  Its tiny-row hypothesis is exactly the
output of `exists_extendedProfileBlock_reservoir_capacity_and_variance`.
The only additional combinatorial input is a partial matching in the
quantized large-option system. -/
theorem exists_jointColoring_of_selectedBlock_reservoirCapacity
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (selected : ∀ v (b : Fin B), Fin k → G.ExtendedProfileState R0 v)
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
            extendedProfileBlockCombinedDeviation
              rho s omega β q r B k)
    (hrhoKappa : rho ≤ extendedProfileSmoothingKappa omega β q r)
    (hscalar :
      extendedProfileCandidateCapacityScale rho s omega β q r /
            ((B * k : ℕ) : ℝ) *
            extendedProfileBlockCombinedDeviation rho s omega β q r B k +
          2 * β ≤
        (1 - rho / extendedProfileSmoothingKappa omega β q r) * r)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ)
    (M : Finset (QuantizedCopy N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega
          (G.encodeExtendedProfileBlockSelection R0 selected))
        (G.selectedBlockResidualOptionMass R0 rho omega
          (G.encodeExtendedProfileBlockSelection R0 selected)))))
    (hM : ((G.largeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
      bucket extraCount).quantized N
        (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected))
          (G.selectedBlockResidualOptionMass R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected)))).IsPartialMatching M) :
    ∃ decision : {e : G.E // e ∈ G.selectedBlockTinyEdges β} →
        Option (Fin (B * k)),
      (∀ e c, decision e = some c →
        0 < G.selectedBlockNormalizedTinyOptionMass R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected) e.1 c ∧
          0 < G.extendedProfileReservoirSize R0 (G.fst e.1)
            (G.decodedExtendedProfileBlockSelection R0
              (G.encodeExtendedProfileBlockSelection R0 selected)
              (G.fst e.1) c) ∧
          0 < G.extendedProfileReservoirSize R0 (G.snd e.1)
            (G.decodedExtendedProfileBlockSelection R0
              (G.encodeExtendedProfileBlockSelection R0 selected)
              (G.snd e.1) c)) ∧
      (∀ e, decision e = none →
        0 < G.selectedBlockResidualOptionMass R0 rho omega
          (G.encodeExtendedProfileBlockSelection R0 selected) e.1) ∧
      (let choice := G.encodeExtendedProfileBlockSelection R0 selected
       let O := G.selectedOrdinaryBaseOptions
          (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
          (G.selectedBlockResidualOptionMass R0 rho omega choice) M
       let hO := G.selectedOrdinaryBaseOptions_isPartialMatching
          (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
          (G.selectedBlockResidualOptionMass R0 rho omega choice) M hM
       G.asMultigraph.IsFeasibleOn
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
  let deviation := extendedProfileBlockCombinedDeviation
    rho s omega β q r B k
  let a := rho / kappa
  let delta := scale / ((B * k : ℕ) : ℝ) * deviation
  have hkappa : 0 < kappa := by
    exact extendedProfileSmoothingKappa_pos
      (β := β) (q := q) (r := r) homega0 homega1
  have ha0 : 0 ≤ a := div_nonneg hrho.le hkappa.le
  have ha1 : a ≤ 1 := (div_le_one hkappa).2 hrhoKappa
  have htinyFractional : ∀ v c,
      G.selectedBlockNormalizedTinyReservoirLoad R0 rho omega choice (v, c) ≤
        a * G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c) + delta := by
    intro v c
    apply le_of_lt
    apply G.selectedBlockNormalizedTinyReservoirLoad_lt_of_capacityRow R0
      hn hs hq hr0 hleft rho omega homega0 homega1 hrho.le choice
    have hrow := htinyCapacity (v, c)
    convert hrow using 1 <;>
      simp [choice, a, delta, scale, deviation, kappa] <;> ring
  have herror : delta + 2 * β ≤ (1 - a) * r := by
    simpa [delta, scale, deviation, a, kappa] using hscalar
  simpa [choice] using
    (G.exists_selectedBlockTinyColorDecision_joint_isFeasibleOn R0
      hn hs hq hr0 hr1 hleft rho omega homega0 homega1 hrho.le choice
      bucket extraCount M hM a delta ha0 ha1 htinyFractional herror)

/-- A selected block family is ready for the graph-level composition if
every partial matching supplied by the large-option rounding step can be
completed by the support-preserving tiny decision. -/
def SelectedBlockJointCompletion
    (hn : 0 < B * k) (rho omega : ℝ)
    (selected : ∀ v (b : Fin B), Fin k → G.ExtendedProfileState R0 v)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ) : Prop :=
  ∀ (N : ℕ)
    (M : Finset (QuantizedCopy N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega
          (G.encodeExtendedProfileBlockSelection R0 selected))
        (G.selectedBlockResidualOptionMass R0 rho omega
          (G.encodeExtendedProfileBlockSelection R0 selected)))))
    (hM : ((G.largeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
      bucket extraCount).quantized N
        (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected))
          (G.selectedBlockResidualOptionMass R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected)))).IsPartialMatching M),
    ∃ decision : {e : G.E // e ∈ G.selectedBlockTinyEdges β} →
        Option (Fin (B * k)),
      (let choice := G.encodeExtendedProfileBlockSelection R0 selected
       let O := G.selectedOrdinaryBaseOptions
          (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
          (G.selectedBlockResidualOptionMass R0 rho omega choice) M
       let hO := G.selectedOrdinaryBaseOptions_isPartialMatching
          (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
          (G.selectedBlockResidualOptionMass R0 rho omega choice) M hM
       G.asMultigraph.IsFeasibleOn
         (G.ordinarySelectedEdges O ∪
           G.tinyDecisionColoredEdges (G.selectedBlockTinyEdges β) decision)
         (G.ordinaryTinyJointColor hn O hO
           (G.selectedBlockTinyEdges β) decision)) ∧
      ∀ v,
        G.tinyResidualIntegralLossLoad decision v ≤
          G.tinyResidualLossLoad (G.selectedBlockTinyEdges β)
            (fun e ↦ G.selectedBlockResidualOptionMass R0 rho omega
              (G.encodeExtendedProfileBlockSelection R0 selected) e.1) v +
            2 * β

/-- The raw reservoir-row output and the scalar slack inequality establish
the reusable continuation property. -/
theorem selectedBlockJointCompletion_of_reservoirCapacity
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (selected : ∀ v (b : Fin B), Fin k → G.ExtendedProfileState R0 v)
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
            extendedProfileBlockCombinedDeviation
              rho s omega β q r B k)
    (hrhoKappa : rho ≤ extendedProfileSmoothingKappa omega β q r)
    (hscalar :
      extendedProfileCandidateCapacityScale rho s omega β q r /
            ((B * k : ℕ) : ℝ) *
            extendedProfileBlockCombinedDeviation rho s omega β q r B k +
          2 * β ≤
        (1 - rho / extendedProfileSmoothingKappa omega β q r) * r)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ) :
    G.SelectedBlockJointCompletion R0 hn rho omega selected
      bucket extraCount := by
  intro N M hM
  obtain ⟨decision, hpositive, hresidual, hfeasible, hloss⟩ :=
    G.exists_jointColoring_of_selectedBlock_reservoirCapacity R0
      hB hk hn hs hq hr0 hr1 hleft omega homega0 homega1 rho hrho
      selected htinyCapacity hrhoKappa hscalar bucket extraCount M hM
  exact ⟨decision, hfeasible, hloss⟩

/-- Direct selector-to-feasibility wrapper.  It returns the selected-state
support, the large-row estimate needed by the still-separate large-option
matching theorem, the quadratic estimate needed by capture arithmetic, and
the tiny completion continuation. -/
theorem exists_extendedProfileBlock_selection_and_jointCompletion
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (hpack : G.LocallyPacksInto (B * k))
    (K : ℕ) (hK : 0 < K)
    (hRK : extendedProfileBlockCombinedMeanBound
      rho s omega β q r B k ≤ K)
    (dummyProb : ExtendedProfilePackedBlockState k β q r → ℝ)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1)
    (hrhoKappa : rho ≤ extendedProfileSmoothingKappa omega β q r)
    (hscalar :
      extendedProfileCandidateCapacityScale rho s omega β q r /
            ((B * k : ℕ) : ℝ) *
            extendedProfileBlockCombinedDeviation rho s omega β q r B k +
          2 * β ≤
        (1 - rho / extendedProfileSmoothingKappa omega β q r) * r)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ) :
    ∃ selected : ∀ v (b : Fin B), Fin k → G.ExtendedProfileState R0 v,
      (∀ v b,
        0 < G.extendedProfileBlockMass R0 omega v (selected v b)) ∧
      (∀ large : G.ExtendedProfileLargeRow
          (n := B * k) (β := β) (q := q) (r := r),
        G.selectedBlockCapacityLoad R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected)
            (Sum.inl large) /
              extendedProfileCandidateCapacityScale rho s omega β q r <
          ((B * k : ℕ) : ℝ) * rho /
            (extendedProfileCandidateCapacityScale rho s omega β q r *
              extendedProfileSmoothingKappa omega β q r) +
            extendedProfileBlockCombinedDeviation
              rho s omega β q r B k) ∧
      (∀ v,
        G.selectedTotalRawExtendedProfileBlockVariance R0 rho omega
            (G.encodeExtendedProfileBlockSelection R0 selected) v ≤
          extendedProfileBlockSelectedVarianceBound
            rho s omega β q r B k) ∧
      G.SelectedBlockJointCompletion R0 hn rho omega selected
        bucket extraCount := by
  obtain ⟨selected, hselected, hlarge, htiny, hvariance⟩ :=
    G.exists_extendedProfileBlock_reservoir_capacity_and_variance R0
      hB hk hn hs hspos hq hr0 hleft omega homega0 homega1 rho hrho
      hpack K hK hRK dummyProb hdummy0 hdummySum
  refine ⟨selected, hselected, hlarge, hvariance, ?_⟩
  exact G.selectedBlockJointCompletion_of_reservoirCapacity R0
    hB hk hn hs hq hr0 hr1 hleft omega homega0 homega1 rho hrho
    selected htiny hrhoKappa hscalar bucket extraCount

/-! ## One explicit parameter family -/

/-- Sampling factor used by the explicit scalar instantiation. -/
def jointProfileS (tau : ℝ) : ℝ := 1 - 2 * tau

/-- Large/tiny cutoff used by the explicit scalar instantiation. -/
def jointProfileBeta (tau : ℝ) : ℝ := tau ^ 2 / 16

/-- Slot-rounding unit used by the explicit scalar instantiation. -/
def jointProfileQ (tau : ℝ) : ℝ := tau

/-- Reservoir-rounding unit used by the explicit scalar instantiation. -/
def jointProfileR (tau : ℝ) : ℝ := tau

/-- The smoothing probability is small, so the retained fraction can tend to
one with `tau`. -/
def jointProfileOmega (tau : ℝ) : ℝ := tau

/-- The edge sampling rate tends to one with `tau`. -/
def jointProfileRho (tau : ℝ) : ℝ := 1 - 2 * tau

/-- All elementary parameter inequalities for the explicit family.  The
last clause is the quantitative point: the unused reservoir fraction is at
least `tau`. -/
theorem jointProfile_parameters
    {tau : ℝ} (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4) :
    0 < jointProfileS tau ∧
      0 < jointProfileBeta tau ∧
      0 < jointProfileQ tau ∧
      0 < jointProfileR tau ∧
      0 < jointProfileOmega tau ∧ jointProfileOmega tau ≤ 1 ∧
      0 ≤ 1 - jointProfileS tau *
        (1 + jointProfileQ tau + jointProfileR tau) ∧
      jointProfileR tau ≤ 1 ∧
      0 < jointProfileRho tau ∧
      jointProfileRho tau ≤
        extendedProfileSmoothingKappa (jointProfileOmega tau)
          (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) ∧
      tau ≤ 1 - jointProfileRho tau /
          extendedProfileSmoothingKappa (jointProfileOmega tau)
            (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) := by
  let stateCount : ℝ := extendedProfileStateBound
    (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau)
  let kappa := extendedProfileSmoothingKappa (jointProfileOmega tau)
    (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau)
  have hstateNat : 1 ≤ extendedProfileStateBound
      (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) := by
    unfold extendedProfileStateBound
    omega
  have hstate : (1 : ℝ) ≤ stateCount := by
    dsimp [stateCount]
    exact_mod_cast hstateNat
  have hstate0 : 0 < stateCount := zero_lt_one.trans_le hstate
  have htauDiv0 : 0 ≤ tau / stateCount :=
    div_nonneg htau0.le hstate0.le
  have htauDivLe : tau / stateCount ≤ tau := by
    apply (div_le_iff₀ hstate0).2
    have hmul := mul_nonneg htau0.le (sub_nonneg.mpr hstate)
    nlinarith
  have homega0 : 0 < jointProfileOmega tau := by
    simpa [jointProfileOmega] using htau0
  have homega1 : jointProfileOmega tau ≤ 1 := by
    unfold jointProfileOmega
    linarith
  have hkappa0 : 0 < kappa := by
    exact extendedProfileSmoothingKappa_pos homega0 homega1
  have hkappaFormula : kappa = 1 - tau + tau / stateCount := by
    simp [kappa, extendedProfileSmoothingKappa,
      extendedProfileSmoothingDelta, jointProfileOmega, stateCount]
  have hkappa1 : kappa ≤ 1 := by
    rw [hkappaFormula]
    linarith
  have hrhoKappa : jointProfileRho tau ≤ kappa := by
    rw [hkappaFormula]
    unfold jointProfileRho
    linarith
  have hgap : tau ≤ kappa - jointProfileRho tau := by
    rw [hkappaFormula]
    unfold jointProfileRho
    linarith
  have hfraction : tau ≤ 1 - jointProfileRho tau / kappa := by
    have hrewrite : 1 - jointProfileRho tau / kappa =
        (kappa - jointProfileRho tau) / kappa := by
      field_simp [hkappa0.ne']
      <;> ring
    rw [hrewrite]
    apply (le_div_iff₀ hkappa0).2
    calc
      tau * kappa ≤ tau * 1 :=
        mul_le_mul_of_nonneg_left hkappa1 htau0.le
      _ = tau := by ring
      _ ≤ kappa - jointProfileRho tau := hgap
  refine ⟨?_, ?_, htau0, htau0, homega0, homega1, ?_, ?_, ?_, ?_, ?_⟩
  · unfold jointProfileS
    linarith
  · unfold jointProfileBeta
    positivity
  · unfold jointProfileS jointProfileQ jointProfileR
    nlinarith [sq_nonneg tau]
  · unfold jointProfileR
    linarith
  · unfold jointProfileRho
    linarith
  · simpa [kappa] using hrhoKappa
  · simpa [kappa] using hfraction

/-- With the explicit parameters, a deviation at most
`tau^2 * n / (4*scale)` leaves enough reservoir slack. -/
theorem jointProfile_scalarSlack_of_deviation
    {tau D : ℝ} {n : ℕ}
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4) (hn : 0 < n)
    (hD : D ≤
      tau ^ 2 /
          (4 * extendedProfileCandidateCapacityScale
            (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
            (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau)) *
        n) :
    extendedProfileCandidateCapacityScale
          (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
          (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) /
        (n : ℝ) * D + 2 * jointProfileBeta tau ≤
      (1 - jointProfileRho tau /
          extendedProfileSmoothingKappa (jointProfileOmega tau)
            (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau)) *
        jointProfileR tau := by
  let scale := extendedProfileCandidateCapacityScale
    (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
    (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau)
  rcases jointProfile_parameters htau0 htau1 with
    ⟨hs, hβ, hq, hr, homega0, homega1, hleft, hr1,
      hrho, hrhoKappa, hfraction⟩
  have hscale : 0 < scale := by
    exact extendedProfileCandidateCapacityScale_pos hrho hs homega0
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hdelta : scale / (n : ℝ) * D ≤ tau ^ 2 / 4 := by
    calc
      scale / (n : ℝ) * D ≤
          scale / (n : ℝ) * (tau ^ 2 / (4 * scale) * n) :=
        mul_le_mul_of_nonneg_left hD (div_nonneg hscale.le hnreal.le)
      _ = tau ^ 2 / 4 := by
        field_simp [hscale.ne', hnreal.ne']
        <;> ring
  have hreservoirSlack : tau ^ 2 ≤
      (1 - jointProfileRho tau /
          extendedProfileSmoothingKappa (jointProfileOmega tau)
            (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau)) *
        jointProfileR tau := by
    unfold jointProfileR
    simpa [pow_two] using
      (mul_le_mul_of_nonneg_right hfraction htau0.le)
  change scale / (n : ℝ) * D + 2 * jointProfileBeta tau ≤ _
  have hbeta : 2 * jointProfileBeta tau = tau ^ 2 / 8 := by
    unfold jointProfileBeta
    ring
  rw [hbeta]
  nlinarith [sq_nonneg tau]

/-- The explicit scalar slack is eventually available uniformly in the
number of blocks, by sublinearity of the combined selector deviation. -/
theorem jointProfile_scalarSlack_eventually
    {k : ℕ} {tau : ℝ} (hk : 0 < k)
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4) :
    ∃ N : ℕ, ∀ B : ℕ, N ≤ B * k →
      extendedProfileCandidateCapacityScale
            (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
            (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) /
          ((B * k : ℕ) : ℝ) *
          extendedProfileBlockCombinedDeviation
            (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
            (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau)
            B k +
          2 * jointProfileBeta tau ≤
        (1 - jointProfileRho tau /
            extendedProfileSmoothingKappa (jointProfileOmega tau)
              (jointProfileBeta tau) (jointProfileQ tau)
                (jointProfileR tau)) * jointProfileR tau := by
  let scale := extendedProfileCandidateCapacityScale
    (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
    (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau)
  rcases jointProfile_parameters htau0 htau1 with
    ⟨hs, hβ, hq, hr, homega0, homega1, hleft, hr1,
      hrho, hrhoKappa, hfraction⟩
  have hscale : 0 < scale := by
    exact extendedProfileCandidateCapacityScale_pos hrho hs homega0
  have hepsilon : 0 < tau ^ 2 / (4 * scale) := by positivity
  obtain ⟨N0, hN0⟩ :=
    extendedProfileBlockCombinedDeviation_sublinear
      (k := k) (rho := jointProfileRho tau) (s := jointProfileS tau)
      (omega := jointProfileOmega tau) (β := jointProfileBeta tau)
      (q := jointProfileQ tau) (r := jointProfileR tau)
      hβ hrho.le hs.le homega0 homega1
      (tau ^ 2 / (4 * scale)) hepsilon
  refine ⟨max N0 1, ?_⟩
  intro B hB
  have hN0B : N0 ≤ B * k := (le_max_left N0 1).trans hB
  have hn : 0 < B * k := Nat.zero_lt_of_lt
    ((le_max_right N0 1).trans hB)
  apply jointProfile_scalarSlack_of_deviation htau0 htau1 hn
  simpa [scale] using hN0 B hN0B

end WeightedSimpleGraph

end

end WeightedEdgeColoring
