import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileLargeMatchingDecoder

/-!
# Initial large-option bounds for color-dependent selected profiles

This ports the deterministic input estimates of the existing selected-profile
endpoint iteration to a proposal whose coordinates have independently selected
profile states.  The ambient star bound is the external parameter `n`; no local
unit-bin packing hypothesis is used.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k n N reserve C S0 L mult : ℕ}
variable {s β q r proposalGamma extraGamma rho omega C0 scale deviation
    lambda ordinaryRate : ℝ}
variable {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

theorem boundedClassResidual_selectedColorDependentLargeResidual_mul_beta_le_starWeight
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (selected : G.ColorDependentSelectedStates proposal R)
    (bucket : G.E → Bool × Fin (L + 1)) (v : G.V)
    (h : Bool × Fin (L + 1)) :
    G.boundedClassResidual bucket
        (G.selectedColorDependentLargeResidual proposal R rho omega selected)
        v h * β ≤ G.starWeight v := by
  have hres1 := G.selectedColorDependentLargeResidual_le_one proposal R
    hs hq hr0 hleft homega0 homega1 hrho selected
  unfold boundedClassResidual
  rw [Finset.sum_mul]
  calc
    (∑ e,
      ((if (G.fst e, bucket e) = (v, h) then
          G.selectedColorDependentLargeResidual proposal R rho omega selected e
        else 0) +
       (if (G.snd e, bucket e) = (v, h) then
          G.selectedColorDependentLargeResidual proposal R rho omega selected e
        else 0)) * β) ≤
      ∑ e, if G.Inc v e then G.weight e else 0 := by
        apply Finset.sum_le_sum
        intro e _
        have hedge :
            G.selectedColorDependentLargeResidual proposal R rho omega selected e * β ≤
              G.weight e := by
          by_cases he : β ≤ G.weight e
          · have htoBeta :
                G.selectedColorDependentLargeResidual proposal R rho omega selected e * β ≤
                  β := by
              simpa only [one_mul] using
                mul_le_mul_of_nonneg_right (hres1 e) hβ.le
            exact htoBeta.trans he
          · simp [selectedColorDependentLargeResidual, he, G.weight_nonneg]
        by_cases hf : (G.fst e, bucket e) = (v, h)
        · have hfv : G.fst e = v := congrArg Prod.fst hf
          have hinc : G.Inc v e := Or.inl hfv
          have hsnd : (G.snd e, bucket e) ≠ (v, h) := by
            intro heq
            exact G.noLoop e (hfv.trans (congrArg Prod.fst heq).symm)
          rw [if_pos hf, if_neg hsnd, add_zero, if_pos hinc]
          exact hedge
        · by_cases hsnd : (G.snd e, bucket e) = (v, h)
          · have hsv : G.snd e = v := congrArg Prod.fst hsnd
            have hinc : G.Inc v e := Or.inr hsv
            rw [if_neg hf, if_pos hsnd, zero_add, if_pos hinc]
            exact hedge
          · by_cases hinc : G.Inc v e
            · simp [hf, hsnd, hinc, G.weight_nonneg]
            · simp [hf, hsnd, hinc]
    _ = G.starWeight v := by
      unfold starWeight
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype
        ((Finset.univ : Finset G.E).filter (G.Inc v))
        (by intro e; simp) G.weight

/-- The local extra support count is controlled by the ambient star bound,
not by a local packing hypothesis. -/
theorem colorDependent_graphDyadicLargeResidual_supportCount_le
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (selected : G.ColorDependentSelectedStates proposal R)
    (hstar : ∀ v, G.starWeight v ≤ n)
    (hreserve : 0 < reserve) (hextraGamma1 : extraGamma < 1)
    (E : ℕ)
    (hE : 2 * (((n : ℕ) : ℝ) / β / (1 - extraGamma) +
      1 + reserve) ≤ E) (e : G.E) :
    DivisibleLocalExtraChoice.supportCount G.fst G.snd
      (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L)
      (G.boundedDyadicExtraSlotCount
        (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L)
        (G.selectedColorDependentLargeResidual proposal R rho omega selected)
        extraGamma reserve) e ≤ E := by
  let bucket : G.E → Bool × Fin (L + 1) := G.colorDependentRetainedDyadicBucket proposal proposalGamma β L
  have count_le (v : G.V) (h : Bool × Fin (L + 1)) :
      G.boundedDyadicExtraSlotCount bucket
          (G.selectedColorDependentLargeResidual proposal R rho omega selected)
          extraGamma reserve v h ≤ E := by
    have hc := G.boundedDyadicExtraSlotCount_cast_le bucket
      (G.selectedColorDependentLargeResidual proposal R rho omega selected)
      (G.selectedColorDependentLargeResidual_nonneg proposal R rho omega selected)
      extraGamma hreserve hextraGamma1 v h
    have hmul :=
      G.boundedClassResidual_selectedColorDependentLargeResidual_mul_beta_le_starWeight
        proposal R hs hq hr0 hleft homega0 homega1 hrho selected bucket v h
    have hclass : G.boundedClassResidual bucket
        (G.selectedColorDependentLargeResidual proposal R rho omega selected) v h ≤
        (n : ℝ) / β := by
      apply (le_div_iff₀ hβ).2
      exact hmul.trans (hstar v)
    have hgap : 0 < 1 - extraGamma := sub_pos.mpr hextraGamma1
    have hdiv := div_le_div_of_nonneg_right hclass hgap.le
    have hinside :
        G.boundedClassResidual bucket
              (G.selectedColorDependentLargeResidual proposal R rho omega selected)
              v h / (1 - extraGamma) + 1 + reserve ≤
          (n : ℝ) / β / (1 - extraGamma) + 1 + reserve := by
      nlinarith [hdiv]
    have hscaled :
        2 * (G.boundedClassResidual bucket
              (G.selectedColorDependentLargeResidual proposal R rho omega selected)
              v h / (1 - extraGamma) + 1 + reserve) ≤
          2 * ((n : ℝ) / β / (1 - extraGamma) + 1 + reserve) :=
      mul_le_mul_of_nonneg_left hinside (by norm_num)
    have hreal :
        (G.boundedDyadicExtraSlotCount bucket
          (G.selectedColorDependentLargeResidual proposal R rho omega selected)
          extraGamma reserve v h : ℝ) ≤ E :=
      hc.trans (hscaled.trans hE)
    exact_mod_cast hreal
  unfold DivisibleLocalExtraChoice.supportCount
  exact max_le (count_le _ _) (count_le _ _)

theorem colorDependentSelectedDyadicLarge_slots_card_eq_two
    (selected : G.ColorDependentSelectedStates proposal R)
    (o : (G.colorDependentSelectedDyadicSystem
      (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
      proposal R proposalGamma extraGamma rho omega selected).ActiveJobOption
        (G.largeEdgeJobs β)) :
    (((G.largeEdgeJobSystem
      (G.colorDependentSelectedDyadicSystem
        (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
        proposal R proposalGamma extraGamma rho omega selected) β).slots o).card) = 2 := by
  exact G.quantized_dyadicLargeEdgeOptionSystem_slots_card_eq_two
    (explicitLargeSlotBound β q r)
    (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L) extraGamma reserve
    (G.selectedColorDependentLargeResidual proposal R rho omega selected)
    (G.flattenedSelectedColorDependentNormalizedLarge
      proposal R rho omega selected) N o.1

theorem colorDependentSelectedDyadicLarge_jobDegree_lower
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (selected : G.ColorDependentSelectedStates proposal R)
    (hCN : C ≤ N)
    (hchoices : ∀ e,
      (B * k) * explicitLargeSlotBound β q r *
          explicitLargeSlotBound β q r +
        DivisibleLocalExtraChoice.supportCount G.fst G.snd
          (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L)
          (G.boundedDyadicExtraSlotCount
            (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L)
            (G.selectedColorDependentLargeResidual proposal R rho omega selected)
            extraGamma reserve) e ≤ C)
    (e : (G.largeEdgeRestriction β).E) :
    N - C ≤
      ((G.largeEdgeJobSystem
        (G.colorDependentSelectedDyadicSystem
          (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
          proposal R proposalGamma extraGamma rho omega selected) β).fiber e).card := by
  rw [RankThreeOptionSystem.inducedOnJobs_fiber_card]
  let bucket : G.E → Bool × Fin (L + 1) := G.colorDependentRetainedDyadicBucket proposal proposalGamma β L
  let residual := G.selectedColorDependentLargeResidual
    proposal R rho omega selected
  let x := G.flattenedSelectedColorDependentNormalizedLarge
    proposal R rho omega selected
  have hbase := G.dyadicLargeEdge_quantizedJobDegree_lower
    (explicitLargeSlotBound β q r) bucket extraGamma reserve residual x N e.1
  have hmass := G.sum_flattenedSelectedColorDependentNormalizedLarge_add_residual
    proposal R hs hq hr0 hleft homega0 homega1 hrho selected e.1
      (G.mem_largeEdgeJobs.mp e.2)
  rw [hmass, mul_one] at hbase
  rw [← RankThreeOptionSystem.quantized_fiber_card] at hbase
  have hchoiceR :
      (((B * k) * explicitLargeSlotBound β q r *
          explicitLargeSlotBound β q r +
        DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
          (G.boundedDyadicExtraSlotCount bucket residual extraGamma reserve) e.1 : ℕ) : ℝ) ≤ C := by
    exact_mod_cast hchoices e.1
  have hbase' :
      (N : ℝ) -
          (((B * k) * explicitLargeSlotBound β q r *
            explicitLargeSlotBound β q r +
          DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
            (G.boundedDyadicExtraSlotCount bucket residual extraGamma reserve)
            e.1 : ℕ) : ℝ) ≤
        ((G.colorDependentSelectedDyadicSystem
          (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
          proposal R proposalGamma extraGamma rho omega selected).fiber e.1).card := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul] using hbase
  have hreal : ((N - C : ℕ) : ℝ) ≤
      ((G.colorDependentSelectedDyadicSystem
        (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
        proposal R proposalGamma extraGamma rho omega selected).fiber e.1).card := by
    rw [Nat.cast_sub hCN]
    exact (sub_le_sub_left hchoiceR N).trans hbase'
  exact_mod_cast hreal

theorem colorDependentSelectedDyadicLarge_slotDegree_le
    (hn : 0 < n) (hN : 0 < N)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (hscale : 0 < scale)
    (selected : G.ColorDependentSelectedStates proposal R)
    (hrow : ∀ v c slot,
      FiniteCategoricalSelection.rowLoad
        (G.colorDependentBlockCandidateUse proposal R n scale rho omega)
        (G.selectedColorDependentLargeCapacityRow proposal R selected v c slot)
        (G.encodedColorDependentSelectedBlock proposal R selected) <
      (n : ℝ) * (rho / (1 - omega)) / scale + deviation)
    (hordinaryRate : rho / (1 - omega) + scale / n * deviation ≤ ordinaryRate)
    (hordinaryCap : (N : ℝ) * ordinaryRate ≤ S0)
    (hreserve : 0 < reserve) (hextraGamma0 : 0 ≤ extraGamma)
    (hextraGamma1 : extraGamma < 1)
    (hextraCap : (1 - extraGamma) * N ≤ S0)
    (slot : G.DyadicLargeEdgeSlot
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
      (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L) extraGamma reserve
      (G.selectedColorDependentLargeResidual proposal R rho omega selected)) :
    (G.largeEdgeJobSystem
      (G.colorDependentSelectedDyadicSystem
        (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
        proposal R proposalGamma extraGamma rho omega selected) β).slotDegree slot ≤ S0 := by
  let bucket : G.E → Bool × Fin (L + 1) := G.colorDependentRetainedDyadicBucket proposal proposalGamma β L
  let residual := G.selectedColorDependentLargeResidual
    proposal R rho omega selected
  let x := G.flattenedSelectedColorDependentNormalizedLarge
    proposal R rho omega selected
  apply (G.largeEdgeJobSystem_slotDegree_le
    (G.colorDependentSelectedDyadicSystem
      (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
      proposal R proposalGamma extraGamma rho omega selected) β slot).trans
  cases slot with
  | inl slot =>
      have hdeg := G.colorDependent_quantizedOrdinarySlotDegree_lt
        proposal R hn hN hs hq hr0 hleft homega0 homega1 hrho
        scale deviation hscale selected bucket extraGamma reserve residual
        hrow slot
      have hreal :
          (((G.colorDependentSelectedDyadicSystem
            (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
            proposal R proposalGamma extraGamma rho omega selected).slotDegree
              (Sum.inl slot) : ℕ) : ℝ) ≤ S0 :=
        hdeg.le.trans ((mul_le_mul_of_nonneg_left hordinaryRate
          (Nat.cast_nonneg N)).trans hordinaryCap)
      exact_mod_cast hreal
  | inr slot =>
      have hres0 := G.selectedColorDependentLargeResidual_nonneg
        proposal R rho omega selected
      have hdeg := G.dyadicLargeEdge_quantized_slotDegree_inr_le
        (explicitLargeSlotBound β q r) bucket extraGamma reserve residual x
        hres0 hreserve hextraGamma0 hextraGamma1 N slot
      exact_mod_cast hdeg.trans hextraCap

theorem colorDependentSelectedDyadicLarge_jobSlotCodegree_le
    (hn : 0 < n)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (hC0 : 0 ≤ C0) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hreserve : 0 < reserve)
    (hordinary : (N : ℝ) *
      (2 * colorDependentCandidateCapacityScale rho s omega β q r C0 / n) ≤ lambda)
    (hextra : (N : ℝ) / reserve ≤ lambda)
    (selected : G.ColorDependentSelectedStates proposal R)
    (e : (G.largeEdgeRestriction β).E)
    (slot : G.DyadicLargeEdgeSlot
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
      (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L) extraGamma reserve
      (G.selectedColorDependentLargeResidual proposal R rho omega selected)) :
    (G.largeEdgeJobSystem
      (G.colorDependentSelectedDyadicSystem
        (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
        proposal R proposalGamma extraGamma rho omega selected) β).jobSlotCodegree e slot ≤ lambda := by
  let bucket : G.E → Bool × Fin (L + 1) := G.colorDependentRetainedDyadicBucket proposal proposalGamma β L
  let residual := G.selectedColorDependentLargeResidual
    proposal R rho omega selected
  let x := G.flattenedSelectedColorDependentNormalizedLarge
    proposal R rho omega selected
  rw [G.largeEdgeJobSystem_jobSlotCodegree
    (G.colorDependentSelectedDyadicSystem
      (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
      proposal R proposalGamma extraGamma rho omega selected) β e slot]
  cases slot with
  | inl slot =>
      have hdeg := G.colorDependent_quantizedOrdinaryJobSlotCodegree_le
        (N := N) proposal R hn hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
        hproposal0 hproposal selected bucket extraGamma reserve residual
        e.1 slot
      exact_mod_cast hdeg.trans hordinary
  | inr slot =>
      have hres0 := G.selectedColorDependentLargeResidual_nonneg
        proposal R rho omega selected
      have hres1 := G.selectedColorDependentLargeResidual_le_one proposal R
        hs hq hr0 hleft homega0 homega1 hrho selected
      have hdeg := G.dyadicLargeEdge_quantized_jobSlotCodegree_inr_le
        (explicitLargeSlotBound β q r) bucket extraGamma reserve residual x
        hres0 hres1 hreserve N e.1 slot
      exact_mod_cast hdeg.trans hextra

theorem colorDependentSelectedDyadicLarge_slotPairCodegree_le
    (hmult : G.PairMultiplicityAtMost mult)
    (hn : 0 < n)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (hC0 : 0 ≤ C0) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hreserve : 0 < reserve)
    (hordinary : 2 * colorDependentCandidateCapacityScale
      rho s omega β q r C0 / n ≤ 1 / (reserve : ℝ))
    (hcap : (mult : ℝ) * (N : ℝ) / reserve ≤ lambda)
    (selected : G.ColorDependentSelectedStates proposal R)
    (left right : G.DyadicLargeEdgeSlot
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
      (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L) extraGamma reserve
      (G.selectedColorDependentLargeResidual proposal R rho omega selected))
    (hne : left ≠ right) :
    (G.largeEdgeJobSystem
      (G.colorDependentSelectedDyadicSystem
        (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
        proposal R proposalGamma extraGamma rho omega selected) β).slotPairCodegree left right ≤ lambda := by
  let bucket : G.E → Bool × Fin (L + 1) := G.colorDependentRetainedDyadicBucket proposal proposalGamma β L
  let residual := G.selectedColorDependentLargeResidual
    proposal R rho omega selected
  let x := G.flattenedSelectedColorDependentNormalizedLarge
    proposal R rho omega selected
  have hrestrict := G.largeEdgeJobSystem_slotPairCodegree_le
    (G.colorDependentSelectedDyadicSystem
      (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
      proposal R proposalGamma extraGamma rho omega selected) β left right
  have hrestrictR :
      ((G.largeEdgeJobSystem
        (G.colorDependentSelectedDyadicSystem
          (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
          proposal R proposalGamma extraGamma rho omega selected) β).slotPairCodegree
            left right : ℝ) ≤
        ((G.colorDependentSelectedDyadicSystem
          (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
          proposal R proposalGamma extraGamma rho omega selected).slotPairCodegree
            left right : ℝ) := by
    exact_mod_cast hrestrict
  have hx0 := G.flattenedSelectedColorDependentNormalizedLarge_nonneg
    proposal R hs hq hr0 hleft homega0 homega1 hrho selected
  have hx : ∀ e c i j,
      G.flattenedSelectedColorDependentNormalizedLarge
        proposal R rho omega selected e c i j ≤ 1 / (reserve : ℝ) := by
    intro e c i j
    exact (G.flattenedSelectedColorDependentNormalizedLarge_le proposal R
      hn hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
      hproposal0 hproposal selected e c i j).trans hordinary
  have hres0 := G.selectedColorDependentLargeResidual_nonneg
    proposal R rho omega selected
  have hres1 := G.selectedColorDependentLargeResidual_le_one proposal R
    hs hq hr0 hleft homega0 homega1 hrho selected
  have hdeg := G.dyadicLargeEdge_quantized_slotPairCodegree_le
    (explicitLargeSlotBound β q r) bucket extraGamma reserve residual hmult x
    hx0 hx hres0 hres1 hreserve N hne
  exact hrestrictR.trans (hdeg.trans hcap)

end WeightedMultigraph

end

end WeightedEdgeColoring
