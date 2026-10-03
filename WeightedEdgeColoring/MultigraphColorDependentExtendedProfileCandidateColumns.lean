import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileCandidateRows

/-!
# Polynomial columns for color-dependent candidate rows

For one fixed color, a source state sees only rows centered at the opposite
endpoint of an incident edge.  Simplicity gives a single edge for each
source--center pair.  Large edges are counted using the threshold `beta`,
and tiny rows retain the edge weight.  The resulting per-color column is
linear in the local packing parameter; the whole dependent word adds only
the number of colors.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})
variable {Color : Type w} [Fintype Color] [DecidableEq Color]
variable {n : ℕ} {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}

section CandidateRowSums

variable {proposal : G.E → Color → ℝ}
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

private theorem sum_colorDependentLargeCandidateRows
    (c : Color) (f : G.ColorDependentLargeCandidateRow R c → ℝ) :
    (∑ row, f row) =
      ∑ v, ∑ z : G.ColorDependentExtendedProfileState R v c,
        ∑ i, f { center := v, candidate := z, slot := i } := by
  calc
    (∑ row, f row) =
        ∑ x : Σ v : G.V,
          G.ColorDependentExtendedProfileState R v c ×
            Fin (explicitLargeSlotBound β q r),
          f ((G.colorDependentLargeCandidateRowEquiv R c).symm x) := by
      exact Fintype.sum_equiv
        (G.colorDependentLargeCandidateRowEquiv R c) _ _ (fun _ ↦ rfl)
    _ = ∑ v, ∑ z : G.ColorDependentExtendedProfileState R v c,
        ∑ i, f { center := v, candidate := z, slot := i } := by
      simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
      rfl

private theorem sum_colorDependentTinyCandidateRows
    (c : Color) (f : G.ColorDependentTinyCandidateRow R c → ℝ) :
    (∑ row, f row) =
      ∑ v, ∑ z : G.ColorDependentExtendedProfileState R v c,
        f { center := v, candidate := z } := by
  calc
    (∑ row, f row) =
        ∑ x : Σ v : G.V,
          G.ColorDependentExtendedProfileState R v c,
          f ((G.colorDependentTinyCandidateRowEquiv R c).symm x) := by
      exact Fintype.sum_equiv
        (G.colorDependentTinyCandidateRowEquiv R c) _ _ (fun _ ↦ rfl)
    _ = ∑ v, ∑ z : G.ColorDependentExtendedProfileState R v c,
        f { center := v, candidate := z } := by
      simp only [Fintype.sum_sigma]
      rfl

end CandidateRowSums

def colorDependentCandidatePerColorColumnBound
  (n : ℕ) (β q r : ℝ) : ℝ :=
  (n : ℝ) * extendedProfileStateBound β q r *
    (explicitLargeSlotBound β q r / β + 1)

section ProposalDependentColumns

variable (proposal : G.E → Color → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

private theorem sum_scaledColorDependentLargeRows_edge_le
    (hn : 0 < n) (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c)
    (e : G.E) :
    (∑ row : G.ColorDependentLargeCandidateRow R c,
      (n : ℝ) * G.colorDependentLargeCandidateEdgeUse proposal R rho omega
        source c sourceState e row /
          colorDependentCandidateCapacityScale rho s omega β q r C0) ≤
      if G.Inc source e ∧ β ≤ G.weight e then
        extendedProfileStateBound β q r * explicitLargeSlotBound β q r
      else 0 := by
  classical
  let scale := colorDependentCandidateCapacityScale rho s omega β q r C0
  have hscale : 0 < scale := colorDependentCandidateCapacityScale_pos
    (C0 := C0) hrho hs hC0 homega0
  rw [G.sum_colorDependentLargeCandidateRows R c]
  by_cases hsourceFst : source = G.fst e
  · subst source
    have hsourceSnd : G.snd e ≠ G.fst e := (G.noLoop e).symm
    by_cases hlarge : β ≤ G.weight e
    · simp only [WeightedMultigraph.Inc, eq_self, true_or, true_and,
        hlarge, if_true]
      have hterm : ∀ (z : G.ColorDependentExtendedProfileState R (G.snd e) c)
          (i : Fin (explicitLargeSlotBound β q r)),
          (n : ℝ) * G.colorDependentLargeCandidateEdgeUse proposal R rho omega
              (G.fst e) c sourceState e
                { center := G.snd e, candidate := z, slot := i } / scale ≤ 1 := by
        intro z i
        apply (div_le_one hscale).2
        exact G.n_mul_colorDependentLargeCandidateEdgeUse_le_scale proposal R
          hn hs.le hq hr0 hleft homega0 homega1 hrho.le hC0.le hproposal
          (G.fst e) c sourceState e _
      calc
        (∑ v, ∑ z : G.ColorDependentExtendedProfileState R v c, ∑ i,
          (n : ℝ) * G.colorDependentLargeCandidateEdgeUse proposal R rho omega
            (G.fst e) c sourceState e
              { center := v, candidate := z, slot := i } / scale) =
            ∑ z : G.ColorDependentExtendedProfileState R (G.snd e) c, ∑ i,
              (n : ℝ) * G.colorDependentLargeCandidateEdgeUse proposal R rho omega
                (G.fst e) c sourceState e
                  { center := G.snd e, candidate := z, slot := i } / scale := by
          apply Fintype.sum_eq_single (G.snd e)
          intro v hv
          simp [colorDependentLargeCandidateEdgeUse, hv, hsourceSnd,
            G.noLoop e]
        _ ≤ ∑ _z : G.ColorDependentExtendedProfileState R (G.snd e) c,
              ∑ _i : Fin (explicitLargeSlotBound β q r), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro z _hz
          exact Finset.sum_le_sum fun i _hi ↦ hterm z i
        _ = (Fintype.card (G.ColorDependentExtendedProfileState R (G.snd e) c) : ℝ) *
              (explicitLargeSlotBound β q r : ℝ) := by simp
        _ ≤ (extendedProfileStateBound β q r : ℝ) *
              (explicitLargeSlotBound β q r : ℝ) := by
          gcongr
          exact_mod_cast G.colorDependentExtendedProfileState_card_le R
            (G.snd e) c
        _ = ((extendedProfileStateBound β q r *
              explicitLargeSlotBound β q r : ℕ) : ℝ) := by
          rw [Nat.cast_mul]
    · have hy : G.colorDependentExtendedProfileLargeEdgeColorMass
          (s := s) (β := β) proposal e c = 0 := by
        simp [colorDependentExtendedProfileLargeEdgeColorMass, hlarge]
      simp [WeightedMultigraph.Inc, hsourceSnd, hlarge,
        colorDependentLargeCandidateEdgeUse,
        colorDependentExtendedProfileLargeProductMass, pairedOption, hy]
  · by_cases hsourceSnd : source = G.snd e
    · subst source
      have hsourceFst : G.fst e ≠ G.snd e := G.noLoop e
      by_cases hlarge : β ≤ G.weight e
      · simp only [WeightedMultigraph.Inc, hsourceFst, eq_self,
          false_or, true_and, hlarge, if_true]
        have hterm : ∀ (z : G.ColorDependentExtendedProfileState R (G.fst e) c)
            (i : Fin (explicitLargeSlotBound β q r)),
            (n : ℝ) * G.colorDependentLargeCandidateEdgeUse proposal R rho omega
                (G.snd e) c sourceState e
                  { center := G.fst e, candidate := z, slot := i } / scale ≤ 1 := by
          intro z i
          apply (div_le_one hscale).2
          exact G.n_mul_colorDependentLargeCandidateEdgeUse_le_scale proposal R
            hn hs.le hq hr0 hleft homega0 homega1 hrho.le hC0.le hproposal
            (G.snd e) c sourceState e _
        calc
          (∑ v, ∑ z : G.ColorDependentExtendedProfileState R v c, ∑ i,
            (n : ℝ) * G.colorDependentLargeCandidateEdgeUse proposal R rho omega
              (G.snd e) c sourceState e
                { center := v, candidate := z, slot := i } / scale) =
              ∑ z : G.ColorDependentExtendedProfileState R (G.fst e) c, ∑ i,
                (n : ℝ) * G.colorDependentLargeCandidateEdgeUse proposal R rho omega
                  (G.snd e) c sourceState e
                    { center := G.fst e, candidate := z, slot := i } / scale := by
            apply Fintype.sum_eq_single (G.fst e)
            intro v hv
            simp [colorDependentLargeCandidateEdgeUse, hv, hsourceFst,
              (G.noLoop e).symm]
          _ ≤ ∑ _z : G.ColorDependentExtendedProfileState R (G.fst e) c,
                ∑ _i : Fin (explicitLargeSlotBound β q r), (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro z _hz
            exact Finset.sum_le_sum fun i _hi ↦ hterm z i
          _ = (Fintype.card (G.ColorDependentExtendedProfileState R (G.fst e) c) : ℝ) *
                (explicitLargeSlotBound β q r : ℝ) := by simp
          _ ≤ (extendedProfileStateBound β q r : ℝ) *
                (explicitLargeSlotBound β q r : ℝ) := by
            gcongr
            exact_mod_cast G.colorDependentExtendedProfileState_card_le R
              (G.fst e) c
          _ = ((extendedProfileStateBound β q r *
                explicitLargeSlotBound β q r : ℕ) : ℝ) := by
            rw [Nat.cast_mul]
      · have hy : G.colorDependentExtendedProfileLargeEdgeColorMass
            (s := s) (β := β) proposal e c = 0 := by
          simp [colorDependentExtendedProfileLargeEdgeColorMass, hlarge]
        simp [WeightedMultigraph.Inc, hsourceFst, hlarge,
          colorDependentLargeCandidateEdgeUse,
          colorDependentExtendedProfileLargeProductMass, pairedOption, hy]
    · have hsourceFst' : G.fst e ≠ source := Ne.symm hsourceFst
      have hsourceSnd' : G.snd e ≠ source := Ne.symm hsourceSnd
      simp [WeightedMultigraph.Inc, hsourceFst, hsourceSnd,
        hsourceFst', hsourceSnd', colorDependentLargeCandidateEdgeUse]

private theorem sum_scaledColorDependentTinyRows_edge_le
    (hn : 0 < n) (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c)
    (e : G.E) :
    (∑ row : G.ColorDependentTinyCandidateRow R c,
      (n : ℝ) * G.colorDependentTinyCandidateEdgeUse proposal R rho omega
        source c sourceState e row /
          colorDependentCandidateCapacityScale rho s omega β q r C0) ≤
      if G.Inc source e then
        extendedProfileStateBound β q r * G.weight e else 0 := by
  classical
  let scale := colorDependentCandidateCapacityScale rho s omega β q r C0
  have hscale : 0 < scale := colorDependentCandidateCapacityScale_pos
    (C0 := C0) hrho hs hC0 homega0
  rw [G.sum_colorDependentTinyCandidateRows R c]
  by_cases hsourceFst : source = G.fst e
  · subst source
    have hsourceSnd : G.snd e ≠ G.fst e := (G.noLoop e).symm
    simp only [WeightedMultigraph.Inc, eq_self, true_or, if_true]
    have hterm : ∀ z : G.ColorDependentExtendedProfileState R (G.snd e) c,
        (n : ℝ) * G.colorDependentTinyCandidateEdgeUse proposal R rho omega
            (G.fst e) c sourceState e { center := G.snd e, candidate := z } /
            scale ≤ G.weight e := by
      intro z
      apply (div_le_iff₀ hscale).2
      simpa [mul_comm] using
        G.n_mul_colorDependentTinyCandidateEdgeUse_le_weight_mul_scale
          proposal R hn hs.le hq hr0 hleft homega0 homega1 hrho.le hC0.le
            hproposal (G.fst e) c sourceState e _
    calc
      (∑ v, ∑ z : G.ColorDependentExtendedProfileState R v c,
        (n : ℝ) * G.colorDependentTinyCandidateEdgeUse proposal R rho omega
          (G.fst e) c sourceState e { center := v, candidate := z } / scale) =
          ∑ z : G.ColorDependentExtendedProfileState R (G.snd e) c,
            (n : ℝ) * G.colorDependentTinyCandidateEdgeUse proposal R rho omega
              (G.fst e) c sourceState e
                { center := G.snd e, candidate := z } / scale := by
        apply Fintype.sum_eq_single (G.snd e)
        intro v hv
        simp [colorDependentTinyCandidateEdgeUse, hv, hsourceSnd,
          G.noLoop e]
      _ ≤ ∑ _z : G.ColorDependentExtendedProfileState R (G.snd e) c,
          G.weight e := Finset.sum_le_sum fun z _hz ↦ hterm z
      _ = Fintype.card (G.ColorDependentExtendedProfileState R (G.snd e) c) *
          G.weight e := by simp
      _ ≤ extendedProfileStateBound β q r * G.weight e := by
        have hcardR :
            (Fintype.card
              (G.ColorDependentExtendedProfileState R (G.snd e) c) : ℝ) ≤
              extendedProfileStateBound β q r := by
          exact_mod_cast G.colorDependentExtendedProfileState_card_le R
            (G.snd e) c
        exact mul_le_mul_of_nonneg_right hcardR (G.weight_nonneg e)
  · by_cases hsourceSnd : source = G.snd e
    · subst source
      have hsourceFst : G.fst e ≠ G.snd e := G.noLoop e
      simp only [WeightedMultigraph.Inc, hsourceFst, eq_self,
        false_or, if_true]
      have hterm : ∀ z : G.ColorDependentExtendedProfileState R (G.fst e) c,
          (n : ℝ) * G.colorDependentTinyCandidateEdgeUse proposal R rho omega
              (G.snd e) c sourceState e { center := G.fst e, candidate := z } /
              scale ≤ G.weight e := by
        intro z
        apply (div_le_iff₀ hscale).2
        simpa [mul_comm] using
          G.n_mul_colorDependentTinyCandidateEdgeUse_le_weight_mul_scale
            proposal R hn hs.le hq hr0 hleft homega0 homega1 hrho.le hC0.le
              hproposal (G.snd e) c sourceState e _
      calc
        (∑ v, ∑ z : G.ColorDependentExtendedProfileState R v c,
          (n : ℝ) * G.colorDependentTinyCandidateEdgeUse proposal R rho omega
            (G.snd e) c sourceState e { center := v, candidate := z } / scale) =
            ∑ z : G.ColorDependentExtendedProfileState R (G.fst e) c,
              (n : ℝ) * G.colorDependentTinyCandidateEdgeUse proposal R rho omega
                (G.snd e) c sourceState e
                  { center := G.fst e, candidate := z } / scale := by
          apply Fintype.sum_eq_single (G.fst e)
          intro v hv
          simp [colorDependentTinyCandidateEdgeUse, hv, hsourceFst,
            (G.noLoop e).symm]
        _ ≤ ∑ _z : G.ColorDependentExtendedProfileState R (G.fst e) c,
            G.weight e := Finset.sum_le_sum fun z _hz ↦ hterm z
        _ = Fintype.card (G.ColorDependentExtendedProfileState R (G.fst e) c) *
            G.weight e := by simp
        _ ≤ extendedProfileStateBound β q r * G.weight e := by
          have hcardR :
              (Fintype.card
                (G.ColorDependentExtendedProfileState R (G.fst e) c) : ℝ) ≤
                extendedProfileStateBound β q r := by
            exact_mod_cast G.colorDependentExtendedProfileState_card_le R
              (G.fst e) c
          exact mul_le_mul_of_nonneg_right hcardR (G.weight_nonneg e)
    · have hsourceFst' : G.fst e ≠ source := Ne.symm hsourceFst
      have hsourceSnd' : G.snd e ≠ source := Ne.symm hsourceSnd
      simp [WeightedMultigraph.Inc, hsourceFst, hsourceSnd,
        hsourceFst', hsourceSnd', colorDependentTinyCandidateEdgeUse]

/-- Per-color polynomial column bound for the normalized candidate use. -/
theorem sum_scaledColorDependentCandidateAtomUse_le_column
    (hn : 0 < n) (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c) :
    (∑ row : G.ColorDependentCandidateRowAt R c,
      G.scaledColorDependentCandidateAtomUse proposal R n
        (colorDependentCandidateCapacityScale rho s omega β q r C0)
        rho omega source c sourceState row) ≤
      colorDependentCandidatePerColorColumnBound n β q r := by
  classical
  let scale := colorDependentCandidateCapacityScale rho s omega β q r C0
  let M : ℝ := extendedProfileStateBound β q r
  let K : ℝ := explicitLargeSlotBound β q r
  have hlargeEdges : ((G.largeStarEdges β source).card : ℝ) ≤ (n : ℝ) / β := by
    apply (le_div_iff₀ hβ).2
    exact (G.largeStarEdges_card_mul_beta_le_starWeight β source).trans
      (hstar source)
  rw [Fintype.sum_sum_type]
  have hlarge :
      (∑ row : G.ColorDependentLargeCandidateRow R c,
        G.scaledColorDependentCandidateAtomUse proposal R n scale rho omega
          source c sourceState (Sum.inl row)) ≤
        M * K * ((G.largeStarEdges β source).card : ℝ) := by
    calc
      (∑ row : G.ColorDependentLargeCandidateRow R c,
        G.scaledColorDependentCandidateAtomUse proposal R n scale rho omega
          source c sourceState (Sum.inl row)) =
          ∑ e, ∑ row : G.ColorDependentLargeCandidateRow R c,
            (n : ℝ) * G.colorDependentLargeCandidateEdgeUse proposal R rho omega
              source c sourceState e row / scale := by
        unfold scaledColorDependentCandidateAtomUse colorDependentCandidateAtomUse
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum, Finset.sum_div]
      _ ≤ ∑ e, if G.Inc source e ∧ β ≤ G.weight e then M * K else 0 := by
        apply Finset.sum_le_sum
        intro e _he
        simpa [scale, M, K] using
          G.sum_scaledColorDependentLargeRows_edge_le proposal R hn hs hq hr0
            hleft homega0 homega1 hrho hC0 hproposal source c sourceState e
      _ = M * K * ((G.largeStarEdges β source).card : ℝ) := by
        calc
          (∑ e, if G.Inc source e ∧ β ≤ G.weight e then M * K else 0) =
              ∑ e, if G.Inc source e then
                (if β ≤ G.weight e then M * K else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro e _he
            by_cases hinc : G.Inc source e <;> simp [hinc]
          _ = ∑ e ∈ Finset.univ.filter (G.Inc source),
              if β ≤ G.weight e then M * K else 0 := by
            rw [← Finset.sum_filter]
          _ =
              ∑ e : G.StarEdge source, if β ≤ G.weight e.1 then M * K else 0 := by
            exact Finset.sum_subtype (Finset.univ.filter (G.Inc source))
              (by intro e; simp)
              (fun e ↦ if β ≤ G.weight e then M * K else 0)
          _ = M * K * ((G.largeStarEdges β source).card : ℝ) := by
            rw [← Finset.sum_filter]
            simp [largeStarEdges]
            ring
  have htiny :
      (∑ row : G.ColorDependentTinyCandidateRow R c,
        G.scaledColorDependentCandidateAtomUse proposal R n scale rho omega
          source c sourceState (Sum.inr row)) ≤ M * G.starWeight source := by
    calc
      (∑ row : G.ColorDependentTinyCandidateRow R c,
        G.scaledColorDependentCandidateAtomUse proposal R n scale rho omega
          source c sourceState (Sum.inr row)) =
          ∑ e, ∑ row : G.ColorDependentTinyCandidateRow R c,
            (n : ℝ) * G.colorDependentTinyCandidateEdgeUse proposal R rho omega
              source c sourceState e row / scale := by
        unfold scaledColorDependentCandidateAtomUse colorDependentCandidateAtomUse
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum, Finset.sum_div]
      _ ≤ ∑ e, if G.Inc source e then M * G.weight e else 0 := by
        apply Finset.sum_le_sum
        intro e _he
        simpa [scale, M] using
          G.sum_scaledColorDependentTinyRows_edge_le proposal R hn hs hq hr0
            hleft homega0 homega1 hrho hC0 hproposal source c sourceState e
      _ = M * G.starWeight source := by
        calc
          (∑ e, if G.Inc source e then M * G.weight e else 0) =
              M * (∑ e, if G.Inc source e then G.weight e else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e _he
            split <;> simp
          _ = M * G.starWeight source := by
            rw [← Finset.sum_filter]
            congr 1
            exact Finset.sum_subtype (Finset.univ.filter (G.Inc source))
              (by intro e; simp) G.weight
  calc
    (∑ row : G.ColorDependentLargeCandidateRow R c,
        G.scaledColorDependentCandidateAtomUse proposal R n scale rho omega
          source c sourceState (Sum.inl row)) +
      ∑ row : G.ColorDependentTinyCandidateRow R c,
        G.scaledColorDependentCandidateAtomUse proposal R n scale rho omega
          source c sourceState (Sum.inr row) ≤
        M * K * ((n : ℝ) / β) + M * n :=
      add_le_add
        (hlarge.trans (mul_le_mul_of_nonneg_left hlargeEdges (by positivity)))
        (htiny.trans (mul_le_mul_of_nonneg_left (hstar source) (by positivity)))
    _ = colorDependentCandidatePerColorColumnBound n β q r := by
      simp [colorDependentCandidatePerColorColumnBound, M, K]
      field_simp [hβ.ne']
      <;> ring

theorem sum_scaledColorDependentCandidateAtomUse_mul_le_column
    {L : ℕ} (hL : 0 < L)
    (hn : 0 < n) (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c) :
    (∑ row : G.ColorDependentCandidateRowAt R c,
      G.scaledColorDependentCandidateAtomUse proposal R n
        ((L : ℝ) * colorDependentCandidateCapacityScale
          rho s omega β q r C0)
        rho omega source c sourceState row) ≤
      colorDependentCandidatePerColorColumnBound n β q r := by
  let baseScale := colorDependentCandidateCapacityScale rho s omega β q r C0
  have hbase : 0 < baseScale :=
    colorDependentCandidateCapacityScale_pos
      (C0 := C0) hrho hs hC0 homega0
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hscale : 0 < (L : ℝ) * baseScale := by positivity
  calc
    (∑ row : G.ColorDependentCandidateRowAt R c,
      G.scaledColorDependentCandidateAtomUse proposal R n
        ((L : ℝ) * colorDependentCandidateCapacityScale
          rho s omega β q r C0)
        rho omega source c sourceState row) ≤
        ∑ row : G.ColorDependentCandidateRowAt R c,
          G.scaledColorDependentCandidateAtomUse proposal R n baseScale
            rho omega source c sourceState row := by
      apply Finset.sum_le_sum
      intro row _hrow
      unfold scaledColorDependentCandidateAtomUse
      apply (div_le_div_iff₀ hscale hbase).2
      have huse := G.colorDependentCandidateAtomUse_nonneg proposal R
        hs.le hq hr0 hleft homega0 homega1 hrho.le source c sourceState row
      have hnum : 0 ≤ (n : ℝ) *
          G.colorDependentCandidateAtomUse proposal R rho omega source c
            sourceState row := mul_nonneg (Nat.cast_nonneg n) huse
      exact mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul_of_nonneg_right hLreal hbase.le) hnum
    _ ≤ colorDependentCandidatePerColorColumnBound n β q r := by
      simpa [baseScale] using
        G.sum_scaledColorDependentCandidateAtomUse_le_column proposal R
          hn hs hq hr0 hleft homega0 homega1 hrho hC0 hproposal hstar
            source c sourceState

/-- Direct whole-word column bound consumed by the generic dependent-word
mean-relative selector. -/
theorem sum_scaledColorDependentWordCandidateUse_le_column
    (hn : 0 < n) (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (source : G.V)
    (word : G.ColorDependentExtendedProfileWord R source) :
    (∑ c : Color, ∑ row : G.ColorDependentCandidateRowAt R c,
      G.scaledColorDependentCandidateAtomUse proposal R n
        (colorDependentCandidateCapacityScale rho s omega β q r C0)
        rho omega source c (word c) row) ≤
      Fintype.card Color *
        colorDependentCandidatePerColorColumnBound n β q r := by
  calc
    (∑ c : Color, ∑ row : G.ColorDependentCandidateRowAt R c,
      G.scaledColorDependentCandidateAtomUse proposal R n
        (colorDependentCandidateCapacityScale rho s omega β q r C0)
        rho omega source c (word c) row) ≤
      ∑ _c : Color, colorDependentCandidatePerColorColumnBound n β q r := by
        apply Finset.sum_le_sum
        intro c _hc
        exact G.sum_scaledColorDependentCandidateAtomUse_le_column proposal R
          hn hs hq hr0 hleft homega0 homega1 hrho hC0 hproposal hstar
            source c (word c)
    _ = Fintype.card Color *
        colorDependentCandidatePerColorColumnBound n β q r := by simp

/-- Scaling by a positive fixed endpoint-pair multiplicity only decreases
the whole-word column load. -/
theorem sum_scaledColorDependentWordCandidateUse_mul_le_column
    {L : ℕ} (hL : 0 < L)
    (hn : 0 < n) (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (source : G.V)
    (word : G.ColorDependentExtendedProfileWord R source) :
    (∑ c : Color, ∑ row : G.ColorDependentCandidateRowAt R c,
      G.scaledColorDependentCandidateAtomUse proposal R n
        ((L : ℝ) * colorDependentCandidateCapacityScale
          rho s omega β q r C0)
        rho omega source c (word c) row) ≤
      Fintype.card Color *
        colorDependentCandidatePerColorColumnBound n β q r := by
  let baseScale := colorDependentCandidateCapacityScale rho s omega β q r C0
  have hbase : 0 < baseScale :=
    colorDependentCandidateCapacityScale_pos
      (C0 := C0) hrho hs hC0 homega0
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hscale : 0 < (L : ℝ) * baseScale := by positivity
  calc
    (∑ c : Color, ∑ row : G.ColorDependentCandidateRowAt R c,
      G.scaledColorDependentCandidateAtomUse proposal R n
        ((L : ℝ) * colorDependentCandidateCapacityScale
          rho s omega β q r C0)
        rho omega source c (word c) row) ≤
        ∑ c : Color, ∑ row : G.ColorDependentCandidateRowAt R c,
          G.scaledColorDependentCandidateAtomUse proposal R n baseScale
            rho omega source c (word c) row := by
      apply Finset.sum_le_sum
      intro c _hc
      apply Finset.sum_le_sum
      intro row _hrow
      unfold scaledColorDependentCandidateAtomUse
      apply (div_le_div_iff₀ hscale hbase).2
      have huse := G.colorDependentCandidateAtomUse_nonneg proposal R
        hs.le hq hr0 hleft homega0 homega1 hrho.le
        source c (word c) row
      have hnum : 0 ≤ (n : ℝ) *
          G.colorDependentCandidateAtomUse proposal R rho omega source c
            (word c) row := mul_nonneg (Nat.cast_nonneg n) huse
      exact mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul_of_nonneg_right hLreal hbase.le) hnum
    _ ≤ Fintype.card Color *
        colorDependentCandidatePerColorColumnBound n β q r := by
      simpa [baseScale] using
        G.sum_scaledColorDependentWordCandidateUse_le_column proposal R
          hn hs hq hr0 hleft homega0 homega1 hrho hC0 hproposal hstar
            source word

/-- Closed mean-relative capacity selector for diffuse color-dependent
proposals.  The conclusion deliberately retains the exact row mean; the
large and tiny sharp bounds in `ColorDependentExtendedProfileCandidateRows`
can therefore be substituted after the selected center state is known. -/
theorem exists_colorDependentCandidateCapacityWord
    {L : ℕ} (hL : 0 < L) (hmult : G.PairMultiplicityAtMost L)
    (hn : 0 < n) (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (hcolumnOne : 1 ≤ Fintype.card Color *
      colorDependentCandidatePerColorColumnBound n β q r)
    (K : ℕ) (hK : 0 < K)
    (hmeanK : (n : ℝ) * (rho / (1 - omega)) /
        ((L : ℝ) * colorDependentCandidateCapacityScale
          rho s omega β q r C0) ≤ K) :
    ∃ word : ∀ v, G.ColorDependentExtendedProfileWord R v,
      (∀ v, 0 < G.colorDependentExtendedProfileWordMass R omega v (word v)) ∧
      ∀ row : G.ColorDependentExtendedProfileCapacityRow
          (G.ColorDependentCandidateRowAt R),
        (∑ v, G.scaledColorDependentCandidateAtomUse proposal R n
          ((L : ℝ) * colorDependentCandidateCapacityScale
            rho s omega β q r C0)
          rho omega v row.1 (word v row.1) row.2) <
        (∑ v, ∑ z : G.ColorDependentExtendedProfileState R v row.1,
          G.smoothedColorDependentExtendedProfileProbability
              R omega v row.1 z *
            G.scaledColorDependentCandidateAtomUse proposal R n
              ((L : ℝ) * colorDependentCandidateCapacityScale
                rho s omega β q r C0)
              rho omega v row.1 z row.2) +
          FinitePartialResamplingNumerics.packingDeviation
            ((n : ℝ) * (rho / (1 - omega)) /
              ((L : ℝ) * colorDependentCandidateCapacityScale
                rho s omega β q r C0))
            (Fintype.card Color *
              colorDependentCandidatePerColorColumnBound n β q r) := by
  let scale := (L : ℝ) *
    colorDependentCandidateCapacityScale rho s omega β q r C0
  let meanBound := (n : ℝ) * (rho / (1 - omega)) / scale
  let columnBound := colorDependentCandidatePerColorColumnBound n β q r
  have hscale : 0 < scale := mul_pos (by exact_mod_cast hL)
    (colorDependentCandidateCapacityScale_pos
      (C0 := C0) hrho hs hC0 homega0)
  have hmean0 : 0 < meanBound := by
    unfold meanBound
    exact div_pos
      (mul_pos (by exact_mod_cast hn)
        (div_pos hrho (sub_pos.mpr homega1)))
      hscale
  have hcolumn0 : 0 ≤ columnBound := by
    unfold columnBound colorDependentCandidatePerColorColumnBound
    positivity
  apply G.exists_colorDependentExtendedProfileWord_rowLoad_lt_rowMean_add_deviation
    R (G.ColorDependentCandidateRowAt R) omega meanBound columnBound
      hs.le hq hr0 hleft homega0 homega1.le hmean0 hcolumn0
      (by simpa [columnBound] using hcolumnOne) K hK (by simpa [meanBound] using hmeanK)
      (G.scaledColorDependentCandidateAtomUse proposal R n scale rho omega)
  · intro v c z row
    exact G.scaledColorDependentCandidateAtomUse_nonneg proposal R
      hs.le hq hr0 hleft homega0 homega1.le hrho.le hscale.le v c z row
  · intro v c z row
    exact G.scaledColorDependentCandidateAtomUse_le_one proposal R
      hL hmult hn hs hq hr0 hleft homega0 homega1.le hrho hC0 hproposal
        v c z row
  · intro c row
    simpa [meanBound, scale] using
      G.scaledColorDependentCandidateAtomMean_le_one_sub_omega proposal R
        n scale hs.le hq hr0 hleft homega0 homega1 hrho.le hscale c row
  · intro v c z
    simpa [columnBound, scale] using
      G.sum_scaledColorDependentCandidateAtomUse_mul_le_column proposal R
        hL hn hs hq hr0 hleft homega0 homega1.le hrho hC0 hproposal hstar
          v c z

end ProposalDependentColumns

end WeightedMultigraph

end

end WeightedEdgeColoring
