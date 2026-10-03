import WeightedEdgeColoring.SubtwoMixedGraphPackedWords

/-!
# Endpoint-label support of concrete mixed assignments

Every positive large or tiny assignment in a mixed graph atom comes from a
positive conditional profile assignment.  Since a conditional proposal is
zero off its chosen endpoint label, the atom's selected label is exactly the
label of the assigned physical edge.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {v : G.V} {Label : Type*} [Fintype Label] [DecidableEq Label]
variable (edgeLabel : G.StarEdge v → Label)
variable (x : G.StarEdge v → ℝ)
variable (q : Finset (G.StarEdge v) → ℝ)
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : ∀ label : Label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal edgeLabel x q label)
    s β qstep r hβ hr)

private theorem conditionalEndpointProposal_pos_label
    (label : Label) (e : G.StarEdge v)
    (hpos : 0 < G.conditionalEndpointProposal edgeLabel x q label e) :
    edgeLabel e = label := by
  by_cases h : edgeLabel e = label
  · exact h
  · simp [conditionalEndpointProposal, h] at hpos

theorem positive_localExtendedProfileLargeAssign_label
    (hs : 0 ≤ s) (label : Label) (e : G.StarEdge v)
    (z : G.LocalExtendedProfileState (R label))
    (i : Fin (explicitLargeSlotBound β qstep r))
    (hpos : 0 < G.localExtendedProfileLargeAssign (R label) e z i) :
    edgeLabel e = label := by
  cases z with
  | inl P =>
      change 0 < G.localActualProfilePaddedAssign (R label) e P i at hpos
      unfold localActualProfilePaddedAssign at hpos
      have hnonneg : ∀ j : G.RoundedProfileOrdinarySlot
          (R label).law P.1,
          0 ≤ (if G.paddedLargeSlotCode (R label) (some ⟨P, j⟩) = i then
            (R label).largeAssign e (some ⟨P, j⟩) else 0) := by
        intro j
        split
        · exact (R label).largeAssign_nonneg e (some ⟨P, j⟩)
        · exact le_rfl
      obtain ⟨j, _, hjpos⟩ :=
        (Finset.sum_pos_iff_of_nonneg
          (fun j _ ↦ hnonneg j)).mp hpos
      by_cases hcode : G.paddedLargeSlotCode (R label)
          (some ⟨P, j⟩) = i
      · have hlarge : 0 < (R label).largeAssign e (some ⟨P, j⟩) := by
          simpa [hcode] using hjpos
        exact BoundedProfileRealization.positive_largeAssign_respects_support
          G (R label) hs (fun e ↦ edgeLabel e = label)
          (fun e he ↦ G.conditionalEndpointProposal_pos_label
            edgeLabel x q label e he)
          e (some ⟨P, j⟩) hlarge
      · simp [hcode] at hjpos
  | inr k =>
      change 0 < (if k.1 = 0 then
        if G.paddedLargeSlotCode (R label) none = i then
          (R label).largeAssign e none else 0 else 0) at hpos
      by_cases hk : k.1 = 0
      · by_cases hcode : G.paddedLargeSlotCode (R label) none = i
        · have hlarge : 0 < (R label).largeAssign e none := by
            simpa [hk, hcode] using hpos
          exact BoundedProfileRealization.positive_largeAssign_respects_support
            G (R label) hs (fun e ↦ edgeLabel e = label)
            (fun e he ↦ G.conditionalEndpointProposal_pos_label
              edgeLabel x q label e he)
            e none hlarge
        · simp [hk, hcode] at hpos
      · simp [hk] at hpos

theorem positive_localExtendedProfileTinyAssign_label
    (hs : 0 ≤ s) (label : Label) (e : G.StarEdge v)
    (z : G.LocalExtendedProfileState (R label))
    (hpos : 0 < G.localExtendedProfileTinyAssign (R label) e z) :
    edgeLabel e = label := by
  cases z with
  | inl P =>
      exact BoundedProfileRealization.positive_tinyAssign_respects_support
        G (R label) hs (fun e ↦ edgeLabel e = label)
        (fun e he ↦ G.conditionalEndpointProposal_pos_label
          edgeLabel x q label e he)
        e (some P) hpos
  | inr k =>
      change 0 < (if k.1 = 1 then
        (R label).tinyAssign e none else 0) at hpos
      by_cases hk : k.1 = 1
      · have htiny : 0 < (R label).tinyAssign e none := by
          simpa [hk] using hpos
        exact BoundedProfileRealization.positive_tinyAssign_respects_support
          G (R label) hs (fun e ↦ edgeLabel e = label)
          (fun e he ↦ G.conditionalEndpointProposal_pos_label
            edgeLabel x q label e he)
          e none htiny
      · simp [hk] at hpos

theorem positive_mixedLabelGraphLargeAssign_label
    (hq0 : ∀ S, 0 ≤ q S) (hs : 0 ≤ s)
    (e : G.StarEdge v)
    (a : G.MixedLabelGraphAtom edgeLabel x q R)
    (i : Fin (explicitLargeSlotBound β qstep r))
    (hpos : 0 < G.mixedLabelGraphLargeAssign edgeLabel x q R e a i) :
    Subtwo.labelMixtureAtomLabel
      (fun label ↦ G.LocalExtendedProfileState (R label)) a =
        some (edgeLabel e) := by
  cases a with
  | none => simp [mixedLabelGraphLargeAssign] at hpos
  | some lz =>
      have hmass0 := G.subsetLabelMass_nonneg_local
        edgeLabel q hq0 lz.1
      have hlocal : 0 < G.localExtendedProfileLargeAssign
          (R lz.1) e lz.2 i := by
        by_contra hnot
        have hle : G.localExtendedProfileLargeAssign
            (R lz.1) e lz.2 i ≤ 0 := le_of_not_gt hnot
        have hprod := mul_nonpos_of_nonneg_of_nonpos hmass0 hle
        exact (not_lt_of_ge hprod) hpos
      have hlabel := G.positive_localExtendedProfileLargeAssign_label
        edgeLabel x q R hs lz.1 e lz.2 i hlocal
      simp [Subtwo.labelMixtureAtomLabel, hlabel]

theorem positive_mixedLabelGraphTinyAssign_label
    (hq0 : ∀ S, 0 ≤ q S) (hs : 0 ≤ s)
    (e : G.StarEdge v)
    (a : G.MixedLabelGraphAtom edgeLabel x q R)
    (hpos : 0 < G.mixedLabelGraphTinyAssign edgeLabel x q R e a) :
    Subtwo.labelMixtureAtomLabel
      (fun label ↦ G.LocalExtendedProfileState (R label)) a =
        some (edgeLabel e) := by
  cases a with
  | none => simp [mixedLabelGraphTinyAssign] at hpos
  | some lz =>
      have hmass0 := G.subsetLabelMass_nonneg_local
        edgeLabel q hq0 lz.1
      have hlocal : 0 < G.localExtendedProfileTinyAssign
          (R lz.1) e lz.2 := by
        by_contra hnot
        have hle : G.localExtendedProfileTinyAssign
            (R lz.1) e lz.2 ≤ 0 := le_of_not_gt hnot
        have hprod := mul_nonpos_of_nonneg_of_nonpos hmass0 hle
        exact (not_lt_of_ge hprod) hpos
      have hlabel := G.positive_localExtendedProfileTinyAssign_label
        edgeLabel x q R hs lz.1 e lz.2 hlocal
      simp [Subtwo.labelMixtureAtomLabel, hlabel]

end WeightedMultigraph

end

end WeightedEdgeColoring

namespace WeightedEdgeColoring

noncomputable section

/-- A positive two-endpoint option uses positive assigned mass at each end.
This elementary fact transfers endpoint-label support through `pairedOption`.
-/
theorem positive_pairedOption_uses
    {PU PV IU IV : Type*}
    (rho y : ℝ) (lambdaU : PU → ℝ) (lambdaV : PV → ℝ)
    (aU : PU → IU → ℝ) (aV : PV → IV → ℝ)
    (p : PU) (q : PV) (i : IU) (j : IV)
    (hrho : 0 ≤ rho) (hy0 : 0 ≤ y)
    (hlamU : 0 < lambdaU p) (hlamV : 0 < lambdaV q)
    (ha0 : 0 ≤ aU p i) (hb0 : 0 ≤ aV q j)
    (hpos : 0 < pairedOption rho y lambdaU lambdaV aU aV p q i j) :
    0 < aU p i ∧ 0 < aV q j := by
  have hy : 0 < y := by
    by_contra hnot
    have hzero : y = 0 := le_antisymm (le_of_not_gt hnot) hy0
    simp [pairedOption, hzero] at hpos
  have hden : 0 < y * lambdaU p * lambdaV q :=
    mul_pos (mul_pos hy hlamU) hlamV
  simp only [pairedOption, if_neg hy.ne'] at hpos
  have hnum : 0 < rho * aU p i * aV q j := by
    rcases div_pos_iff.mp hpos with h | h
    · exact h.1
    · exact (not_lt_of_ge hden.le h.2).elim
  have hb : 0 < aV q j := by
    rcases mul_pos_iff.mp hnum with h | h
    · exact h.2
    · exact (not_lt_of_ge hb0 h.2).elim
  have hra : 0 < rho * aU p i := by
    rcases mul_pos_iff.mp hnum with h | h
    · exact h.1
    · exact (not_lt_of_ge hb0 h.2).elim
  have ha : 0 < aU p i := by
    rcases mul_pos_iff.mp hra with h | h
    · exact h.2
    · exact (not_lt_of_ge hrho h.1).elim
  exact ⟨ha, hb⟩

end

end WeightedEdgeColoring
