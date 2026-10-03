import WeightedEdgeColoring.WeightedMomentGraphStatistics

/-!
# Reindexing graph moments by the opposite endpoint

For component-coin selection it is convenient to group residual edges by
the vertex whose missing palette they read.  `firstLinkCharge v w` is the
first-moment coefficient sent from `w` to the row based at `v`, and
`secondLinkCharge v w` is its squared-denominator analogue.  The graph
moments are finite sums of these link charges times the appropriate missing
indicators at `w`.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open scoped BigOperators
open WeightedEdgeColoring.WeightedMomentStatistics

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

def firstLinkCharge {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (v w : G.V) : ℝ :=
  ∑ e : R,
    if G.Inc v e.1 ∧ G.kempeOtherEndpoint v e.1 = w then
      charge e.1 / G.momentMissingSize F color w
    else 0

def secondLinkCharge {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (v w : G.V) : ℝ :=
  ∑ e : R,
    if G.Inc v e.1 ∧ G.kempeOtherEndpoint v e.1 = w then
      charge e.1 / (G.momentMissingSize F color w) ^ 2
    else 0

private theorem inc_otherEndpoint_eq_iff_eq_otherEndpoint
    {w x : G.V} {e : G.E} (hw : G.Inc w e) :
    (G.Inc x e ∧ G.kempeOtherEndpoint x e = w) ↔
      x = G.kempeOtherEndpoint w e := by
  let v := G.kempeOtherEndpoint w e
  have hv : G.Inc v e := by
    rcases hw with hfst | hsnd
    · exact Or.inr (by simp [v, kempeOtherEndpoint, hfst])
    · have hne : G.fst e ≠ w := by
        intro h
        exact G.noLoop e (h.trans hsnd.symm)
      exact Or.inl (by simp [v, kempeOtherEndpoint, hne])
  have hvw : v ≠ w := by
    rcases hw with hfst | hsnd
    · intro hvw
      have hsndw : G.snd e = w := by
        simpa [v, kempeOtherEndpoint, hfst] using hvw
      exact G.noLoop e (hfst.trans hsndw.symm)
    · have hne : G.fst e ≠ w := by
        intro h
        exact G.noLoop e (h.trans hsnd.symm)
      intro hvw
      apply hne
      rw [show v = G.fst e by simp [v, kempeOtherEndpoint, hne]] at hvw
      exact hvw
  have hother : G.kempeOtherEndpoint v e = w :=
    G.kempeOtherEndpoint_eq_of_incident hv hw hvw
  constructor
  · rintro ⟨hx, hxother⟩
    have hwx : w ≠ x := by
      intro hwx
      subst x
      apply hvw
      simpa [v] using hxother
    have hvx : G.kempeOtherEndpoint w e = x :=
      G.kempeOtherEndpoint_eq_of_incident hw hx hwx
    simpa [v] using hvx.symm
  · intro hxv
    subst x
    exact ⟨hv, hother⟩

theorem firstLinkCharge_nonneg {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (v w : G.V) :
    0 ≤ G.firstLinkCharge R charge F color v w := by
  unfold firstLinkCharge
  apply Finset.sum_nonneg
  intro e _he
  split
  · exact div_nonneg (hcharge e.1 e.2) (by
      unfold momentMissingSize
      exact Nat.cast_nonneg _)
  · exact le_rfl

theorem secondLinkCharge_nonneg {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (v w : G.V) :
    0 ≤ G.secondLinkCharge R charge F color v w := by
  unfold secondLinkCharge
  apply Finset.sum_nonneg
  intro e _he
  split
  · exact div_nonneg (hcharge e.1 e.2) (sq_nonneg _)
  · exact le_rfl

theorem graphFirstMoment_eq_sum_firstLinkCharge {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (v : G.V) (c : Fin q) :
    G.graphFirstMoment R charge F color v c =
      ∑ w : G.V, G.firstLinkCharge R charge F color v w *
        paletteIndicator (G.missingColorsAt F color w) c := by
  unfold graphFirstMoment firstMoment graphMomentItemPalette
    graphMomentItemWeight paletteSize firstLinkCharge
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hinc : G.Inc v e.1
  · simp [hinc, momentMissingSize, paletteIndicator]
    rw [Finset.sum_eq_single (G.kempeOtherEndpoint v e.1)]
    · simp
    · intro x _hx hxne
      simp [Ne.symm hxne]
    · simp
  · simp [hinc]

theorem graphDiagonalMoment_eq_sum_secondLinkCharge {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (v : G.V) (c : Fin q) :
    G.graphDiagonalMoment R charge F color v c =
      ∑ w : G.V, G.secondLinkCharge R charge F color v w *
        paletteIndicator (G.missingColorsAt F color w) c := by
  unfold graphDiagonalMoment diagonalMoment graphMomentItemPalette
    graphMomentItemWeight paletteSize secondLinkCharge
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hinc : G.Inc v e.1
  · simp [hinc, momentMissingSize, paletteIndicator]
    rw [Finset.sum_eq_single (G.kempeOtherEndpoint v e.1)]
    · simp
    · intro x _hx hxne
      simp [Ne.symm hxne]
    · simp
  · simp [hinc]

theorem graphPairMoment_eq_sum_secondLinkCharge {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (v : G.V) (c d : Fin q) :
    G.graphPairMoment R charge F color v c d =
      if c = d then 0 else
        ∑ w : G.V, G.secondLinkCharge R charge F color v w *
          paletteIndicator (G.missingColorsAt F color w) c *
          paletteIndicator (G.missingColorsAt F color w) d := by
  unfold graphPairMoment pairMoment graphMomentItemPalette
    graphMomentItemWeight paletteSize secondLinkCharge
  by_cases hcd : c = d
  · simp [hcd]
  · rw [if_neg hcd, if_neg hcd]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _he
    by_cases hinc : G.Inc v e.1
    · simp [hinc, momentMissingSize, paletteIndicator]
      rw [Finset.sum_eq_single (G.kempeOtherEndpoint v e.1)]
      · simp
      · intro x _hx hxne
        simp [Ne.symm hxne]
      · simp
    · simp [hinc]

/-- Summing first-link charge over all receiving vertices gives the
restricted charge at `w`, divided by the missing-palette size at `w`. -/
theorem sum_firstLinkCharge {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (w : G.V) :
    (∑ v : G.V, G.firstLinkCharge R charge F color v w) =
      G.restrictedCharge R charge w /
        G.momentMissingSize F color w := by
  unfold firstLinkCharge restrictedCharge
  rw [Finset.sum_comm, Finset.sum_div]
  conv_rhs => rw [← Finset.sum_attach, Finset.attach_eq_univ]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hw : G.Inc w e.1
  · let v := G.kempeOtherEndpoint w e.1
    have hiff (x : G.V) :
        (G.Inc x e.1 ∧ G.kempeOtherEndpoint x e.1 = w) ↔ x = v := by
      simpa [v] using
        (inc_otherEndpoint_eq_iff_eq_otherEndpoint G hw (x := x))
    rw [show
        (∑ x : G.V,
          if G.Inc x e.1 ∧ G.kempeOtherEndpoint x e.1 = w then
            charge e.1 / G.momentMissingSize F color w else 0) =
          ∑ x : G.V, if x = v then
            charge e.1 / G.momentMissingSize F color w else 0 by
      apply Finset.sum_congr rfl
      intro x _hx
      simp only [hiff x]]
    simp [hw]
  · have hnone : ∀ v, ¬(G.Inc v e.1 ∧
        G.kempeOtherEndpoint v e.1 = w) := by
      intro v hv
      apply hw
      rcases hv.1 with hfst | hsnd
      · right
        simpa [kempeOtherEndpoint, hfst] using hv.2
      · have hne : G.fst e.1 ≠ v := by
          intro h
          exact G.noLoop e.1 (h.trans hsnd.symm)
        left
        simpa [kempeOtherEndpoint, hne] using hv.2
    simp [hw, hnone]

theorem sum_secondLinkCharge {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (w : G.V) :
    (∑ v : G.V, G.secondLinkCharge R charge F color v w) =
      G.restrictedCharge R charge w /
        (G.momentMissingSize F color w) ^ 2 := by
  unfold secondLinkCharge restrictedCharge
  rw [Finset.sum_comm, Finset.sum_div]
  conv_rhs => rw [← Finset.sum_attach, Finset.attach_eq_univ]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hw : G.Inc w e.1
  · let v := G.kempeOtherEndpoint w e.1
    have hiff (x : G.V) :
        (G.Inc x e.1 ∧ G.kempeOtherEndpoint x e.1 = w) ↔ x = v := by
      simpa [v] using
        (inc_otherEndpoint_eq_iff_eq_otherEndpoint G hw (x := x))
    rw [show
        (∑ x : G.V,
          if G.Inc x e.1 ∧ G.kempeOtherEndpoint x e.1 = w then
            charge e.1 / (G.momentMissingSize F color w) ^ 2 else 0) =
          ∑ x : G.V, if x = v then
            charge e.1 / (G.momentMissingSize F color w) ^ 2 else 0 by
      apply Finset.sum_congr rfl
      intro x _hx
      simp only [hiff x]]
    simp [hw]
  · have hnone : ∀ v, ¬(G.Inc v e.1 ∧
        G.kempeOtherEndpoint v e.1 = w) := by
      intro v hv
      apply hw
      rcases hv.1 with hfst | hsnd
      · right
        simpa [kempeOtherEndpoint, hfst] using hv.2
      · have hne : G.fst e.1 ≠ v := by
          intro h
          exact G.noLoop e.1 (h.trans hsnd.symm)
        left
        simpa [kempeOtherEndpoint, hne] using hv.2
    simp [hw, hnone]

end

end WeightedMultigraph
end WeightedEdgeColoring
