import WeightedEdgeColoring.BPThreeModeLocalCounts
import WeightedEdgeColoring.FinitePaletteMerge

/-!
# The selected three-mode certificate

One simultaneous two-row rounding chooses all three compatible modes.  Each
mode is colored by the compatible-copy lemma, and the three disjoint palettes
are merged without an extra fallback color.  The residual estimate remains
in its raw remainder-probability form, ready for the separate `104/75`
one-bin charge theorem.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Union of the three selected mode edge sets. -/
def threeModeSelectedEdges (label : G.E → Option ThreeMode) : Finset G.E :=
  Finset.univ.biUnion (G.selectedModeEdges label)

/-- Total size of the three disjoint selected palettes. -/
noncomputable def threeModeTotalPaletteSize : ℕ :=
  G.threeModePaletteSize (0 : ThreeMode) +
    G.threeModePaletteSize (1 : ThreeMode) +
      G.threeModePaletteSize (2 : ThreeMode)

/-- The fractional residual harmonic charge before applying the one-bin
`104/75` estimate. -/
noncomputable def threeModeExpectedResidualCharge (v : G.V) : ℝ :=
  ∑ e : G.E, if G.Inc v e then
    G.compatibleModeRemainderProbability G.threeModeHeavyEdges
      G.threeModeLightEdges threeModeHeavyProbability
      threeModeLightProbability e * harmonicCharge (G.weight e)
    else 0

/-- The three ceilings and the additive-two rounding losses cost at most nine
colors beyond `(7/30) bp(G)`. -/
theorem threeModeTotalPaletteSize_bound :
    (G.threeModeTotalPaletteSize : ℝ) ≤
      (7 / 30 : ℝ) * G.bp + 9 := by
  have hp0 : 0 ≤ threeModeHeavyProbability (0 : ThreeMode) * (G.bp : ℝ) :=
    mul_nonneg (threeModeHeavyProbability_nonneg _) (by positivity)
  have hp1 : 0 ≤ threeModeHeavyProbability (1 : ThreeMode) * (G.bp : ℝ) :=
    mul_nonneg (threeModeHeavyProbability_nonneg _) (by positivity)
  have hp2 : 0 ≤ threeModeHeavyProbability (2 : ThreeMode) * (G.bp : ℝ) :=
    mul_nonneg (threeModeHeavyProbability_nonneg _) (by positivity)
  have hc0 := (Nat.ceil_lt_add_one hp0).le
  have hc1 := (Nat.ceil_lt_add_one hp1).le
  have hc2 := (Nat.ceil_lt_add_one hp2).le
  have hp0eq : threeModeHeavyProbability (0 : ThreeMode) = 1 / 20 := by
    rfl
  have hp1eq : threeModeHeavyProbability (1 : ThreeMode) = 1 / 10 := by
    rfl
  have hp2eq : threeModeHeavyProbability (2 : ThreeMode) = 1 / 12 := by
    rfl
  rw [hp0eq] at hc0
  rw [hp1eq] at hc1
  rw [hp2eq] at hc2
  unfold threeModeTotalPaletteSize threeModePaletteSize
  rw [hp0eq, hp1eq, hp2eq]
  push_cast
  norm_num at hc0 hc1 hc2 ⊢
  linarith

/-- Data produced by the simultaneous three-mode selection. -/
structure ThreeModeSelectionCertificate where
  label : G.E → Option ThreeMode
  eligible : ∀ e m, label e = some m →
    e ∈ G.threeModeHeavyEdges m ∨ e ∈ G.threeModeLightEdges m
  color : G.E → Fin G.threeModeTotalPaletteSize
  feasible : G.IsFeasibleOn (G.threeModeSelectedEdges label) color
  selected_residual_disjoint :
    Disjoint (G.threeModeSelectedEdges label)
      (G.selectedModeResidualEdges label)
  cover : G.threeModeSelectedEdges label ∪
      G.selectedModeResidualEdges label = Finset.univ
  raw_residual_bound : ∀ v,
    (∑ e : G.E, if label e = none ∧ G.Inc v e then
      harmonicCharge (G.weight e) else 0) ≤
      G.threeModeExpectedResidualCharge v + 2
  residual_charge_bound : ∀ v,
    G.harmonicChargeOn (G.selectedModeResidualEdges label) v ≤
      G.threeModeExpectedResidualCharge v + 2

/-- Construct and color all three selected modes with a common label. -/
theorem exists_threeModeSelectionCertificate
    (bip : G.Bipartition) :
    Nonempty G.ThreeModeSelectionCertificate := by
  classical
  obtain ⟨label, heligible, hheavySelected, hlightSelected, hresidual⟩ :=
    G.exists_compatible_mode_selection G.threeModeHeavyEdges
      G.threeModeLightEdges threeModeHeavyProbability
      threeModeLightProbability threeModeHeavyProbability_nonneg
      threeModeLightProbability_nonneg G.threeMode_probability_sum_le_one
  have hlightDiff (m : ThreeMode) :
      G.threeModeLightEdges m \ G.threeModeHeavyEdges m =
        G.threeModeLightEdges m := by
    apply Finset.Subset.antisymm
    · exact Finset.sdiff_subset
    · intro e heS
      apply Finset.mem_sdiff.mpr
      refine ⟨heS, ?_⟩
      intro heH
      exact Finset.disjoint_left.mp (G.threeModeHeavy_light_disjoint m) heH heS
  have hmodeColor : ∀ m : ThreeMode,
      ∃ color : G.E → Fin (G.threeModePaletteSize m),
        G.IsFeasibleOn (G.selectedModeEdges label m) color := by
    intro m
    have hlightSelected' : ∀ v,
        (G.degreeOn
            (G.selectedModeLightEdges label G.threeModeHeavyEdges
              G.threeModeLightEdges m) v : ℝ) ≤
          threeModeLightProbability m *
            (G.degreeOn (G.threeModeLightEdges m) v : ℝ) + 2 := by
      intro v
      simpa [hlightDiff m] using hlightSelected m v
    have hdegree : ∀ v,
        G.degreeOn
            (G.selectedModeHeavyEdges label G.threeModeHeavyEdges m) v ≤
            G.threeModePaletteSize m ∧
          G.degreeOn
              (G.selectedModeHeavyEdges label G.threeModeHeavyEdges m) v +
            G.degreeOn
              (G.selectedModeLightEdges label G.threeModeHeavyEdges
                G.threeModeLightEdges m) v ≤
              threeModeCopies m * G.threeModePaletteSize m := by
      intro v
      exact G.threeMode_rounded_local_degree_bounds m v
        (G.selectedModeHeavyEdges label G.threeModeHeavyEdges m)
        (G.selectedModeLightEdges label G.threeModeHeavyEdges
          G.threeModeLightEdges m)
        (hheavySelected m v) (hlightSelected' v)
    apply exists_feasibleOn_of_compatible_copies bip
      (G.selectedModeEdges label m)
      (G.selectedModeHeavyEdges label G.threeModeHeavyEdges m)
      (G.selectedModeLightEdges label G.threeModeHeavyEdges
        G.threeModeLightEdges m)
      (G.selectedModeEdges_eq_heavy_union_light label G.threeModeHeavyEdges
        G.threeModeLightEdges heligible m)
      (G.selectedModeHeavy_light_disjoint label G.threeModeHeavyEdges
        G.threeModeLightEdges m)
      (r := threeModeCopies m) (L := G.threeModePaletteSize m)
      (heavyCap := threeModeHeavyCap m)
      (lightCap := threeModeLightCap m)
    · rw [threeModeCopies_eq_two]
    · unfold threeModePaletteSize
      omega
    · exact threeModeLightCap_nonneg m
    · intro e he
      exact G.threeModeHeavy_weight_le m
        (Finset.mem_filter.mp he).2.2
    · intro e he
      exact G.threeModeLight_weight_le m
        (Finset.mem_filter.mp he).2.2.2
    · exact threeMode_small_capacity m
    · exact threeMode_mixed_capacity m
    · exact fun v => (hdegree v).1
    · exact fun v => (hdegree v).2
  choose modeColor hmodeFeasible using hmodeColor
  have hdisj01 : Disjoint
      (G.selectedModeEdges label (0 : ThreeMode))
      (G.selectedModeEdges label (1 : ThreeMode)) :=
    G.selectedModeEdges_pairwise_disjoint label (by decide)
  obtain ⟨color01, hcolor01⟩ := G.merge_feasibleOn
    (G.selectedModeEdges label (0 : ThreeMode))
    (G.selectedModeEdges label (1 : ThreeMode)) hdisj01
    (modeColor (0 : ThreeMode)) (hmodeFeasible (0 : ThreeMode))
    (modeColor (1 : ThreeMode)) (hmodeFeasible (1 : ThreeMode))
  have hdisj012 : Disjoint
      (G.selectedModeEdges label (0 : ThreeMode) ∪
        G.selectedModeEdges label (1 : ThreeMode))
      (G.selectedModeEdges label (2 : ThreeMode)) := by
    rw [Finset.disjoint_left]
    intro e he01 he2
    rcases Finset.mem_union.mp he01 with he0 | he1
    · exact Finset.disjoint_left.mp
        (G.selectedModeEdges_pairwise_disjoint label (by decide)) he0 he2
    · exact Finset.disjoint_left.mp
        (G.selectedModeEdges_pairwise_disjoint label (by decide)) he1 he2
  obtain ⟨color012, hcolor012⟩ := G.merge_feasibleOn
    (G.selectedModeEdges label (0 : ThreeMode) ∪
      G.selectedModeEdges label (1 : ThreeMode))
    (G.selectedModeEdges label (2 : ThreeMode)) hdisj012
    color01 hcolor01 (modeColor (2 : ThreeMode))
    (hmodeFeasible (2 : ThreeMode))
  have hselectedEq :
      G.threeModeSelectedEdges label =
        (G.selectedModeEdges label (0 : ThreeMode) ∪
          G.selectedModeEdges label (1 : ThreeMode)) ∪
            G.selectedModeEdges label (2 : ThreeMode) := by
    ext e
    simp only [threeModeSelectedEdges, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨m, hem⟩
      fin_cases m
      · exact Or.inl (Or.inl hem)
      · exact Or.inl (Or.inr hem)
      · exact Or.inr hem
    · rintro ((he0 | he1) | he2)
      · exact ⟨(0 : ThreeMode), he0⟩
      · exact ⟨(1 : ThreeMode), he1⟩
      · exact ⟨(2 : ThreeMode), he2⟩
  let color : G.E → Fin G.threeModeTotalPaletteSize := color012
  have hfeasible : G.IsFeasibleOn (G.threeModeSelectedEdges label) color := by
    rw [hselectedEq]
    exact hcolor012
  have hselectedResidual : Disjoint
      (G.threeModeSelectedEdges label)
      (G.selectedModeResidualEdges label) := by
    rw [Finset.disjoint_left]
    intro e heSelected heResidual
    rw [threeModeSelectedEdges, Finset.mem_biUnion] at heSelected
    obtain ⟨m, _hm, hem⟩ := heSelected
    exact Finset.disjoint_left.mp
      (G.selectedModeEdges_residual_disjoint label m) hem heResidual
  have hcover : G.threeModeSelectedEdges label ∪
      G.selectedModeResidualEdges label = Finset.univ := by
    exact G.selectedModes_cover_univ label
  have hresidualCharge : ∀ v,
      G.harmonicChargeOn (G.selectedModeResidualEdges label) v ≤
        G.threeModeExpectedResidualCharge v + 2 := by
    intro v
    have heq :
        G.harmonicChargeOn (G.selectedModeResidualEdges label) v =
          ∑ e : G.E, if label e = none ∧ G.Inc v e then
            harmonicCharge (G.weight e) else 0 := by
      unfold harmonicChargeOn chargeOn selectedModeResidualEdges
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hl : label e = none <;>
        by_cases hi : G.Inc v e <;> simp [hl, hi]
    rw [heq]
    simpa [threeModeExpectedResidualCharge] using hresidual v
  exact ⟨{
    label := label
    eligible := heligible
    color := color
    feasible := hfeasible
    selected_residual_disjoint := hselectedResidual
    cover := hcover
    raw_residual_bound := by
      intro v
      simpa [threeModeExpectedResidualCharge] using hresidual v
    residual_charge_bound := hresidualCharge
  }⟩

end WeightedMultigraph
end WeightedEdgeColoring
