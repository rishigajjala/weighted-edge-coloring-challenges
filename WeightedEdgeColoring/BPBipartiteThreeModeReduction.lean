import WeightedEdgeColoring.BPThreeModeSelectionCertificate
import WeightedEdgeColoring.BPThreeModeCharge
import WeightedEdgeColoring.BPHarmonicColoringInterface

/-!
# Final reduction for the bipartite `81/50` bound

This file connects the simultaneous three-mode certificate to the exact
`104/75` one-bin charge theorem, using the bipartite harmonic-charge coloring
interface as a hypothesis.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- The sum of the three graph-defined proposal probabilities is the scalar
proposal used by the one-bin charge calculation. -/
theorem threeMode_probability_sum_eq_proposal (e : G.E) :
    (∑ m : ThreeMode,
      G.compatibleModeProbability G.threeModeHeavyEdges
        G.threeModeLightEdges threeModeHeavyProbability
        threeModeLightProbability e m) =
      threeModeProposal (G.weight e) := by
  simp only [Fin.sum_univ_succ]
  simp [compatibleModeProbability, threeModeHeavyEdges,
    threeModeLightEdges, threeModeHeavyProbability,
    threeModeLightProbability, threeModeHeavyCap, threeModeLightCap,
    threeModeClassK,
    threeModeProposal, firstModeProposal, secondModeProposal,
    thirdModeProposal, add_assoc]

/-- Hence the graph-defined remainder probability gives exactly the scalar
residual charge. -/
theorem compatibleModeRemainder_mul_harmonic_eq_threeModeResidualCharge
    (e : G.E) :
    G.compatibleModeRemainderProbability G.threeModeHeavyEdges
        G.threeModeLightEdges threeModeHeavyProbability
        threeModeLightProbability e * harmonicCharge (G.weight e) =
      threeModeResidualCharge (G.weight e) := by
  rw [compatibleModeRemainderProbability,
    G.threeMode_probability_sum_eq_proposal e]
  rw [threeModeResidualCharge_eq]
  ring

/-- The expected residual charge in the selection certificate is the star
charge for the scalar three-mode residual charge. -/
theorem threeModeExpectedResidualCharge_eq_starCharge (v : G.V) :
    G.threeModeExpectedResidualCharge v =
      G.starCharge threeModeResidualCharge v := by
  rw [G.starCharge_eq_chargeOn_univ]
  unfold threeModeExpectedResidualCharge chargeOn
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hinc : G.Inc v e
  · simp only [if_pos hinc]
    exact G.compatibleModeRemainder_mul_harmonic_eq_threeModeResidualCharge e
  · simp [hinc]

/-- Applying the `104/75` one-bin theorem to the `bp(G)` local bins bounds
the expected residual charge at every vertex. -/
theorem threeModeExpectedResidualCharge_le (v : G.V) :
    G.threeModeExpectedResidualCharge v ≤
      (G.bp : ℝ) * (104 / 75 : ℝ) := by
  rw [G.threeModeExpectedResidualCharge_eq_starCharge v]
  apply G.starCharge_le_mul_of_packsStarInto threeModeResidualCharge
    (104 / 75 : ℝ) (G.locallyPacksInto_bp v)
  intro S hload
  exact threeModeResidualCharge_sum_le S (fun e => G.weight e.1)
    (fun e _he => G.weight_pos e.1) hload

/-- The actual residual chosen by the integral selection has harmonic charge
at most `(104/75) bp(G) + 2`. -/
theorem ThreeModeSelectionCertificate.residual_harmonicCharge_le
    (C : G.ThreeModeSelectionCertificate) (v : G.V) :
    G.harmonicChargeOn (G.selectedModeResidualEdges C.label) v ≤
      (104 / 75 : ℝ) * G.bp + 2 := by
  calc
    G.harmonicChargeOn (G.selectedModeResidualEdges C.label) v ≤
        G.threeModeExpectedResidualCharge v + 2 :=
      C.residual_charge_bound v
    _ ≤ (G.bp : ℝ) * (104 / 75 : ℝ) + 2 := by
      gcongr
      exact G.threeModeExpectedResidualCharge_le v
    _ = (104 / 75 : ℝ) * G.bp + 2 := by ring

/-- The same residual bound on the restricted residual graph. -/
theorem ThreeModeSelectionCertificate.residual_graph_harmonicCharge_le
    (C : G.ThreeModeSelectionCertificate) (v : G.V) :
    (G.edgeRestriction (G.selectedModeResidualEdges C.label)).starCharge
        harmonicCharge v ≤ (104 / 75 : ℝ) * G.bp + 2 := by
  rw [G.edgeRestriction_starCharge harmonicCharge
    (G.selectedModeResidualEdges C.label) v]
  exact ThreeModeSelectionCertificate.residual_harmonicCharge_le G C v

end WeightedMultigraph

universe u

/-- The harmonic-charge coloring theorem, together with the finite
three-mode construction, gives the exact bipartite coefficient `81/50`. -/
theorem bipartiteMultigraphBPAsymptotic_of_harmonicChargeColoring
    (hcolor : BipartiteHarmonicChargeColoring.{u}) :
    BipartiteMultigraphBPAsymptotic.{u} := by
  intro ε hε
  obtain ⟨Ncharge, hcharge⟩ := hcolor (ε / 2) (half_pos hε)
  let Nadd : ℕ := Nat.ceil (24 / ε)
  let N : ℕ := max Ncharge Nadd
  refine ⟨N, ?_⟩
  intro G hbip hN
  have hNcharge : Ncharge ≤ G.bp := (le_max_left _ _).trans hN
  have hNadd : Nadd ≤ G.bp := (le_max_right _ _).trans hN
  have hratio : (24 : ℝ) / ε ≤ (G.bp : ℝ) := by
    calc
      (24 : ℝ) / ε ≤ (Nadd : ℝ) := Nat.le_ceil _
      _ ≤ (G.bp : ℝ) := by exact_mod_cast hNadd
  have haddSmall : (12 : ℝ) ≤ (ε / 2) * G.bp := by
    have hmul := (div_le_iff₀ hε).mp hratio
    nlinarith
  rcases hbip with ⟨bip⟩
  obtain ⟨C⟩ := G.exists_threeModeSelectionCertificate bip
  let R : Finset G.E := G.selectedModeResidualEdges C.label
  let H := G.edgeRestriction R
  let A : ℝ := (104 / 75 : ℝ) * G.bp + 2
  have hbipH : H.IsBipartite := by
    apply G.edgeRestriction_isBipartite R
    exact ⟨bip⟩
  have hlocalH : H.LocallyPacksInto G.bp := by
    exact G.edgeRestriction_locallyPacksInto R G.locallyPacksInto_bp
  have hstarH : ∀ v, H.starWeight v ≤ (G.bp : ℝ) := by
    intro v
    exact H.starWeight_le_of_packsStarInto (hlocalH v)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hchargeH : ∀ v, H.starCharge harmonicCharge v ≤ A := by
    intro v
    simpa [H, R, A] using
      WeightedMultigraph.ThreeModeSelectionCertificate.residual_graph_harmonicCharge_le
        G C v
  have hchiH : (H.chiW : ℝ) ≤ A + (ε / 2) * G.bp :=
    hcharge H G.bp A hbipH hNcharge hA hstarH hchargeH
  have hHcolor : H.HasWeightedColoring (H.chiW + 1) :=
    H.hasWeightedColoring_mono (Nat.le_succ _) H.hasWeightedColoring_chiW
  obtain ⟨rightSub, hrightSub⟩ := hHcolor
  have hrpos : 0 < H.chiW + 1 := Nat.succ_pos _
  let right : G.E → Fin (H.chiW + 1) :=
    G.liftRestrictedColor hrpos R rightSub
  have hright : G.IsFeasibleOn R right := by
    exact G.feasibleOn_liftRestrictedColor hrpos R rightSub hrightSub
  obtain ⟨merged, hmerged⟩ := G.merge_feasibleOn
    (G.threeModeSelectedEdges C.label) R C.selected_residual_disjoint
    C.color C.feasible right hright
  have hfull : G.HasWeightedColoring
      (G.threeModeTotalPaletteSize + (H.chiW + 1)) := by
    refine ⟨merged, (G.isWeightedColoring_iff_feasibleOn_univ merged).2 ?_⟩
    rw [← C.cover]
    exact hmerged
  have hchiNat := G.chiW_le_of_hasWeightedColoring hfull
  have hchi : (G.chiW : ℝ) ≤
      (G.threeModeTotalPaletteSize : ℝ) + (H.chiW : ℝ) + 1 := by
    exact_mod_cast hchiNat
  have hselected := G.threeModeTotalPaletteSize_bound
  have hresidual : (H.chiW : ℝ) ≤
      (104 / 75 : ℝ) * G.bp + 2 + (ε / 2) * G.bp := by
    simpa [A] using hchiH
  calc
    (G.chiW : ℝ) ≤
        (G.threeModeTotalPaletteSize : ℝ) + (H.chiW : ℝ) + 1 := hchi
    _ ≤ ((7 / 30 : ℝ) * G.bp + 9) +
          ((104 / 75 : ℝ) * G.bp + 2 + (ε / 2) * G.bp) + 1 := by
      gcongr
    _ = ((81 / 50 : ℝ) + ε / 2) * (G.bp : ℝ) + 12 := by ring
    _ ≤ ((81 / 50 : ℝ) + ε / 2) * (G.bp : ℝ) +
          (ε / 2) * G.bp := by gcongr
    _ = ((81 / 50 : ℝ) + ε) * (G.bp : ℝ) := by ring

end WeightedEdgeColoring
