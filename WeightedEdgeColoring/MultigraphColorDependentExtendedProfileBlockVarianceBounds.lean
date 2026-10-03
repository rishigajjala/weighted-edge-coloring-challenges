import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileBlockVarianceRows
import WeightedEdgeColoring.FiniteCoordinateDependentWordMoments

/-!
# First-moment bounds for colour-dependent block variance
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

local instance : ∀ p : Prop, Decidable p := Classical.propDecidable

/-- Pointwise total-mass estimate for the product coupling. -/
private theorem sum_pairedOption_le_ratio
    {IU IV : Type*} [Fintype IU] [Fintype IV]
    (rho y lambdaU lambdaV kappa : ℝ)
    (aU : IU → ℝ) (aV : IV → ℝ)
    (hrho : 0 ≤ rho) (hy : 0 ≤ y) (hkappa : 0 < kappa)
    (hlambdaU : kappa ≤ lambdaU) (hlambdaV : kappa ≤ lambdaV)
    (haU0 : ∀ i, 0 ≤ aU i) (haV0 : ∀ j, 0 ≤ aV j)
    (haU : ∑ i, aU i ≤ y) (haV : ∑ j, aV j ≤ y) :
    (∑ i, ∑ j, pairedOption rho y (fun _ : Unit ↦ lambdaU)
      (fun _ : Unit ↦ lambdaV) (fun _ ↦ aU) (fun _ ↦ aV)
        () () i j) ≤ rho * y / kappa ^ 2 := by
  by_cases hy0 : y = 0
  · simp [pairedOption, hy0, hkappa.ne']
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hlU : 0 < lambdaU := lt_of_lt_of_le hkappa hlambdaU
  have hlV : 0 < lambdaV := lt_of_lt_of_le hkappa hlambdaV
  have hAU0 : 0 ≤ ∑ i, aU i := Finset.sum_nonneg fun i _hi ↦ haU0 i
  have hAV0 : 0 ≤ ∑ j, aV j := Finset.sum_nonneg fun j _hj ↦ haV0 j
  have hsumUdiv : (∑ i, aU i / lambdaU) = (∑ i, aU i) / lambdaU :=
    by rw [← Finset.sum_div]
  have hsumVdiv : (∑ j, aV j / lambdaV) = (∑ j, aV j) / lambdaV :=
    by rw [← Finset.sum_div]
  have hAU : (∑ i, aU i) / lambdaU ≤ y / kappa :=
    (div_le_div_of_nonneg_right haU hlU.le).trans
      (div_le_div_of_nonneg_left hy hkappa hlambdaU)
  have hAV : (∑ j, aV j) / lambdaV ≤ y / kappa :=
    (div_le_div_of_nonneg_right haV hlV.le).trans
      (div_le_div_of_nonneg_left hy hkappa hlambdaV)
  have hratio0 : 0 ≤ rho / y := div_nonneg hrho hy
  have hyk0 : 0 ≤ y / kappa := div_nonneg hy hkappa.le
  have hprod :
      ((∑ i, aU i) / lambdaU) * ((∑ j, aV j) / lambdaV) ≤
        (y / kappa) * (y / kappa) :=
    mul_le_mul hAU hAV (div_nonneg hAV0 hlV.le) hyk0
  calc
    (∑ i, ∑ j, pairedOption rho y (fun _ : Unit ↦ lambdaU)
      (fun _ : Unit ↦ lambdaV) (fun _ ↦ aU) (fun _ ↦ aV)
        () () i j) =
      (rho / y) * (((∑ i, aU i) / lambdaU) *
        ((∑ j, aV j) / lambdaV)) := by
      simp only [pairedOption, if_neg hy0]
      calc
        (∑ i, ∑ j,
          rho * aU i * aV j / (y * lambdaU * lambdaV)) =
            ∑ i, ∑ j,
              (rho / y) * (aU i / lambdaU) * (aV j / lambdaV) := by
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro j _hj
          field_simp [hy0, hlU.ne', hlV.ne']
        _ = ∑ i, ((rho / y) * (aU i / lambdaU)) *
              ((∑ j, aV j) / lambdaV) := by
          apply Finset.sum_congr rfl
          intro i _hi
          calc
            (∑ j, (rho / y) * (aU i / lambdaU) *
                (aV j / lambdaV)) =
                (rho / y) * (aU i / lambdaU) *
                  (∑ j, aV j / lambdaV) := by
              rw [Finset.mul_sum]
            _ = (rho / y) * (aU i / lambdaU) *
                  ((∑ j, aV j) / lambdaV) := by
              rw [Finset.sum_div]
        _ = (rho / y) * (((∑ i, aU i) / lambdaU) *
              ((∑ j, aV j) / lambdaV)) := by
          calc
            (∑ i, (rho / y) * (aU i / lambdaU) *
                ((∑ j, aV j) / lambdaV)) =
                ∑ i, (rho / y) *
                  ((aU i / lambdaU) * ((∑ j, aV j) / lambdaV)) := by
              apply Finset.sum_congr rfl
              intro i _hi
              ring
            _ = (rho / y) *
                (∑ i, (aU i / lambdaU) *
                  ((∑ j, aV j) / lambdaV)) := by
              rw [Finset.mul_sum]
            _ = (rho / y) *
                ((∑ i, aU i / lambdaU) *
                  ((∑ j, aV j) / lambdaV)) := by
              rw [Finset.sum_mul]
            _ = (rho / y) * (((∑ i, aU i) / lambdaU) *
                  ((∑ j, aV j) / lambdaV)) := by
              rw [hsumUdiv]
    _ ≤ (rho / y) * ((y / kappa) * (y / kappa)) :=
      mul_le_mul_of_nonneg_left hprod hratio0
    _ = rho * y / kappa ^ 2 := by
      field_simp [hy0, hkappa.ne']

theorem colorDependentLarge_add_tinyEdgeColorMass
    (e : G.E) (c : Fin B × Fin k) :
    G.colorDependentExtendedProfileLargeEdgeColorMass
        (s := s) (β := β) proposal e c +
      G.colorDependentExtendedProfileTinyEdgeColorMass
        (s := s) (β := β) proposal e c = s * proposal e c := by
  unfold colorDependentExtendedProfileLargeEdgeColorMass
    colorDependentExtendedProfileTinyEdgeColorMass
  by_cases h : β ≤ G.weight e
  · simp [h, not_lt.mpr h]
  · have h' : G.weight e < β := lt_of_not_ge h
    simp [h, h']

/-- Diffuseness and smoothing give a uniform `O(1/n)` envelope for one
colour's complete raw option mass. -/
theorem colorDependentCoordinateOptionMass_le_two_scale_div_n
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (e : G.E) (c : Fin B × Fin k)
    (P : G.ColorDependentExtendedProfileState R (G.fst e) c)
    (Q : G.ColorDependentExtendedProfileState R (G.snd e) c) :
    G.colorDependentCoordinateOptionMass proposal R rho omega e c P Q ≤
      2 * colorDependentCandidateCapacityScale
        rho s omega β q r C0 / n := by
  let M : ℝ := extendedProfileStateBound β q r
  let kappa : ℝ := omega / M
  have hM : 0 < M := by
    unfold M extendedProfileStateBound profileStateBound
    positivity
  have hkappa : 0 < kappa := div_pos homega0 hM
  have hlamP : kappa ≤
      G.smoothedColorDependentExtendedProfileProbability
        R omega (G.fst e) c P :=
    G.omega_div_stateBound_le_smoothedColorDependentProbability R
      hs hq hr0 hleft homega0 homega1 (G.fst e) c P
  have hlamQ : kappa ≤
      G.smoothedColorDependentExtendedProfileProbability
        R omega (G.snd e) c Q :=
    G.omega_div_stateBound_le_smoothedColorDependentProbability R
      hs hq hr0 hleft homega0 homega1 (G.snd e) c Q
  let yl := G.colorDependentExtendedProfileLargeEdgeColorMass
    (s := s) (β := β) proposal e c
  let yt := G.colorDependentExtendedProfileTinyEdgeColorMass
    (s := s) (β := β) proposal e c
  have hyl0 : 0 ≤ yl :=
    G.colorDependentExtendedProfileLargeEdgeColorMass_nonneg proposal R e c
  have hyt0 : 0 ≤ yt :=
    G.colorDependentExtendedProfileTinyEdgeColorMass_nonneg proposal R e c
  have hylCap : yl ≤ s * C0 / n := by
    unfold yl colorDependentExtendedProfileLargeEdgeColorMass
    split
    · calc
        s * proposal e c ≤ s * (C0 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (hproposal e c) hs
        _ = s * C0 / n := by ring
    · exact div_nonneg (mul_nonneg hs hC0) (Nat.cast_nonneg n)
  have hytCap : yt ≤ s * C0 / n := by
    unfold yt colorDependentExtendedProfileTinyEdgeColorMass
    split
    · calc
        s * proposal e c ≤ s * (C0 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (hproposal e c) hs
        _ = s * C0 / n := by ring
    · exact div_nonneg (mul_nonneg hs hC0) (Nat.cast_nonneg n)
  have hlarge :
      (∑ i, ∑ j, G.colorDependentExtendedProfileLargeProductMass
        proposal R rho omega e c P Q i j) ≤ rho * yl / kappa ^ 2 := by
    simpa [colorDependentExtendedProfileLargeProductMass, yl] using
      sum_pairedOption_le_ratio rho yl
        (G.smoothedColorDependentExtendedProfileProbability
          R omega (G.fst e) c P)
        (G.smoothedColorDependentExtendedProfileProbability
          R omega (G.snd e) c Q) kappa
        (G.colorDependentExtendedProfileLargeAssign R
          (G.fst e) c (G.fstStarEdge e) P)
        (G.colorDependentExtendedProfileLargeAssign R
          (G.snd e) c (G.sndStarEdge e) Q)
        hrho hyl0 hkappa hlamP hlamQ
        (fun i ↦ G.colorDependentExtendedProfileLargeAssign_nonneg
          R (G.fst e) c (G.fstStarEdge e) P i)
        (fun j ↦ G.colorDependentExtendedProfileLargeAssign_nonneg
          R (G.snd e) c (G.sndStarEdge e) Q j)
        (G.sum_colorDependentExtendedProfileLargeAssign_le_edgeColorMass
          proposal R (G.fst e) c (G.fstStarEdge e) P)
        (G.sum_colorDependentExtendedProfileLargeAssign_le_edgeColorMass
          proposal R (G.snd e) c (G.sndStarEdge e) Q)
  have htiny :
      G.colorDependentExtendedProfileTinyProductMass
        proposal R rho omega e c P Q ≤ rho * yt / kappa ^ 2 := by
    have h := sum_pairedOption_le_ratio (IU := Fin 1) (IV := Fin 1)
      rho yt
      (G.smoothedColorDependentExtendedProfileProbability
        R omega (G.fst e) c P)
      (G.smoothedColorDependentExtendedProfileProbability
        R omega (G.snd e) c Q) kappa
      (fun _ ↦ G.colorDependentExtendedProfileTinyAssign
        R (G.fst e) c (G.fstStarEdge e) P)
      (fun _ ↦ G.colorDependentExtendedProfileTinyAssign
        R (G.snd e) c (G.sndStarEdge e) Q)
      hrho hyt0 hkappa hlamP hlamQ
      (fun _ ↦ G.colorDependentExtendedProfileTinyAssign_nonneg
        R (G.fst e) c (G.fstStarEdge e) P)
      (fun _ ↦ G.colorDependentExtendedProfileTinyAssign_nonneg
        R (G.snd e) c (G.sndStarEdge e) Q)
      (by
        simpa using
          (G.colorDependentExtendedProfileTinyAssign_le_edgeColorMass
            proposal R (G.fst e) c (G.fstStarEdge e) P))
      (by
        simpa using
          (G.colorDependentExtendedProfileTinyAssign_le_edgeColorMass
            proposal R (G.snd e) c (G.sndStarEdge e) Q))
    simpa [colorDependentExtendedProfileTinyProductMass, yt] using h
  have hlargeCap : rho * yl / kappa ^ 2 ≤
      colorDependentCandidateCapacityScale rho s omega β q r C0 / n := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    unfold colorDependentCandidateCapacityScale
    dsimp [kappa, M]
    calc
      rho * yl / (omega / extendedProfileStateBound β q r) ^ 2 ≤
          rho * (s * C0 / n) /
            (omega / extendedProfileStateBound β q r) ^ 2 := by gcongr
      _ = rho * s * C0 *
          ((extendedProfileStateBound β q r : ℝ) / omega) ^ 2 / n := by
            field_simp
  have htinyCap : rho * yt / kappa ^ 2 ≤
      colorDependentCandidateCapacityScale rho s omega β q r C0 / n := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    unfold colorDependentCandidateCapacityScale
    dsimp [kappa, M]
    calc
      rho * yt / (omega / extendedProfileStateBound β q r) ^ 2 ≤
          rho * (s * C0 / n) /
            (omega / extendedProfileStateBound β q r) ^ 2 := by gcongr
      _ = rho * s * C0 *
          ((extendedProfileStateBound β q r : ℝ) / omega) ^ 2 / n := by
            field_simp
  unfold colorDependentCoordinateOptionMass
  calc
    _ ≤ rho * yl / kappa ^ 2 + rho * yt / kappa ^ 2 :=
      add_le_add hlarge htiny
    _ ≤ colorDependentCandidateCapacityScale
          rho s omega β q r C0 / n +
        colorDependentCandidateCapacityScale
          rho s omega β q r C0 / n :=
      add_le_add hlargeCap htinyCap
    _ = 2 * colorDependentCandidateCapacityScale
          rho s omega β q r C0 / n := by ring

def colorDependentBlockOptionUpper
    (n k : ℕ) (rho s omega β q r C0 : ℝ) : ℝ :=
  (k : ℝ) *
    (2 * colorDependentCandidateCapacityScale rho s omega β q r C0 / n)

def colorDependentBlockTargetUpper
    (n k : ℕ) (rho s C0 : ℝ) : ℝ :=
  rho * s * (k : ℝ) * C0 / n

def colorDependentBlockVariancePairScale
    (n k : ℕ) (rho s omega β q r C0 : ℝ) : ℝ :=
  (colorDependentBlockOptionUpper n k rho s omega β q r C0 +
    colorDependentBlockTargetUpper n k rho s C0) ^ 2

theorem colorDependentBlockVariancePairScale_pos
    (hn : 0 < n) (hk : 0 < k) (hrho : 0 < rho)
    (hs : 0 < s) (homega : 0 < omega) (hC0 : 0 < C0) :
    0 < colorDependentBlockVariancePairScale
      n k rho s omega β q r C0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hscale : 0 <
      colorDependentCandidateCapacityScale rho s omega β q r C0 :=
    colorDependentCandidateCapacityScale_pos hrho hs hC0 homega
  unfold colorDependentBlockVariancePairScale
    colorDependentBlockOptionUpper colorDependentBlockTargetUpper
  positivity

/-- The natural normalization of a self row.  A conditional block row is at
most `n * pairScale`, so this normalization makes every self coefficient at
most one. -/
def colorDependentBlockVarianceSelfScale
    (n k : ℕ) (rho s omega β q r C0 : ℝ) : ℝ :=
  (n : ℝ) * colorDependentBlockVariancePairScale
    n k rho s omega β q r C0

theorem colorDependentBlockVariance_le_weight_mul_pairScale
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (e : G.E) (b : Fin B)
    (left right : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) :
    G.colorDependentBlockVariance proposal R rho omega e b left right ≤
      G.weight e * colorDependentBlockVariancePairScale
        n k rho s omega β q r C0 := by
  let X := G.colorDependentBlockOptionMass proposal R rho omega e b left right
  let T := G.colorDependentBlockTarget proposal rho s e b
  let U := colorDependentBlockOptionUpper n k rho s omega β q r C0
  let V := colorDependentBlockTargetUpper n k rho s C0
  have hX0 : 0 ≤ X := by
    unfold X colorDependentBlockOptionMass
    exact Finset.sum_nonneg fun i _hi ↦ by
      unfold colorDependentCoordinateOptionMass
      exact add_nonneg
        (Finset.sum_nonneg fun i _hi ↦ Finset.sum_nonneg fun j _hj ↦
          G.colorDependentExtendedProfileLargeProductMass_nonneg
            proposal R hs hq hr0 hleft homega0 homega1 hrho _ _ _ _ _ _)
        (G.colorDependentExtendedProfileTinyProductMass_nonneg
          proposal R hs hq hr0 hleft homega0 homega1 hrho _ _ _ _)
  have hXU : X ≤ U := by
    unfold X U colorDependentBlockOptionMass colorDependentBlockOptionUpper
    calc
      (∑ i : Fin k, _) ≤ ∑ _i : Fin k,
          2 * colorDependentCandidateCapacityScale
            rho s omega β q r C0 / n := by
        apply Finset.sum_le_sum
        intro i _hi
        exact G.colorDependentCoordinateOptionMass_le_two_scale_div_n
          proposal R hn hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
          hproposal0 hproposal e (b, i) _ _
      _ = _ := by simp
  have hT0 : 0 ≤ T := by
    unfold T colorDependentBlockTarget
    exact mul_nonneg (mul_nonneg hrho hs)
      (Finset.sum_nonneg fun i _hi ↦ hproposal0 e (b, i))
  have hTV : T ≤ V := by
    unfold T V colorDependentBlockTarget colorDependentBlockTargetUpper
    have hsum : (∑ i : Fin k, proposal e (b, i)) ≤
        (k : ℝ) * (C0 / n) := by
      calc
        _ ≤ ∑ _i : Fin k, C0 / (n : ℝ) :=
          Finset.sum_le_sum fun i _hi ↦ hproposal e (b, i)
        _ = _ := by simp
    calc
      rho * s * ∑ i : Fin k, proposal e (b, i) ≤
          rho * s * ((k : ℝ) * (C0 / n)) := by gcongr
      _ = rho * s * (k : ℝ) * C0 / n := by ring
  have hsquare : (X - T) ^ 2 ≤ (U + V) ^ 2 := by
    have hU0 : 0 ≤ U := hX0.trans hXU
    have hV0 : 0 ≤ V := hT0.trans hTV
    nlinarith
  unfold colorDependentBlockVariance colorDependentBlockVariancePairScale
  exact mul_le_mul_of_nonneg_left hsquare (G.weight_nonneg e)

private theorem colorDependentBlockVarianceCandidateEdgeUse_eq_zero_of_not_matches
    (rho omega : ℝ) (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r))
    (e : G.E)
    (row : G.ColorDependentBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r))
    (h : ¬(source.2 = row.2.1 ∧
      G.ColorDependentCandidateEdgeMatches row.1 source.1 e)) :
    G.colorDependentBlockVarianceCandidateEdgeUse proposal R rho omega
      source sourceCode e row = 0 := by
  unfold colorDependentBlockVarianceCandidateEdgeUse
  by_cases hb : source.2 = row.2.1
  · rw [if_pos hb]
    have hm : ¬G.ColorDependentCandidateEdgeMatches row.1 source.1 e :=
      fun hm ↦ h ⟨hb, hm⟩
    rcases not_or.mp hm with ⟨hfst, hsnd⟩
    simp [ColorDependentCandidateEdgeMatches, hfst, hsnd]
  · simp [hb]

private theorem colorDependentBlockVarianceCandidateEdgeUse_le_pairScale
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r))
    (e : G.E)
    (row : G.ColorDependentBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    G.colorDependentBlockVarianceCandidateEdgeUse proposal R rho omega
        source sourceCode e row ≤
      colorDependentBlockVariancePairScale
        n k rho s omega β q r C0 := by
  classical
  let pairScale := colorDependentBlockVariancePairScale
    n k rho s omega β q r C0
  by_cases hblock : source.2 = row.2.1
  · by_cases hmatch : G.ColorDependentCandidateEdgeMatches row.1 source.1 e
    · have hweight :
          G.colorDependentBlockVarianceCandidateEdgeUse proposal R rho omega
              source sourceCode e row ≤ G.weight e * pairScale := by
        rcases hmatch with hedge | hedge
        · rw [colorDependentBlockVarianceCandidateEdgeUse,
            if_pos hblock, if_pos ⟨hedge.1, hedge.2⟩]
          exact G.colorDependentBlockVariance_le_weight_mul_pairScale
            proposal R hn hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
            hproposal0 hproposal e row.2.1 _ _
        · have hnot : ¬(row.1 = G.fst e ∧ source.1 = G.snd e) := by
            intro hfirst
            exact G.noLoop e (hfirst.1.symm.trans hedge.1)
          rw [colorDependentBlockVarianceCandidateEdgeUse,
            if_pos hblock, if_neg hnot, if_pos ⟨hedge.1, hedge.2⟩]
          exact G.colorDependentBlockVariance_le_weight_mul_pairScale
            proposal R hn hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
            hproposal0 hproposal e row.2.1 _ _
      exact hweight.trans
        (mul_le_of_le_one_left (sq_nonneg _) (G.weight_le_one e))
    · rw [G.colorDependentBlockVarianceCandidateEdgeUse_eq_zero_of_not_matches
        proposal R rho omega source sourceCode e row
          (not_and_or.mpr (Or.inr hmatch))]
      exact sq_nonneg _
  · rw [colorDependentBlockVarianceCandidateEdgeUse, if_neg hblock]
    exact sq_nonneg _

/-- Fixed endpoint multiplicity enlarges the candidate pair scale by `L`. -/
theorem rawColorDependentBlockVarianceCandidateUse_le_mul_pairScale
    {L : ℕ} (hmult : G.PairMultiplicityAtMost L)
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r))
    (row : G.ColorDependentBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    G.rawColorDependentBlockVarianceCandidateUse proposal R rho omega
        source sourceCode row ≤
      (L : ℝ) * colorDependentBlockVariancePairScale
        n k rho s omega β q r C0 := by
  unfold rawColorDependentBlockVarianceCandidateUse
  apply G.sum_le_mul_of_pairMultiplicityAtMost hmult row.1 source.1
  · exact sq_nonneg _
  · intro e he
    exact G.colorDependentBlockVarianceCandidateEdgeUse_le_pairScale proposal R
      hn hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
      hproposal0 hproposal source sourceCode e row
  · intro e he
    apply G.colorDependentBlockVarianceCandidateEdgeUse_eq_zero_of_not_matches
      proposal R
    exact not_and_or.mpr (Or.inr he)

private theorem colorDependentBlockVarianceCandidateEdgeUse_div_pairScale_le
    (hn : 0 < n) (hk : 0 < k)
    (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r))
    (e : G.E)
    (row : G.ColorDependentBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    G.colorDependentBlockVarianceCandidateEdgeUse proposal R rho omega
        source sourceCode e row /
          colorDependentBlockVariancePairScale
            n k rho s omega β q r C0 ≤
      if source.2 = row.2.1 ∧
          G.ColorDependentCandidateEdgeMatches row.1 source.1 e then
        G.weight e else 0 := by
  classical
  let pairScale := colorDependentBlockVariancePairScale
    n k rho s omega β q r C0
  have hpair : 0 < pairScale :=
    colorDependentBlockVariancePairScale_pos hn hk hrho hs homega0 hC0
  by_cases hblock : source.2 = row.2.1
  · by_cases hmatch : G.ColorDependentCandidateEdgeMatches row.1 source.1 e
    · rw [if_pos ⟨hblock, hmatch⟩]
      rcases hmatch with hmatch | hmatch
      · simp [colorDependentBlockVarianceCandidateEdgeUse, hblock,
          hmatch.1, hmatch.2, pairScale]
        apply (div_le_iff₀ hpair).2
        simpa [mul_comm] using
          G.colorDependentBlockVariance_le_weight_mul_pairScale proposal R
            hn hs.le hq hr0 hleft homega0 homega1 rho C0 hrho.le hC0.le
            hproposal0 hproposal e _ _ _
      · have hnotFirst :
            ¬(row.1 = G.fst e ∧ source.1 = G.snd e) := by
          intro hfirst
          exact G.noLoop e (hfirst.1.symm.trans hmatch.1)
        rw [colorDependentBlockVarianceCandidateEdgeUse,
          if_pos hblock, if_neg hnotFirst,
          if_pos ⟨hmatch.1, hmatch.2⟩]
        apply (div_le_iff₀ hpair).2
        simpa [mul_comm] using
          G.colorDependentBlockVariance_le_weight_mul_pairScale proposal R
            hn hs.le hq hr0 hleft homega0 homega1 rho C0 hrho.le hC0.le
            hproposal0 hproposal e _ _ _
    · rw [if_neg (not_and_or.mpr (Or.inr hmatch))]
      rw [G.colorDependentBlockVarianceCandidateEdgeUse_eq_zero_of_not_matches
        proposal R rho omega source sourceCode e row
          (not_and_or.mpr (Or.inr hmatch))]
      simp
  · rw [if_neg (not_and_or.mpr (Or.inl hblock))]
    simp [colorDependentBlockVarianceCandidateEdgeUse, hblock]

private theorem sum_colorDependentBlockVarianceCandidateRows_edge_le
    (hn : 0 < n) (hk : 0 < k)
    (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) (e : G.E) :
    (∑ row : G.ColorDependentBlockVarianceCandidateRow
        (B := B) (k := k) (β := β) (q := q) (r := r),
      G.colorDependentBlockVarianceCandidateEdgeUse proposal R rho omega
        source sourceCode e row /
          colorDependentBlockVariancePairScale
            n k rho s omega β q r C0) ≤
      if G.Inc source.1 e then
        (extendedProfileStateBound β q r : ℝ) ^ k * G.weight e
      else 0 := by
  classical
  calc
    _ ≤ ∑ row : G.ColorDependentBlockVarianceCandidateRow
          (B := B) (k := k) (β := β) (q := q) (r := r),
        if source.2 = row.2.1 ∧
            G.ColorDependentCandidateEdgeMatches row.1 source.1 e then
          G.weight e else 0 :=
      Finset.sum_le_sum fun row _hrow ↦
        G.colorDependentBlockVarianceCandidateEdgeUse_div_pairScale_le
          proposal R hn hk hs hq hr0 hleft homega0 homega1 rho C0
          hrho hC0 hproposal0 hproposal source sourceCode e row
    _ = if G.Inc source.1 e then
        (extendedProfileStateBound β q r : ℝ) ^ k * G.weight e
      else 0 := by
      simp only [Fintype.sum_prod_type]
      by_cases hfst : source.1 = G.fst e
      · have hne : G.fst e ≠ G.snd e := G.noLoop e
        simp [ColorDependentCandidateEdgeMatches, WeightedMultigraph.Inc,
          hne, hfst, FiniteDependentWordPadding.packedWordState_card,
          ite_and]
      · by_cases hsnd : source.1 = G.snd e
        · have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
          simp [ColorDependentCandidateEdgeMatches, WeightedMultigraph.Inc,
            hfst, hsnd, hne,
            FiniteDependentWordPadding.packedWordState_card, ite_and]
        · have hinc : ¬G.Inc source.1 e := by
            intro h
            rcases h with h | h
            · exact hfst h.symm
            · exact hsnd h.symm
          simp [ColorDependentCandidateEdgeMatches, hfst, hsnd, hinc,
            ite_and]

/-- The candidate part of the variance column has no dependence on the
number of vertices.  Simplicity leaves at most one edge for each center,
and each possible center code costs its incident edge weight. -/
theorem sum_scaledColorDependentBlockVarianceCandidateUse_le_column
    (hn : 0 < n) (hk : 0 < k)
    (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) :
    (∑ row : G.ColorDependentBlockVarianceCandidateRow
        (B := B) (k := k) (β := β) (q := q) (r := r),
      G.scaledColorDependentBlockVarianceCandidateUse proposal R rho omega
        (colorDependentBlockVariancePairScale
          n k rho s omega β q r C0) source sourceCode row) ≤
      (extendedProfileStateBound β q r : ℝ) ^ k * n := by
  unfold scaledColorDependentBlockVarianceCandidateUse
    rawColorDependentBlockVarianceCandidateUse
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ e : G.E, if G.Inc source.1 e then
          (extendedProfileStateBound β q r : ℝ) ^ k * G.weight e
        else 0 :=
      Finset.sum_le_sum fun e _he ↦
        G.sum_colorDependentBlockVarianceCandidateRows_edge_le proposal R
          hn hk hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
          hproposal0 hproposal source sourceCode e
    _ = (extendedProfileStateBound β q r : ℝ) ^ k *
        G.starWeight source.1 := by
      calc
        (∑ e : G.E, if G.Inc source.1 e then
          (extendedProfileStateBound β q r : ℝ) ^ k * G.weight e
          else 0) =
            ∑ e ∈ Finset.univ.filter (G.Inc source.1),
              (extendedProfileStateBound β q r : ℝ) ^ k *
                G.weight e := by rw [Finset.sum_filter]
        _ = ∑ e : G.StarEdge source.1,
              (extendedProfileStateBound β q r : ℝ) ^ k *
                G.weight e.1 := by
          exact Finset.sum_subtype (Finset.univ.filter (G.Inc source.1))
            (by intro e; simp)
            (fun e ↦ (extendedProfileStateBound β q r : ℝ) ^ k *
              G.weight e)
        _ = (extendedProfileStateBound β q r : ℝ) ^ k *
              G.starWeight source.1 := by
          unfold starWeight
          rw [Finset.mul_sum]
    _ ≤ (extendedProfileStateBound β q r : ℝ) ^ k * n := by
      exact mul_le_mul_of_nonneg_left (hstar source.1) (by positivity)

/-- Multiplicity scaling only decreases each normalized candidate-variance
column, so the simple column bound is unchanged. -/
theorem sum_scaledColorDependentBlockVarianceCandidateUse_mul_le_column
    {L : ℕ} (hL : 0 < L)
    (hn : 0 < n) (hk : 0 < k)
    (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) :
    (∑ row : G.ColorDependentBlockVarianceCandidateRow
        (B := B) (k := k) (β := β) (q := q) (r := r),
      G.scaledColorDependentBlockVarianceCandidateUse proposal R rho omega
        ((L : ℝ) * colorDependentBlockVariancePairScale
          n k rho s omega β q r C0) source sourceCode row) ≤
      (extendedProfileStateBound β q r : ℝ) ^ k * n := by
  let baseScale := colorDependentBlockVariancePairScale
    n k rho s omega β q r C0
  have hbase : 0 < baseScale :=
    colorDependentBlockVariancePairScale_pos hn hk hrho hs homega0 hC0
  have hscaled : 0 < (L : ℝ) * baseScale := by positivity
  have hbaseScaled : baseScale ≤ (L : ℝ) * baseScale := by
    have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith [hbase.le]
  calc
    _ ≤ ∑ row : G.ColorDependentBlockVarianceCandidateRow
          (B := B) (k := k) (β := β) (q := q) (r := r),
        G.scaledColorDependentBlockVarianceCandidateUse proposal R rho omega
          baseScale source sourceCode row := by
      apply Finset.sum_le_sum
      intro row _hrow
      unfold scaledColorDependentBlockVarianceCandidateUse
      exact div_le_div_of_nonneg_left
        (G.rawColorDependentBlockVarianceCandidateUse_nonneg
          proposal R rho omega source sourceCode row) hbase hbaseScaled
    _ ≤ _ := G.sum_scaledColorDependentBlockVarianceCandidateUse_le_column
      proposal R hn hk hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
      hproposal0 hproposal hstar source sourceCode

theorem conditionalColorDependentBlockVariance_eq_edge_sum
    (rho omega : ℝ) (v : G.V) (b : Fin B)
    (centerCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) :
    G.conditionalColorDependentBlockVariance proposal R rho omega
        (v, b, centerCode) =
      ∑ e : G.E,
        if v = G.fst e then
          ∑ oppositeCode,
            G.paddedColorDependentExtendedProfileBlockProbability
                proposal R omega (G.snd e, b) oppositeCode *
              G.colorDependentBlockVariance proposal R rho omega e b
                centerCode oppositeCode
        else if v = G.snd e then
          ∑ oppositeCode,
            G.paddedColorDependentExtendedProfileBlockProbability
                proposal R omega (G.fst e, b) oppositeCode *
              G.colorDependentBlockVariance proposal R rho omega e b
                oppositeCode centerCode
        else 0 := by
  classical
  unfold conditionalColorDependentBlockVariance
    FiniteCategoricalSelection.rowMean
    rawColorDependentBlockVarianceCandidateUse
  simp_rw [Finset.mul_sum]
  calc
    (∑ source : G.V × Fin B,
      ∑ sourceCode,
        ∑ e : G.E,
          G.paddedColorDependentExtendedProfileBlockProbability
              proposal R omega source sourceCode *
            G.colorDependentBlockVarianceCandidateEdgeUse proposal R rho omega
              source sourceCode e (v, b, centerCode)) =
      ∑ source : G.V × Fin B, ∑ e : G.E, ∑ sourceCode,
        G.paddedColorDependentExtendedProfileBlockProbability
            proposal R omega source sourceCode *
          G.colorDependentBlockVarianceCandidateEdgeUse proposal R rho omega
            source sourceCode e (v, b, centerCode) := by
      apply Finset.sum_congr rfl
      intro source _hsource
      rw [Finset.sum_comm]
    _ = ∑ e : G.E, ∑ source : G.V × Fin B, ∑ sourceCode,
        G.paddedColorDependentExtendedProfileBlockProbability
            proposal R omega source sourceCode *
          G.colorDependentBlockVarianceCandidateEdgeUse proposal R rho omega
            source sourceCode e (v, b, centerCode) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [Fintype.sum_prod_type]
      by_cases hfst : v = G.fst e
      · subst v
        have hne : G.fst e ≠ G.snd e := G.noLoop e
        simp [colorDependentBlockVarianceCandidateEdgeUse, hne]
      · by_cases hsnd : v = G.snd e
        · subst v
          have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
          simp [colorDependentBlockVarianceCandidateEdgeUse, hfst, hne]
        · simp [colorDependentBlockVarianceCandidateEdgeUse, hfst, hsnd]

theorem conditionalColorDependentBlockVariance_le_n_mul_pairScale
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (row : G.ColorDependentBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    G.conditionalColorDependentBlockVariance proposal R rho omega row ≤
      n * colorDependentBlockVariancePairScale
        n k rho s omega β q r C0 := by
  rcases row with ⟨v, b, centerCode⟩
  rw [G.conditionalColorDependentBlockVariance_eq_edge_sum
    proposal R rho omega v b centerCode]
  let pairScale := colorDependentBlockVariancePairScale
    n k rho s omega β q r C0
  have hpair0 : 0 ≤ pairScale := sq_nonneg _
  have hedge : ∀ e : G.E,
      (if v = G.fst e then
        ∑ oppositeCode,
          G.paddedColorDependentExtendedProfileBlockProbability
              proposal R omega (G.snd e, b) oppositeCode *
            G.colorDependentBlockVariance proposal R rho omega e b
              centerCode oppositeCode
      else if v = G.snd e then
        ∑ oppositeCode,
          G.paddedColorDependentExtendedProfileBlockProbability
              proposal R omega (G.fst e, b) oppositeCode *
            G.colorDependentBlockVariance proposal R rho omega e b
              oppositeCode centerCode
      else 0) ≤ if G.Inc v e then G.weight e * pairScale else 0 := by
    intro e
    by_cases hfst : v = G.fst e
    · subst v
      simp only [eq_self, if_true, WeightedMultigraph.Inc, true_or]
      calc
        _ ≤ ∑ oppositeCode,
            G.paddedColorDependentExtendedProfileBlockProbability
                proposal R omega (G.snd e, b) oppositeCode *
              (G.weight e * pairScale) := by
          apply Finset.sum_le_sum
          intro a _ha
          exact mul_le_mul_of_nonneg_left
            (G.colorDependentBlockVariance_le_weight_mul_pairScale
              proposal R hn hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
              hproposal0 hproposal e b centerCode a)
            (G.paddedColorDependentExtendedProfileBlockProbability_nonneg
              proposal R hs hq hr0 hleft homega0 homega1 _ _)
        _ = G.weight e * pairScale := by
          rw [← Finset.sum_mul,
            G.sum_paddedColorDependentExtendedProfileBlockProbability]
          ring
    · by_cases hsnd : v = G.snd e
      · subst v
        have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
        simp only [hfst, if_false, eq_self, if_true,
          WeightedMultigraph.Inc, or_true]
        calc
          _ ≤ ∑ oppositeCode,
              G.paddedColorDependentExtendedProfileBlockProbability
                  proposal R omega (G.fst e, b) oppositeCode *
                (G.weight e * pairScale) := by
            apply Finset.sum_le_sum
            intro a _ha
            exact mul_le_mul_of_nonneg_left
              (G.colorDependentBlockVariance_le_weight_mul_pairScale
                proposal R hn hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
                hproposal0 hproposal e b a centerCode)
              (G.paddedColorDependentExtendedProfileBlockProbability_nonneg
                proposal R hs hq hr0 hleft homega0 homega1 _ _)
          _ = G.weight e * pairScale := by
            rw [← Finset.sum_mul,
              G.sum_paddedColorDependentExtendedProfileBlockProbability]
            ring
      · have hinc : ¬G.Inc v e := by
          intro h
          rcases h with h | h
          · exact hfst h.symm
          · exact hsnd h.symm
        simp [hfst, hsnd, hinc]
  calc
    _ ≤ ∑ e : G.E, if G.Inc v e then G.weight e * pairScale else 0 :=
      Finset.sum_le_sum fun e _he ↦ hedge e
    _ = pairScale * G.starWeight v := by
      calc
        (∑ e : G.E, if G.Inc v e then G.weight e * pairScale else 0) =
            ∑ e ∈ Finset.univ.filter (G.Inc v),
              G.weight e * pairScale := by rw [Finset.sum_filter]
        _ = ∑ e : G.StarEdge v, G.weight e.1 * pairScale := by
          exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
            (by intro e; simp) (fun e ↦ G.weight e * pairScale)
        _ = pairScale * G.starWeight v := by
          unfold starWeight
          rw [← Finset.sum_mul]
          ring
    _ ≤ pairScale * n := mul_le_mul_of_nonneg_left (hstar v) hpair0
    _ = n * pairScale := by ring

theorem sum_scaledColorDependentBlockVarianceSelfUse_le_one
    (hn : 0 < n) (hk : 0 < k)
    (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) :
    (∑ v, G.scaledColorDependentBlockVarianceSelfUse proposal R rho omega
      (colorDependentBlockVarianceSelfScale
        n k rho s omega β q r C0) source sourceCode v) ≤ 1 := by
  let pairScale := colorDependentBlockVariancePairScale
    n k rho s omega β q r C0
  have hpair : 0 < pairScale :=
    colorDependentBlockVariancePairScale_pos hn hk hrho hs homega0 hC0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Finset.sum_eq_single source.1]
  · unfold scaledColorDependentBlockVarianceSelfUse
    rw [if_pos rfl]
    apply (div_le_one (mul_pos hnR hpair)).2
    exact G.conditionalColorDependentBlockVariance_le_n_mul_pairScale
      proposal R hn hs.le hq hr0 hleft homega0 homega1 rho C0 hrho.le
      hC0.le hproposal0 hproposal hstar (source.1, source.2, sourceCode)
  · intro v _hv hv
    simp [scaledColorDependentBlockVarianceSelfUse, hv, Ne.symm hv]
  · simp

/-- Multiplicity scaling of the self normalization decreases its column. -/
theorem sum_scaledColorDependentBlockVarianceSelfUse_mul_le_one
    {L : ℕ} (hL : 0 < L)
    (hn : 0 < n) (hk : 0 < k)
    (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) :
    (∑ v, G.scaledColorDependentBlockVarianceSelfUse proposal R rho omega
      ((L : ℝ) * colorDependentBlockVarianceSelfScale
        n k rho s omega β q r C0) source sourceCode v) ≤ 1 := by
  let baseScale := colorDependentBlockVarianceSelfScale
    n k rho s omega β q r C0
  have hbase : 0 < baseScale := by
    unfold baseScale colorDependentBlockVarianceSelfScale
    exact mul_pos (by exact_mod_cast hn)
      (colorDependentBlockVariancePairScale_pos
        hn hk hrho hs homega0 hC0)
  have hbaseScaled : baseScale ≤ (L : ℝ) * baseScale := by
    have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith [hbase.le]
  calc
    _ ≤ ∑ v, G.scaledColorDependentBlockVarianceSelfUse proposal R rho omega
          baseScale source sourceCode v := by
      apply Finset.sum_le_sum
      intro v _hv
      unfold scaledColorDependentBlockVarianceSelfUse
      split
      · exact div_le_div_of_nonneg_left
          (G.conditionalColorDependentBlockVariance_nonneg proposal R rho omega
            (G.paddedColorDependentExtendedProfileBlockProbability_nonneg
              proposal R hs.le hq hr0 hleft homega0 homega1) _)
          hbase hbaseScaled
      · exact le_rfl
    _ ≤ 1 := G.sum_scaledColorDependentBlockVarianceSelfUse_le_one
      proposal R hn hk hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
      hproposal0 hproposal hstar source sourceCode

/-- Actual sparse variance-use column.  Its size is the number of padded
block words times the local star weight, plus one self row, and therefore
is independent of the total number of vertices. -/
theorem sum_scaledColorDependentBlockVarianceUse_le_sparseColumn
    (hn : 0 < n) (hk : 0 < k)
    (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) :
    (∑ row : G.ColorDependentBlockVarianceRow
        (B := B) (k := k) (β := β) (q := q) (r := r),
      G.scaledColorDependentBlockVarianceUse proposal R rho omega
        (colorDependentBlockVariancePairScale
          n k rho s omega β q r C0)
        (colorDependentBlockVarianceSelfScale
          n k rho s omega β q r C0)
        source sourceCode row) ≤
      (extendedProfileStateBound β q r : ℝ) ^ k * n + 1 := by
  rw [Fintype.sum_sum_type]
  exact add_le_add
    (G.sum_scaledColorDependentBlockVarianceCandidateUse_le_column
      proposal R hn hk hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
      hproposal0 hproposal hstar source sourceCode)
    (G.sum_scaledColorDependentBlockVarianceSelfUse_le_one
      proposal R hn hk hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
      hproposal0 hproposal hstar source sourceCode)

theorem sum_scaledColorDependentBlockVarianceUse_mul_le_sparseColumn
    {L : ℕ} (hL : 0 < L)
    (hn : 0 < n) (hk : 0 < k)
    (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) :
    (∑ row : G.ColorDependentBlockVarianceRow
        (B := B) (k := k) (β := β) (q := q) (r := r),
      G.scaledColorDependentBlockVarianceUse proposal R rho omega
        ((L : ℝ) * colorDependentBlockVariancePairScale
          n k rho s omega β q r C0)
        ((L : ℝ) * colorDependentBlockVarianceSelfScale
          n k rho s omega β q r C0)
        source sourceCode row) ≤
      (extendedProfileStateBound β q r : ℝ) ^ k * n + 1 := by
  rw [Fintype.sum_sum_type]
  exact add_le_add
    (G.sum_scaledColorDependentBlockVarianceCandidateUse_mul_le_column
      proposal R hL hn hk hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
      hproposal0 hproposal hstar source sourceCode)
    (G.sum_scaledColorDependentBlockVarianceSelfUse_mul_le_one
      proposal R hL hn hk hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
      hproposal0 hproposal hstar source sourceCode)

theorem meanTotalColorDependentBlockVariance_le
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n) (v : G.V) :
    G.meanTotalColorDependentBlockVariance proposal R rho omega v ≤
      B * (n * colorDependentBlockVariancePairScale
        n k rho s omega β q r C0) := by
  let pairScale := colorDependentBlockVariancePairScale
    n k rho s omega β q r C0
  have hbound : ∀ b : Fin B,
      (∑ a,
        G.paddedColorDependentExtendedProfileBlockProbability
            proposal R omega (v, b) a *
          G.conditionalColorDependentBlockVariance proposal R rho omega
            (v, b, a)) ≤ n * pairScale := by
    intro b
    calc
      _ ≤ ∑ a,
          G.paddedColorDependentExtendedProfileBlockProbability
              proposal R omega (v, b) a * (n * pairScale) := by
        apply Finset.sum_le_sum
        intro a _ha
        exact mul_le_mul_of_nonneg_left
          (G.conditionalColorDependentBlockVariance_le_n_mul_pairScale
            proposal R hn hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
            hproposal0 hproposal hstar (v, b, a))
          (G.paddedColorDependentExtendedProfileBlockProbability_nonneg
            proposal R hs hq hr0 hleft homega0 homega1 _ _)
      _ = n * pairScale := by
        rw [← Finset.sum_mul,
          G.sum_paddedColorDependentExtendedProfileBlockProbability]
        ring
  unfold meanTotalColorDependentBlockVariance
  calc
    _ ≤ ∑ _b : Fin B, n * pairScale :=
      Finset.sum_le_sum fun b _hb ↦ hbound b
    _ = B * (n * pairScale) := by simp

/-- Exact one-coordinate option-mass expectation.  It remains valid for a
nonuniform proposal and is the centre used by the block variance. -/
theorem expected_colorDependentCoordinateOptionMass
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (e : G.E) (c : Fin B × Fin k) :
    (∑ P : G.ColorDependentExtendedProfileState R (G.fst e) c,
      G.smoothedColorDependentExtendedProfileProbability
          R omega (G.fst e) c P *
        ∑ Q : G.ColorDependentExtendedProfileState R (G.snd e) c,
          G.smoothedColorDependentExtendedProfileProbability
              R omega (G.snd e) c Q *
            G.colorDependentCoordinateOptionMass
              proposal R rho omega e c P Q) =
      rho * s * proposal e c := by
  let yl := G.colorDependentExtendedProfileLargeEdgeColorMass
    (s := s) (β := β) proposal e c
  let yt := G.colorDependentExtendedProfileTinyEdgeColorMass
    (s := s) (β := β) proposal e c
  have hlarge :
      (∑ P : G.ColorDependentExtendedProfileState R (G.fst e) c,
        G.smoothedColorDependentExtendedProfileProbability
            R omega (G.fst e) c P * ∑ Q,
          G.smoothedColorDependentExtendedProfileProbability
              R omega (G.snd e) c Q *
            ∑ i, ∑ j,
              G.colorDependentExtendedProfileLargeProductMass
                proposal R rho omega e c P Q i j) = rho * yl := by
    by_cases hy : yl = 0
    · simp [yl, colorDependentExtendedProfileLargeProductMass,
        pairedOption, hy]
    · calc
        ( ∑ P : G.ColorDependentExtendedProfileState R (G.fst e) c,
          G.smoothedColorDependentExtendedProfileProbability
              R omega (G.fst e) c P * ∑ Q,
            G.smoothedColorDependentExtendedProfileProbability
                R omega (G.snd e) c Q *
              ∑ i, ∑ j,
                G.colorDependentExtendedProfileLargeProductMass
                  proposal R rho omega e c P Q i j) =
            ∑ P : G.ColorDependentExtendedProfileState R (G.fst e) c,
              G.smoothedColorDependentExtendedProfileProbability
                  R omega (G.fst e) c P * ∑ i, ∑ Q,
                G.smoothedColorDependentExtendedProfileProbability
                    R omega (G.snd e) c Q * ∑ j,
                  G.colorDependentExtendedProfileLargeProductMass
                    proposal R rho omega e c P Q i j := by
          apply Finset.sum_congr rfl
          intro P _hP
          congr 1
          calc
            (∑ Q,
              G.smoothedColorDependentExtendedProfileProbability
                  R omega (G.snd e) c Q *
                ∑ i, ∑ j,
                  G.colorDependentExtendedProfileLargeProductMass
                    proposal R rho omega e c P Q i j) =
                ∑ Q, ∑ i,
                  G.smoothedColorDependentExtendedProfileProbability
                      R omega (G.snd e) c Q * ∑ j,
                    G.colorDependentExtendedProfileLargeProductMass
                      proposal R rho omega e c P Q i j := by
              apply Finset.sum_congr rfl
              intro Q _hQ
              rw [Finset.mul_sum]
            _ = ∑ i, ∑ Q,
                  G.smoothedColorDependentExtendedProfileProbability
                      R omega (G.snd e) c Q * ∑ j,
                    G.colorDependentExtendedProfileLargeProductMass
                      proposal R rho omega e c P Q i j := by
              rw [Finset.sum_comm]
        _ = rho * yl := by
          simpa [yl] using
            (G.colorDependentLargeProductMass_expectation
              proposal R (rho := rho) hs hq hr0 hleft homega0 homega1 hy)
  have htiny :
      (∑ P : G.ColorDependentExtendedProfileState R (G.fst e) c,
        G.smoothedColorDependentExtendedProfileProbability
            R omega (G.fst e) c P * ∑ Q,
          G.smoothedColorDependentExtendedProfileProbability
              R omega (G.snd e) c Q *
            G.colorDependentExtendedProfileTinyProductMass
              proposal R rho omega e c P Q) = rho * yt := by
    by_cases hy : yt = 0
    · simp [yt, colorDependentExtendedProfileTinyProductMass,
        pairedOption, hy]
    · simpa [yt] using
        G.colorDependentTinyProductMass_expectation
          proposal R (rho := rho) hs hq hr0 hleft homega0 homega1 hy
  unfold colorDependentCoordinateOptionMass
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  rw [hlarge, htiny, ← mul_add,
    G.colorDependentLarge_add_tinyEdgeColorMass proposal e c]
  ring

/-- Exact integration of a statistic of the decoded word of one block. -/
private theorem sum_paddedColorDependentBlockProbability_mul_decode
    (omega : ℝ) (v : G.V) (b : Fin B)
    (f : (∀ i : Fin k,
      G.ColorDependentExtendedProfileState R v (b, i)) → ℝ) :
    (∑ a,
      G.paddedColorDependentExtendedProfileBlockProbability
          proposal R omega (v, b) a *
        f (G.decodeColorDependentExtendedProfileBlock
          proposal R (v, b) a)) =
      ∑ word : ∀ i : Fin k,
          G.ColorDependentExtendedProfileState R v (b, i),
        FiniteCoordinateDependentWordMoments.wordMass
            (fun i : Fin k ↦
              G.ColorDependentExtendedProfileState R v (b, i))
            (fun i z ↦
              G.smoothedColorDependentExtendedProfileProbability
                R omega v (b, i) z) word *
          f word := by
  let blockProposal :=
    G.colorDependentExtendedProfileBlockProposal proposal b
  let blockR :=
    G.colorDependentExtendedProfileBlockRealization proposal R b
  calc
    (∑ a,
      G.paddedColorDependentExtendedProfileBlockProbability
          proposal R omega (v, b) a *
        f (G.decodeColorDependentExtendedProfileBlock
          proposal R (v, b) a)) =
        ∑ word : ∀ i : Fin k,
            G.ColorDependentExtendedProfileState R v (b, i),
          G.colorDependentExtendedProfileWordMass blockR omega v word *
            f word := by
      simpa [blockProposal, blockR,
        paddedColorDependentExtendedProfileBlockProbability,
        decodeColorDependentExtendedProfileBlock] using
        (G.sum_paddedColorDependentProbability_mul_decode
          (proposal := blockProposal) blockR omega v f)
    _ = ∑ word : ∀ i : Fin k,
          G.ColorDependentExtendedProfileState R v (b, i),
        FiniteCoordinateDependentWordMoments.wordMass
            (fun i : Fin k ↦
              G.ColorDependentExtendedProfileState R v (b, i))
            (fun i z ↦
              G.smoothedColorDependentExtendedProfileProbability
                R omega v (b, i) z) word *
          f word := by
      apply Finset.sum_congr rfl
      intro word _hword
      congr 1
      unfold colorDependentExtendedProfileWordMass
        FiniteCoordinateDependentWordMoments.wordMass
      apply Finset.prod_congr rfl
      intro i _hi
      cases hwi : word i <;>
        simp [blockR, colorDependentExtendedProfileBlockRealization,
          colorDependentExtendedProfileBlockProposal,
          smoothedColorDependentExtendedProfileProbability,
          colorDependentExtendedProfileProbability, hwi]

/-- The exact target is the sum of the coordinate expectations in a block. -/
theorem expected_colorDependentBlockOptionMass
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (e : G.E) (b : Fin B) :
    (∑ left,
      G.paddedColorDependentExtendedProfileBlockProbability
          proposal R omega (G.fst e, b) left *
        ∑ right,
          G.paddedColorDependentExtendedProfileBlockProbability
              proposal R omega (G.snd e, b) right *
            G.colorDependentBlockOptionMass
              proposal R rho omega e b left right) =
      G.colorDependentBlockTarget proposal rho s e b := by
  let leftR := G.colorDependentExtendedProfileBlockRealization
    proposal R b
  let blockProposal := G.colorDependentExtendedProfileBlockProposal proposal b
  calc
    (∑ left,
      G.paddedColorDependentExtendedProfileBlockProbability
          proposal R omega (G.fst e, b) left *
        ∑ right,
          G.paddedColorDependentExtendedProfileBlockProbability
              proposal R omega (G.snd e, b) right *
            G.colorDependentBlockOptionMass
              proposal R rho omega e b left right) =
      ∑ i : Fin k, ∑ left,
        G.paddedColorDependentExtendedProfileBlockProbability
            proposal R omega (G.fst e, b) left *
          ∑ right,
            G.paddedColorDependentExtendedProfileBlockProbability
                proposal R omega (G.snd e, b) right *
              G.colorDependentCoordinateOptionMass proposal R rho omega
                e (b, i)
                (G.decodeColorDependentExtendedProfileBlock
                  proposal R (G.fst e, b) left i)
                (G.decodeColorDependentExtendedProfileBlock
                  proposal R (G.snd e, b) right i) := by
        unfold colorDependentBlockOptionMass
        simp_rw [Finset.mul_sum]
        calc
          (∑ left, ∑ right, ∑ i : Fin k,
            G.paddedColorDependentExtendedProfileBlockProbability
                proposal R omega (G.fst e, b) left *
              (G.paddedColorDependentExtendedProfileBlockProbability
                  proposal R omega (G.snd e, b) right *
                G.colorDependentCoordinateOptionMass proposal R rho omega
                  e (b, i)
                  (G.decodeColorDependentExtendedProfileBlock
                    proposal R (G.fst e, b) left i)
                  (G.decodeColorDependentExtendedProfileBlock
                    proposal R (G.snd e, b) right i))) =
              ∑ left, ∑ i : Fin k, ∑ right,
                G.paddedColorDependentExtendedProfileBlockProbability
                    proposal R omega (G.fst e, b) left *
                  (G.paddedColorDependentExtendedProfileBlockProbability
                      proposal R omega (G.snd e, b) right *
                    G.colorDependentCoordinateOptionMass proposal R rho omega
                      e (b, i)
                      (G.decodeColorDependentExtendedProfileBlock
                        proposal R (G.fst e, b) left i)
                      (G.decodeColorDependentExtendedProfileBlock
                        proposal R (G.snd e, b) right i)) := by
            apply Finset.sum_congr rfl
            intro left _hleft
            rw [Finset.sum_comm]
          _ = _ := by rw [Finset.sum_comm]
    _ = ∑ i : Fin k,
        ∑ P : G.ColorDependentExtendedProfileState R (G.fst e) (b, i),
          G.smoothedColorDependentExtendedProfileProbability
              R omega (G.fst e) (b, i) P *
            ∑ right,
              G.paddedColorDependentExtendedProfileBlockProbability
                  proposal R omega (G.snd e, b) right *
                G.colorDependentCoordinateOptionMass proposal R rho omega
                  e (b, i) P
                  (G.decodeColorDependentExtendedProfileBlock
                    proposal R (G.snd e, b) right i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simpa [paddedColorDependentExtendedProfileBlockProbability,
        decodeColorDependentExtendedProfileBlock, leftR, blockProposal,
        colorDependentExtendedProfileBlockRealization,
        colorDependentExtendedProfileBlockProposal] using
        (G.sum_paddedColorDependentProbability_mul_decode_coordinate
          (proposal := blockProposal) leftR omega (G.fst e) i
          (fun P ↦ ∑ right,
            G.paddedColorDependentExtendedProfileBlockProbability
                proposal R omega (G.snd e, b) right *
              G.colorDependentCoordinateOptionMass proposal R rho omega
                e (b, i) P
                (G.decodeColorDependentExtendedProfileBlock
                  proposal R (G.snd e, b) right i)))
    _ = ∑ i : Fin k,
        ∑ P : G.ColorDependentExtendedProfileState R (G.fst e) (b, i),
          G.smoothedColorDependentExtendedProfileProbability
              R omega (G.fst e) (b, i) P *
            ∑ Q : G.ColorDependentExtendedProfileState R (G.snd e) (b, i),
              G.smoothedColorDependentExtendedProfileProbability
                  R omega (G.snd e) (b, i) Q *
                G.colorDependentCoordinateOptionMass proposal R rho omega
                  e (b, i) P Q := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro P _hP
      congr 1
      simpa [paddedColorDependentExtendedProfileBlockProbability,
        decodeColorDependentExtendedProfileBlock, leftR, blockProposal,
        colorDependentExtendedProfileBlockRealization,
        colorDependentExtendedProfileBlockProposal] using
        (G.sum_paddedColorDependentProbability_mul_decode_coordinate
          (proposal := blockProposal) leftR omega (G.snd e) i
          (fun Q ↦ G.colorDependentCoordinateOptionMass
            proposal R rho omega e (b, i) P Q))
    _ = ∑ i : Fin k, rho * s * proposal e (b, i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact G.expected_colorDependentCoordinateOptionMass
        proposal R hs hq hr0 hleft homega0 homega1 rho e (b, i)
    _ = G.colorDependentBlockTarget proposal rho s e b := by
      unfold colorDependentBlockTarget
      rw [Finset.mul_sum]

theorem expected_colorDependentBlockVariance_le
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (e : G.E) (b : Fin B) :
    (∑ left,
      G.paddedColorDependentExtendedProfileBlockProbability
          proposal R omega (G.fst e, b) left *
        ∑ right,
          G.paddedColorDependentExtendedProfileBlockProbability
              proposal R omega (G.snd e, b) right *
            G.colorDependentBlockVariance
              proposal R rho omega e b left right) ≤
      G.weight e *
        (colorDependentBlockOptionUpper n 1 rho s omega β q r C0 *
          G.colorDependentBlockTarget proposal rho s e b) := by
  let leftProb : ∀ i : Fin k,
      G.ColorDependentExtendedProfileState R (G.fst e) (b, i) → ℝ :=
    fun i z ↦ G.smoothedColorDependentExtendedProfileProbability
      R omega (G.fst e) (b, i) z
  let rightProb : ∀ i : Fin k,
      G.ColorDependentExtendedProfileState R (G.snd e) (b, i) → ℝ :=
    fun i z ↦ G.smoothedColorDependentExtendedProfileProbability
      R omega (G.snd e) (b, i) z
  let value : ∀ i : Fin k,
      G.ColorDependentExtendedProfileState R (G.fst e) (b, i) →
      G.ColorDependentExtendedProfileState R (G.snd e) (b, i) → ℝ :=
    fun i P Q ↦ G.colorDependentCoordinateOptionMass
      proposal R rho omega e (b, i) P Q
  let mean : Fin k → ℝ := fun i ↦ rho * s * proposal e (b, i)
  let U := 2 * colorDependentCandidateCapacityScale
    rho s omega β q r C0 / n
  let LeftWord := ∀ i : Fin k,
    G.ColorDependentExtendedProfileState R (G.fst e) (b, i)
  let RightWord := ∀ i : Fin k,
    G.ColorDependentExtendedProfileState R (G.snd e) (b, i)
  have hmoment :=
    FiniteCoordinateDependentWordMoments.sum_twoWordMass_mul_centered_sum_sq_le
      (fun i : Fin k ↦
        G.ColorDependentExtendedProfileState R (G.fst e) (b, i))
      (fun i : Fin k ↦
        G.ColorDependentExtendedProfileState R (G.snd e) (b, i))
      leftProb rightProb
      (fun i z ↦ G.smoothedColorDependentExtendedProfileProbability_pos R
        hs hq hr0 hleft homega0 homega1 (G.fst e) (b, i) z |>.le)
      (fun i z ↦ G.smoothedColorDependentExtendedProfileProbability_pos R
        hs hq hr0 hleft homega0 homega1 (G.snd e) (b, i) z |>.le)
      (fun i ↦ G.sum_smoothedColorDependentExtendedProfileProbability
        R omega (G.fst e) (b, i))
      (fun i ↦ G.sum_smoothedColorDependentExtendedProfileProbability
        R omega (G.snd e) (b, i))
      value mean (fun _i ↦ U)
      (fun i P Q ↦ by
        unfold value
        unfold colorDependentCoordinateOptionMass
        exact add_nonneg
          (Finset.sum_nonneg fun x _hx ↦ Finset.sum_nonneg fun y _hy ↦
            G.colorDependentExtendedProfileLargeProductMass_nonneg
              proposal R hs hq hr0 hleft homega0 homega1 hrho _ _ _ _ _ _)
          (G.colorDependentExtendedProfileTinyProductMass_nonneg
            proposal R hs hq hr0 hleft homega0 homega1 hrho _ _ _ _))
      (fun i P Q ↦ by
        unfold value U
        exact G.colorDependentCoordinateOptionMass_le_two_scale_div_n
          proposal R hn hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
          hproposal0 hproposal e (b, i) P Q)
      (fun i ↦ by
        unfold leftProb rightProb value mean
        exact G.expected_colorDependentCoordinateOptionMass
          proposal R hs hq hr0 hleft homega0 homega1 rho e (b, i))
  -- Padding has zero mass off genuine words, so the exact dependent-word
  -- moment transfers to the categorical block states.
  have hpadded :
      (∑ left,
        G.paddedColorDependentExtendedProfileBlockProbability
            proposal R omega (G.fst e, b) left *
          ∑ right,
            G.paddedColorDependentExtendedProfileBlockProbability
                proposal R omega (G.snd e, b) right *
              (G.colorDependentBlockOptionMass proposal R rho omega e b
                  left right -
                G.colorDependentBlockTarget proposal rho s e b) ^ 2) ≤
        ∑ i : Fin k, U * mean i := by
    have hpaddedEq :
        (∑ left,
          G.paddedColorDependentExtendedProfileBlockProbability
              proposal R omega (G.fst e, b) left *
            ∑ right,
              G.paddedColorDependentExtendedProfileBlockProbability
                  proposal R omega (G.snd e, b) right *
                (G.colorDependentBlockOptionMass proposal R rho omega e b
                    left right -
                  G.colorDependentBlockTarget proposal rho s e b) ^ 2) =
          ∑ leftWord : LeftWord,
            FiniteCoordinateDependentWordMoments.wordMass
                (fun i : Fin k ↦
                  G.ColorDependentExtendedProfileState R (G.fst e) (b, i))
                leftProb leftWord *
              ∑ rightWord : RightWord,
                FiniteCoordinateDependentWordMoments.wordMass
                    (fun i : Fin k ↦
                      G.ColorDependentExtendedProfileState R
                        (G.snd e) (b, i))
                    rightProb rightWord *
                  (∑ i, (value i (leftWord i) (rightWord i) - mean i)) ^ 2 := by
      calc
        (∑ left,
          G.paddedColorDependentExtendedProfileBlockProbability
              proposal R omega (G.fst e, b) left *
            ∑ right,
              G.paddedColorDependentExtendedProfileBlockProbability
                  proposal R omega (G.snd e, b) right *
                (G.colorDependentBlockOptionMass proposal R rho omega e b
                    left right -
                  G.colorDependentBlockTarget proposal rho s e b) ^ 2) =
            ∑ left,
              G.paddedColorDependentExtendedProfileBlockProbability
                  proposal R omega (G.fst e, b) left *
                ∑ rightWord : RightWord,
                  FiniteCoordinateDependentWordMoments.wordMass
                      (fun i : Fin k ↦
                        G.ColorDependentExtendedProfileState R
                          (G.snd e) (b, i))
                      rightProb rightWord *
                    (∑ i, (value i
                      (G.decodeColorDependentExtendedProfileBlock
                        proposal R (G.fst e, b) left i)
                      (rightWord i) - mean i)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro left _hleft
          congr 1
          simpa [colorDependentBlockOptionMass, colorDependentBlockTarget,
            value, mean, rightProb, Finset.sum_sub_distrib,
            Finset.mul_sum] using
            (G.sum_paddedColorDependentBlockProbability_mul_decode
              proposal R omega (G.snd e) b
              (fun rightWord ↦
                (∑ i, (value i
                  (G.decodeColorDependentExtendedProfileBlock
                    proposal R (G.fst e, b) left i)
                  (rightWord i) - mean i)) ^ 2))
        _ = ∑ leftWord : LeftWord,
            FiniteCoordinateDependentWordMoments.wordMass
                (fun i : Fin k ↦
                  G.ColorDependentExtendedProfileState R (G.fst e) (b, i))
                leftProb leftWord *
              ∑ rightWord : RightWord,
                FiniteCoordinateDependentWordMoments.wordMass
                    (fun i : Fin k ↦
                      G.ColorDependentExtendedProfileState R
                        (G.snd e) (b, i))
                    rightProb rightWord *
                  (∑ i, (value i (leftWord i) (rightWord i) - mean i)) ^ 2 := by
          simpa [leftProb] using
            (G.sum_paddedColorDependentBlockProbability_mul_decode
              proposal R omega (G.fst e) b
              (fun leftWord ↦
                ∑ rightWord : RightWord,
                  FiniteCoordinateDependentWordMoments.wordMass
                      (fun i : Fin k ↦
                        G.ColorDependentExtendedProfileState R
                          (G.snd e) (b, i))
                      rightProb rightWord *
                    (∑ i, (value i (leftWord i) (rightWord i) - mean i)) ^ 2))
    exact hpaddedEq.trans_le hmoment
  unfold colorDependentBlockVariance
  calc
    _ = G.weight e *
        (∑ left,
          G.paddedColorDependentExtendedProfileBlockProbability
              proposal R omega (G.fst e, b) left *
            ∑ right,
              G.paddedColorDependentExtendedProfileBlockProbability
                  proposal R omega (G.snd e, b) right *
                (G.colorDependentBlockOptionMass proposal R rho omega e b
                    left right -
                  G.colorDependentBlockTarget proposal rho s e b) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro left _hleft
      calc
        G.paddedColorDependentExtendedProfileBlockProbability
              proposal R omega (G.fst e, b) left *
            (∑ right,
              G.paddedColorDependentExtendedProfileBlockProbability
                  proposal R omega (G.snd e, b) right *
                (G.weight e *
                  (G.colorDependentBlockOptionMass proposal R rho omega e b
                      left right -
                    G.colorDependentBlockTarget proposal rho s e b) ^ 2)) =
            ∑ right,
              G.paddedColorDependentExtendedProfileBlockProbability
                  proposal R omega (G.fst e, b) left *
                (G.paddedColorDependentExtendedProfileBlockProbability
                    proposal R omega (G.snd e, b) right *
                  (G.weight e *
                    (G.colorDependentBlockOptionMass proposal R rho omega e b
                        left right -
                      G.colorDependentBlockTarget proposal rho s e b) ^ 2)) := by
          rw [Finset.mul_sum]
        _ = ∑ right,
              G.weight e *
                (G.paddedColorDependentExtendedProfileBlockProbability
                    proposal R omega (G.fst e, b) left *
                  (G.paddedColorDependentExtendedProfileBlockProbability
                      proposal R omega (G.snd e, b) right *
                    (G.colorDependentBlockOptionMass proposal R rho omega e b
                        left right -
                      G.colorDependentBlockTarget proposal rho s e b) ^ 2)) := by
          apply Finset.sum_congr rfl
          intro right _hright
          ring
        _ = G.weight e *
            (G.paddedColorDependentExtendedProfileBlockProbability
                proposal R omega (G.fst e, b) left *
              ∑ right,
                G.paddedColorDependentExtendedProfileBlockProbability
                    proposal R omega (G.snd e, b) right *
                  (G.colorDependentBlockOptionMass proposal R rho omega e b
                      left right -
                    G.colorDependentBlockTarget proposal rho s e b) ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ G.weight e * (∑ i : Fin k, U * mean i) :=
      mul_le_mul_of_nonneg_left hpadded (G.weight_nonneg e)
    _ = G.weight e *
        (colorDependentBlockOptionUpper n 1 rho s omega β q r C0 *
          G.colorDependentBlockTarget proposal rho s e b) := by
      unfold U mean colorDependentBlockOptionUpper colorDependentBlockTarget
      congr 1
      norm_num
      rw [Finset.mul_sum, Finset.mul_sum]

def expectedColorDependentBlockVariance
    (rho omega : ℝ) (e : G.E) (b : Fin B) : ℝ :=
  ∑ left,
    G.paddedColorDependentExtendedProfileBlockProbability
        proposal R omega (G.fst e, b) left *
      ∑ right,
        G.paddedColorDependentExtendedProfileBlockProbability
            proposal R omega (G.snd e, b) right *
          G.colorDependentBlockVariance proposal R rho omega e b left right

theorem sum_centerProbability_mul_conditionalColorDependentBlockVariance
    (rho omega : ℝ) (v : G.V) (b : Fin B) :
    (∑ centerCode,
      G.paddedColorDependentExtendedProfileBlockProbability
          proposal R omega (v, b) centerCode *
        G.conditionalColorDependentBlockVariance proposal R rho omega
          (v, b, centerCode)) =
      ∑ e : G.StarEdge v,
        G.expectedColorDependentBlockVariance proposal R rho omega e.1 b := by
  classical
  simp_rw [G.conditionalColorDependentBlockVariance_eq_edge_sum
    proposal R rho omega v b]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ e : G.E, ∑ centerCode,
      G.paddedColorDependentExtendedProfileBlockProbability
          proposal R omega (v, b) centerCode *
        (if v = G.fst e then
          ∑ oppositeCode,
            G.paddedColorDependentExtendedProfileBlockProbability
                proposal R omega (G.snd e, b) oppositeCode *
              G.colorDependentBlockVariance proposal R rho omega e b
                centerCode oppositeCode
        else if v = G.snd e then
          ∑ oppositeCode,
            G.paddedColorDependentExtendedProfileBlockProbability
                proposal R omega (G.fst e, b) oppositeCode *
              G.colorDependentBlockVariance proposal R rho omega e b
                oppositeCode centerCode
        else 0)) =
      ∑ e : G.E, if G.Inc v e then
        G.expectedColorDependentBlockVariance proposal R rho omega e b
      else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hfst : v = G.fst e
      · subst v
        simp [WeightedMultigraph.Inc,
          expectedColorDependentBlockVariance]
      · by_cases hsnd : v = G.snd e
        · subst v
          have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
          have hswap :
              (∑ centerCode,
                G.paddedColorDependentExtendedProfileBlockProbability
                    proposal R omega (G.snd e, b) centerCode *
                  ∑ oppositeCode,
                    G.paddedColorDependentExtendedProfileBlockProbability
                        proposal R omega (G.fst e, b) oppositeCode *
                      G.colorDependentBlockVariance proposal R rho omega e b
                        oppositeCode centerCode) =
                G.expectedColorDependentBlockVariance
                  proposal R rho omega e b := by
            unfold expectedColorDependentBlockVariance
            calc
              _ = ∑ centerCode, ∑ oppositeCode,
                  G.paddedColorDependentExtendedProfileBlockProbability
                      proposal R omega (G.snd e, b) centerCode *
                    (G.paddedColorDependentExtendedProfileBlockProbability
                        proposal R omega (G.fst e, b) oppositeCode *
                      G.colorDependentBlockVariance proposal R rho omega e b
                        oppositeCode centerCode) := by
                apply Finset.sum_congr rfl
                intro centerCode _hc
                rw [Finset.mul_sum]
              _ = ∑ oppositeCode, ∑ centerCode,
                  G.paddedColorDependentExtendedProfileBlockProbability
                      proposal R omega (G.snd e, b) centerCode *
                    (G.paddedColorDependentExtendedProfileBlockProbability
                        proposal R omega (G.fst e, b) oppositeCode *
                      G.colorDependentBlockVariance proposal R rho omega e b
                        oppositeCode centerCode) := by rw [Finset.sum_comm]
              _ = _ := by
                apply Finset.sum_congr rfl
                intro oppositeCode _ho
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro centerCode _hc
                ring
          simp [WeightedMultigraph.Inc, hfst, hne, hswap]
        · have hinc : ¬G.Inc v e := by
            intro h
            rcases h with h | h
            · exact hfst h.symm
            · exact hsnd h.symm
          simp [hfst, hsnd, hinc]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
        (by intro e; simp)
        (fun e ↦ G.expectedColorDependentBlockVariance
          proposal R rho omega e b)

theorem meanTotalColorDependentBlockVariance_le_sharp
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hmass : ∀ e, ∑ c, proposal e c ≤ 1)
    (hstar : ∀ v, G.starWeight v ≤ n) (v : G.V) :
    G.meanTotalColorDependentBlockVariance proposal R rho omega v ≤
      colorDependentBlockOptionUpper n 1 rho s omega β q r C0 *
        (rho * s * n) := by
  let U := colorDependentBlockOptionUpper n 1 rho s omega β q r C0
  have hU0 : 0 ≤ U := by
    unfold U colorDependentBlockOptionUpper
    exact mul_nonneg (Nat.cast_nonneg 1) (div_nonneg
      (mul_nonneg (by positivity)
        (colorDependentCandidateCapacityScale_nonneg
          (C0 := C0) hrho hs hC0 homega0.le)) (Nat.cast_nonneg n))
  unfold meanTotalColorDependentBlockVariance
  simp_rw [G.sum_centerProbability_mul_conditionalColorDependentBlockVariance
    proposal R rho omega v]
  calc
    (∑ b : Fin B, ∑ e : G.StarEdge v,
      G.expectedColorDependentBlockVariance proposal R rho omega e.1 b) ≤
      ∑ b : Fin B, ∑ e : G.StarEdge v,
        G.weight e.1 * (U * G.colorDependentBlockTarget
          proposal rho s e.1 b) := by
      apply Finset.sum_le_sum
      intro b _hb
      apply Finset.sum_le_sum
      intro e _he
      exact G.expected_colorDependentBlockVariance_le proposal R
        hn hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
        hproposal0 hproposal e.1 b
    _ = U * ∑ e : G.StarEdge v,
        G.weight e.1 * G.colorDependentTotalTarget proposal rho s e.1 := by
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      rw [← G.sum_colorDependentBlockTarget_eq_totalTarget proposal rho s]
      calc
        (∑ b : Fin B, G.weight e.1 *
            (U * G.colorDependentBlockTarget proposal rho s e.1 b)) =
            ∑ b : Fin B, U *
              (G.weight e.1 *
                G.colorDependentBlockTarget proposal rho s e.1 b) := by
          apply Finset.sum_congr rfl
          intro b _hb
          ring
        _ = U * ∑ b : Fin B, G.weight e.1 *
              G.colorDependentBlockTarget proposal rho s e.1 b := by
          rw [Finset.mul_sum]
        _ = U * (G.weight e.1 * ∑ b : Fin B,
              G.colorDependentBlockTarget proposal rho s e.1 b) := by
          congr 1
          rw [Finset.mul_sum]
    _ ≤ U * (rho * s * G.starWeight v) := by
      apply mul_le_mul_of_nonneg_left _ hU0
      calc
        (∑ e : G.StarEdge v,
          G.weight e.1 * G.colorDependentTotalTarget proposal rho s e.1) =
          rho * s * ∑ e : G.StarEdge v,
            G.weight e.1 * ∑ c, proposal e.1 c := by
              unfold colorDependentTotalTarget
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro e _he
              ring
        _ ≤ rho * s * ∑ e : G.StarEdge v, G.weight e.1 := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hrho hs)
          apply Finset.sum_le_sum
          intro e _he
          calc
            G.weight e.1 * (∑ c : Fin B × Fin k, proposal e.1 c) ≤
                G.weight e.1 * 1 := by
              apply mul_le_mul_of_nonneg_left _ (G.weight_nonneg e.1)
              exact hmass e.1
            _ = G.weight e.1 := by ring
        _ = rho * s * G.starWeight v := by rfl
    _ ≤ U * (rho * s * n) := by
      apply mul_le_mul_of_nonneg_left _ hU0
      exact mul_le_mul_of_nonneg_left (hstar v) (mul_nonneg hrho hs)

end WeightedMultigraph

end

end WeightedEdgeColoring
