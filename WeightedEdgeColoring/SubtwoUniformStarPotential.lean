import WeightedEdgeColoring.SubtwoEndpointPotential
import WeightedEdgeColoring.SubtwoUniformModelScalars

set_option maxHeartbeats 4000000

/-! The one-parameter endpoint certificate for the uniform four-spoke star. -/

namespace WeightedEdgeColoring.Subtwo.EndpointPotential

private noncomputable def d (a : ℝ) : ℝ := 1 - a
private noncomputable def q (a : ℝ) : ℝ := 2 * d a / (3 * a)
private noncomputable def hh (a : ℝ) : ℝ := (2 * a - 1) / (3 * a)
private noncomputable def zz (a : ℝ) : ℝ := 5 * a / 2 - 3 / 4
private noncomputable def spokeLeaf (a : ℝ) : ℝ := 2 * a - zz a
private noncomputable def uu (a : ℝ) : ℝ := max ((1 - q a) * d a) (spokeLeaf a - q a * a)

noncomputable def uniformStarM (a : ℝ) : Bundle → ℝ :=
  ![a, a, a, a, d a, d a, d a, d a, d a, d a]
noncomputable def uniformStarRho (a : ℝ) : Bundle → ℝ :=
  ![2/3, 2/3, 2/3, 2/3, 2/3, 2/3, 2/3, 2/3, 2/3, q a]
noncomputable def uniformStarH (a : ℝ) : Vertex → ℝ :=
  ![hh a, hh a, hh a, 0, 0]

private noncomputable def starZ (a : ℝ) : Vertex → Bundle → ℝ :=
  ![![zz a, zz a, zz a, zz a, 0, 0, 0, 0, 0, 0],
    ![spokeLeaf a, 0, 0, 0, d a, d a, d a, 0, 0, 0],
    ![0, spokeLeaf a, 0, 0, d a, 0, 0, d a, d a, 0],
    ![0, 0, spokeLeaf a, 0, 0, d a, 0, d a, 0, d a],
    ![0, 0, 0, spokeLeaf a, 0, 0, d a, 0, d a, d a]]
private noncomputable def starAlpha (a : ℝ) : Vertex → Bundle → ℝ :=
  ![![zz a-2*a/3, zz a-2*a/3, zz a-2*a/3, zz a-2*a/3, 0, 0, 0, 0, 0, 0],
    ![d a/3, 0, 0, 0, d a/3, d a/3, d a/3, 0, 0, 0],
    ![0, d a/3, 0, 0, d a/3, 0, 0, d a/3, d a/3, 0],
    ![0, 0, d a/3, 0, 0, d a/3, 0, d a/3, 0, uu a],
    ![0, 0, 0, d a/3, 0, 0, d a/3, 0, d a/3, uu a]]

private noncomputable def Fs (a : ℝ) : ℝ :=
  4*a/3+2/3+residualCharge*(zz a-2*a/3+d a/3)
private noncomputable def Fc (a : ℝ) : ℝ :=
  4*d a/3+2/3+2*residualCharge*d a/3
private noncomputable def F1 (a : ℝ) : ℝ :=
  (2-q a)*d a+q a+2*residualCharge*(1-q a)*d a
private noncomputable def F2 (a : ℝ) : ℝ :=
  (2-q a)*d a+q a+2*residualCharge*(spokeLeaf a-q a*a)
private noncomputable def PH (a : ℝ) : ℝ := (133-97*a)/108
private noncomputable def PL (a : ℝ) : ℝ :=
  max (max (PH a) (F1 a/2)) (lightCharge*spokeLeaf a)
private noncomputable def P0 (a : ℝ) : ℝ := 157/40-2*PH a-2*PL a
private noncomputable def starC (a : ℝ) : Vertex → ℝ :=
  ![zz a-hh a*a,
    max (spokeLeaf a-hh a*a) (d a-hh a*d a),
    max (spokeLeaf a-hh a*a) (d a-hh a*d a),
    spokeLeaf a, spokeLeaf a]
private noncomputable def starP (a : ℝ) : Vertex → ℝ :=
  ![P0 a, PH a, PH a, PL a, PL a]

private theorem parameter_bounds {a : ℝ} (ha : (1/2:ℝ) ≤ a) (ha1 : a ≤ 1) :
    0 < a ∧ 0 ≤ d a ∧ 0 ≤ hh a ∧ 0 ≤ zz a ∧ 0 ≤ spokeLeaf a ∧
    0 ≤ q a ∧ q a ≤ 2/3 ∧ 0 ≤ zz a-2*a/3 ∧ 0 ≤ uu a := by
  have hp : 0 < a := by linarith
  have hq : q a + 2*hh a = (2/3:ℝ) := by
    simpa [q, hh, d] using WeightedEdgeColoring.subtwo_uniformModel_rho_h_balance hp
  have hhn : 0 ≤ hh a := by
    unfold hh
    exact div_nonneg (by nlinarith) (by positivity)
  have hqn : 0 ≤ q a := by
    unfold q d
    exact div_nonneg (by nlinarith) (by positivity)
  have hu : 0 ≤ uu a := by
    unfold uu
    have : 0 ≤ (1-q a)*d a := mul_nonneg (by linarith) (by simpa [d] using sub_nonneg.mpr ha1)
    exact this.trans (le_max_left _ _)
  constructor; exact hp
  constructor; dsimp [d]; linarith
  constructor; exact hhn
  constructor; dsimp [zz]; linarith
  constructor; dsimp [spokeLeaf, zz]; linarith
  constructor; exact hqn
  constructor; linarith
  constructor; dsimp [zz]; linarith
  exact hu

private theorem algebra_identities {a : ℝ} (ha : 0 < a) :
    Fc a/2=PH a ∧
    PH a-F2 a/2=23*(2*a-1)/144 ∧
    PH a-lightCharge*(spokeLeaf a-hh a*a)-hh a =
      (1318*a^2-1689*a+576)/(1728*a) ∧
    PH a-lightCharge*(d a-hh a*d a)-hh a =
      61*(1-a)*(3*a-1)/(432*a) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  constructor
  · dsimp [Fc, PH, d, residualCharge]
    ring
  constructor
  · dsimp [F2, PH, spokeLeaf, zz, q, d, residualCharge]
    field_simp
    ring
  constructor
  · dsimp [PH, spokeLeaf, zz, hh, lightCharge]
    field_simp
    ring
  · dsimp [PH, d, hh, lightCharge]
    field_simp
    ring

private theorem root_candidate_bounds {a : ℝ}
    (ha : (1/2:ℝ) ≤ a) (_ha1 : a ≤ 1) :
    P0 a ≥ lightCharge*(zz a-hh a*a)+hh a := by
  have hp : 0 < a := by linarith
  have h1 : 0 < (8490*a^2-9283*a+2880)/(8640*a) :=
    WeightedEdgeColoring.subtwo_uniformStar_rootBase_first hp
  have h2 : 0 < (36010*a^2-39043*a+10880)/(8640*a) :=
    WeightedEdgeColoring.subtwo_uniformStar_rootBase_second hp
  have h3 : 0 < (5270*a^2-6453*a+2880)/(8640*a) :=
    WeightedEdgeColoring.subtwo_uniformStar_rootBase_third hp
  have e1 : 157/40-2*PH a-2*PH a-lightCharge*(zz a-hh a*a)-hh a =
      (8490*a^2-9283*a+2880)/(8640*a) := by
    dsimp [PH, zz, hh, lightCharge]
    field_simp
    ring
  have e2 : 157/40-2*PH a-2*(F1 a/2)-lightCharge*(zz a-hh a*a)-hh a =
      (36010*a^2-39043*a+10880)/(8640*a) := by
    dsimp [PH, F1, zz, hh, q, d, lightCharge, residualCharge]
    field_simp
    ring
  have e3 : 157/40-2*PH a-2*(lightCharge*spokeLeaf a)-
      lightCharge*(zz a-hh a*a)-hh a =
      (5270*a^2-6453*a+2880)/(8640*a) := by
    dsimp [PH, spokeLeaf, zz, hh, lightCharge]
    field_simp
    ring
  have hc1 : PH a ≤ (157/40-2*PH a-lightCharge*(zz a-hh a*a)-hh a)/2 := by
    linarith
  have hc2 : F1 a/2 ≤ (157/40-2*PH a-lightCharge*(zz a-hh a*a)-hh a)/2 := by
    linarith
  have hc3 : lightCharge*spokeLeaf a ≤
      (157/40-2*PH a-lightCharge*(zz a-hh a*a)-hh a)/2 := by
    linarith
  have hpl : PL a ≤ (157/40-2*PH a-lightCharge*(zz a-hh a*a)-hh a)/2 := by
    exact max_le (max_le hc1 hc2) hc3
  dsimp [P0]
  linarith

private theorem spoke_candidate_bounds {a : ℝ}
    (ha : (1/2:ℝ) ≤ a) (ha1 : a ≤ 1) :
    Fs a ≤ P0 a+PH a := by
  have hp : 0 < a := by linarith
  have h1 := WeightedEdgeColoring.subtwo_uniformStar_spoke_first ha
  have h2 := WeightedEdgeColoring.subtwo_uniformStar_spoke_second hp
  have h3 := WeightedEdgeColoring.subtwo_uniformStar_spoke_third ha1
  have e1 : 157/40-3*PH a-Fs a = (690*a-317)/2160 := by
    dsimp [PH, Fs, zz, d, residualCharge]
    ring
  have e2 : 157/40-PH a-F1 a-Fs a =
      (7570*a^2-7757*a+2000)/(2160*a) := by
    dsimp [PH, F1, Fs, zz, q, d, residualCharge]
    field_simp
    ring
  have e3 : 157/40-PH a-2*lightCharge*spokeLeaf a-Fs a =
      (781-230*a)/4320 := by
    dsimp [PH, Fs, spokeLeaf, zz, d, lightCharge, residualCharge]
    ring
  have hc1 : PH a ≤ (157/40-PH a-Fs a)/2 := by linarith
  have hc2 : F1 a/2 ≤ (157/40-PH a-Fs a)/2 := by linarith
  have hc3 : lightCharge*spokeLeaf a ≤ (157/40-PH a-Fs a)/2 := by linarith
  have hpl : PL a ≤ (157/40-PH a-Fs a)/2 := max_le (max_le hc1 hc2) hc3
  dsimp [P0]
  linarith

private theorem star_facts {a : ℝ} (ha : (1/2:ℝ) ≤ a) (ha1 : a ≤ 1) :
    0 ≤ d a ∧ 0 ≤ hh a ∧ 0 ≤ zz a ∧ 0 ≤ spokeLeaf a ∧
    0 ≤ zz a-2*a/3 ∧ 0 ≤ uu a ∧
    q a * a = 2*d a/3 ∧ hh a*a = (2*a-1)/3 ∧
    2*a-zz a ≥ d a ∧
    zz a ≥ (5*a-1)/3 := by
  rcases parameter_bounds ha ha1 with ⟨hp, hd, hh0, hz, hs, hqn, hq, hqr, hρ⟩
  have hqa : q a * a = 2*d a/3 := by
    dsimp [q]
    field_simp
  have hha : hh a*a = (2*a-1)/3 := by
    dsimp [hh]
    field_simp
  refine ⟨hd, hh0, hz, hs, hqr, hρ, hqa, hha, ?_, ?_⟩
  · dsimp [zz, d]
    linarith
  · dsimp [zz]
    linarith

private theorem star_c_nonneg {a : ℝ} (ha : (1/2:ℝ) ≤ a) (ha1 : a ≤ 1) :
    0 ≤ zz a-hh a*a ∧
    0 ≤ max (spokeLeaf a-hh a*a) (d a-hh a*d a) := by
  rcases star_facts ha ha1 with ⟨hd, hhn, _, _, _, _, _, hha, _, hz⟩
  have hq := WeightedEdgeColoring.subtwo_uniformModel_rho_h_balance (by linarith : 0 < a)
  change q a + 2*hh a = 2/3 at hq
  have hqn : 0 ≤ q a := (parameter_bounds ha ha1).2.2.2.2.2.1
  have hhle : hh a ≤ 1 := by linarith
  constructor
  · linarith
  · have hm : 0 ≤ d a-hh a*d a := by
      nlinarith [mul_nonneg hd (by linarith : 0 ≤ 1-hh a)]
    exact hm.trans (le_max_right _ _)

private theorem star_PL_ge {a : ℝ} :
    PH a ≤ PL a ∧ F1 a/2 ≤ PL a ∧ lightCharge*spokeLeaf a ≤ PL a := by
  dsimp [PL]
  exact ⟨(le_max_left _ _).trans (le_max_left _ _),
    (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _⟩

noncomputable def uniformStar_certificate (a : ℝ)
    (ha : (1/2:ℝ) ≤ a) (ha1 : a ≤ 1) :
    Certificate (uniformStarM a) (uniformStarRho a) (uniformStarH a) where
  z := starZ a
  c := starC a
  alpha := starAlpha a
  P := starP a
  z_nonneg := by
    intro v e
    rcases star_facts ha ha1 with ⟨hd, _, hz, hs, _, _, _, _, _, _⟩
    fin_cases v <;> fin_cases e <;>
      simp [starZ, d, zz, spokeLeaf] <;> linarith
  c_nonneg := by
    intro v
    obtain ⟨hc0, hcl⟩ := star_c_nonneg ha ha1
    have hspoke : 0 ≤ spokeLeaf a := (star_facts ha ha1).2.2.2.1
    fin_cases v <;> first
      | simpa [starC] using hc0
      | simpa [starC] using hcl
      | simpa [starC] using hspoke
  alpha_nonneg := by
    intro v e
    rcases star_facts ha ha1 with ⟨hd, _, _, _, hza, hu, _, _, _, _⟩
    fin_cases v <;> fin_cases e <;> simp [starAlpha] <;> linarith
  P_nonneg := by
    intro v
    have hroot := root_candidate_bounds ha ha1
    have hph : 0 ≤ PH a := by dsimp [PH]; linarith
    have hpl : 0 ≤ PL a := le_trans hph (star_PL_ge.1)
    obtain ⟨hc0, _⟩ := star_c_nonneg ha ha1
    have hh0 : 0 ≤ hh a := (parameter_bounds ha ha1).2.2.1
    have hA : 0 ≤ lightCharge := by norm_num [lightCharge]
    have hp0 : 0 ≤ P0 a := by nlinarith [mul_nonneg hA hc0]
    fin_cases v <;> first
      | simpa [starP] using hp0
      | simpa [starP] using hph
      | simpa [starP] using hpl
  split := by
    intro e
    fin_cases e <;> simp [starZ, uniformStarM, left, right, spokeLeaf] <;> ring
  light := by
    intro v e he
    rcases star_facts ha ha1 with ⟨hd, hh0, hz, hs, _, _, _, hha, hleaf, _⟩
    change d a ≤ spokeLeaf a at hleaf
    have hmx1 : spokeLeaf a-hh a*a ≤
        max (spokeLeaf a-hh a*a) (d a-hh a*d a) := le_max_left _ _
    have hmx2 : d a-hh a*d a ≤
        max (spokeLeaf a-hh a*a) (d a-hh a*d a) := le_max_right _ _
    fin_cases v <;> fin_cases e <;>
      simp [Inc, left, right] at he <;>
      simp [starZ, starC, uniformStarM, uniformStarH] <;>
      linarith
  baseline := by
    intro v
    have hroot := root_candidate_bounds ha ha1
    have hleaf := algebra_identities (by linarith : 0 < a)
    have hleaf1 := WeightedEdgeColoring.subtwo_uniformStar_leaf_first (by linarith : 0 < a)
    have hleaf2 := WeightedEdgeColoring.subtwo_uniformStar_leaf_second ha ha1
    have hpl := star_PL_ge (a:=a)
    have hb1 : lightCharge*(spokeLeaf a-hh a*a)+hh a ≤ PH a := by
      linarith [hleaf.2.2.1]
    have hb2 : lightCharge*(d a-hh a*d a)+hh a ≤ PH a := by
      linarith [hleaf.2.2.2]
    have hbmax : lightCharge*max (spokeLeaf a-hh a*a) (d a-hh a*d a)+hh a ≤ PH a := by
      rcases le_total (spokeLeaf a-hh a*a) (d a-hh a*d a) with hxy | hyx
      · rw [max_eq_right hxy]; exact hb2
      · rw [max_eq_left hyx]; exact hb1
    fin_cases v <;>
      simp [starP, starC, uniformStarH] <;>
      try { exact hroot } <;>
      try { exact hpl.2.2 } <;>
      try { exact hbmax }
  off := by
    intro v e f he hf hfe
    rcases star_facts ha ha1 with ⟨hd, hh0, hz, hs, hza, hu, hqa, hha, hleaf, hroot⟩
    obtain ⟨_, _, _, _, _, _, hqq, _, _⟩ := parameter_bounds ha ha1
    have hu1 : (1-q a)*d a ≤ uu a := le_max_left _ _
    have hu2 : spokeLeaf a-q a*a ≤ uu a := le_max_right _ _
    have hsl : spokeLeaf a ≤ 2*a/3+d a/3 := by
      dsimp [spokeLeaf, zz, d]
      linarith
    fin_cases v <;> fin_cases e <;> fin_cases f <;>
      simp [Inc, left, right] at he hf hfe <;>
      simp [starZ, starAlpha, uniformStarM, uniformStarRho] <;>
      linarith
  same := by
    intro v e he
    rcases star_facts ha ha1 with ⟨hd, _, _, _, _, _, hqa, _, _, _⟩
    have hu1 : (1-q a)*d a ≤ uu a := le_max_left _ _
    have hsl : spokeLeaf a ≤ 2*a/3+d a/3 := by
      dsimp [spokeLeaf, zz, d]
      linarith
    obtain ⟨_, _, _, _, _, _, hqq, _, _⟩ := parameter_bounds ha ha1
    have hqd : 0 ≤ (1-q a)*d a := mul_nonneg (by linarith) hd
    fin_cases v <;> fin_cases e <;>
      simp [Inc, left, right] at he <;>
      simp [starZ, starAlpha, uniformStarM, uniformStarRho] <;>
      linarith
  pair := by
    intro e
    rcases star_facts ha ha1 with ⟨hd, _, _, _, _, _, hqa, _, _, hroot⟩
    have hu1 : (1-q a)*d a ≤ uu a := le_max_left _ _
    obtain ⟨_, _, _, _, _, _, hqq, _, _⟩ := parameter_bounds ha ha1
    have hsp : 2*a/3 ≤ zz a-2*a/3+d a/3 := by
      dsimp [d]
      linarith
    have hqd : 0 ≤ (2-3*q a)*d a := mul_nonneg (by linarith) hd
    fin_cases e <;>
      simp [left, right, starAlpha, uniformStarM, uniformStarRho] <;>
      linarith
  edge := by
    intro e
    have hspoke := spoke_candidate_bounds ha ha1
    have hcore : Fc a/2 = PH a := (algebra_identities (by linarith : 0 < a)).1
    have houter : PH a-F2 a/2 = 23*(2*a-1)/144 :=
      (algebra_identities (by linarith : 0 < a)).2.1
    have houter0 := WeightedEdgeColoring.subtwo_uniformStar_outer_branch ha
    have hpl := star_PL_ge (a:=a)
    have hF1 : F1 a ≤ 2*PL a := by linarith [hpl.2.1]
    have hF2 : F2 a ≤ 2*PL a := by linarith
    have hf : (2-q a)*d a+q a+2*residualCharge*uu a ≤ 2*PL a := by
      rcases le_total ((1-q a)*d a) (spokeLeaf a-q a*a) with h | h
      · simp only [uu, max_eq_right h]
        dsimp [F2] at hF2
        nlinarith
      · simp only [uu, max_eq_left h]
        dsimp [F1] at hF1
        nlinarith
    have hspokeL : Fs a ≤ P0 a+PL a := by linarith [hspoke, hpl.1]
    have hcoreHH : Fc a ≤ PH a+PH a := by linarith
    have hcoreHL : Fc a ≤ PH a+PL a := by linarith [hcoreHH, hpl.1]
    have hcoreLL : Fc a ≤ PL a+PL a := by linarith [hcoreHH, hpl.1]
    dsimp [Fs, Fc] at hspoke hspokeL hcoreHH hcoreHL hcoreLL
    fin_cases e <;>
      simp [left, right, starP, starAlpha, uniformStarM, uniformStarRho] <;>
      linarith

theorem uniformStar_budget (a : ℝ) (ha : (1/2:ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∑ v, (uniformStar_certificate a ha ha1).P v = (157/40:ℝ) := by
  simp [uniformStar_certificate, starP, Fin.sum_univ_five, P0]
  ring

end WeightedEdgeColoring.Subtwo.EndpointPotential
