import WeightedEdgeColoring.MultigraphProposalDeficit
import WeightedEdgeColoring.TinyEdgePartialRounding
import WeightedEdgeColoring.MultigraphTinyEdgeResidualRounding
import WeightedEdgeColoring.MultigraphLargeStarCategoricalDependency

/-!
# Trimming and deterministic rounding of the tiny proposal part

Edges whose proposal mass is small can be charged directly to the proposal
deficit.  On the remaining tiny edges, normalize the proposal to mass one
and apply the already proved two-constraint rounding theorem.  This leaves
only the genuinely macroscopic edges for the whole-edge argument.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

def proposalMass {Color : Type*} [Fintype Color]
    (x : G.E → Color → ℝ) (e : G.E) : ℝ :=
  ∑ c, x e c

def lowProposalMassEdges {Color : Type*} [Fintype Color]
    (x : G.E → Color → ℝ)
    (gamma : ℝ) : Finset G.E :=
  Finset.univ.filter fun e ↦ G.proposalMass x e < 1 - gamma

def retainedTinyEdges {Color : Type*} [Fintype Color]
    (x : G.E → Color → ℝ)
    (gamma tau : ℝ) : Finset G.E :=
  Finset.univ.filter fun e ↦
    1 - gamma ≤ G.proposalMass x e ∧ G.weight e < tau

def retainedMacroscopicEdges {Color : Type*} [Fintype Color]
    (x : G.E → Color → ℝ)
    (gamma tau : ℝ) : Finset G.E :=
  Finset.univ.filter fun e ↦
    1 - gamma ≤ G.proposalMass x e ∧ tau ≤ G.weight e

def macroscopicEdges (tau : ℝ) : Finset G.E :=
  Finset.univ.filter fun e ↦ tau ≤ G.weight e

def normalizedRetainedProposal {Color : Type*} [Fintype Color]
    (x : G.E → Color → ℝ)
    (gamma tau : ℝ) (e : {e : G.E // e ∈ G.retainedTinyEdges x gamma tau})
    (c : Color) : ℝ :=
  x e.1 c / G.proposalMass x e.1

/-- The colors to which the proposal assigns positive mass on an edge. -/
def proposalSupport {Color : Type*} [Fintype Color]
    (x : G.E → Color → ℝ) (e : G.E) : Finset Color :=
  Finset.univ.filter fun c ↦ 0 < x e c

/-- The macroscopic edges in one star.  This is the star-indexed form of
`macroscopicEdges`, convenient for degree bounds. -/
def macroscopicStarEdges (tau : ℝ) (v : G.V) : Finset (G.StarEdge v) :=
  Finset.univ.filter fun e ↦ tau ≤ G.weight e.1

@[simp] theorem mem_lowProposalMassEdges {Color : Type*} [Fintype Color]
    (x : G.E → Color → ℝ) (gamma : ℝ) (e : G.E) :
    e ∈ G.lowProposalMassEdges x gamma ↔
      G.proposalMass x e < 1 - gamma := by
  simp [lowProposalMassEdges]

@[simp] theorem mem_retainedTinyEdges {Color : Type*} [Fintype Color]
    (x : G.E → Color → ℝ) (gamma tau : ℝ) (e : G.E) :
    e ∈ G.retainedTinyEdges x gamma tau ↔
      1 - gamma ≤ G.proposalMass x e ∧ G.weight e < tau := by
  simp [retainedTinyEdges]

@[simp] theorem mem_retainedMacroscopicEdges {Color : Type*} [Fintype Color]
    (x : G.E → Color → ℝ) (gamma tau : ℝ) (e : G.E) :
    e ∈ G.retainedMacroscopicEdges x gamma tau ↔
      1 - gamma ≤ G.proposalMass x e ∧ tau ≤ G.weight e := by
  simp [retainedMacroscopicEdges]

theorem retainedMacroscopicEdges_disjoint_retainedTinyEdges
    {Color : Type*} [Fintype Color]
    (x : G.E → Color → ℝ) (gamma tau : ℝ) :
    Disjoint (G.retainedMacroscopicEdges x gamma tau)
      (G.retainedTinyEdges x gamma tau) := by
  rw [Finset.disjoint_left]
  intro e heMacro heTiny
  have hge := (G.mem_retainedMacroscopicEdges x gamma tau e).mp heMacro |>.2
  have hlt := (G.mem_retainedTinyEdges x gamma tau e).mp heTiny |>.2
  exact (not_lt_of_ge hge) hlt

/-- The two retained classes are exactly the edges whose proposal mass is
at least `1-gamma`. -/
theorem mem_retainedMacroscopic_union_retainedTiny
    {Color : Type*} [Fintype Color]
    (x : G.E → Color → ℝ) (gamma tau : ℝ) (e : G.E) :
    e ∈ G.retainedMacroscopicEdges x gamma tau ∪
        G.retainedTinyEdges x gamma tau ↔
      1 - gamma ≤ G.proposalMass x e := by
  constructor
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · exact (G.mem_retainedMacroscopicEdges x gamma tau e).mp he |>.1
    · exact (G.mem_retainedTinyEdges x gamma tau e).mp he |>.1
  · intro he
    by_cases hweight : G.weight e < tau
    · exact Finset.mem_union_right _
        ((G.mem_retainedTinyEdges x gamma tau e).mpr ⟨he, hweight⟩)
    · exact Finset.mem_union_left _
        ((G.mem_retainedMacroscopicEdges x gamma tau e).mpr
          ⟨he, le_of_not_gt hweight⟩)

@[simp] theorem mem_proposalSupport {Color : Type*} [Fintype Color]
    (x : G.E → Color → ℝ) (e : G.E) (c : Color) :
    c ∈ G.proposalSupport x e ↔ 0 < x e c := by
  simp [proposalSupport]

@[simp] theorem mem_macroscopicStarEdges
    (tau : ℝ) (v : G.V) (e : G.StarEdge v) :
    e ∈ G.macroscopicStarEdges tau v ↔ tau ≤ G.weight e.1 := by
  simp [macroscopicStarEdges]

/-- A pointwise diffuse proposal can put total mass `m` on an edge only if
the edge has at least `m n / C0` available colors.  The multiplicative form
avoids division and is the useful Hall-capacity inequality. -/
theorem proposalMass_le_cap_mul_supportCard
    {Color : Type*} [Fintype Color] {n : ℕ}
    (x : G.E → Color → ℝ) (C0 : ℝ)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hcap : ∀ e c, x e c ≤ C0 / n) (e : G.E) :
    G.proposalMass x e ≤
      (G.proposalSupport x e).card * (C0 / n) := by
  classical
  have hrestrict :
      (∑ c : Color, x e c) =
        ∑ c ∈ G.proposalSupport x e, x e c := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro c _hc hnot
    have hnpos : ¬ 0 < x e c := by
      simpa [proposalSupport] using hnot
    exact le_antisymm (le_of_not_gt hnpos) (hx0 e c)
  rw [proposalMass, hrestrict]
  calc
    (∑ c ∈ G.proposalSupport x e, x e c) ≤
        ∑ _c ∈ G.proposalSupport x e, C0 / n := by
      apply Finset.sum_le_sum
      intro c _hc
      exact hcap e c
    _ = (G.proposalSupport x e).card * (C0 / n) := by simp

/-- On a retained edge the diffuse cap gives an explicit linear lower bound
on the number of supported colors. -/
theorem retained_support_capacity
    {Color : Type*} [Fintype Color] {n : ℕ}
    (x : G.E → Color → ℝ) (C0 gamma tau : ℝ)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hcap : ∀ e c, x e c ≤ C0 / n)
    (e : G.E) (he : e ∈ G.retainedTinyEdges x gamma tau) :
    1 - gamma ≤
      (G.proposalSupport x e).card * (C0 / n) := by
  exact ((G.mem_retainedTinyEdges x gamma tau e).mp he).1.trans
    (G.proposalMass_le_cap_mul_supportCard x C0 hx0 hcap e)

/-- The number of edges of weight at least `tau` incident with a vertex is at most
the star weight divided by `tau`.  This needs no local-packing witness. -/
theorem macroscopicStarEdges_card_le_div
    (tau : ℝ) (htau : 0 < tau) (v : G.V) :
    ((G.macroscopicStarEdges tau v).card : ℝ) ≤
      G.starWeight v / tau := by
  apply (le_div_iff₀ htau).2
  calc
    ((G.macroscopicStarEdges tau v).card : ℝ) * tau =
        ∑ _e ∈ G.macroscopicStarEdges tau v, tau := by simp
    _ ≤ ∑ e ∈ G.macroscopicStarEdges tau v, G.weight e.1 := by
      apply Finset.sum_le_sum
      intro e he
      exact (G.mem_macroscopicStarEdges tau v e).mp he
    _ ≤ ∑ e : G.StarEdge v, G.weight e.1 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun _ _ ↦ Finset.mem_univ _)
        (fun e _ _ ↦ G.weight_nonneg e.1)
    _ = G.starWeight v := rfl

/-- Uniform degree form of `macroscopicStarEdges_card_le_div`. -/
theorem macroscopicStarEdges_card_le_n_div
    {n : ℕ} (tau : ℝ) (htau : 0 < tau)
    (hstar : ∀ v, G.starWeight v ≤ n) (v : G.V) :
    ((G.macroscopicStarEdges tau v).card : ℝ) ≤ (n : ℝ) / tau := by
  exact (G.macroscopicStarEdges_card_le_div tau htau v).trans
    (div_le_div_of_nonneg_right (hstar v) htau.le)

/-- The support-capacity estimate without referring to a particular edge
class.  In applications `hmass` is the high-mass side of the trim. -/
theorem support_capacity_of_proposalMass_ge
    {Color : Type*} [Fintype Color] {n : ℕ}
    (x : G.E → Color → ℝ) (C0 m : ℝ)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hcap : ∀ e c, x e c ≤ C0 / n)
    (e : G.E) (hmass : m ≤ G.proposalMass x e) :
    m ≤ (G.proposalSupport x e).card * (C0 / n) := by
  exact hmass.trans
    (G.proposalMass_le_cap_mul_supportCard x C0 hx0 hcap e)

/-- The entire low-mass edge set is paid for by the fractional proposal
deficit, with the sharp factor `1/gamma`. -/
theorem lowProposalMassWeight_le_deficit_div {q : ℕ}
    (x : G.E → Fin q → ℝ) (gamma : ℝ) (hgamma : 0 < gamma)
    (hmass : ∀ e, G.proposalMass x e ≤ 1) (v : G.V) :
    (∑ e ∈ G.lowProposalMassEdges x gamma,
      if G.Inc v e then G.weight e else 0) ≤
      G.proposalDeficit x v / gamma := by
  apply (le_div_iff₀ hgamma).2
  calc
    (∑ e ∈ G.lowProposalMassEdges x gamma,
        if G.Inc v e then G.weight e else 0) * gamma =
        ∑ e ∈ G.lowProposalMassEdges x gamma,
          (if G.Inc v e then G.weight e else 0) * gamma := by
      rw [Finset.sum_mul]
    _ ≤ ∑ e ∈ G.lowProposalMassEdges x gamma,
          if G.Inc v e then
            G.weight e * (1 - G.proposalMass x e) else 0 := by
      apply Finset.sum_le_sum
      intro e he
      have heLow := G.mem_lowProposalMassEdges x gamma e |>.mp he
      by_cases hinc : G.Inc v e
      · simp only [hinc, if_true]
        have hgap : gamma ≤ 1 - G.proposalMass x e := by
          linarith
        exact mul_le_mul_of_nonneg_left hgap (G.weight_nonneg e)
      · simp [hinc]
    _ ≤ ∑ e : G.E,
          if G.Inc v e then
            G.weight e * (1 - G.proposalMass x e) else 0 := by
      apply Finset.sum_le_univ_sum_of_nonneg
      intro e
      by_cases hinc : G.Inc v e
      · simp only [hinc, if_true]
        exact mul_nonneg (G.weight_nonneg e) (sub_nonneg.mpr (hmass e))
      · simp [hinc]
    _ = G.proposalDeficit x v := by
      rfl

/-- After the deterministic tiny rounding, every remaining edge is either
low-proposal-mass or genuinely macroscopic. -/
theorem residualWeight_retainedTiny_le {q : ℕ}
    (x : G.E → Fin q → ℝ) (gamma tau : ℝ) (hgamma : 0 < gamma)
    (hmass : ∀ e, G.proposalMass x e ≤ 1) (v : G.V) :
    (∑ e ∈ Finset.univ \ G.retainedTinyEdges x gamma tau,
      if G.Inc v e then G.weight e else 0) ≤
      G.proposalDeficit x v / gamma +
        ∑ e ∈ G.macroscopicEdges tau,
          if G.Inc v e then G.weight e else 0 := by
  let f : G.E → ℝ := fun e ↦ if G.Inc v e then G.weight e else 0
  have hf0 : ∀ e, 0 ≤ f e := by
    intro e
    dsimp [f]
    split
    · exact G.weight_nonneg e
    · exact le_rfl
  have hpoint : ∀ e,
      (if e ∈ Finset.univ \ G.retainedTinyEdges x gamma tau then f e else 0) ≤
        (if e ∈ G.lowProposalMassEdges x gamma then f e else 0) +
          (if e ∈ G.macroscopicEdges tau then f e else 0) := by
    intro e
    by_cases heR : e ∈ Finset.univ \ G.retainedTinyEdges x gamma tau
    · have hnot : ¬(1 - gamma ≤ G.proposalMass x e ∧ G.weight e < tau) := by
        intro h
        exact (Finset.mem_sdiff.mp heR).2
          (G.mem_retainedTinyEdges x gamma tau e |>.mpr h)
      have hsplit : G.proposalMass x e < 1 - gamma ∨ tau ≤ G.weight e := by
        by_cases hlow : G.proposalMass x e < 1 - gamma
        · exact Or.inl hlow
        · right
          exact le_of_not_gt fun hweight ↦ hnot ⟨le_of_not_gt hlow, hweight⟩
      rcases hsplit with hlow | hlarge
      · have hmem : e ∈ G.lowProposalMassEdges x gamma :=
          G.mem_lowProposalMassEdges x gamma e |>.mpr hlow
        rw [if_pos heR, if_pos hmem]
        apply le_add_of_nonneg_right
        by_cases hmacro : e ∈ G.macroscopicEdges tau
        · simp [hmacro, hf0 e]
        · simp [hmacro]
      · have hmem : e ∈ G.macroscopicEdges tau := by
          simp [macroscopicEdges, hlarge]
        rw [if_pos heR, if_pos hmem]
        apply le_add_of_nonneg_left
        by_cases hlowMem : e ∈ G.lowProposalMassEdges x gamma
        · simp [hlowMem, hf0 e]
        · simp [hlowMem]
    · rw [if_neg heR]
      apply add_nonneg
      · by_cases hlow : e ∈ G.lowProposalMassEdges x gamma
        · simp [hlow, hf0 e]
        · simp [hlow]
      · by_cases hmacro : e ∈ G.macroscopicEdges tau
        · simp [hmacro, hf0 e]
        · simp [hmacro]
  have hsum := Finset.sum_le_sum (fun e (_he : e ∈ (Finset.univ : Finset G.E)) ↦
    hpoint e)
  simp only [Finset.sum_add_distrib] at hsum
  have hfilterSum (S : Finset G.E) :
      (∑ e : G.E, if e ∈ S then f e else 0) = ∑ e ∈ S, f e := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext e
      simp
    · intro e _he
      rfl
  have hlow := G.lowProposalMassWeight_le_deficit_div
    x gamma hgamma hmass v
  have hlow' :
      (∑ e : G.E, if e ∈ G.lowProposalMassEdges x gamma then f e else 0) ≤
        G.proposalDeficit x v / gamma := by
    rw [hfilterSum]
    simpa [f] using hlow
  change (∑ e ∈ Finset.univ \ G.retainedTinyEdges x gamma tau, f e) ≤
    G.proposalDeficit x v / gamma +
      ∑ e ∈ G.macroscopicEdges tau, f e
  rw [← hfilterSum (Finset.univ \ G.retainedTinyEdges x gamma tau),
    ← hfilterSum (G.macroscopicEdges tau)]
  exact hsum.trans (add_le_add hlow' le_rfl)

theorem sum_normalizedRetainedProposal {Color : Type*} [Fintype Color]
    (x : G.E → Color → ℝ) (gamma tau : ℝ) (hgamma : gamma < 1)
    (e : {e : G.E // e ∈ G.retainedTinyEdges x gamma tau}) :
    ∑ c, G.normalizedRetainedProposal x gamma tau e c = 1 := by
  have he := G.mem_retainedTinyEdges x gamma tau e.1 |>.mp e.2
  have hmassPos : 0 < G.proposalMass x e.1 :=
    lt_of_lt_of_le (sub_pos.mpr hgamma) he.1
  unfold normalizedRetainedProposal proposalMass
  rw [← Finset.sum_div]
  exact div_self hmassPos.ne'

/-- Normalization increases every retained fractional row by at most the
factor `(1-gamma)⁻¹`. -/
theorem tinyOnFractionalLoad_normalizedRetained_le {q : ℕ}
    (x : G.E → Fin q → ℝ) (gamma tau : ℝ) (hgamma : gamma < 1)
    (hx0 : ∀ e c, 0 ≤ x e c) (v : G.V) (c : Fin q) :
    G.tinyOnFractionalLoad
        (G.retainedTinyEdges x gamma tau)
        (G.normalizedRetainedProposal x gamma tau) v c ≤
      (1 / (1 - gamma)) *
        ∑ e : G.StarEdge v, G.weight e.1 * x e.1 c := by
  let R := G.retainedTinyEdges x gamma tau
  unfold WeightedMultigraph.tinyOnFractionalLoad
    normalizedRetainedProposal
  calc
    (∑ e : {e : G.E // e ∈ R},
      if G.Inc v e.1 then
        x e.1 c / G.proposalMass x e.1 * G.weight e.1 else 0) ≤
        ∑ e : {e : G.E // e ∈ R},
          if G.Inc v e.1 then
            (1 / (1 - gamma)) * (G.weight e.1 * x e.1 c) else 0 := by
      apply Finset.sum_le_sum
      intro e _he
      have heR := G.mem_retainedTinyEdges x gamma tau e.1 |>.mp e.2
      have hden : 0 < 1 - gamma := sub_pos.mpr hgamma
      have hmassPos : 0 < G.proposalMass x e.1 := hden.trans_le heR.1
      by_cases hinc : G.Inc v e.1
      · simp only [hinc, if_true]
        have hinv : 1 / G.proposalMass x e.1 ≤ 1 / (1 - gamma) :=
          one_div_le_one_div_of_le hden heR.1
        calc
          x e.1 c / G.proposalMass x e.1 * G.weight e.1 =
              (1 / G.proposalMass x e.1) * (G.weight e.1 * x e.1 c) := by ring
          _ ≤ (1 / (1 - gamma)) * (G.weight e.1 * x e.1 c) :=
            mul_le_mul_of_nonneg_right hinv
              (mul_nonneg (G.weight_nonneg e.1) (hx0 e.1 c))
      · simp [hinc]
    _ = ∑ e ∈ R,
          if G.Inc v e then
            (1 / (1 - gamma)) * (G.weight e * x e c) else 0 := by
      exact (Finset.sum_subtype (p := fun e : G.E ↦ e ∈ R) R
        (by intro e; simp)
        (fun e ↦ if G.Inc v e then
          (1 / (1 - gamma)) * (G.weight e * x e c) else 0)).symm
    _ ≤ ∑ e : G.E,
          if G.Inc v e then
            (1 / (1 - gamma)) * (G.weight e * x e c) else 0 := by
      apply Finset.sum_le_univ_sum_of_nonneg
      intro e
      by_cases hinc : G.Inc v e
      · simp [hinc]
        exact mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hgamma.le))
          (mul_nonneg (G.weight_nonneg e) (hx0 e c))
      · simp [hinc]
    _ = (1 / (1 - gamma)) *
        ∑ e : G.StarEdge v, G.weight e.1 * x e.1 c := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
        (by intro e; simp) (fun e ↦
          (1 / (1 - gamma)) * (G.weight e * x e c))

/-- Support-preserving form of the restricted tiny-edge rounding theorem.
It records the row estimate as well as positivity of every selected proposal
coordinate. -/
theorem exists_retainedTinyColoring_with_load {q : ℕ}
    (hq : 0 < q) (x : G.E → Fin q → ℝ)
    (gamma tau : ℝ) (hgamma1 : gamma < 1) (htau : 0 < tau)
    (hx0 : ∀ e c, 0 ≤ x e c) :
    ∃ color : G.E → Fin q,
      (∀ v c,
        G.colorLoadOn (G.retainedTinyEdges x gamma tau)
            color v c ≤
          G.tinyOnFractionalLoad
              (G.retainedTinyEdges x gamma tau)
              (G.normalizedRetainedProposal x gamma tau) v c + 2 * tau) ∧
      ∀ e ∈ G.retainedTinyEdges x gamma tau,
        0 < x e (color e) := by
  let R := G.retainedTinyEdges x gamma tau
  let y : {e : G.E // e ∈ R} → Fin q → ℝ :=
    G.normalizedRetainedProposal x gamma tau
  have hy0 : ∀ e c, 0 ≤ y e c := by
    intro e c
    unfold y normalizedRetainedProposal
    have heR := G.mem_retainedTinyEdges x gamma tau e.1 |>.mp e.2
    have hmassPos : 0 < G.proposalMass x e.1 :=
      (sub_pos.mpr hgamma1).trans_le heR.1
    exact div_nonneg (hx0 e.1 c) hmassPos.le
  have hysum : ∀ e, ∑ c, y e c = 1 := by
    intro e
    exact G.sum_normalizedRetainedProposal x gamma tau hgamma1 e
  have hweight : ∀ e ∈ R, G.weight e ≤ tau := by
    intro e he
    exact (G.mem_retainedTinyEdges x gamma tau e).mp he |>.2.le
  rcases G.exists_tinyColorDecision R tau htau y
      (fun _e ↦ 0) hy0 (fun _e ↦ le_rfl)
      (by intro e; simp [hysum e]) hweight with
    ⟨decision, hpositive, hnone, hcolorLoad, _hloss⟩
  have hsome : ∀ e, ∃ c, decision e = some c := by
    intro e
    cases h : decision e with
    | none => exact False.elim ((hnone e h).false)
    | some c => exact ⟨c, rfl⟩
  let chosen : {e : G.E // e ∈ R} → Fin q :=
    fun e ↦ Classical.choose (hsome e)
  have hchosen : ∀ e, decision e = some (chosen e) := by
    intro e
    exact Classical.choose_spec (hsome e)
  let fallback : Fin q := ⟨0, hq⟩
  let color : G.E → Fin q := fun e ↦
    if he : e ∈ R then chosen ⟨e, he⟩ else fallback
  have hloadEq : ∀ v c,
      G.colorLoadOn R color v c =
        G.tinyResidualIntegralColorLoad decision v c := by
    intro v c
    unfold WeightedMultigraph.colorLoadOn
      WeightedMultigraph.tinyResidualIntegralColorLoad
    rw [Finset.sum_subtype (p := fun e : G.E ↦ e ∈ R) R
      (by intro e; simp)]
    apply Finset.sum_congr rfl
    intro e _he
    rw [hchosen e]
    simp [color, e.2, chosen]
  refine ⟨color, ?_, ?_⟩
  · intro v c
    rw [hloadEq]
    exact hcolorLoad v c
  · intro e he
    have hmass : 0 < G.proposalMass x e := by
      have heR := (G.mem_retainedTinyEdges x gamma tau e).mp he
      exact (sub_pos.mpr hgamma1).trans_le heR.1
    have hcolorEq : color e = chosen ⟨e, he⟩ := by
      unfold color
      rw [dif_pos he]
    have hySelected : 0 < y ⟨e, he⟩ (color e) := by
      rw [hcolorEq]
      exact hpositive ⟨e, he⟩ (chosen ⟨e, he⟩) (hchosen ⟨e, he⟩)
    unfold y normalizedRetainedProposal at hySelected
    rcases (div_pos_iff.mp hySelected) with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge (hx0 e (color e))) h.1)

/-- Extend an arbitrary feasible coloring of the macroscopic part by all
retained tiny edges.  The only compatibility condition is the displayed
per-row residual-capacity inequality.  The extension keeps the old colors
and selects every new color from positive proposal support. -/
theorem exists_extend_with_retainedTiny_exact {q : ℕ}
    (hq : 0 < q) (x : G.E → Fin q → ℝ)
    (gamma tau : ℝ) (hgamma1 : gamma < 1) (htau : 0 < tau)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (P : Finset G.E) (base : G.E → Fin q)
    (hdisj : Disjoint P (G.retainedTinyEdges x gamma tau))
    (hbase : G.IsFeasibleOn P base)
    (hroom : ∀ v c,
      G.colorLoadOn P base v c +
          G.tinyOnFractionalLoad
            (G.retainedTinyEdges x gamma tau)
            (G.normalizedRetainedProposal x gamma tau) v c +
          2 * tau ≤ 1) :
    ∃ color : G.E → Fin q,
      G.IsFeasibleOn
        (P ∪ G.retainedTinyEdges x gamma tau) color ∧
      (∀ e ∈ P, color e = base e) ∧
      ∀ e ∈ G.retainedTinyEdges x gamma tau,
        0 < x e (color e) := by
  let R := G.retainedTinyEdges x gamma tau
  rcases G.exists_retainedTinyColoring_with_load
      hq x gamma tau hgamma1 htau hx0 with
    ⟨tiny, htinyLoad, htinySupport⟩
  let color : G.E → Fin q := fun e ↦ if e ∈ P then base e else tiny e
  refine ⟨color, ?_, ?_, ?_⟩
  · intro v c
    have hload :
        G.colorLoadOn (P ∪ R) color v c =
          G.colorLoadOn P base v c +
            G.colorLoadOn R tiny v c := by
      unfold WeightedMultigraph.colorLoadOn
      rw [Finset.sum_union hdisj]
      congr 1
      · apply Finset.sum_congr rfl
        intro e heP
        simp [color, heP]
      · apply Finset.sum_congr rfl
        intro e heR
        have heNP : e ∉ P := fun heP ↦
          Finset.disjoint_left.mp hdisj heP heR
        simp [color, heNP]
    rw [hload]
    calc
      G.colorLoadOn P base v c +
          G.colorLoadOn R tiny v c ≤
        G.colorLoadOn P base v c +
          (G.tinyOnFractionalLoad R
              (G.normalizedRetainedProposal x gamma tau) v c +
          2 * tau) := by
            simpa [R] using add_le_add_left (htinyLoad v c)
              (G.colorLoadOn P base v c)
      _ = G.colorLoadOn P base v c +
          G.tinyOnFractionalLoad R
            (G.normalizedRetainedProposal x gamma tau) v c +
          2 * tau := by ring
      _ ≤ 1 := hroom v c
  · intro e heP
    simp [color, heP]
  · intro e heR
    have heNP : e ∉ P := fun heP ↦
      Finset.disjoint_left.mp hdisj heP heR
    simpa [color, heNP] using htinySupport e heR

/-- A coarser but often convenient corollary in terms of the original full
proposal row. -/
theorem exists_extend_with_retainedTiny {q : ℕ}
    (hq : 0 < q) (x : G.E → Fin q → ℝ)
    (gamma tau : ℝ) (hgamma1 : gamma < 1) (htau : 0 < tau)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (P : Finset G.E) (base : G.E → Fin q)
    (hdisj : Disjoint P (G.retainedTinyEdges x gamma tau))
    (hbase : G.IsFeasibleOn P base)
    (hroom : ∀ v c,
      G.colorLoadOn P base v c +
          (1 / (1 - gamma)) *
            (∑ e : G.StarEdge v, G.weight e.1 * x e.1 c) +
          2 * tau ≤ 1) :
    ∃ color : G.E → Fin q,
      G.IsFeasibleOn
        (P ∪ G.retainedTinyEdges x gamma tau) color ∧
      (∀ e ∈ P, color e = base e) ∧
      ∀ e ∈ G.retainedTinyEdges x gamma tau,
        0 < x e (color e) := by
  apply G.exists_extend_with_retainedTiny_exact hq x gamma tau hgamma1 htau
    hx0 P base hdisj hbase
  intro v c
  calc
    G.colorLoadOn P base v c +
          G.tinyOnFractionalLoad
            (G.retainedTinyEdges x gamma tau)
            (G.normalizedRetainedProposal x gamma tau) v c +
          2 * tau ≤
      G.colorLoadOn P base v c +
          (1 / (1 - gamma)) *
            (∑ e : G.StarEdge v, G.weight e.1 * x e.1 c) +
          2 * tau := by
      gcongr
      exact G.tinyOnFractionalLoad_normalizedRetained_le
        x gamma tau hgamma1 hx0 v c
    _ ≤ 1 := hroom v c

/-- Exact trim-and-extend reduction.  Once the high-mass macroscopic edges
have a support-preserving coloring leaving the normalized tiny rows enough
room, every high-mass edge is colored.  Consequently the entire residual is
charged to proposal deficit, with factor `1/gamma` and no additional
macroscopic-weight term. -/
theorem exists_partialColoring_of_macroscopic_core {q : ℕ}
    (hq : 0 < q) (x : G.E → Fin q → ℝ)
    (gamma tau : ℝ) (hgamma0 : 0 < gamma) (hgamma1 : gamma < 1)
    (htau : 0 < tau)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hmass : ∀ e, G.proposalMass x e ≤ 1)
    (base : G.E → Fin q)
    (hbase : G.IsFeasibleOn
      (G.retainedMacroscopicEdges x gamma tau) base)
    (hbaseSupport : ∀ e ∈ G.retainedMacroscopicEdges x gamma tau,
      0 < x e (base e))
    (hroom : ∀ v c,
      G.colorLoadOn
            (G.retainedMacroscopicEdges x gamma tau) base v c +
          G.tinyOnFractionalLoad
            (G.retainedTinyEdges x gamma tau)
            (G.normalizedRetainedProposal x gamma tau) v c +
          2 * tau ≤ 1) :
    ∃ (P : Finset G.E) (color : G.E → Fin q),
      G.IsFeasibleOn P color ∧
      (∀ e ∈ P, 0 < x e (color e)) ∧
      ∀ v,
        (∑ e ∈ Finset.univ \ P,
          if G.Inc v e then G.weight e else 0) ≤
            G.proposalDeficit x v / gamma := by
  let H := G.retainedMacroscopicEdges x gamma tau
  let R := G.retainedTinyEdges x gamma tau
  have hdisj : Disjoint H R :=
    G.retainedMacroscopicEdges_disjoint_retainedTinyEdges x gamma tau
  rcases G.exists_extend_with_retainedTiny_exact
      hq x gamma tau hgamma1 htau hx0 H base hdisj hbase hroom with
    ⟨color, hfeasible, hcolorH, hcolorR⟩
  refine ⟨H ∪ R, color, hfeasible, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with heH | heR
    · rw [hcolorH e heH]
      exact hbaseSupport e heH
    · exact hcolorR e heR
  · intro v
    have hcompl : (Finset.univ : Finset G.E) \ (H ∪ R) =
        G.lowProposalMassEdges x gamma := by
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_union, G.mem_lowProposalMassEdges]
      rw [not_or]
      constructor
      · intro h
        exact lt_of_not_ge fun hmassHigh ↦ by
          have hu := (G.mem_retainedMacroscopic_union_retainedTiny
            x gamma tau e).mpr hmassHigh
          rcases Finset.mem_union.mp hu with heH | heR
          · exact h.1 heH
          · exact h.2 heR
      · intro hlow
        have hnot : ¬ 1 - gamma ≤ G.proposalMass x e :=
          not_le.mpr hlow
        constructor <;> intro he
        · exact hnot
            ((G.mem_retainedMacroscopicEdges x gamma tau e).mp he).1
        · exact hnot ((G.mem_retainedTinyEdges x gamma tau e).mp he).1
    rw [hcompl]
    exact G.lowProposalMassWeight_le_deficit_div
      x gamma hgamma0 hmass v

/-- Partial-core form of the trim-and-extend reduction.  The macroscopic
rounder may leave an explicit star-weight budget `eta`; after all retained
tiny edges are colored, the final residual is at most proposal deficit over
`gamma` plus that budget. -/
theorem exists_partialColoring_of_partial_macroscopic_core {q : ℕ}
    (hq : 0 < q) (x : G.E → Fin q → ℝ)
    (gamma tau eta : ℝ) (hgamma0 : 0 < gamma) (hgamma1 : gamma < 1)
    (htau : 0 < tau)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hmass : ∀ e, G.proposalMass x e ≤ 1)
    (P : Finset G.E) (base : G.E → Fin q)
    (hP : P ⊆ G.retainedMacroscopicEdges x gamma tau)
    (hbase : G.IsFeasibleOn P base)
    (hbaseSupport : ∀ e ∈ P, 0 < x e (base e))
    (hmacroLoss : ∀ v,
      (∑ e ∈ G.retainedMacroscopicEdges x gamma tau \ P,
        if G.Inc v e then G.weight e else 0) ≤ eta)
    (hroom : ∀ v c,
      G.colorLoadOn P base v c +
          G.tinyOnFractionalLoad
            (G.retainedTinyEdges x gamma tau)
            (G.normalizedRetainedProposal x gamma tau) v c +
          2 * tau ≤ 1) :
    ∃ (P' : Finset G.E) (color : G.E → Fin q),
      G.IsFeasibleOn P' color ∧
      (∀ e ∈ P', 0 < x e (color e)) ∧
      ∀ v,
        (∑ e ∈ Finset.univ \ P',
          if G.Inc v e then G.weight e else 0) ≤
            G.proposalDeficit x v / gamma + eta := by
  let H := G.retainedMacroscopicEdges x gamma tau
  let T := G.retainedTinyEdges x gamma tau
  have hdisjHT : Disjoint H T :=
    G.retainedMacroscopicEdges_disjoint_retainedTinyEdges x gamma tau
  have hdisjPT : Disjoint P T :=
    Finset.disjoint_left.mpr fun e heP heT ↦
      Finset.disjoint_left.mp hdisjHT (hP heP) heT
  rcases G.exists_extend_with_retainedTiny_exact
      hq x gamma tau hgamma1 htau hx0 P base hdisjPT hbase hroom with
    ⟨color, hfeasible, hcolorP, hcolorT⟩
  refine ⟨P ∪ T, color, hfeasible, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with heP | heT
    · rw [hcolorP e heP]
      exact hbaseSupport e heP
    · exact hcolorT e heT
  · intro v
    let f : G.E → ℝ := fun e ↦ if G.Inc v e then G.weight e else 0
    have hf0 : ∀ e, 0 ≤ f e := by
      intro e
      unfold f
      split
      · exact G.weight_nonneg e
      · exact le_rfl
    have hpoint : ∀ e,
        (if e ∈ (Finset.univ : Finset G.E) \ (P ∪ T) then f e else 0) ≤
          (if e ∈ G.lowProposalMassEdges x gamma then f e else 0) +
            (if e ∈ H \ P then f e else 0) := by
      intro e
      by_cases heResidual : e ∈ (Finset.univ : Finset G.E) \ (P ∪ T)
      · have heNot : e ∉ P ∧ e ∉ T := by
          simpa using (Finset.mem_sdiff.mp heResidual).2
        by_cases heLow : G.proposalMass x e < 1 - gamma
        · have heLowMem : e ∈ G.lowProposalMassEdges x gamma :=
            G.mem_lowProposalMassEdges x gamma e |>.mpr heLow
          rw [if_pos heResidual, if_pos heLowMem]
          apply le_add_of_nonneg_right
          by_cases heHP : e ∈ H \ P
          · simp [heHP, hf0 e]
          · simp [heHP]
        · have heHigh : 1 - gamma ≤ G.proposalMass x e :=
            le_of_not_gt heLow
          have heUnion :=
            (G.mem_retainedMacroscopic_union_retainedTiny x gamma tau e).mpr
              heHigh
          have heH : e ∈ H := by
            rcases Finset.mem_union.mp heUnion with heH | heT
            · exact heH
            · exact False.elim (heNot.2 heT)
          have heHP : e ∈ H \ P := Finset.mem_sdiff.mpr ⟨heH, heNot.1⟩
          rw [if_pos heResidual, if_pos heHP]
          apply le_add_of_nonneg_left
          by_cases heLowMem : e ∈ G.lowProposalMassEdges x gamma
          · simp [heLowMem, hf0 e]
          · simp [heLowMem]
      · rw [if_neg heResidual]
        apply add_nonneg
        · by_cases heLowMem : e ∈ G.lowProposalMassEdges x gamma
          · simp [heLowMem, hf0 e]
          · simp [heLowMem]
        · by_cases heHP : e ∈ H \ P
          · simp [heHP, hf0 e]
          · simp [heHP]
    have hsum := Finset.sum_le_sum
      (fun e (_he : e ∈ (Finset.univ : Finset G.E)) ↦ hpoint e)
    simp only [Finset.sum_add_distrib] at hsum
    have hfilterSum (S : Finset G.E) :
        (∑ e : G.E, if e ∈ S then f e else 0) = ∑ e ∈ S, f e := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext e
        simp
      · intro e _he
        rfl
    have hlow := G.lowProposalMassWeight_le_deficit_div
      x gamma hgamma0 hmass v
    have hmacro := hmacroLoss v
    have hlow' :
        (∑ e : G.E, if e ∈ G.lowProposalMassEdges x gamma then f e else 0) ≤
          G.proposalDeficit x v / gamma := by
      rw [hfilterSum]
      simpa [f] using hlow
    have hmacro' :
        (∑ e : G.E, if e ∈ H \ P then f e else 0) ≤ eta := by
      rw [hfilterSum]
      simpa [f, H] using hmacro
    change (∑ e ∈ (Finset.univ : Finset G.E) \ (P ∪ T), f e) ≤
      G.proposalDeficit x v / gamma + eta
    rw [← hfilterSum ((Finset.univ : Finset G.E) \ (P ∪ T))]
    exact hsum.trans (add_le_add hlow' hmacro')

/-- Deterministically color every high-proposal-mass edge of weight at most
`tau`.  The output retains proposal support.  Thus any future whole-edge
argument only has to handle low-mass loss and edges heavier than `tau`. -/
theorem exists_feasibleColoring_retainedTiny {q : ℕ}
    (hq : 0 < q) (x : G.E → Fin q → ℝ)
    (gamma tau : ℝ) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1)
    (htau : 0 < tau)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hload : ∀ v c,
      (∑ e : G.StarEdge v, G.weight e.1 * x e.1 c) ≤ 1 / 2)
    (hroom : 1 / (2 * (1 - gamma)) + 2 * tau ≤ 1) :
    ∃ color : G.E → Fin q,
      G.IsFeasibleOn (G.retainedTinyEdges x gamma tau) color ∧
      ∀ e ∈ G.retainedTinyEdges x gamma tau,
        0 < x e (color e) := by
  let R := G.retainedTinyEdges x gamma tau
  let y : {e : G.E // e ∈ R} → Fin q → ℝ :=
    G.normalizedRetainedProposal x gamma tau
  have hy0 : ∀ e c, 0 ≤ y e c := by
    intro e c
    unfold y normalizedRetainedProposal
    have heR := G.mem_retainedTinyEdges x gamma tau e.1 |>.mp e.2
    have hmassPos : 0 < G.proposalMass x e.1 :=
      (sub_pos.mpr hgamma1).trans_le heR.1
    exact div_nonneg (hx0 e.1 c) hmassPos.le
  have hysum : ∀ e, ∑ c, y e c = 1 := by
    intro e
    exact G.sum_normalizedRetainedProposal x gamma tau hgamma1 e
  have hweight : ∀ e ∈ R, G.weight e ≤ tau := by
    intro e he
    exact (G.mem_retainedTinyEdges x gamma tau e).mp he |>.2.le
  rcases G.exists_tinyColorDecision R tau htau y
      (fun _e ↦ 0) hy0 (fun _e ↦ le_rfl)
      (by intro e; simp [hysum e]) hweight with
    ⟨decision, hpositive, hnone, hcolorLoad, _hloss⟩
  have hsome : ∀ e, ∃ c, decision e = some c := by
    intro e
    cases h : decision e with
    | none => exact False.elim ((hnone e h).false)
    | some c => exact ⟨c, rfl⟩
  let chosen : {e : G.E // e ∈ R} → Fin q := fun e ↦ Classical.choose (hsome e)
  have hchosen : ∀ e, decision e = some (chosen e) := by
    intro e
    exact Classical.choose_spec (hsome e)
  let fallback : Fin q := ⟨0, hq⟩
  let color : G.E → Fin q := fun e ↦
    if he : e ∈ R then chosen ⟨e, he⟩ else fallback
  have hloadEq : ∀ v c,
      G.colorLoadOn R color v c =
        G.tinyResidualIntegralColorLoad decision v c := by
    intro v c
    unfold WeightedMultigraph.colorLoadOn
      WeightedMultigraph.tinyResidualIntegralColorLoad
    rw [Finset.sum_subtype (p := fun e : G.E ↦ e ∈ R) R
      (by intro e; simp)]
    apply Finset.sum_congr rfl
    intro e _he
    rw [hchosen e]
    simp [color, e.2, chosen]
  have hfeasible : G.IsFeasibleOn R color := by
    intro v c
    rw [hloadEq]
    calc
      G.tinyResidualIntegralColorLoad decision v c ≤
          G.tinyResidualColorLoad R y v c + 2 * tau :=
        hcolorLoad v c
      _ ≤ (1 / (1 - gamma)) * (1 / 2) + 2 * tau := by
        gcongr
        have hnormalized :=
          (G.tinyOnFractionalLoad_normalizedRetained_le
            x gamma tau hgamma1 hx0 v c).trans
              (mul_le_mul_of_nonneg_left (hload v c)
                (div_nonneg zero_le_one (sub_nonneg.mpr hgamma1.le)))
        simpa [WeightedMultigraph.tinyResidualColorLoad,
          WeightedMultigraph.tinyOnFractionalLoad, mul_comm] using hnormalized
      _ = 1 / (2 * (1 - gamma)) + 2 * tau := by
        have hden : 1 - gamma ≠ 0 := (sub_pos.mpr hgamma1).ne'
        field_simp [hden]
      _ ≤ 1 := hroom
  refine ⟨color, hfeasible, ?_⟩
  intro e he
  have hmass : 0 < G.proposalMass x e := by
    have heR := (G.mem_retainedTinyEdges x gamma tau e).mp he
    exact (sub_pos.mpr hgamma1).trans_le heR.1
  have hcolorEq : color e = chosen ⟨e, he⟩ := by
    unfold color
    rw [dif_pos he]
  have hySelected : 0 < y ⟨e, he⟩ (color e) := by
    rw [hcolorEq]
    exact hpositive ⟨e, he⟩ (chosen ⟨e, he⟩) (hchosen ⟨e, he⟩)
  unfold y normalizedRetainedProposal at hySelected
  rcases (div_pos_iff.mp hySelected) with h | h
  · exact h.1
  · exact False.elim ((not_lt_of_ge (hx0 e (color e))) h.1)

end WeightedMultigraph
end
end WeightedEdgeColoring
