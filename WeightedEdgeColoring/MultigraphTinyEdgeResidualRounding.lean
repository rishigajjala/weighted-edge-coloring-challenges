import WeightedEdgeColoring.Conversions
import WeightedEdgeColoring.TwoConstraintChoice

/-!
# Rounding multigraph tiny colour options with an explicit uncoloured option

For every edge in a fixed set, the fractional point may either choose one
palette colour or leave the edge uncoloured.  A coloured option uses the two
endpoint--colour rows.  An uncoloured option uses the two endpoint loss rows.
Thus every option touches at most two rows, and the elementary
two-constraint rounding theorem applies without changing the palette.

The result below keeps the two kinds of rows separate.  It is the finite
rounding step needed after edgewise normalization of the selected profile
options.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u

namespace WeightedMultigraph

variable (G : WeightedMultigraph.{u})

/-- An option consists of its edge and either a palette colour or `none`,
which means that the edge is left uncoloured. -/
abbrev TinyResidualOption {q : ℕ} (R : Finset G.E) :=
  {e : G.E // e ∈ R} × Option (Fin q)

/-- The two families of capacity rows: palette rows and uncoloured-loss
rows. -/
abbrev TinyResidualConstraint (q : ℕ) :=
  (G.V × Fin q) ⊕ G.V

/-- Fractional mass of a coloured or uncoloured option. -/
def tinyResidualOptionMass {q : ℕ} {R : Finset G.E}
    (x : {e : G.E // e ∈ R} → Fin q → ℝ)
    (residual : {e : G.E // e ∈ R} → ℝ)
    (o : G.TinyResidualOption (q := q) R) : ℝ :=
  match o.2 with
  | some c => x o.1 c
  | none => residual o.1

/-- Resource use of an option.  A coloured option contributes its edge
weight to the two endpoint rows of its colour.  An uncoloured option
contributes the same weight to the two endpoint loss rows. -/
def tinyResidualUse {q : ℕ} {R : Finset G.E}
    (o : G.TinyResidualOption (q := q) R)
    (row : G.TinyResidualConstraint q) : ℝ :=
  match o.2, row with
  | some c, Sum.inl vc =>
      if G.Inc vc.1 o.1.1 ∧ c = vc.2 then G.weight o.1.1 else 0
  | none, Sum.inr v =>
      if G.Inc v o.1.1 then G.weight o.1.1 else 0
  | _, _ => 0

/-- Fractional coloured load in one endpoint--colour row. -/
def tinyResidualColorLoad {q : ℕ} (R : Finset G.E)
    (x : {e : G.E // e ∈ R} → Fin q → ℝ)
    (v : G.V) (c : Fin q) : ℝ :=
  ∑ e : {e : G.E // e ∈ R},
    if G.Inc v e.1 then x e c * G.weight e.1 else 0

/-- Fractional weight left uncoloured at one endpoint. -/
def tinyResidualLossLoad (R : Finset G.E)
    (residual : {e : G.E // e ∈ R} → ℝ)
    (v : G.V) : ℝ :=
  ∑ e : {e : G.E // e ∈ R},
    if G.Inc v e.1 then residual e * G.weight e.1 else 0

/-- Integral coloured load determined by a coloured-or-uncoloured decision
for every edge. -/
def tinyResidualIntegralColorLoad {q : ℕ} {R : Finset G.E}
    (decision : {e : G.E // e ∈ R} → Option (Fin q))
    (v : G.V) (c : Fin q) : ℝ :=
  ∑ e : {e : G.E // e ∈ R},
    if G.Inc v e.1 ∧ decision e = some c then G.weight e.1 else 0

/-- Integral uncoloured weight determined by the same decision. -/
def tinyResidualIntegralLossLoad {q : ℕ} {R : Finset G.E}
    (decision : {e : G.E // e ∈ R} → Option (Fin q))
    (v : G.V) : ℝ :=
  ∑ e : {e : G.E // e ∈ R},
    if G.Inc v e.1 ∧ decision e = none then G.weight e.1 else 0

theorem tinyResidualUse_nonneg {q : ℕ} {R : Finset G.E}
    (o : G.TinyResidualOption R)
    (row : G.TinyResidualConstraint q) :
    0 ≤ G.tinyResidualUse o row := by
  rcases o with ⟨e, c⟩
  cases c with
  | none =>
      cases row with
      | inl vc => simp [tinyResidualUse]
      | inr v =>
          simp only [tinyResidualUse]
          split
          · exact G.weight_nonneg e.1
          · exact le_rfl
  | some c =>
      cases row with
      | inl vc =>
          simp only [tinyResidualUse]
          split
          · exact G.weight_nonneg e.1
          · exact le_rfl
      | inr v => simp [tinyResidualUse]

theorem tinyResidualUse_le {q : ℕ} {R : Finset G.E}
    (tau : ℝ) (hweight : ∀ e ∈ R, G.weight e ≤ tau)
    (o : G.TinyResidualOption R)
    (row : G.TinyResidualConstraint q) :
    G.tinyResidualUse o row ≤ tau := by
  rcases o with ⟨e, c⟩
  have htau0 : 0 ≤ tau :=
    (G.weight_pos e.1).le.trans (hweight e.1 e.2)
  cases c with
  | none =>
      cases row with
      | inl vc => simpa [tinyResidualUse] using htau0
      | inr v =>
          simp only [tinyResidualUse]
          split
          · exact hweight e.1 e.2
          · exact htau0
  | some c =>
      cases row with
      | inl vc =>
          simp only [tinyResidualUse]
          split
          · exact hweight e.1 e.2
          · exact htau0
      | inr v => simpa [tinyResidualUse] using htau0

/-- Every coloured or uncoloured option reads at most its two endpoint
rows. -/
theorem tinyResidualUse_support_card_le_two
    {q : ℕ} {R : Finset G.E} (o : G.TinyResidualOption R) :
    ((Finset.univ : Finset (G.TinyResidualConstraint q)).filter
      fun row ↦ G.tinyResidualUse o row ≠ 0).card ≤ 2 := by
  rcases o with ⟨e, c⟩
  cases c with
  | none =>
      let A : Finset (G.TinyResidualConstraint q) :=
        {Sum.inr (G.fst e.1)}
      let B : Finset (G.TinyResidualConstraint q) :=
        {Sum.inr (G.snd e.1)}
      have hsub :
          (Finset.univ.filter fun row : G.TinyResidualConstraint q ↦
            G.tinyResidualUse (e, none) row ≠ 0) ⊆ A ∪ B := by
        intro row hrow
        have hne := (Finset.mem_filter.mp hrow).2
        rcases row with vc | v
        · simp [tinyResidualUse] at hne
        · have hinc : G.Inc v e.1 := by
            by_contra h
            simp [tinyResidualUse, h] at hne
          rcases hinc with hfst | hsnd
          · apply Finset.mem_union_left
            have : Sum.inr v =
                (Sum.inr (G.fst e.1) : G.TinyResidualConstraint q) := by
              congr
              exact hfst.symm
            simp [A, this]
          · apply Finset.mem_union_right
            have : Sum.inr v =
                (Sum.inr (G.snd e.1) : G.TinyResidualConstraint q) := by
              congr
              exact hsnd.symm
            simp [B, this]
      calc
        (Finset.univ.filter fun row : G.TinyResidualConstraint q ↦
            G.tinyResidualUse (e, none) row ≠ 0).card ≤ (A ∪ B).card :=
          Finset.card_le_card hsub
        _ ≤ A.card + B.card := Finset.card_union_le A B
        _ = 2 := by simp [A, B]
  | some c =>
      let A : Finset (G.TinyResidualConstraint q) :=
        {Sum.inl (G.fst e.1, c)}
      let B : Finset (G.TinyResidualConstraint q) :=
        {Sum.inl (G.snd e.1, c)}
      have hsub :
          (Finset.univ.filter fun row : G.TinyResidualConstraint q ↦
            G.tinyResidualUse (e, some c) row ≠ 0) ⊆ A ∪ B := by
        intro row hrow
        have hne := (Finset.mem_filter.mp hrow).2
        rcases row with vc | v
        · have hinc : G.Inc vc.1 e.1 ∧ c = vc.2 := by
            by_contra h
            simp [tinyResidualUse, h] at hne
          rcases hinc.1 with hfst | hsnd
          · apply Finset.mem_union_left
            have : Sum.inl vc =
                (Sum.inl (G.fst e.1, c) : G.TinyResidualConstraint q) := by
              congr
              exact Prod.ext hfst.symm hinc.2.symm
            simp [A, this]
          · apply Finset.mem_union_right
            have : Sum.inl vc =
                (Sum.inl (G.snd e.1, c) : G.TinyResidualConstraint q) := by
              congr
              exact Prod.ext hsnd.symm hinc.2.symm
            simp [B, this]
        · simp [tinyResidualUse] at hne
      calc
        (Finset.univ.filter fun row : G.TinyResidualConstraint q ↦
            G.tinyResidualUse (e, some c) row ≠ 0).card ≤ (A ∪ B).card :=
          Finset.card_le_card hsub
        _ ≤ A.card + B.card := Finset.card_union_le A B
        _ = 2 := by simp [A, B]

private theorem tinyResidual_jobMass
    {q : ℕ} {R : Finset G.E}
    (x : {e : G.E // e ∈ R} → Fin q → ℝ)
    (residual : {e : G.E // e ∈ R} → ℝ)
    (htotal : ∀ e, (∑ c, x e c) + residual e = 1)
    (e : {e : G.E // e ∈ R}) :
    optionJobMass Prod.fst (G.tinyResidualOptionMass x residual) e = 1 := by
  rw [optionJobMass, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single e]
  · rw [Fintype.sum_option]
    simpa [tinyResidualOptionMass, add_comm] using htotal e
  · intro f _hf hfe
    simp [hfe]
  · simp

private theorem tinyResidual_optionLoad_color
    {q : ℕ} {R : Finset G.E}
    (x : {e : G.E // e ∈ R} → Fin q → ℝ)
    (residual : {e : G.E // e ∈ R} → ℝ)
    (v : G.V) (c : Fin q) :
    optionLoad G.tinyResidualUse (G.tinyResidualOptionMass x residual)
        (Sum.inl (v, c)) =
      G.tinyResidualColorLoad R x v c := by
  rw [optionLoad, Fintype.sum_prod_type]
  unfold tinyResidualColorLoad
  apply Finset.sum_congr rfl
  intro e _he
  rw [Fintype.sum_option]
  by_cases hinc : G.Inc v e.1
  · simp [tinyResidualUse, tinyResidualOptionMass, hinc]
  · simp [tinyResidualUse, tinyResidualOptionMass, hinc]

private theorem tinyResidual_optionLoad_loss
    {q : ℕ} {R : Finset G.E}
    (x : {e : G.E // e ∈ R} → Fin q → ℝ)
    (residual : {e : G.E // e ∈ R} → ℝ)
    (v : G.V) :
    optionLoad G.tinyResidualUse (G.tinyResidualOptionMass x residual)
        (Sum.inr v) =
      G.tinyResidualLossLoad R residual v := by
  rw [optionLoad, Fintype.sum_prod_type]
  unfold tinyResidualLossLoad
  apply Finset.sum_congr rfl
  intro e _he
  rw [Fintype.sum_option]
  by_cases hinc : G.Inc v e.1
  · simp [tinyResidualUse, tinyResidualOptionMass, hinc]
  · simp [tinyResidualUse, tinyResidualOptionMass, hinc]

/-- Simultaneously round colour choices and the private uncoloured choice.
The integral coloured load of every endpoint--colour row, and the integral
uncoloured weight at every endpoint, exceed their fractional values by at
most `2 * tau`. -/
theorem exists_tinyColoredOrResidualChoice
    {q : ℕ} (R : Finset G.E) (tau : ℝ) (htau : 0 < tau)
    (x : {e : G.E // e ∈ R} → Fin q → ℝ)
    (residual : {e : G.E // e ∈ R} → ℝ)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hresidual0 : ∀ e, 0 ≤ residual e)
    (htotal : ∀ e, (∑ c, x e c) + residual e = 1)
    (hweight : ∀ e ∈ R, G.weight e ≤ tau) :
    ∃ selected : {e : G.E // e ∈ R} → G.TinyResidualOption R,
      (∀ e, (selected e).1 = e) ∧
      (∀ e, 0 < G.tinyResidualOptionMass x residual (selected e)) ∧
      (∀ v c,
        (∑ e, G.tinyResidualUse (selected e) (Sum.inl (v, c))) ≤
          G.tinyResidualColorLoad R x v c + 2 * tau) ∧
      ∀ v,
        (∑ e, G.tinyResidualUse (selected e) (Sum.inr v)) ≤
          G.tinyResidualLossLoad R residual v + 2 * tau := by
  let mass : G.TinyResidualOption R → ℝ :=
    G.tinyResidualOptionMass x residual
  have hmass01 : ∀ o, 0 ≤ mass o ∧ mass o ≤ 1 := by
    intro o
    rcases o with ⟨e, c⟩
    cases c with
    | none =>
        have hsum0 : 0 ≤ ∑ d, x e d :=
          Finset.sum_nonneg fun d _hd ↦ hx0 e d
        have hle : residual e ≤ (∑ d, x e d) + residual e := by
          linarith
        constructor
        · exact hresidual0 e
        · simpa [mass, tinyResidualOptionMass, htotal e] using hle
    | some c =>
        have hterm : x e c ≤ ∑ d, x e d :=
          Finset.single_le_sum (fun d _hd ↦ hx0 e d) (Finset.mem_univ c)
        have hle : x e c ≤ (∑ d, x e d) + residual e :=
          hterm.trans (le_add_of_nonneg_right (hresidual0 e))
        constructor
        · exact hx0 e c
        · simpa [mass, tinyResidualOptionMass, htotal e] using hle
  obtain ⟨selected, howner, hpositive, hload⟩ :=
    choose_one_option_per_job_support
      (Job := {e : G.E // e ∈ R})
      (Option := G.TinyResidualOption R)
      (Constraint := G.TinyResidualConstraint q)
      Prod.fst G.tinyResidualUse tau mass htau hmass01
      (G.tinyResidual_jobMass x residual htotal)
      G.tinyResidualUse_nonneg
      (G.tinyResidualUse_le tau hweight)
      G.tinyResidualUse_support_card_le_two
  refine ⟨selected, howner, hpositive, ?_, ?_⟩
  · intro v c
    have h := hload (Sum.inl (v, c))
    rw [show mass = G.tinyResidualOptionMass x residual from rfl,
      G.tinyResidual_optionLoad_color x residual v c] at h
    exact h
  · intro v
    have h := hload (Sum.inr v)
    rw [show mass = G.tinyResidualOptionMass x residual from rfl,
      G.tinyResidual_optionLoad_loss x residual v] at h
    exact h

/-- Decision-valued form of `exists_tinyColoredOrResidualChoice`.  Every
edge is either assigned an actual palette colour or marked uncoloured, and
the two displayed integral loads obey the same additive bounds. -/
theorem exists_tinyColorDecision
    {q : ℕ} (R : Finset G.E) (tau : ℝ) (htau : 0 < tau)
    (x : {e : G.E // e ∈ R} → Fin q → ℝ)
    (residual : {e : G.E // e ∈ R} → ℝ)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hresidual0 : ∀ e, 0 ≤ residual e)
    (htotal : ∀ e, (∑ c, x e c) + residual e = 1)
    (hweight : ∀ e ∈ R, G.weight e ≤ tau) :
    ∃ decision : {e : G.E // e ∈ R} → Option (Fin q),
      (∀ e c, decision e = some c → 0 < x e c) ∧
      (∀ e, decision e = none → 0 < residual e) ∧
      (∀ v c,
        G.tinyResidualIntegralColorLoad decision v c ≤
          G.tinyResidualColorLoad R x v c + 2 * tau) ∧
      ∀ v,
        G.tinyResidualIntegralLossLoad decision v ≤
          G.tinyResidualLossLoad R residual v + 2 * tau := by
  obtain ⟨selected, howner, hpositive, hcolor, hloss⟩ :=
    G.exists_tinyColoredOrResidualChoice R tau htau x residual
      hx0 hresidual0 htotal hweight
  let decision : {e : G.E // e ∈ R} → Option (Fin q) :=
    fun e ↦ (selected e).2
  have hselected (e : {e : G.E // e ∈ R}) :
      selected e = (e, decision e) := by
    apply Prod.ext
    · exact howner e
    · rfl
  have hdecisionColor : ∀ e c, decision e = some c → 0 < x e c := by
    intro e c hec
    have h := hpositive e
    rw [hselected e] at h
    simpa [tinyResidualOptionMass, hec] using h
  have hdecisionResidual : ∀ e, decision e = none → 0 < residual e := by
    intro e he
    have h := hpositive e
    rw [hselected e] at h
    simpa [tinyResidualOptionMass, he] using h
  refine ⟨decision, hdecisionColor, hdecisionResidual, ?_, ?_⟩
  · intro v c
    rw [show G.tinyResidualIntegralColorLoad decision v c =
        ∑ e, G.tinyResidualUse (selected e) (Sum.inl (v, c)) by
      unfold tinyResidualIntegralColorLoad
      apply Finset.sum_congr rfl
      intro e _he
      rw [hselected e]
      cases h : decision e <;>
        simp [tinyResidualUse, h]]
    exact hcolor v c
  · intro v
    rw [show G.tinyResidualIntegralLossLoad decision v =
        ∑ e, G.tinyResidualUse (selected e) (Sum.inr v) by
      unfold tinyResidualIntegralLossLoad
      apply Finset.sum_congr rfl
      intro e _he
      rw [hselected e]
      cases h : decision e <;>
        simp [tinyResidualUse, h]]
    exact hloss v

end WeightedMultigraph

end

end WeightedEdgeColoring
