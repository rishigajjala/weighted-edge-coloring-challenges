import WeightedEdgeColoring.TwoConstraintChoice
import WeightedEdgeColoring.WeightedInsertion

/-!
# Tiny-edge rounding inside an existing palette

This is the partial version of `TinyEdgeRounding`.  It assigns a colour to
every edge in a specified set `R`, while increasing each vertex--colour row
by at most twice the largest edge weight.  A second theorem merges the
result into an already coloured disjoint set using the same palette.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u

namespace WeightedMultigraph

variable (G : WeightedMultigraph.{u})

/-- Consumption of one restricted edge--colour option in one row. -/
def tinyOnColorUse {q : ℕ} {R : Finset G.E}
    (o : {e : G.E // e ∈ R} × Fin q) (r : G.V × Fin q) : ℝ :=
  if G.Inc r.1 o.1.1 ∧ o.2 = r.2 then G.weight o.1.1 else 0

theorem tinyOnColorUse_nonneg {q : ℕ} {R : Finset G.E}
    (o : {e : G.E // e ∈ R} × Fin q) (r : G.V × Fin q) :
    0 ≤ G.tinyOnColorUse o r := by
  unfold tinyOnColorUse
  split
  · exact G.weight_nonneg o.1.1
  · exact le_rfl

theorem tinyOnColorUse_le {q : ℕ} {R : Finset G.E} (τ : ℝ)
    (hweight : ∀ e ∈ R, G.weight e ≤ τ)
    (o : {e : G.E // e ∈ R} × Fin q) (r : G.V × Fin q) :
    G.tinyOnColorUse o r ≤ τ := by
  unfold tinyOnColorUse
  split
  · exact hweight o.1.1 o.1.2
  · linarith [G.weight_pos o.1.1, hweight o.1.1 o.1.2]

theorem tinyOnColorUse_support_card_le_two {q : ℕ} {R : Finset G.E}
    (o : {e : G.E // e ∈ R} × Fin q) :
    ((Finset.univ : Finset (G.V × Fin q)).filter
      fun r ↦ G.tinyOnColorUse o r ≠ 0).card ≤ 2 := by
  let A : Finset (G.V × Fin q) := {(G.fst o.1.1, o.2)}
  let B : Finset (G.V × Fin q) := {(G.snd o.1.1, o.2)}
  have hsub :
      (Finset.univ.filter fun r : G.V × Fin q ↦
        G.tinyOnColorUse o r ≠ 0) ⊆ A ∪ B := by
    intro r hr
    have hne := (Finset.mem_filter.mp hr).2
    have hinc : G.Inc r.1 o.1.1 ∧ o.2 = r.2 := by
      by_contra h
      simp [tinyOnColorUse, h] at hne
    rcases hinc.1 with hfst | hsnd
    · apply Finset.mem_union_left
      have : r = (G.fst o.1.1, o.2) := by
        apply Prod.ext
        · exact hfst.symm
        · exact hinc.2.symm
      simp [A, this]
    · apply Finset.mem_union_right
      have : r = (G.snd o.1.1, o.2) := by
        apply Prod.ext
        · exact hsnd.symm
        · exact hinc.2.symm
      simp [B, this]
  calc
    (Finset.univ.filter fun r : G.V × Fin q ↦
        G.tinyOnColorUse o r ≠ 0).card ≤ (A ∪ B).card :=
      Finset.card_le_card hsub
    _ ≤ A.card + B.card := Finset.card_union_le A B
    _ = 2 := by simp [A, B]

/-- Fractional load of the restricted tiny edges in one row. -/
def tinyOnFractionalLoad {q : ℕ} (R : Finset G.E)
    (x : {e : G.E // e ∈ R} → Fin q → ℝ)
    (v : G.V) (c : Fin q) : ℝ :=
  ∑ e : {e : G.E // e ∈ R},
    if G.Inc v e.1 then x e c * G.weight e.1 else 0

private theorem tinyOn_jobMass {q : ℕ} {R : Finset G.E}
    (x : {e : G.E // e ∈ R} → Fin q → ℝ)
    (hxsum : ∀ e, ∑ c, x e c = 1) (e : {e : G.E // e ∈ R}) :
    optionJobMass Prod.fst
      (fun o : {e : G.E // e ∈ R} × Fin q ↦ x o.1 o.2) e = 1 := by
  rw [optionJobMass, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single e]
  · simpa using hxsum e
  · intro f _hf hfe
    simp [hfe]
  · simp

private theorem tinyOn_optionLoad {q : ℕ} {R : Finset G.E}
    (x : {e : G.E // e ∈ R} → Fin q → ℝ) (v : G.V) (c : Fin q) :
    optionLoad G.tinyOnColorUse
      (fun o : {e : G.E // e ∈ R} × Fin q ↦ x o.1 o.2) (v, c) =
      G.tinyOnFractionalLoad R x v c := by
  rw [optionLoad, Fintype.sum_prod_type]
  simp only [tinyOnColorUse, tinyOnFractionalLoad]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hinc : G.Inc v e.1
  · simp [hinc]
  · simp [hinc]

/-- Round arbitrary fractional proposals on a restricted tiny edge set.
The chosen integral load of every row is at most its fractional load plus
`2 * τ`. -/
theorem exists_tinyColoringOn_of_fractional
    {q : ℕ} (hq : 0 < q) (R : Finset G.E) (τ : ℝ) (hτ : 0 < τ)
    (x : {e : G.E // e ∈ R} → Fin q → ℝ)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hxsum : ∀ e, ∑ c, x e c = 1)
    (hweight : ∀ e ∈ R, G.weight e ≤ τ) :
    ∃ color : G.E → Fin q, ∀ v c,
      G.colorLoadOn R color v c ≤ G.tinyOnFractionalLoad R x v c + 2 * τ := by
  let mass : {e : G.E // e ∈ R} × Fin q → ℝ := fun o ↦ x o.1 o.2
  have hmass01 : ∀ o, 0 ≤ mass o ∧ mass o ≤ 1 := by
    intro o
    constructor
    · exact hx0 o.1 o.2
    · have hone : x o.1 o.2 ≤ ∑ c, x o.1 c :=
        Finset.single_le_sum (fun c _hc ↦ hx0 o.1 c) (Finset.mem_univ o.2)
      simpa [mass, hxsum o.1] using hone
  obtain ⟨selected, howner, hload⟩ :=
    choose_one_option_per_job
      (Job := {e : G.E // e ∈ R})
      (Option := {e : G.E // e ∈ R} × Fin q)
      (Constraint := G.V × Fin q)
      Prod.fst G.tinyOnColorUse τ mass hτ hmass01
      (G.tinyOn_jobMass x hxsum)
      G.tinyOnColorUse_nonneg
      (G.tinyOnColorUse_le τ hweight)
      G.tinyOnColorUse_support_card_le_two
  let fallback : Fin q := ⟨0, hq⟩
  let color : G.E → Fin q := fun e ↦
    if he : e ∈ R then (selected ⟨e, he⟩).2 else fallback
  refine ⟨color, ?_⟩
  intro v c
  have hrow := hload (v, c)
  rw [show mass =
      (fun o : {e : G.E // e ∈ R} × Fin q ↦ x o.1 o.2) from rfl,
    G.tinyOn_optionLoad x v c] at hrow
  calc
    G.colorLoadOn R color v c =
        ∑ e : {e : G.E // e ∈ R},
          G.tinyOnColorUse (selected e) (v, c) := by
      unfold colorLoadOn
      rw [show
        (∑ e ∈ R,
          if G.Inc v e ∧ color e = c then G.weight e else 0) =
        ∑ e : {e : G.E // e ∈ R},
          if G.Inc v e.1 ∧ color e.1 = c then G.weight e.1 else 0 by
            exact Finset.sum_subtype (p := fun e : G.E ↦ e ∈ R) R
              (by intro e; simp)
              (fun e ↦ if G.Inc v e ∧ color e = c then G.weight e else 0)]
      apply Finset.sum_congr rfl
      intro e _he
      have hsel : (selected e).1 = e := howner e
      by_cases hinc : G.Inc v e.1
      · by_cases hcol : (selected e).2 = c <;>
          simp [tinyOnColorUse, color, e.2, hsel, hinc, hcol]
      · simp [tinyOnColorUse, color, e.2, hsel, hinc]
    _ ≤ G.tinyOnFractionalLoad R x v c + 2 * τ := hrow

/-- Merge tiny-edge rounding into an existing disjoint partial colouring in
the same palette, provided the displayed fractional row plus the rounding
error fits in the remaining capacity. -/
theorem exists_extend_feasibleOn_with_fractional_tiny
    {q : ℕ} (hq : 0 < q) (P R : Finset G.E) (hdisj : Disjoint P R)
    (base : G.E → Fin q) (hbase : G.IsFeasibleOn P base)
    (τ : ℝ) (hτ : 0 < τ)
    (x : {e : G.E // e ∈ R} → Fin q → ℝ)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hxsum : ∀ e, ∑ c, x e c = 1)
    (hweight : ∀ e ∈ R, G.weight e ≤ τ)
    (hroom : ∀ v c,
      G.colorLoadOn P base v c + G.tinyOnFractionalLoad R x v c +
        2 * τ ≤ 1) :
    ∃ color : G.E → Fin q, G.IsFeasibleOn (P ∪ R) color := by
  obtain ⟨tiny, htiny⟩ :=
    G.exists_tinyColoringOn_of_fractional hq R τ hτ x hx0 hxsum hweight
  let color : G.E → Fin q := fun e ↦ if e ∈ P then base e else tiny e
  refine ⟨color, ?_⟩
  intro v c
  have hload :
      G.colorLoadOn (P ∪ R) color v c =
        G.colorLoadOn P base v c + G.colorLoadOn R tiny v c := by
    unfold colorLoadOn
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
    G.colorLoadOn P base v c + G.colorLoadOn R tiny v c ≤
        G.colorLoadOn P base v c +
          (G.tinyOnFractionalLoad R x v c + 2 * τ) :=
      add_le_add_right (htiny v c) _
    _ = G.colorLoadOn P base v c +
        G.tinyOnFractionalLoad R x v c + 2 * τ := by ring
    _ ≤ 1 := hroom v c

end WeightedMultigraph

end

end WeightedEdgeColoring
