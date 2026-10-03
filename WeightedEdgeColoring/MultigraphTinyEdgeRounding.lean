import WeightedEdgeColoring.TwoConstraintChoice
import WeightedEdgeColoring.WeightedMultigraph

/-!
# Direct rounding for uniformly tiny edges

If every edge is tiny, independent fractional use of a common palette can
be rounded without any probabilistic theorem.  An edge--colour option uses
only the two endpoint--colour rows, so the finite two-constraint rounding
theorem loses at most twice the largest edge weight in every row.

This is the deterministic dust step needed by the whole-edge argument.  It
is uniform in the number of vertices and edges.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u

namespace WeightedMultigraph

variable (G : WeightedMultigraph.{u})

/-- The row consumption of assigning edge `e` colour `c`. -/
def tinyColorUse {q : ℕ} (o : G.E × Fin q) (r : G.V × Fin q) : ℝ :=
  if G.Inc r.1 o.1 ∧ o.2 = r.2 then G.weight o.1 else 0

theorem tinyColorUse_nonneg {q : ℕ} (o : G.E × Fin q) (r : G.V × Fin q) :
    0 ≤ G.tinyColorUse o r := by
  unfold tinyColorUse
  split
  · exact G.weight_nonneg o.1
  · exact le_rfl

theorem tinyColorUse_le {q : ℕ} (τ : ℝ)
    (hweight : ∀ e, G.weight e ≤ τ)
    (o : G.E × Fin q) (r : G.V × Fin q) :
    G.tinyColorUse o r ≤ τ := by
  unfold tinyColorUse
  split
  · exact hweight o.1
  · have := G.weight_pos o.1
    have := hweight o.1
    linarith

/-- One edge--colour option has nonzero consumption in at most its two
endpoint rows. -/
theorem tinyColorUse_support_card_le_two {q : ℕ} (o : G.E × Fin q) :
    ((Finset.univ : Finset (G.V × Fin q)).filter
      fun r ↦ G.tinyColorUse o r ≠ 0).card ≤ 2 := by
  let T : Finset (G.V × Fin q) := {(G.fst o.1, o.2), (G.snd o.1, o.2)}
  have hsub :
      (Finset.univ.filter fun r : G.V × Fin q ↦
        G.tinyColorUse o r ≠ 0) ⊆ T := by
    intro r hr
    have hne := (Finset.mem_filter.mp hr).2
    have hinc : G.Inc r.1 o.1 ∧ o.2 = r.2 := by
      by_contra h
      simp [tinyColorUse, h] at hne
    rcases hinc.1 with hfst | hsnd
    · have : r = (G.fst o.1, o.2) := by
        apply Prod.ext
        · exact hfst.symm
        · exact hinc.2.symm
      simp [T, this]
    · have : r = (G.snd o.1, o.2) := by
        apply Prod.ext
        · exact hsnd.symm
        · exact hinc.2.symm
      simp [T, this]
  calc
    (Finset.univ.filter fun r : G.V × Fin q ↦
        G.tinyColorUse o r ≠ 0).card ≤ T.card := Finset.card_le_card hsub
    _ ≤ 2 := by
      dsimp [T]
      exact (Finset.card_insert_le _ _).trans (by simp)

/-- Fractional load of one proposed colour on one star. -/
def tinyFractionalColorLoad {q : ℕ} (x : G.E → Fin q → ℝ)
    (v : G.V) (c : Fin q) : ℝ :=
  ∑ e : G.StarEdge v, x e.1 c * G.weight e.1

private theorem tiny_proposal_jobMass {q : ℕ}
    (x : G.E → Fin q → ℝ) (hsum : ∀ e, ∑ c, x e c = 1) (e : G.E) :
    optionJobMass Prod.fst (fun o : G.E × Fin q ↦ x o.1 o.2) e = 1 := by
  rw [optionJobMass, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single e]
  · simpa using hsum e
  · intro f _hf hfe
    simp [hfe]
  · simp

private theorem tiny_proposal_optionLoad {q : ℕ}
    (x : G.E → Fin q → ℝ) (v : G.V) (c : Fin q) :
    optionLoad G.tinyColorUse (fun o : G.E × Fin q ↦ x o.1 o.2) (v, c) =
      G.tinyFractionalColorLoad x v c := by
  rw [optionLoad, Fintype.sum_prod_type]
  simp only [tinyColorUse, tinyFractionalColorLoad]
  calc
    (∑ e : G.E, ∑ d : Fin q,
      x e d * (if G.Inc v e ∧ d = c then G.weight e else 0)) =
        ∑ e : G.E,
          if G.Inc v e then x e c * G.weight e else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hinc : G.Inc v e
      · simp [hinc]
      · simp [hinc]
    _ = ∑ e : G.StarEdge v, x e.1 c * G.weight e.1 := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
        (by intro e; simp) (fun e ↦ x e c * G.weight e)

/-- Deterministic tiny-edge rounding for arbitrary fractional colour
proposals.  Every edge receives one of its proposed colours, and every row
increases by at most `2 * τ`. -/
theorem hasWeightedColoring_of_fractional_tiny
    {q : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (x : G.E → Fin q → ℝ)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hxsum : ∀ e, ∑ c, x e c = 1)
    (hweight : ∀ e, G.weight e ≤ τ)
    (hroom : ∀ v c, G.tinyFractionalColorLoad x v c + 2 * τ ≤ 1) :
    G.HasWeightedColoring q := by
  let mass : G.E × Fin q → ℝ := fun o ↦ x o.1 o.2
  have hmass01 : ∀ o, 0 ≤ mass o ∧ mass o ≤ 1 := by
    intro o
    constructor
    · exact hx0 o.1 o.2
    · have hone : x o.1 o.2 ≤ ∑ c, x o.1 c :=
        Finset.single_le_sum (fun c _hc ↦ hx0 o.1 c) (Finset.mem_univ o.2)
      simpa [mass, hxsum o.1] using hone
  obtain ⟨selected, howner, hload⟩ :=
    choose_one_option_per_job
      (Job := G.E) (Option := G.E × Fin q) (Constraint := G.V × Fin q)
      Prod.fst G.tinyColorUse τ mass hτ hmass01
      (G.tiny_proposal_jobMass x hxsum)
      G.tinyColorUse_nonneg
      (G.tinyColorUse_le τ hweight)
      G.tinyColorUse_support_card_le_two
  let color : G.E → Fin q := fun e ↦ (selected e).2
  refine ⟨color, ?_⟩
  intro v c
  have hselected : ∀ e, (selected e).1 = e := howner
  have hrow := hload (v, c)
  rw [show mass = (fun o : G.E × Fin q ↦ x o.1 o.2) from rfl,
    G.tiny_proposal_optionLoad x v c] at hrow
  calc
    G.colorLoad color v c =
        ∑ e : G.E, G.tinyColorUse (selected e) (v, c) := by
      rw [colorLoad]
      have hsub :
          (∑ e : G.E,
            if G.Inc v e then
              (if color e = c then G.weight e else 0) else 0) =
            ∑ e : G.StarEdge v,
              if color e.1 = c then G.weight e.1 else 0 := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
          (by intro e; simp)
          (fun e ↦ if color e = c then G.weight e else 0)
      rw [← hsub]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hinc : G.Inc v e
      · by_cases hcol : (selected e).2 = c <;>
          simp [tinyColorUse, color, hselected e, hinc, hcol]
      · simp [tinyColorUse, hselected e, hinc]
    _ ≤ G.tinyFractionalColorLoad x v c + 2 * τ := hrow
    _ ≤ 1 := hroom v c

private theorem tiny_uniform_jobMass {q : ℕ} (hq : 0 < q) (e : G.E) :
    optionJobMass Prod.fst (fun _ : G.E × Fin q ↦ 1 / (q : ℝ)) e = 1 := by
  rw [optionJobMass, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single e]
  · simp [hq.ne']
  · intro f _hf hfe
    simp [hfe]
  · simp

private theorem tiny_uniform_optionLoad {q : ℕ} (hq : 0 < q)
    (v : G.V) (c : Fin q) :
    optionLoad G.tinyColorUse (fun _ : G.E × Fin q ↦ 1 / (q : ℝ)) (v, c) =
      G.starWeight v / q := by
  rw [optionLoad, Fintype.sum_prod_type]
  simp only [tinyColorUse]
  calc
    (∑ e : G.E, ∑ d : Fin q,
        (1 / (q : ℝ)) *
          (if G.Inc v e ∧ d = c then G.weight e else 0)) =
        ∑ e : G.E, if G.Inc v e then G.weight e / q else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hinc : G.Inc v e
      · simp [hinc, div_eq_mul_inv, mul_comm]
      · simp [hinc]
    _ = (∑ e : G.E, if G.Inc v e then G.weight e else 0) / q := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hinc : G.Inc v e <;> simp [hinc]
    _ = (∑ e : G.StarEdge v, G.weight e.1) / q := by
      congr 1
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
        (by intro e; simp) G.weight
    _ = G.starWeight v / q := rfl

/-- If the uniform fractional load plus the two-constraint rounding error
fits in one, all edges can be coloured with the common palette. -/
theorem hasWeightedColoring_of_tiny
    {q : ℕ} (hq : 0 < q) (τ : ℝ) (hτ : 0 < τ)
    (hweight : ∀ e, G.weight e ≤ τ)
    (hroom : ∀ v, G.starWeight v / q + 2 * τ ≤ 1) :
    G.HasWeightedColoring q := by
  let x : G.E × Fin q → ℝ := fun _ ↦ 1 / (q : ℝ)
  obtain ⟨selected, howner, hload⟩ :=
    choose_one_option_per_job
      (Job := G.E) (Option := G.E × Fin q) (Constraint := G.V × Fin q)
      Prod.fst G.tinyColorUse τ x hτ
      (by
        intro o
        constructor
        · positivity
        · have hqR : (0 : ℝ) < q := by exact_mod_cast hq
          rw [show x o = 1 / (q : ℝ) from rfl]
          exact (div_le_iff₀ hqR).2 (by
            have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
            simpa using hqOne))
      (G.tiny_uniform_jobMass hq)
      G.tinyColorUse_nonneg
      (G.tinyColorUse_le τ hweight)
      G.tinyColorUse_support_card_le_two
  let color : G.E → Fin q := fun e ↦ (selected e).2
  refine ⟨color, ?_⟩
  intro v c
  have hselected : ∀ e, (selected e).1 = e := howner
  have hrow := hload (v, c)
  rw [G.tiny_uniform_optionLoad hq v c] at hrow
  calc
    G.colorLoad color v c =
        ∑ e : G.E, G.tinyColorUse (selected e) (v, c) := by
      rw [colorLoad]
      calc
        (∑ e : G.StarEdge v,
            if color e.1 = c then G.weight e.1 else 0) =
            ∑ e : G.E,
              if G.Inc v e then
                (if color e = c then G.weight e else 0) else 0 := by
          have hsub :
              (∑ e : G.E,
                if G.Inc v e then
                  (if color e = c then G.weight e else 0) else 0) =
                ∑ e : G.StarEdge v,
                  if color e.1 = c then G.weight e.1 else 0 := by
            rw [← Finset.sum_filter]
            exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
              (by intro e; simp)
              (fun e ↦ if color e = c then G.weight e else 0)
          exact hsub.symm
        _ = ∑ e : G.E, G.tinyColorUse (selected e) (v, c) := by
          apply Finset.sum_congr rfl
          intro e _he
          by_cases hinc : G.Inc v e
          · by_cases hcol : (selected e).2 = c <;>
              simp [tinyColorUse, color, hselected e, hinc, hcol]
          · simp [tinyColorUse, color, hselected e, hinc]
    _ ≤ G.starWeight v / q + 2 * τ := hrow
    _ ≤ 1 := hroom v

end WeightedMultigraph

end

end WeightedEdgeColoring
