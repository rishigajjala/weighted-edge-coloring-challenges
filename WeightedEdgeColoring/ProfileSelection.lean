import WeightedEdgeColoring.TwoConstraintRounding

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# A finite two-sparse profile selector

This file puts `choose_one_option_per_job_indicators` into the form needed by
profile selection.  A source has a finite probability distribution on states;
choosing a state contributes a nonnegative amount to each row.  If every
source-state column is supported on at most two rows and every entry is at
most `tau`, one can choose one state at every source while increasing no row
by more than `2 * tau` above its fractional mean.

Unlike an assertion of the Harris--Srinivasan many-sums theorem, the result
below is a proved finite theorem.  Its two-row support hypothesis is stronger
than the column-sum hypothesis used in the manuscript's profile-selection
step; see the module docstring after the theorem for the remaining gap.
-/

noncomputable section

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- The load of a row before selecting one state at each source. -/
def profileRowMean (prob : Source → State → ℝ)
    (use : Source → State → Row → ℝ) (r : Row) : ℝ :=
  ∑ s, ∑ a, prob s a * use s a r

/-- A finite set of source-state pairs contains exactly one state for every
source. -/
def IsStateSelection (selected : Finset (Source × State)) : Prop :=
  ∀ s, ∃! a, (s, a) ∈ selected

private theorem optionJobMass_prod
    (z : Source × State → ℝ) (s : Source) :
    optionJobMass Prod.fst z s = ∑ a, z (s, a) := by
  rw [optionJobMass, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _hb hbs
    simp [hbs]
  · simp

/-- Select one state at each source with a dimension-free additive row error,
provided every source-state column touches at most two rows.

The right side is the exact fractional row mean.  Thus the conclusion does
not depend on the number of sources, states, or rows. -/
theorem exists_twoSparse_profile_selection
    (prob : Source → State → ℝ)
    (use : Source → State → Row → ℝ) (tau : ℝ)
    (htau : 0 < tau)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huseTau : ∀ s a r, use s a r ≤ tau)
    (hsparse : ∀ s a,
      (Finset.univ.filter fun r ↦ use s a r ≠ 0).card ≤ 2) :
    ∃ selected : Finset (Source × State),
      IsStateSelection selected ∧
      ∀ r, (∑ o ∈ selected, use o.1 o.2 r) ≤
        profileRowMean prob use r + 2 * tau := by
  let job : Source × State → Source := Prod.fst
  let x : Source × State → ℝ := fun o ↦ prob o.1 o.2
  let u : Source × State → Row → ℝ := fun o r ↦ use o.1 o.2 r
  have hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1 := by
    intro o
    constructor
    · exact hprob0 o.1 o.2
    · have hle : prob o.1 o.2 ≤ ∑ a, prob o.1 a := by
        exact Finset.single_le_sum (fun a _ ↦ hprob0 o.1 a) (Finset.mem_univ o.2)
      simpa [x, hprobSum o.1] using hle
  have hjob : ∀ s, optionJobMass job x s = 1 := by
    intro s
    rw [show job = Prod.fst from rfl, optionJobMass_prod]
    simpa [x] using hprobSum s
  obtain ⟨y, hy01, hyjob, hyload⟩ :=
    choose_one_option_per_job_indicators job u tau x htau hx hjob
      (fun o r ↦ huse0 o.1 o.2 r) (fun o r ↦ huseTau o.1 o.2 r)
      (fun o ↦ hsparse o.1 o.2)
  let selected : Finset (Source × State) := Finset.univ.filter fun o ↦ y o = 1
  have hyNonneg : ∀ o, 0 ≤ y o := by
    intro o
    rcases hy01 o with h0 | h1
    · simp [h0]
    · simp [h1]
  have hsum : ∀ s, ∑ a, y (s, a) = 1 := by
    intro s
    rw [← optionJobMass_prod]
    exact hyjob s
  have hselection : IsStateSelection selected := by
    intro s
    have hex : ∃ a, y (s, a) = 1 := by
      by_contra hnone
      push Not at hnone
      have hallZero : ∀ a, y (s, a) = 0 := by
        intro a
        exact (hy01 (s, a)).resolve_right (hnone a)
      have := hsum s
      simp [hallZero] at this
    obtain ⟨a, ha⟩ := hex
    refine ⟨a, by simp [selected, ha], ?_⟩
    intro b hb
    have hb1 : y (s, b) = 1 := by
      simpa [selected] using hb
    by_contra hab
    have hmem : b ∈ (Finset.univ : Finset State).erase a := by
      simp [hab]
    have hb_le : y (s, b) ≤ ∑ c ∈ (Finset.univ : Finset State).erase a, y (s, c) :=
      Finset.single_le_sum (fun c _ ↦ hyNonneg (s, c)) hmem
    have hdecomp := Finset.sum_erase_add (Finset.univ : Finset State)
      (fun c ↦ y (s, c)) (Finset.mem_univ a)
    change (∑ c ∈ (Finset.univ : Finset State).erase a, y (s, c)) +
      y (s, a) = ∑ c, y (s, c) at hdecomp
    rw [hsum s, ha] at hdecomp
    rw [hb1] at hb_le
    linarith
  refine ⟨selected, hselection, ?_⟩
  intro r
  have hselectedLoad :
      (∑ o ∈ selected, use o.1 o.2 r) = optionLoad u y r := by
    rw [optionLoad]
    simp only [selected, Finset.sum_filter, u]
    apply Finset.sum_congr rfl
    intro o _ho
    rcases hy01 o with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [hselectedLoad]
  calc
    optionLoad u y r ≤ optionLoad u x r + 2 * tau := hyload r
    _ = profileRowMean prob use r + 2 * tau := by
      congr 1
      simp only [optionLoad, Fintype.sum_prod_type, u, x, profileRowMean]

end

end WeightedEdgeColoring
