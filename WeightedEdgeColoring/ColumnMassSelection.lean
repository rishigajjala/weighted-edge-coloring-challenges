import WeightedEdgeColoring.ProfileSelection

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# Finite profile selection from a column-mass bound

This module proves a deterministic assignment-packing theorem which applies
to an arbitrary finite family of rows.  One state is selected at every
source.  If the total nonnegative coefficient mass of each source-state
column is at most `budget`, then every row increases by at most `budget`
above its fractional load.

The proof is finite iterative rounding.  At a fractional point we preserve
the equation for every unfinished source and every row whose positive
support could exceed its budget.  A sum-of-slacks count shows that there are
fewer such equations than fractional variables, so a nonzero null direction
exists.  Moving to the boundary eliminates a fractional variable and the
process terminates.

This is an axiom-free column-sum analogue of the two-sparse theorem in
`ProfileSelection`.  Its error is linear in the column mass; the stronger
square-root/logarithmic Harris--Srinivasan estimate needed in the full
whole-edge synchronization step is not claimed here.
-/

noncomputable section

variable {Job Option Constraint : Type*}
variable [Fintype Job] [DecidableEq Job]
variable [Fintype Option] [DecidableEq Option]
variable [Fintype Constraint] [DecidableEq Constraint]

/-- Rows which would exceed their allowed additive column-mass budget if
every currently positive option were rounded upward. -/
def columnMassActiveConstraints
    (use : Option → Constraint → ℝ) (base : Constraint → ℝ)
    (budget : ℝ) (x : Option → ℝ) : Finset Constraint :=
  Finset.univ.filter fun r ↦
    optionSupportLoad use x r > base r + budget

/-- Static invariant for column-mass iterative rounding. -/
def IsColumnMassRoundingState
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (base : Constraint → ℝ) (budget : ℝ) (x : Option → ℝ) : Prop :=
  (∀ o, 0 ≤ x o ∧ x o ≤ 1) ∧
  (∀ j, optionJobMass job x j = 1) ∧
  ∀ r ∈ columnMassActiveConstraints use base budget x,
    optionLoad use x r = base r

/-- The initial fractional point satisfies the column-mass invariant. -/
theorem initial_isColumnMassRoundingState
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (budget : ℝ) (x : Option → ℝ)
    (hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1)
    (hjob : ∀ j, optionJobMass job x j = 1) :
    IsColumnMassRoundingState job use (optionLoad use x) budget x := by
  exact ⟨hx, hjob, fun r _hr ↦ rfl⟩

/-- Every active row has more than one complete column budget of remaining
upward load. -/
theorem budget_lt_fractional_gap_of_active
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (base : Constraint → ℝ) (budget : ℝ) (x : Option → ℝ)
    (hstate : IsColumnMassRoundingState job use base budget x)
    {r : Constraint}
    (hr : r ∈ columnMassActiveConstraints use base budget x) :
    budget <
      ∑ o ∈ optionFractionalSet x, (1 - x o) * use o r := by
  have hload : optionLoad use x r = base r := hstate.2.2 r hr
  have hactive : base r + budget < optionSupportLoad use x r := by
    simpa [columnMassActiveConstraints] using hr
  rw [← optionSupportLoad_sub_load use x hstate.1 r, hload]
  linarith

/-- Summing the remaining upward loads over any set of rows costs at most
one column budget times the total fractional slack. -/
theorem sum_fractional_gap_le_budget_mul_slack
    (use : Option → Constraint → ℝ) (budget : ℝ) (x : Option → ℝ)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (hcolumn : ∀ o, ∑ r, use o r ≤ budget)
    (A : Finset Constraint) :
    (∑ r ∈ A, ∑ o ∈ optionFractionalSet x,
        (1 - x o) * use o r) ≤
      budget * ∑ o ∈ optionFractionalSet x, (1 - x o) := by
  rw [show
      (∑ r ∈ A, ∑ o ∈ optionFractionalSet x,
          (1 - x o) * use o r) =
        ∑ o ∈ optionFractionalSet x,
          (1 - x o) * ∑ r ∈ A, use o r by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro o _ho
    rw [Finset.mul_sum]]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o ho
  have hofrac : 0 < x o ∧ x o < 1 := by
    simpa [optionFractionalSet] using ho
  have hpartial : (∑ r ∈ A, use o r) ≤ ∑ r, use o r := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun _ _ ↦ Finset.mem_univ _) (fun r _hr _hrA ↦ huse0 o r)
  have hsum : (∑ r ∈ A, use o r) ≤ budget :=
    hpartial.trans (hcolumn o)
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hofrac.2.le))

/-- The active row equations and unfinished-job equations leave a nonzero
rounding direction. -/
theorem columnMass_active_add_unfinished_lt_fractional
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (base : Constraint → ℝ) (budget : ℝ) (x : Option → ℝ)
    (hbudget : 0 < budget)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (hcolumn : ∀ o, ∑ r, use o r ≤ budget)
    (hF : (optionFractionalSet x).Nonempty)
    (hstate : IsColumnMassRoundingState job use base budget x) :
    (unfinishedJobs job x).card +
        (columnMassActiveConstraints use base budget x).card <
      (optionFractionalSet x).card := by
  let F := optionFractionalSet x
  let U := unfinishedJobs job x
  let A := columnMassActiveConstraints use base budget x
  by_cases hA : A.Nonempty
  · have hgap_each : ∀ r ∈ A, budget <
        ∑ o ∈ F, (1 - x o) * use o r := by
      intro r hr
      exact budget_lt_fractional_gap_of_active job use base budget x hstate hr
    have hsum_lower : budget * (A.card : ℝ) <
        ∑ r ∈ A, ∑ o ∈ F, (1 - x o) * use o r := by
      calc
        budget * (A.card : ℝ) = ∑ _r ∈ A, budget := by
          simp [mul_comm]
        _ < ∑ r ∈ A, ∑ o ∈ F, (1 - x o) * use o r := by
          exact Finset.sum_lt_sum_of_nonempty hA hgap_each
    have hsum_upper :
        (∑ r ∈ A, ∑ o ∈ F, (1 - x o) * use o r) ≤
          budget * ∑ o ∈ F, (1 - x o) :=
      sum_fractional_gap_le_budget_mul_slack use budget x huse0 hcolumn A
    have hslack := sum_one_sub_fractional_eq job x hstate.1 hstate.2.1
    have hreal : (A.card : ℝ) < (F.card : ℝ) - (U.card : ℝ) := by
      have hmul : budget * (A.card : ℝ) <
          budget * ((F.card : ℝ) - (U.card : ℝ)) := by
        calc
          budget * (A.card : ℝ) <
              ∑ r ∈ A, ∑ o ∈ F, (1 - x o) * use o r := hsum_lower
          _ ≤ budget * ∑ o ∈ F, (1 - x o) := hsum_upper
          _ = budget * ((F.card : ℝ) - (U.card : ℝ)) := by
            simpa [F, U] using congrArg (fun z : ℝ ↦ budget * z) hslack
      nlinarith
    have hnat : A.card + U.card < F.card := by
      exact_mod_cast (by linarith : (A.card : ℝ) + U.card < F.card)
    simpa [F, U, A, Nat.add_comm] using hnat
  · have hAeq : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    have htwice : 2 * U.card ≤ F.card :=
      twice_unfinishedJobs_card_le_fractional_card job x hstate.1 hstate.2.1
    have hFpos : 0 < F.card := Finset.card_pos.mpr (by simpa [F] using hF)
    have hUF : U.card < F.card := by omega
    simpa [F, U, A, hAeq] using hUF

/-- A nonzero direction supported on fractional options which preserves all
unfinished-job equations and all active row equations. -/
theorem exists_columnMass_rounding_direction
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (base : Constraint → ℝ) (budget : ℝ) (x : Option → ℝ)
    (hbudget : 0 < budget)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (hcolumn : ∀ o, ∑ r, use o r ≤ budget)
    (hF : (optionFractionalSet x).Nonempty)
    (hstate : IsColumnMassRoundingState job use base budget x) :
    ∃ z : Option → ℝ,
      z ≠ 0 ∧
      (∀ o, o ∉ optionFractionalSet x → z o = 0) ∧
      (∀ j, (∑ o, if job o = j then z o else 0) = 0) ∧
      ∀ r ∈ columnMassActiveConstraints use base budget x,
        ∑ o, z o * use o r = 0 := by
  let F := optionFractionalSet x
  let U := unfinishedJobs job x
  let A := columnMassActiveConstraints use base budget x
  have hcount : U.card + A.card < F.card := by
    simpa [F, U, A] using
      columnMass_active_add_unfinished_lt_fractional job use base budget x
        hbudget huse0 hcolumn hF hstate
  let Row := Sum {j : Job // j ∈ U} {r : Constraint // r ∈ A}
  let Col := {o : Option // o ∈ F}
  let M : Matrix Row Col ℝ := fun row o =>
    match row with
    | Sum.inl j => if job o.1 = j.1 then 1 else 0
    | Sum.inr r => use o.1 r.1
  have hcard : Fintype.card Row < Fintype.card Col := by
    simpa [Row, Col, Fintype.card_sum, Fintype.card_coe] using hcount
  obtain ⟨zF, hzF, hrows⟩ := exists_nonzero_annihilated_vector hcard M
  let z : Option → ℝ := fun o ↦ if ho : o ∈ F then zF ⟨o, ho⟩ else 0
  have hz : z ≠ 0 := by
    intro hz0
    apply hzF
    funext o
    have := congr_fun hz0 o.1
    simpa [z, o.2] using this
  have hzout : ∀ o, o ∉ F → z o = 0 := by
    intro o ho
    simp [z, ho]
  refine ⟨z, hz, by simpa [F] using hzout, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ U
    · have hrow := hrows (Sum.inl ⟨j, hj⟩ : Row)
      have hrestrict :
          (∑ o, if job o = j then z o else 0) =
            ∑ o ∈ F, (if job o = j then z o else 0) := by
        symm
        apply Finset.sum_subset (fun _ _ ↦ Finset.mem_univ _)
        intro o _ho hnot
        have hoF : o ∉ F := by simpa using hnot
        simp [hzout o hoF]
      rw [hrestrict]
      calc
        (∑ o ∈ F, (if job o = j then z o else 0)) =
            ∑ o : Col, (if job o.1 = j then zF o else 0) := by
              rw [← Finset.sum_attach]
              simp [Col, z]
        _ = 0 := by
          simpa [M, Row, Col] using hrow
    · have hzero : ∀ o, (if job o = j then z o else 0) = 0 := by
        intro o
        by_cases hoj : job o = j
        · have hoF : o ∉ F := by
            intro hoF
            exact hj (Finset.mem_image.mpr ⟨o, hoF, hoj⟩)
          simp [hoj, hzout o hoF]
        · simp [hoj]
      simp [hzero]
  · intro r hr
    have hrow := hrows (Sum.inr ⟨r, hr⟩ : Row)
    have hrestrict : (∑ o, z o * use o r) =
        ∑ o ∈ F, z o * use o r := by
      symm
      apply Finset.sum_subset (fun _ _ ↦ Finset.mem_univ _)
      intro o _ho hnot
      have hoF : o ∉ F := by simpa using hnot
      simp [hzout o hoF]
    rw [hrestrict]
    calc
      (∑ o ∈ F, z o * use o r) =
          ∑ o : Col, zF o * use o.1 r := by
            rw [← Finset.sum_attach]
            simp [Col, z]
      _ = 0 := by
        simpa [M, Row, Col, mul_comm] using hrow

/-- One column-mass rounding step reaches a new boundary coordinate while
preserving the invariant. -/
theorem exists_columnMass_state_step
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (base : Constraint → ℝ) (budget : ℝ) (x : Option → ℝ)
    (hbudget : 0 < budget)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (hcolumn : ∀ o, ∑ r, use o r ≤ budget)
    (hF : (optionFractionalSet x).Nonempty)
    (hstate : IsColumnMassRoundingState job use base budget x) :
    ∃ x' : Option → ℝ,
      IsColumnMassRoundingState job use base budget x' ∧
      optionFractionalSet x' ⊂ optionFractionalSet x := by
  let F := optionFractionalSet x
  obtain ⟨z, hz, hzout, hzjob, hzactive⟩ :=
    exists_columnMass_rounding_direction job use base budget x hbudget
      huse0 hcolumn hF hstate
  let Col := {o : Option // o ∈ F}
  let xF : Col → ℝ := fun o ↦ x o.1
  let zF : Col → ℝ := fun o ↦ z o.1
  have hxF : ∀ o, 0 < xF o ∧ xF o < 1 := by
    intro o
    have hoF : o.1 ∈ optionFractionalSet x := by simpa [F] using o.2
    have := (Finset.mem_filter.mp hoF).2
    simpa [xF] using this
  have hzF : zF ≠ 0 := by
    intro hzero
    apply hz
    funext o
    by_cases ho : o ∈ F
    · have := congr_fun hzero (⟨o, ho⟩ : Col)
      simpa [zF] using this
    · exact hzout o (by simpa [F] using ho)
  obtain ⟨t, ht, hboundsF, ob, hob⟩ :=
    exists_positive_step_to_boundary xF zF hxF hzF
  let x' : Option → ℝ := fun o ↦ x o + t * z o
  have hbounds : ∀ o, 0 ≤ x' o ∧ x' o ≤ 1 := by
    intro o
    by_cases ho : o ∈ F
    · simpa [x', xF, zF, Col] using hboundsF (⟨o, ho⟩ : Col)
    · have hzo : z o = 0 := hzout o (by simpa [F] using ho)
      simpa [x', hzo] using hstate.1 o
  have hpositive_subset : optionPositiveSet x' ⊆ optionPositiveSet x := by
    intro o ho'
    have hxp : 0 < x' o := by simpa [optionPositiveSet] using ho'
    by_cases ho : o ∈ F
    · have hxo : 0 < x o := by
        have := (by simpa [F, optionFractionalSet] using ho :
          0 < x o ∧ x o < 1)
        exact this.1
      simpa [optionPositiveSet, hxo]
    · have hzo : z o = 0 := hzout o (by simpa [F] using ho)
      have hxo : 0 < x o := by simpa [x', hzo] using hxp
      simpa [optionPositiveSet, hxo]
  have hsupport_mono : ∀ r,
      optionSupportLoad use x' r ≤ optionSupportLoad use x r := by
    intro r
    unfold optionSupportLoad
    exact Finset.sum_le_sum_of_subset_of_nonneg hpositive_subset
      (fun o _ _ ↦ huse0 o r)
  have hjob' : ∀ j, optionJobMass job x' j = 1 := by
    intro j
    have hterm : ∀ o,
        (if job o = j then x' o else 0) =
          (if job o = j then x o else 0) +
            t * (if job o = j then z o else 0) := by
      intro o
      by_cases hoj : job o = j
      · simp [hoj, x']
      · simp [hoj]
    rw [optionJobMass]
    calc
      (∑ o, if job o = j then x' o else 0) =
          ∑ o, ((if job o = j then x o else 0) +
            t * (if job o = j then z o else 0)) := by
              apply Finset.sum_congr rfl
              intro o _ho
              exact hterm o
      _ = optionJobMass job x j +
          t * (∑ o, if job o = j then z o else 0) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
            rfl
      _ = 1 := by rw [hstate.2.1 j, hzjob j]; ring
  have hload_preserved :
      ∀ r ∈ columnMassActiveConstraints use base budget x,
        optionLoad use x' r = optionLoad use x r := by
    intro r hr
    have hterm : ∀ o,
        x' o * use o r = x o * use o r + t * (z o * use o r) := by
      intro o
      simp only [x']
      ring
    rw [optionLoad, optionLoad]
    calc
      (∑ o, x' o * use o r) =
          ∑ o, (x o * use o r + t * (z o * use o r)) := by
            apply Finset.sum_congr rfl
            intro o _ho
            exact hterm o
      _ = (∑ o, x o * use o r) + t * (∑ o, z o * use o r) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ o, x o * use o r := by rw [hzactive r hr]; ring
  have hactive' :
      ∀ r ∈ columnMassActiveConstraints use base budget x',
        optionLoad use x' r = base r := by
    intro r hr'
    have hactive_val : base r + budget < optionSupportLoad use x' r := by
      simpa [columnMassActiveConstraints] using hr'
    have hr : r ∈ columnMassActiveConstraints use base budget x := by
      simp only [columnMassActiveConstraints, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hactive_val.trans_le (hsupport_mono r)
    rw [hload_preserved r hr]
    exact hstate.2.2 r hr
  refine ⟨x', ⟨hbounds, hjob', hactive'⟩, ?_⟩
  have hsubset : optionFractionalSet x' ⊆ F := by
    intro o ho'
    have hfrac' : 0 < x' o ∧ x' o < 1 := by
      simpa [optionFractionalSet] using ho'
    by_contra hoF
    have hzo : z o = 0 := hzout o (by simpa [F] using hoF)
    have hfrac : 0 < x o ∧ x o < 1 := by simpa [x', hzo] using hfrac'
    exact hoF (by simpa [F, optionFractionalSet] using hfrac)
  have hobF : ob.1 ∈ F := ob.2
  have hob_not : ob.1 ∉ optionFractionalSet x' := by
    intro hmem
    have hfrac' : 0 < x' ob.1 ∧ x' ob.1 < 1 := by
      simpa [optionFractionalSet] using hmem
    have heq : x' ob.1 = 0 ∨ x' ob.1 = 1 := by
      simpa [x', xF, zF, Col] using hob
    rcases heq with h0 | h1
    · linarith
    · linarith
  have hne : optionFractionalSet x' ≠ F := by
    intro heq
    exact hob_not (heq.symm ▸ hobF)
  exact (Finset.ssubset_iff_subset_ne).mpr ⟨hsubset, hne⟩

/-- Repeated column-mass rounding terminates at a zero-one point. -/
theorem exists_integral_columnMass_state
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (base : Constraint → ℝ) (budget : ℝ) (x : Option → ℝ)
    (hbudget : 0 < budget)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (hcolumn : ∀ o, ∑ r, use o r ≤ budget)
    (hstate : IsColumnMassRoundingState job use base budget x) :
    ∃ y : Option → ℝ,
      IsColumnMassRoundingState job use base budget y ∧
      ∀ o, y o = 0 ∨ y o = 1 := by
  let P : ℕ → Prop := fun k ↦
    ∀ x : Option → ℝ, (optionFractionalSet x).card = k →
      IsColumnMassRoundingState job use base budget x →
      ∃ y : Option → ℝ,
        IsColumnMassRoundingState job use base budget y ∧
        ∀ o, y o = 0 ∨ y o = 1
  have hP : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hxcard hstateX
      by_cases hF : (optionFractionalSet x).Nonempty
      · obtain ⟨x', hstate', hproper⟩ :=
          exists_columnMass_state_step job use base budget x hbudget
            huse0 hcolumn hF hstateX
        have hcardlt : (optionFractionalSet x').card < k := by
          rw [← hxcard]
          exact Finset.card_lt_card hproper
        exact ih _ hcardlt x' rfl hstate'
      · refine ⟨x, hstateX, ?_⟩
        intro o
        by_contra hnot
        have hne : x o ≠ 0 ∧ x o ≠ 1 := not_or.mp hnot
        have hpos : 0 < x o :=
          lt_of_le_of_ne (hstateX.1 o).1 (Ne.symm hne.1)
        have hlt : x o < 1 :=
          lt_of_le_of_ne (hstateX.1 o).2 hne.2
        exact hF ⟨o, by simp [optionFractionalSet, hpos, hlt]⟩
  exact hP (optionFractionalSet x).card x rfl hstate

/-- Select exactly one option for every job.  If every option has total
nonnegative use at most `budget` across all rows, every row exceeds its
fractional load by at most `budget`. -/
theorem choose_one_option_per_job_columnMass
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (budget : ℝ) (x : Option → ℝ)
    (hbudget : 0 < budget)
    (hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1)
    (hjob : ∀ j, optionJobMass job x j = 1)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (hcolumn : ∀ o, ∑ r, use o r ≤ budget) :
    ∃ y : Option → ℝ,
      (∀ o, y o = 0 ∨ y o = 1) ∧
      (∀ j, optionJobMass job y j = 1) ∧
      ∀ r, optionLoad use y r ≤ optionLoad use x r + budget := by
  let base : Constraint → ℝ := optionLoad use x
  have hinitial : IsColumnMassRoundingState job use base budget x := by
    exact initial_isColumnMassRoundingState job use budget x hx hjob
  obtain ⟨y, hstate, hy01⟩ :=
    exists_integral_columnMass_state job use base budget x hbudget
      huse0 hcolumn hinitial
  refine ⟨y, hy01, hstate.2.1, ?_⟩
  intro r
  have hfracempty : optionFractionalSet y = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro o ho
    have hfrac : 0 < y o ∧ y o < 1 := by
      simpa [optionFractionalSet] using ho
    rcases hy01 o with h0 | h1 <;> linarith
  have heqSupport : optionSupportLoad use y r = optionLoad use y r := by
    have hdiff := optionSupportLoad_sub_load use y hstate.1 r
    rw [hfracempty] at hdiff
    simp only [Finset.sum_empty] at hdiff
    linarith
  by_cases hle : optionSupportLoad use y r ≤ base r + budget
  · simpa [base, heqSupport] using hle
  · have hr : r ∈ columnMassActiveConstraints use base budget y := by
      simp only [columnMassActiveConstraints, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact lt_of_not_ge hle
    have hload := hstate.2.2 r hr
    rw [hload]
    dsimp [base]
    linarith

section Profiles

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- Profile-selection form of column-mass rounding. -/
theorem exists_columnMass_profile_selection
    (prob : Source → State → ℝ)
    (use : Source → State → Row → ℝ) (budget : ℝ)
    (hbudget : 0 < budget)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (hcolumn : ∀ s a, ∑ r, use s a r ≤ budget) :
    ∃ selected : Finset (Source × State),
      IsStateSelection selected ∧
      ∀ r, (∑ o ∈ selected, use o.1 o.2 r) ≤
        profileRowMean prob use r + budget := by
  let job : Source × State → Source := Prod.fst
  let x : Source × State → ℝ := fun o ↦ prob o.1 o.2
  let u : Source × State → Row → ℝ := fun o r ↦ use o.1 o.2 r
  have hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1 := by
    intro o
    constructor
    · exact hprob0 o.1 o.2
    · have hle : prob o.1 o.2 ≤ ∑ a, prob o.1 a := by
        exact Finset.single_le_sum (fun a _ ↦ hprob0 o.1 a)
          (Finset.mem_univ o.2)
      simpa [x, hprobSum o.1] using hle
  have hjob : ∀ s, optionJobMass job x s = 1 := by
    intro s
    rw [show job = Prod.fst from rfl]
    rw [optionJobMass, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single s]
    · simpa [x] using hprobSum s
    · intro b _hb hbs
      simp [hbs]
    · simp
  obtain ⟨y, hy01, hyjob, hyload⟩ :=
    choose_one_option_per_job_columnMass job u budget x hbudget hx hjob
      (fun o r ↦ huse0 o.1 o.2 r) (fun o ↦ hcolumn o.1 o.2)
  let selected : Finset (Source × State) :=
    Finset.univ.filter fun o ↦ y o = 1
  have hyNonneg : ∀ o, 0 ≤ y o := by
    intro o
    rcases hy01 o with h0 | h1
    · simp [h0]
    · simp [h1]
  have hsum : ∀ s, ∑ a, y (s, a) = 1 := by
    intro s
    have hs := hyjob s
    rw [show job = Prod.fst from rfl, optionJobMass,
      Fintype.sum_prod_type] at hs
    rw [Finset.sum_eq_single s] at hs
    · simpa using hs
    · intro b _hb hbs
      simp [hbs]
    · simp
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
    have hb_le : y (s, b) ≤
        ∑ c ∈ (Finset.univ : Finset State).erase a, y (s, c) :=
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
    optionLoad u y r ≤ optionLoad u x r + budget := hyload r
    _ = profileRowMean prob use r + budget := by
      congr 1
      simp only [optionLoad, Fintype.sum_prod_type, u, x, profileRowMean]

/-- Bounded-support corollary.  If a state touches at most `d` rows and
each entry is at most `tau`, the additive loss is `d * tau`. -/
theorem exists_boundedSupport_profile_selection
    (prob : Source → State → ℝ)
    (use : Source → State → Row → ℝ)
    (d : ℕ) (tau : ℝ)
    (hd : 0 < d) (htau : 0 < tau)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huseTau : ∀ s a r, use s a r ≤ tau)
    (hsupport : ∀ s a,
      (Finset.univ.filter fun r ↦ use s a r ≠ 0).card ≤ d) :
    ∃ selected : Finset (Source × State),
      IsStateSelection selected ∧
      ∀ r, (∑ o ∈ selected, use o.1 o.2 r) ≤
        profileRowMean prob use r + (d : ℝ) * tau := by
  have hbudget : 0 < (d : ℝ) * tau :=
    mul_pos (by exact_mod_cast hd) htau
  apply exists_columnMass_profile_selection prob use ((d : ℝ) * tau)
    hbudget hprob0 hprobSum huse0
  intro s a
  let A : Finset Row := Finset.univ.filter fun r ↦ use s a r ≠ 0
  have hrewrite : (∑ r, use s a r) = ∑ r ∈ A, use s a r := by
    symm
    apply Finset.sum_subset (fun _ _ ↦ Finset.mem_univ _)
    intro r _hr hrA
    have : use s a r = 0 := by
      by_contra hne
      exact hrA (by simp [A, hne])
    simp [this]
  rw [hrewrite]
  calc
    (∑ r ∈ A, use s a r) ≤ ∑ _r ∈ A, tau := by
      exact Finset.sum_le_sum fun r _hr ↦ huseTau s a r
    _ = (A.card : ℝ) * tau := by simp
    _ ≤ (d : ℝ) * tau := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast (hsupport s a) : (A.card : ℝ) ≤ d) htau.le

end Profiles

end

end WeightedEdgeColoring
