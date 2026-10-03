import WeightedEdgeColoring.TwoConstraintRounding

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u v w

variable {Job : Type u} {Option : Type v} {Constraint : Type w}
variable [Fintype Job] [DecidableEq Job]
variable [Fintype Option] [DecidableEq Option]
variable [Fintype Constraint] [DecidableEq Constraint]

/-- The options of one job whose zero-one indicator is one. -/
def selectedFiber (job : Option → Job) (y : Option → ℝ)
    (j : Job) : Finset Option :=
  Finset.univ.filter fun o ↦ job o = j ∧ y o = 1

/-- A zero-one vector of job mass one selects exactly one option from each
job fibre. -/
theorem card_selectedFiber_eq_one
    (job : Option → Job) (y : Option → ℝ)
    (hy01 : ∀ o, y o = 0 ∨ y o = 1)
    (hjob : ∀ j, optionJobMass job y j = 1)
    (j : Job) :
    (selectedFiber job y j).card = 1 := by
  let F : Finset Option := Finset.univ.filter fun o ↦ job o = j
  let S : Finset Option := F.filter fun o ↦ y o = 1
  have hS : S = selectedFiber job y j := by
    ext o
    simp [S, F, selectedFiber]
  have hsumF : ∑ o ∈ F, y o = 1 := by
    simpa [optionJobMass, F, Finset.sum_filter] using hjob j
  have hsumFS : ∑ o ∈ F, y o = ∑ o ∈ S, y o := by
    symm
    apply Finset.sum_subset
    · intro o ho
      exact (Finset.mem_filter.mp ho).1
    · intro o hoF hoS
      have hne : y o ≠ 1 := by
        intro hone
        exact hoS (Finset.mem_filter.mpr ⟨hoF, hone⟩)
      rcases hy01 o with hzero | hone
      · exact hzero
      · exact (hne hone).elim
  have hsumS : ∑ o ∈ S, y o = (S.card : ℝ) := by
    calc
      (∑ o ∈ S, y o) = ∑ _o ∈ S, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro o ho
        exact (Finset.mem_filter.mp ho).2
      _ = (S.card : ℝ) := by simp
  have hcardReal : (S.card : ℝ) = 1 := by
    rw [hsumFS, hsumS] at hsumF
    exact hsumF
  have hcard : S.card = 1 := by exact_mod_cast hcardReal
  simpa [hS] using hcard

/-- Choose the unique option carrying indicator one in every job fibre. -/
def selectedOption
    (job : Option → Job) (y : Option → ℝ)
    (hy01 : ∀ o, y o = 0 ∨ y o = 1)
    (hjob : ∀ j, optionJobMass job y j = 1) : Job → Option :=
  fun j ↦ Classical.choose
    ((Finset.card_eq_one.mp
      (card_selectedFiber_eq_one job y hy01 hjob j)))

theorem selectedFiber_eq_single
    (job : Option → Job) (y : Option → ℝ)
    (hy01 : ∀ o, y o = 0 ∨ y o = 1)
    (hjob : ∀ j, optionJobMass job y j = 1)
    (j : Job) :
    selectedFiber job y j = {selectedOption job y hy01 hjob j} := by
  exact Classical.choose_spec
    ((Finset.card_eq_one.mp
      (card_selectedFiber_eq_one job y hy01 hjob j)))

theorem selectedOption_mem
    (job : Option → Job) (y : Option → ℝ)
    (hy01 : ∀ o, y o = 0 ∨ y o = 1)
    (hjob : ∀ j, optionJobMass job y j = 1)
    (j : Job) :
    selectedOption job y hy01 hjob j ∈ selectedFiber job y j := by
  rw [selectedFiber_eq_single job y hy01 hjob j]
  simp

theorem owner_selectedOption
    (job : Option → Job) (y : Option → ℝ)
    (hy01 : ∀ o, y o = 0 ∨ y o = 1)
    (hjob : ∀ j, optionJobMass job y j = 1)
    (j : Job) :
    job (selectedOption job y hy01 hjob j) = j := by
  exact (Finset.mem_filter.mp
    (selectedOption_mem job y hy01 hjob j)).2.1

theorem value_selectedOption
    (job : Option → Job) (y : Option → ℝ)
    (hy01 : ∀ o, y o = 0 ∨ y o = 1)
    (hjob : ∀ j, optionJobMass job y j = 1)
    (j : Job) :
    y (selectedOption job y hy01 hjob j) = 1 := by
  exact (Finset.mem_filter.mp
    (selectedOption_mem job y hy01 hjob j)).2.2

theorem selectedOption_injective
    (job : Option → Job) (y : Option → ℝ)
    (hy01 : ∀ o, y o = 0 ∨ y o = 1)
    (hjob : ∀ j, optionJobMass job y j = 1) :
    Function.Injective (selectedOption job y hy01 hjob) := by
  intro i j hij
  have := congrArg job hij
  simpa [owner_selectedOption job y hy01 hjob] using this

theorem value_eq_one_iff_eq_selectedOption_owner
    (job : Option → Job) (y : Option → ℝ)
    (hy01 : ∀ o, y o = 0 ∨ y o = 1)
    (hjob : ∀ j, optionJobMass job y j = 1)
    (o : Option) :
    y o = 1 ↔ selectedOption job y hy01 hjob (job o) = o := by
  constructor
  · intro hone
    let S := selectedFiber job y (job o)
    have hoS : o ∈ S := by simp [S, selectedFiber, hone]
    have hset := selectedFiber_eq_single job y hy01 hjob (job o)
    have : o = selectedOption job y hy01 hjob (job o) := by
      simpa [S, hset] using hoS
    exact this.symm
  · intro h
    rw [← h]
    exact value_selectedOption job y hy01 hjob (job o)

/-- The load of a zero-one option vector is exactly the load of its selected
option function. -/
theorem optionLoad_eq_sum_selectedOption
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (y : Option → ℝ)
    (hy01 : ∀ o, y o = 0 ∨ y o = 1)
    (hjob : ∀ j, optionJobMass job y j = 1)
    (r : Constraint) :
    optionLoad use y r =
      ∑ j, use (selectedOption job y hy01 hjob j) r := by
  let choose : Job → Option := selectedOption job y hy01 hjob
  have hinj : Function.Injective choose :=
    selectedOption_injective job y hy01 hjob
  calc
    optionLoad use y r = ∑ o ∈ (Finset.univ : Finset Option),
        y o * use o r := by rfl
    _ = ∑ o ∈ Finset.univ.image choose, y o * use o r := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro o _ho hnot
      have hne : y o ≠ 1 := by
        intro hone
        apply hnot
        refine Finset.mem_image.mpr ⟨job o, Finset.mem_univ _, ?_⟩
        exact (value_eq_one_iff_eq_selectedOption_owner
          job y hy01 hjob o).mp hone
      rcases hy01 o with hzero | hone
      · simp [hzero]
      · exact (hne hone).elim
    _ = ∑ o ∈ Finset.univ.image choose, use o r := by
      apply Finset.sum_congr rfl
      intro o ho
      rcases Finset.mem_image.mp ho with ⟨j, _hj, rfl⟩
      rw [value_selectedOption job y hy01 hjob]
      simp
    _ = ∑ j, use (choose j) r := by
      rw [Finset.sum_image hinj.injOn]

/-- Function-valued form of two-constraint rounding.  It chooses one listed
option for every job and retains the same additive `2*tau` capacity bound as
the indicator theorem. -/
theorem choose_one_option_per_job
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (tau : ℝ) (x : Option → ℝ)
    (htau : 0 < tau)
    (hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1)
    (hjob : ∀ j, optionJobMass job x j = 1)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (huseTau : ∀ o r, use o r ≤ tau)
    (hsparse : ∀ o,
      (Finset.univ.filter fun r ↦ use o r ≠ 0).card ≤ 2) :
    ∃ selected : Job → Option,
      (∀ j, job (selected j) = j) ∧
      ∀ r,
        (∑ j, use (selected j) r) ≤ optionLoad use x r + 2 * tau := by
  obtain ⟨y, hy01, hyjob, hyload⟩ :=
    choose_one_option_per_job_indicators job use tau x htau hx hjob
      huse0 huseTau hsparse
  let selected : Job → Option := selectedOption job y hy01 hyjob
  refine ⟨selected, ?_, ?_⟩
  · intro j
    exact owner_selectedOption job y hy01 hyjob j
  · intro r
    rw [← optionLoad_eq_sum_selectedOption job use y hy01 hyjob r]
    exact hyload r

/-- Support-preserving function-valued form.  In addition to the same
capacity bound, the option chosen for each job has positive mass in the
input fractional point. -/
theorem choose_one_option_per_job_support
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (tau : ℝ) (x : Option → ℝ)
    (htau : 0 < tau)
    (hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1)
    (hjob : ∀ j, optionJobMass job x j = 1)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (huseTau : ∀ o r, use o r ≤ tau)
    (hsparse : ∀ o,
      (Finset.univ.filter fun r ↦ use o r ≠ 0).card ≤ 2) :
    ∃ selected : Job → Option,
      (∀ j, job (selected j) = j) ∧
      (∀ j, 0 < x (selected j)) ∧
      ∀ r,
        (∑ j, use (selected j) r) ≤ optionLoad use x r + 2 * tau := by
  obtain ⟨y, hy01, hyjob, hysupport, hyload⟩ :=
    choose_one_option_per_job_indicators_support job use tau x htau hx hjob
      huse0 huseTau hsparse
  let selected : Job → Option := selectedOption job y hy01 hyjob
  refine ⟨selected, ?_, ?_, ?_⟩
  · intro j
    exact owner_selectedOption job y hy01 hyjob j
  · intro j
    apply hysupport
    exact value_selectedOption job y hy01 hyjob j
  · intro r
    rw [← optionLoad_eq_sum_selectedOption job use y hy01 hyjob r]
    exact hyload r

end

end WeightedEdgeColoring
