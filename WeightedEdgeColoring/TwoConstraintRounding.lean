import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# Linear-algebra core of two-constraint rounding

The whole-edge rounding proof repeatedly preserves fewer affine equations
than there are fractional option values.  The first theorem below is the
kernel statement that makes such a move possible.
-/

/-- A real matrix with fewer rows than columns has a nonzero vector on which
all row sums vanish. -/
theorem exists_nonzero_annihilated_vector
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    (hcard : Fintype.card Row < Fintype.card Col)
    (A : Matrix Row Col ℝ) :
    ∃ z : Col → ℝ, z ≠ 0 ∧ ∀ r, ∑ c, A r c * z c = 0 := by
  let L : (Col → ℝ) →ₗ[ℝ] (Row → ℝ) := Matrix.mulVecLin A
  have hdim : Module.finrank ℝ (Row → ℝ) < Module.finrank ℝ (Col → ℝ) := by
    simpa only [Module.finrank_fintype_fun_eq_card] using hcard
  have hker : LinearMap.ker L ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨z, hzker, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨z, hz0, ?_⟩
  have hL : L z = 0 := LinearMap.mem_ker.mp hzker
  intro r
  have := congr_fun hL r
  simpa only [L, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply]
    using this

/-- Move a genuinely fractional vector in any nonzero direction until the
first coordinate reaches `0` or `1`.  No coordinate leaves the unit interval.
This is the second elementary step in the linear-algebra rounding process. -/
theorem exists_positive_step_to_boundary
    {Col : Type*} [Fintype Col] [DecidableEq Col]
    (x z : Col → ℝ) (hx : ∀ c, 0 < x c ∧ x c < 1) (hz : z ≠ 0) :
    ∃ t : ℝ, 0 < t ∧
      (∀ c, 0 ≤ x c + t * z c ∧ x c + t * z c ≤ 1) ∧
      ∃ c, x c + t * z c = 0 ∨ x c + t * z c = 1 := by
  let S : Finset Col := Finset.univ.filter fun c => z c ≠ 0
  have hS : S.Nonempty := by
    by_contra hempty
    have hzero : ∀ c, z c = 0 := by
      intro c
      by_contra hc
      exact hempty ⟨c, by simp [S, hc]⟩
    exact hz (funext hzero)
  let cap : Col → ℝ := fun c =>
    if 0 < z c then (1 - x c) / z c else x c / (-z c)
  have hcap_pos : ∀ c ∈ S, 0 < cap c := by
    intro c hc
    have hzc : z c ≠ 0 := by simpa [S] using hc
    by_cases hp : 0 < z c
    · simp only [cap, if_pos hp]
      exact div_pos (sub_pos.mpr (hx c).2) hp
    · have hn : z c < 0 := lt_of_le_of_ne (le_of_not_gt hp) hzc
      simp only [cap, if_neg hp]
      exact div_pos (hx c).1 (neg_pos.mpr hn)
  let B : Finset ℝ := S.image cap
  have hB : B.Nonempty := hS.image cap
  let t : ℝ := B.min' hB
  have ht_mem : t ∈ B := B.min'_mem hB
  have htpos : 0 < t := by
    rcases Finset.mem_image.mp ht_mem with ⟨c, hcS, hct⟩
    rw [← hct]
    exact hcap_pos c hcS
  have ht_le_cap : ∀ c ∈ S, t ≤ cap c := by
    intro c hc
    exact B.min'_le (cap c) (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  refine ⟨t, htpos, ?_, ?_⟩
  · intro c
    by_cases hzc : z c = 0
    · simp [hzc, (hx c).1.le, (hx c).2.le]
    · have hcS : c ∈ S := by simp [S, hzc]
      have htc := ht_le_cap c hcS
      by_cases hp : 0 < z c
      · have hupper : t * z c ≤ 1 - x c := by
          exact (le_div_iff₀ hp).mp (by simpa [cap, hp] using htc)
        have htz : 0 ≤ t * z c := mul_nonneg htpos.le hp.le
        have hx0 : 0 < x c := (hx c).1
        constructor
        · linarith
        · linarith
      · have hn : z c < 0 := lt_of_le_of_ne (le_of_not_gt hp) hzc
        have hlower : t * (-z c) ≤ x c := by
          exact (le_div_iff₀ (neg_pos.mpr hn)).mp (by simpa [cap, hp] using htc)
        have htz : t * z c ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos htpos.le hn.le
        have hx0 : 0 < x c := (hx c).1
        have hx1 : x c < 1 := (hx c).2
        constructor
        · nlinarith
        · linarith
  · rcases Finset.mem_image.mp ht_mem with ⟨c, hcS, hct⟩
    refine ⟨c, ?_⟩
    have hzc : z c ≠ 0 := by simpa [S] using hcS
    by_cases hp : 0 < z c
    · right
      have heq : t = (1 - x c) / z c := by simpa [t, cap, hp] using hct.symm
      rw [heq]
      field_simp [hp.ne']
      linarith
    · left
      have hn : z c < 0 := lt_of_le_of_ne (le_of_not_gt hp) hzc
      have heq : t = x c / (-z c) := by simpa [t, cap, hp] using hct.symm
      rw [heq]
      field_simp [hzc]
      ring

noncomputable section TwoSparseSystem

variable {Job Option Constraint : Type*}
variable [Fintype Job] [DecidableEq Job]
variable [Fintype Option] [DecidableEq Option]
variable [Fintype Constraint] [DecidableEq Constraint]

/-- Options whose current values are strictly between zero and one, written
using endpoint inequalities so it can be used without any ambient bounds. -/
def optionFractionalSet (x : Option → ℝ) : Finset Option :=
  Finset.univ.filter fun o => 0 < x o ∧ x o < 1

/-- Options with positive current value. -/
def optionPositiveSet (x : Option → ℝ) : Finset Option :=
  Finset.univ.filter fun o => 0 < x o

/-- Total fractional mass belonging to one job. -/
def optionJobMass (job : Option → Job) (x : Option → ℝ) (j : Job) : ℝ :=
  ∑ o, if job o = j then x o else 0

/-- Expected use of one capacity constraint. -/
def optionLoad (use : Option → Constraint → ℝ) (x : Option → ℝ)
    (r : Constraint) : ℝ :=
  ∑ o, x o * use o r

/-- The load obtained if every currently positive option were rounded up. -/
def optionSupportLoad (use : Option → Constraint → ℝ) (x : Option → ℝ)
    (r : Constraint) : ℝ :=
  ∑ o ∈ optionPositiveSet x, use o r

/-- Jobs containing at least one fractional option. -/
def unfinishedJobs (job : Option → Job) (x : Option → ℝ) : Finset Job :=
  (optionFractionalSet x).image job

/-- Constraints whose current positive support could exceed the allowed
additive error.  These are precisely the equations that must still be kept. -/
def activeConstraints (use : Option → Constraint → ℝ)
    (base : Constraint → ℝ) (tau : ℝ) (x : Option → ℝ) : Finset Constraint :=
  Finset.univ.filter fun r => optionSupportLoad use x r > base r + 2 * tau

/-- Amount by which fractional options using one constraint could still
increase if each were rounded upward.  This is measured in units of option
count, before multiplying by the maximum amount `tau`. -/
def optionRemainingPotential (use : Option → Constraint → ℝ)
    (x : Option → ℝ) (r : Constraint) : ℝ :=
  ∑ o ∈ optionFractionalSet x,
    if use o r = 0 then 0 else 1 - x o

/-- Static invariant for the iterative proof.  An unsafe capacity row is
held at its original fractional load.  Safe rows need no equation, because
future steps only shrink positive support. -/
def IsTwoConstraintRoundingState
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (base : Constraint → ℝ) (tau : ℝ) (x : Option → ℝ) : Prop :=
  (∀ o, 0 ≤ x o ∧ x o ≤ 1) ∧
  (∀ j, optionJobMass job x j = 1) ∧
  ∀ r ∈ activeConstraints use base tau x, optionLoad use x r = base r

/-- The initial fractional point satisfies the static invariant by taking
`base` to be its own capacity-load vector. -/
theorem initial_isTwoConstraintRoundingState
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (tau : ℝ) (x : Option → ℝ)
    (hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1)
    (hjob : ∀ j, optionJobMass job x j = 1) :
    IsTwoConstraintRoundingState job use (optionLoad use x) tau x := by
  exact ⟨hx, hjob, fun r _hr => rfl⟩

/-- A job containing a fractional option cannot contain an option of value
one, since its total mass is one and all option values are nonnegative. -/
theorem value_ne_one_of_job_has_fractional
    (job : Option → Job) (x : Option → ℝ)
    (hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1)
    (hjob : ∀ j, optionJobMass job x j = 1)
    {j : Job} (hj : j ∈ unfinishedJobs job x)
    {o : Option} (hoj : job o = j) : x o ≠ 1 := by
  rcases Finset.mem_image.mp hj with ⟨f, hf, hfj⟩
  have hffrac : 0 < x f ∧ x f < 1 := by
    simpa [optionFractionalSet] using hf
  intro hone
  have hsum : optionJobMass job x j = 1 := hjob j
  have hfo : f ≠ o := by
    intro h
    subst f
    linarith
  have hle : x f + x o ≤ optionJobMass job x j := by
    dsimp [optionJobMass]
    let s : Finset Option := {f, o}
    have hs : s ⊆ Finset.univ := fun _ _ => Finset.mem_univ _
    calc
      x f + x o = ∑ q ∈ s, (if job q = j then x q else 0) := by
        simp [s, hfo, hoj, hfj]
      _ ≤ ∑ q ∈ Finset.univ, (if job q = j then x q else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hs
        intro q _hq _hqs
        split_ifs
        · exact (hx q).1
        · exact le_rfl
      _ = optionJobMass job x j := by
        simp only [optionJobMass]
  rw [hsum, hone] at hle
  linarith

/-- Every unfinished job has at least two fractional options. -/
theorem two_le_fractional_fiber_card
    (job : Option → Job) (x : Option → ℝ)
    (hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1)
    (hjob : ∀ j, optionJobMass job x j = 1)
    {j : Job} (hj : j ∈ unfinishedJobs job x) :
    2 ≤ ((optionFractionalSet x).filter fun o => job o = j).card := by
  rcases Finset.mem_image.mp hj with ⟨f, hf, hfj⟩
  have hffrac : 0 < x f ∧ x f < 1 := by
    simpa [optionFractionalSet] using hf
  have hfmem : f ∈ (optionFractionalSet x).filter fun o => job o = j := by
    exact Finset.mem_filter.mpr ⟨hf, hfj⟩
  by_contra hnot
  have hcardle : ((optionFractionalSet x).filter fun o => job o = j).card ≤ 1 := by
    omega
  have hsingleton : (optionFractionalSet x).filter (fun o => job o = j) = {f} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hfmem, ?_⟩
    intro q hq
    by_contra hqf
    have htwo : 1 < ((optionFractionalSet x).filter fun o => job o = j).card :=
      Finset.one_lt_card.mpr ⟨f, hfmem, q, hq, fun h => hqf h.symm⟩
    omega
  have hsum_other_zero :
      ∑ o ∈ Finset.univ.filter (fun o => job o = j), x o = x f := by
    have hzero : ∀ o ∈ Finset.univ.filter (fun o => job o = j), o ≠ f → x o = 0 := by
      intro o ho hof
      have hoj : job o = j := (Finset.mem_filter.mp ho).2
      have hneone : x o ≠ 1 :=
        value_ne_one_of_job_has_fractional job x hx hjob hj hoj
      by_contra hxzero
      have hxpos : 0 < x o := lt_of_le_of_ne (hx o).1 (Ne.symm hxzero)
      have hxlt : x o < 1 := lt_of_le_of_ne (hx o).2 hneone
      have homem : o ∈ (optionFractionalSet x).filter fun q => job q = j := by
        simp [optionFractionalSet, hxpos, hxlt, hoj]
      have : o = f := by simpa [hsingleton] using homem
      exact hof this
    rw [← Finset.sum_erase_add (Finset.univ.filter (fun o => job o = j)) x
      (by exact Finset.mem_filter.mpr ⟨Finset.mem_univ f, hfj⟩)]
    have : ∑ o ∈ (Finset.univ.filter (fun o => job o = j)).erase f, x o = 0 := by
      apply Finset.sum_eq_zero
      intro o ho
      exact hzero o (Finset.mem_of_mem_erase ho) (Finset.ne_of_mem_erase ho)
    rw [this]
    simp
  have hmass_as_filter : optionJobMass job x j =
      ∑ o ∈ Finset.univ.filter (fun o => job o = j), x o := by
    simp only [optionJobMass, Finset.sum_ite_irrel, Finset.sum_filter]
  have := hjob j
  rw [hmass_as_filter, hsum_other_zero] at this
  linarith

/-- The fractional options of an unfinished job carry its full unit mass. -/
theorem sum_fractional_fiber_eq_one
    (job : Option → Job) (x : Option → ℝ)
    (hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1)
    (hjob : ∀ j, optionJobMass job x j = 1)
    {j : Job} (hj : j ∈ unfinishedJobs job x) :
    ∑ o ∈ (optionFractionalSet x).filter (fun o => job o = j), x o = 1 := by
  have hzero : ∀ o, job o = j → o ∉ optionFractionalSet x → x o = 0 := by
    intro o hoj hof
    have hneone : x o ≠ 1 :=
      value_ne_one_of_job_has_fractional job x hx hjob hj hoj
    have hnotfrac : ¬(0 < x o ∧ x o < 1) := by
      simpa [optionFractionalSet] using hof
    rcases not_and_or.mp hnotfrac with hnpos | hnlt
    · exact le_antisymm (le_of_not_gt hnpos) (hx o).1
    · have : x o = 1 := le_antisymm (hx o).2 (le_of_not_gt hnlt)
      exact (hneone this).elim
  have htotal : ∑ o ∈ Finset.univ.filter (fun o => job o = j), x o = 1 := by
    have hjmass := hjob j
    simpa only [optionJobMass, Finset.sum_filter] using hjmass
  calc
    ∑ o ∈ (optionFractionalSet x).filter (fun o => job o = j), x o
        = ∑ o ∈ Finset.univ.filter (fun o => job o = j), x o := by
          apply Finset.sum_subset
          · intro o ho
            have hparts := Finset.mem_filter.mp ho
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hparts.2⟩
          · intro o hoBig hoSmall
            have hoj : job o = j := (Finset.mem_filter.mp hoBig).2
            have hofrac : o ∉ optionFractionalSet x := by
              intro hof
              exact hoSmall (Finset.mem_filter.mpr ⟨hof, hoj⟩)
            exact hzero o hoj hofrac
    _ = 1 := htotal

/-- There are at least two fractional option values for every unfinished
job, hence twice as many fractional values as unfinished jobs. -/
theorem twice_unfinishedJobs_card_le_fractional_card
    (job : Option → Job) (x : Option → ℝ)
    (hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1)
    (hjob : ∀ j, optionJobMass job x j = 1) :
    2 * (unfinishedJobs job x).card ≤ (optionFractionalSet x).card := by
  let F := optionFractionalSet x
  let U := unfinishedJobs job x
  have hmaps : (F : Set Option).MapsTo job U := by
    intro o ho
    exact Finset.mem_image.mpr ⟨o, ho, rfl⟩
  have hdecomp : F.card = ∑ j ∈ U, (F.filter fun o => job o = j).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  rw [hdecomp]
  calc
    2 * U.card = ∑ _j ∈ U, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ j ∈ U, (F.filter fun o => job o = j).card := by
      apply Finset.sum_le_sum
      intro j hj
      exact two_le_fractional_fiber_card job x hx hjob hj

/-- Summed over all fractional options, the remaining upward movement is
the number of fractional values minus the number of unfinished jobs. -/
theorem sum_one_sub_fractional_eq
    (job : Option → Job) (x : Option → ℝ)
    (hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1)
    (hjob : ∀ j, optionJobMass job x j = 1) :
    (∑ o ∈ optionFractionalSet x, (1 - x o)) =
      ((optionFractionalSet x).card : ℝ) - (unfinishedJobs job x).card := by
  let F := optionFractionalSet x
  let U := unfinishedJobs job x
  have hmaps : (F : Set Option).MapsTo job U := by
    intro o ho
    exact Finset.mem_image.mpr ⟨o, ho, rfl⟩
  have hsumx : ∑ o ∈ F, x o = (U.card : ℝ) := by
    calc
      ∑ o ∈ F, x o = ∑ j ∈ U, ∑ o ∈ F.filter (fun q => job q = j), x o := by
        symm
        exact Finset.sum_fiberwise_of_maps_to hmaps x
      _ = ∑ _j ∈ U, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact sum_fractional_fiber_eq_one job x hx hjob hj
      _ = (U.card : ℝ) := by simp
  calc
    (∑ o ∈ optionFractionalSet x, (1 - x o))
        = (F.card : ℝ) - ∑ o ∈ F, x o := by
          dsimp [F]
          rw [Finset.sum_sub_distrib]
          simp
    _ = (F.card : ℝ) - (U.card : ℝ) := by rw [hsumx]
    _ = ((optionFractionalSet x).card : ℝ) -
        (unfinishedJobs job x).card := by rfl

/-- The positive-support load minus the current fractional load is exactly
the sum of all remaining upward contributions. -/
theorem optionSupportLoad_sub_load
    (use : Option → Constraint → ℝ) (x : Option → ℝ)
    (hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1) (r : Constraint) :
    optionSupportLoad use x r - optionLoad use x r =
      ∑ o ∈ optionFractionalSet x, (1 - x o) * use o r := by
  rw [show optionSupportLoad use x r =
      ∑ o, if 0 < x o then use o r else 0 by
        simp [optionSupportLoad, optionPositiveSet, Finset.sum_filter]]
  rw [optionLoad, ← Finset.sum_sub_distrib]
  calc
    (∑ o, ((if 0 < x o then use o r else 0) - x o * use o r)) =
        ∑ o, if 0 < x o ∧ x o < 1 then (1 - x o) * use o r else 0 := by
          apply Finset.sum_congr rfl
          intro o _ho
          by_cases hpos : 0 < x o
          · by_cases hlt : x o < 1
            · simp [hpos, hlt]
              ring
            · have hxone : x o = 1 :=
                le_antisymm (hx o).2 (le_of_not_gt hlt)
              simp [hpos, hlt, hxone]
          · have hxzero : x o = 0 :=
              le_antisymm (le_of_not_gt hpos) (hx o).1
            simp [hpos, hxzero]
    _ = ∑ o ∈ optionFractionalSet x, (1 - x o) * use o r := by
          simp [optionFractionalSet, Finset.sum_filter]

/-- Every active capacity equation has remaining option-count potential
strictly larger than two. -/
theorem two_lt_potential_of_active
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (base : Constraint → ℝ) (tau : ℝ) (x : Option → ℝ)
    (htau : 0 < tau)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (huseTau : ∀ o r, use o r ≤ tau)
    (hstate : IsTwoConstraintRoundingState job use base tau x)
    {r : Constraint} (hr : r ∈ activeConstraints use base tau x) :
    2 < optionRemainingPotential use x r := by
  have hx := hstate.1
  have hload : optionLoad use x r = base r := hstate.2.2 r hr
  have hactive : base r + 2 * tau < optionSupportLoad use x r := by
    simpa [activeConstraints] using hr
  have hgap : 2 * tau <
      ∑ o ∈ optionFractionalSet x, (1 - x o) * use o r := by
    rw [← optionSupportLoad_sub_load use x hx r, hload]
    linarith
  have hupper :
      (∑ o ∈ optionFractionalSet x, (1 - x o) * use o r) ≤
        tau * optionRemainingPotential use x r := by
    rw [optionRemainingPotential, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro o ho
    have hofrac : 0 < x o ∧ x o < 1 := by
      simpa [optionFractionalSet] using ho
    by_cases hu : use o r = 0
    · simp [hu]
    · simp only [if_neg hu]
      have hone : 0 ≤ 1 - x o := sub_nonneg.mpr hofrac.2.le
      nlinarith [huseTau o r]
  have : 2 * tau < tau * optionRemainingPotential use x r :=
    hgap.trans_le hupper
  nlinarith

/-- Summing the remaining potentials over any set of constraints costs at
most two copies of the total fractional slack when each option touches at
most two constraints. -/
theorem sum_potential_le_two_mul_slack
    (use : Option → Constraint → ℝ) (x : Option → ℝ)
    (hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1)
    (hsparse : ∀ o,
      (Finset.univ.filter fun r => use o r ≠ 0).card ≤ 2)
    (A : Finset Constraint) :
    (∑ r ∈ A, optionRemainingPotential use x r) ≤
      2 * ∑ o ∈ optionFractionalSet x, (1 - x o) := by
  rw [show (∑ r ∈ A, optionRemainingPotential use x r) =
      ∑ o ∈ optionFractionalSet x,
        ∑ r ∈ A, (if use o r = 0 then 0 else 1 - x o) by
    simp only [optionRemainingPotential]
    rw [Finset.sum_comm]]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o ho
  have hofrac : 0 < x o ∧ x o < 1 := by
    simpa [optionFractionalSet] using ho
  have hinner : (∑ r ∈ A, (if use o r = 0 then 0 else 1 - x o)) =
      ((A.filter fun r => use o r ≠ 0).card : ℝ) * (1 - x o) := by
    rw [Finset.sum_ite]
    simp [mul_comm]
    ring
  rw [hinner]
  have hcard : (A.filter fun r => use o r ≠ 0).card ≤ 2 := by
    calc
      (A.filter fun r => use o r ≠ 0).card ≤
          (Finset.univ.filter fun r => use o r ≠ 0).card := by
            apply Finset.card_le_card
            intro r hr
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2⟩
      _ ≤ 2 := hsparse o
  have hcast : ((A.filter fun r => use o r ≠ 0).card : ℝ) ≤ 2 := by
    exact_mod_cast hcard
  nlinarith

/-- The number of unfinished job equations plus the number of active
capacity equations is strictly smaller than the number of fractional
variables.  This is the manuscript's decisive equation count. -/
theorem active_add_unfinished_lt_fractional
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (base : Constraint → ℝ) (tau : ℝ) (x : Option → ℝ)
    (htau : 0 < tau)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (huseTau : ∀ o r, use o r ≤ tau)
    (hsparse : ∀ o,
      (Finset.univ.filter fun r => use o r ≠ 0).card ≤ 2)
    (hF : (optionFractionalSet x).Nonempty)
    (hstate : IsTwoConstraintRoundingState job use base tau x) :
    (unfinishedJobs job x).card +
        (activeConstraints use base tau x).card <
      (optionFractionalSet x).card := by
  let F := optionFractionalSet x
  let U := unfinishedJobs job x
  let A := activeConstraints use base tau x
  by_cases hA : A.Nonempty
  · have hpot_each : ∀ r ∈ A, 2 < optionRemainingPotential use x r := by
      intro r hr
      exact two_lt_potential_of_active job use base tau x htau huse0 huseTau hstate hr
    have hsum_lower : (2 : ℝ) * A.card <
        ∑ r ∈ A, optionRemainingPotential use x r := by
      calc
        (2 : ℝ) * A.card = ∑ _r ∈ A, (2 : ℝ) := by simp [mul_comm]
        _ < ∑ r ∈ A, optionRemainingPotential use x r := by
          exact Finset.sum_lt_sum_of_nonempty hA hpot_each
    have hsum_upper : (∑ r ∈ A, optionRemainingPotential use x r) ≤
        2 * ∑ o ∈ F, (1 - x o) :=
      sum_potential_le_two_mul_slack use x hstate.1 hsparse A
    have hslack := sum_one_sub_fractional_eq job x hstate.1 hstate.2.1
    have hreal : (A.card : ℝ) < (F.card : ℝ) - (U.card : ℝ) := by
      have : (2 : ℝ) * A.card < 2 * ((F.card : ℝ) - (U.card : ℝ)) := by
        calc
          (2 : ℝ) * A.card < ∑ r ∈ A, optionRemainingPotential use x r := hsum_lower
          _ ≤ 2 * ∑ o ∈ F, (1 - x o) := hsum_upper
          _ = 2 * ((F.card : ℝ) - (U.card : ℝ)) := by
            simpa [F, U] using congrArg (fun z : ℝ => 2 * z) hslack
      linarith
    have hnat : A.card + U.card < F.card := by
      exact_mod_cast (by linarith : (A.card : ℝ) + U.card < F.card)
    simpa [F, U, A, Nat.add_comm] using hnat
  · have hAeq : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    have htwice : 2 * U.card ≤ F.card :=
      twice_unfinishedJobs_card_le_fractional_card job x hstate.1 hstate.2.1
    have hFpos : 0 < F.card := Finset.card_pos.mpr (by simpa [F] using hF)
    have hUF : U.card < F.card := by omega
    simpa [F, U, A, hAeq] using hUF

/-- If fractional values remain, there is a nonzero direction supported on
them that preserves every job equation and every currently active capacity
equation. -/
theorem exists_twoConstraint_rounding_direction
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (base : Constraint → ℝ) (tau : ℝ) (x : Option → ℝ)
    (htau : 0 < tau)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (huseTau : ∀ o r, use o r ≤ tau)
    (hsparse : ∀ o,
      (Finset.univ.filter fun r => use o r ≠ 0).card ≤ 2)
    (hF : (optionFractionalSet x).Nonempty)
    (hstate : IsTwoConstraintRoundingState job use base tau x) :
    ∃ z : Option → ℝ,
      z ≠ 0 ∧
      (∀ o, o ∉ optionFractionalSet x → z o = 0) ∧
      (∀ j, (∑ o, if job o = j then z o else 0) = 0) ∧
      ∀ r ∈ activeConstraints use base tau x,
        ∑ o, z o * use o r = 0 := by
  let F := optionFractionalSet x
  let U := unfinishedJobs job x
  let A := activeConstraints use base tau x
  have hcount : U.card + A.card < F.card := by
    simpa [F, U, A] using
      active_add_unfinished_lt_fractional job use base tau x htau huse0
        huseTau hsparse hF hstate
  let Row := Sum {j : Job // j ∈ U} {r : Constraint // r ∈ A}
  let Col := {o : Option // o ∈ F}
  let M : Matrix Row Col ℝ := fun row o =>
    match row with
    | Sum.inl j => if job o.1 = j.1 then 1 else 0
    | Sum.inr r => use o.1 r.1
  have hcard : Fintype.card Row < Fintype.card Col := by
    simpa [Row, Col, Fintype.card_sum, Fintype.card_coe] using hcount
  obtain ⟨zF, hzF, hrows⟩ := exists_nonzero_annihilated_vector hcard M
  let z : Option → ℝ := fun o => if ho : o ∈ F then zF ⟨o, ho⟩ else 0
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
        apply Finset.sum_subset (fun _ _ => Finset.mem_univ _)
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
      apply Finset.sum_subset (fun _ _ => Finset.mem_univ _)
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

/-- One linear-algebra step preserves the static invariant and strictly
reduces the number of fractional option values. -/
theorem exists_twoConstraint_state_step
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (base : Constraint → ℝ) (tau : ℝ) (x : Option → ℝ)
    (htau : 0 < tau)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (huseTau : ∀ o r, use o r ≤ tau)
    (hsparse : ∀ o,
      (Finset.univ.filter fun r => use o r ≠ 0).card ≤ 2)
    (hF : (optionFractionalSet x).Nonempty)
    (hstate : IsTwoConstraintRoundingState job use base tau x) :
    ∃ x' : Option → ℝ,
      IsTwoConstraintRoundingState job use base tau x' ∧
      optionFractionalSet x' ⊂ optionFractionalSet x ∧
      optionPositiveSet x' ⊆ optionPositiveSet x := by
  let F := optionFractionalSet x
  obtain ⟨z, hz, hzout, hzjob, hzactive⟩ :=
    exists_twoConstraint_rounding_direction job use base tau x htau huse0
      huseTau hsparse hF hstate
  let Col := {o : Option // o ∈ F}
  let xF : Col → ℝ := fun o => x o.1
  let zF : Col → ℝ := fun o => z o.1
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
  let x' : Option → ℝ := fun o => x o + t * z o
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
        have := (by simpa [F, optionFractionalSet] using ho : 0 < x o ∧ x o < 1)
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
      (fun o _ _ => huse0 o r)
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
  have hload_preserved : ∀ r ∈ activeConstraints use base tau x,
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
  have hactive' : ∀ r ∈ activeConstraints use base tau x',
      optionLoad use x' r = base r := by
    intro r hr'
    have hactive_val : base r + 2 * tau < optionSupportLoad use x' r := by
      simpa [activeConstraints] using hr'
    have hr : r ∈ activeConstraints use base tau x := by
      simp only [activeConstraints, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hactive_val.trans_le (hsupport_mono r)
    rw [hload_preserved r hr]
    exact hstate.2.2 r hr
  refine ⟨x', ⟨hbounds, hjob', hactive'⟩, ?_, hpositive_subset⟩
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

/-- Repeating the state step terminates at a zero-one vector. -/
theorem exists_integral_twoConstraint_state
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (base : Constraint → ℝ) (tau : ℝ) (x : Option → ℝ)
    (htau : 0 < tau)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (huseTau : ∀ o r, use o r ≤ tau)
    (hsparse : ∀ o,
      (Finset.univ.filter fun r => use o r ≠ 0).card ≤ 2)
    (hstate : IsTwoConstraintRoundingState job use base tau x) :
    ∃ y : Option → ℝ,
      IsTwoConstraintRoundingState job use base tau y ∧
      ∀ o, y o = 0 ∨ y o = 1 := by
  let P : ℕ → Prop := fun k =>
    ∀ x : Option → ℝ, (optionFractionalSet x).card = k →
      IsTwoConstraintRoundingState job use base tau x →
      ∃ y : Option → ℝ,
        IsTwoConstraintRoundingState job use base tau y ∧
        ∀ o, y o = 0 ∨ y o = 1
  have hP : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hxcard hstateX
      by_cases hF : (optionFractionalSet x).Nonempty
      · obtain ⟨x', hstate', hproper, _hpositive⟩ :=
          exists_twoConstraint_state_step job use base tau x htau huse0
            huseTau hsparse hF hstateX
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

/-- Support-preserving form of the terminating two-constraint rounding.
Coordinates which start at zero stay zero throughout the linear-algebra
iteration. -/
theorem exists_integral_twoConstraint_state_support
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (base : Constraint → ℝ) (tau : ℝ) (x : Option → ℝ)
    (htau : 0 < tau)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (huseTau : ∀ o r, use o r ≤ tau)
    (hsparse : ∀ o,
      (Finset.univ.filter fun r => use o r ≠ 0).card ≤ 2)
    (hstate : IsTwoConstraintRoundingState job use base tau x) :
    ∃ y : Option → ℝ,
      IsTwoConstraintRoundingState job use base tau y ∧
      (∀ o, y o = 0 ∨ y o = 1) ∧
      optionPositiveSet y ⊆ optionPositiveSet x := by
  let P : ℕ → Prop := fun k =>
    ∀ x : Option → ℝ, (optionFractionalSet x).card = k →
      IsTwoConstraintRoundingState job use base tau x →
      ∃ y : Option → ℝ,
        IsTwoConstraintRoundingState job use base tau y ∧
        (∀ o, y o = 0 ∨ y o = 1) ∧
        optionPositiveSet y ⊆ optionPositiveSet x
  have hP : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hxcard hstateX
      by_cases hF : (optionFractionalSet x).Nonempty
      · obtain ⟨x', hstate', hproper, hpositive⟩ :=
          exists_twoConstraint_state_step job use base tau x htau huse0
            huseTau hsparse hF hstateX
        have hcardlt : (optionFractionalSet x').card < k := by
          rw [← hxcard]
          exact Finset.card_lt_card hproper
        obtain ⟨y, hstateY, hy01, hypos⟩ :=
          ih _ hcardlt x' rfl hstate'
        exact ⟨y, hstateY, hy01, hypos.trans hpositive⟩
      · refine ⟨x, hstateX, ?_, fun _ ho ↦ ho⟩
        intro o
        by_contra hnot
        have hne : x o ≠ 0 ∧ x o ≠ 1 := not_or.mp hnot
        have hpos : 0 < x o :=
          lt_of_le_of_ne (hstateX.1 o).1 (Ne.symm hne.1)
        have hlt : x o < 1 :=
          lt_of_le_of_ne (hstateX.1 o).2 hne.2
        exact hF ⟨o, by simp [optionFractionalSet, hpos, hlt]⟩
  exact hP (optionFractionalSet x).card x rfl hstate

/-- Indicator rounding with the additional guarantee that every selected
coordinate had positive input mass. -/
theorem choose_one_option_per_job_indicators_support
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (tau : ℝ) (x : Option → ℝ)
    (htau : 0 < tau)
    (hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1)
    (hjob : ∀ j, optionJobMass job x j = 1)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (huseTau : ∀ o r, use o r ≤ tau)
    (hsparse : ∀ o,
      (Finset.univ.filter fun r => use o r ≠ 0).card ≤ 2) :
    ∃ y : Option → ℝ,
      (∀ o, y o = 0 ∨ y o = 1) ∧
      (∀ j, optionJobMass job y j = 1) ∧
      (∀ o, y o = 1 → 0 < x o) ∧
      ∀ r, optionLoad use y r ≤ optionLoad use x r + 2 * tau := by
  let base : Constraint → ℝ := optionLoad use x
  have hinitial : IsTwoConstraintRoundingState job use base tau x := by
    exact initial_isTwoConstraintRoundingState job use tau x hx hjob
  obtain ⟨y, hstate, hy01, hsupport⟩ :=
    exists_integral_twoConstraint_state_support job use base tau x htau
      huse0 huseTau hsparse hinitial
  have hselected : ∀ o, y o = 1 → 0 < x o := by
    intro o hone
    have hoy : o ∈ optionPositiveSet y := by
      simp [optionPositiveSet, hone]
    have hox := hsupport hoy
    simpa [optionPositiveSet] using hox
  refine ⟨y, hy01, hstate.2.1, hselected, ?_⟩
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
  by_cases hle : optionSupportLoad use y r ≤ base r + 2 * tau
  · simpa [base, heqSupport] using hle
  · have hr : r ∈ activeConstraints use base tau y := by
      simp only [activeConstraints, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_not_ge hle
    have hload := hstate.2.2 r hr
    rw [hload]
    dsimp [base]
    linarith

/-- Full two-constraint rounding in zero-one indicator form.  Each job has
exactly one selected option (its selected indicators sum to one), and every
capacity load exceeds its fractional expectation by at most `2 * tau`. -/
theorem choose_one_option_per_job_indicators
    (job : Option → Job) (use : Option → Constraint → ℝ)
    (tau : ℝ) (x : Option → ℝ)
    (htau : 0 < tau)
    (hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1)
    (hjob : ∀ j, optionJobMass job x j = 1)
    (huse0 : ∀ o r, 0 ≤ use o r)
    (huseTau : ∀ o r, use o r ≤ tau)
    (hsparse : ∀ o,
      (Finset.univ.filter fun r => use o r ≠ 0).card ≤ 2) :
    ∃ y : Option → ℝ,
      (∀ o, y o = 0 ∨ y o = 1) ∧
      (∀ j, optionJobMass job y j = 1) ∧
      ∀ r, optionLoad use y r ≤ optionLoad use x r + 2 * tau := by
  let base : Constraint → ℝ := optionLoad use x
  have hinitial : IsTwoConstraintRoundingState job use base tau x := by
    exact initial_isTwoConstraintRoundingState job use tau x hx hjob
  obtain ⟨y, hstate, hy01⟩ :=
    exists_integral_twoConstraint_state job use base tau x htau huse0
      huseTau hsparse hinitial
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
  by_cases hle : optionSupportLoad use y r ≤ base r + 2 * tau
  · simpa [base, heqSupport] using hle
  · have hr : r ∈ activeConstraints use base tau y := by
      simp only [activeConstraints, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_not_ge hle
    have hload := hstate.2.2 r hr
    rw [hload]
    dsimp [base]
    linarith

end TwoSparseSystem

end WeightedEdgeColoring
