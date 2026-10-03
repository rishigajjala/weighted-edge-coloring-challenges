import WeightedEdgeColoring.RankThreeResidualFixedRateParameters
import WeightedEdgeColoring.RankThreeResidualInvariantStep

/-!
# Natural budgets for the fixed-rate active-slot round

This file rounds the real fixed-rate parameters to natural budgets.  The
floor is used for guaranteed slot shrink and the ceiling for the protected
job loss.  All one-unit rounding losses are stated explicitly.
-/

namespace WeightedEdgeColoring

/-- Natural lower-deletion budget at every active slot. -/
noncomputable def fixedRateSlotBudget (lambda S : ℕ) : ℕ :=
  ⌊fixedRateKappa * (S : ℝ) / (20 * (lambda : ℝ))⌋₊

/-- Natural upper-deletion budget at every surviving job. -/
noncomputable def fixedRateJobBudget (lambda S : ℕ) : ℕ :=
  ⌈8 * fixedRateKappa * (S : ℝ) / (lambda : ℝ)⌉₊

/-- Slots below this threshold are already at most half the current cap. -/
def fixedRateSlotThreshold (S : ℕ) : ℕ := (S + 1) / 2

/-- The slot cap after charging half of the guaranteed deletion budget. -/
noncomputable def fixedRateNextSlotBound (lambda S : ℕ) : ℕ :=
  S - fixedRateSlotBudget lambda S / 2

theorem fixedRateSlotBudget_nonneg_real (lambda S : ℕ) :
    0 ≤ fixedRateKappa * (S : ℝ) / (20 * (lambda : ℝ)) := by
  exact div_nonneg
    (mul_nonneg fixedRateKappa_nonneg (Nat.cast_nonneg S))
    (mul_nonneg (by norm_num) (Nat.cast_nonneg lambda))

theorem fixedRateJobBudget_nonneg_real (lambda S : ℕ) :
    0 ≤ 8 * fixedRateKappa * (S : ℝ) / (lambda : ℝ) := by
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) fixedRateKappa_nonneg)
      (Nat.cast_nonneg S))
    (Nat.cast_nonneg lambda)

/-- A floor never exceeds its real argument. -/
theorem fixedRateSlotBudget_cast_le (lambda S : ℕ) :
    (fixedRateSlotBudget lambda S : ℝ) ≤
      fixedRateKappa * (S : ℝ) / (20 * (lambda : ℝ)) := by
  exact Nat.floor_le (fixedRateSlotBudget_nonneg_real lambda S)

/-- The floor loses less than one. -/
theorem fixedRateSlotBudget_lt_cast_add_one (lambda S : ℕ) :
    fixedRateKappa * (S : ℝ) / (20 * (lambda : ℝ)) <
      (fixedRateSlotBudget lambda S : ℝ) + 1 := by
  exact Nat.lt_floor_add_one _

/-- A ceiling is at least its real argument. -/
theorem fixedRateJobBudget_cast_ge (lambda S : ℕ) :
    8 * fixedRateKappa * (S : ℝ) / (lambda : ℝ) ≤
      (fixedRateJobBudget lambda S : ℝ) := by
  exact Nat.le_ceil _

/-- The ceiling adds less than one. -/
theorem fixedRateJobBudget_cast_lt_add_one (lambda S : ℕ) :
    (fixedRateJobBudget lambda S : ℝ) <
      8 * fixedRateKappa * (S : ℝ) / (lambda : ℝ) + 1 := by
  exact Nat.ceil_lt_add_one (fixedRateJobBudget_nonneg_real lambda S)

/-- Additive-minus-one lower estimate for the floor budget. -/
theorem fixedRateSlotBudget_cast_gt_sub_one (lambda S : ℕ) :
    fixedRateKappa * (S : ℝ) / (20 * (lambda : ℝ)) - 1 <
      (fixedRateSlotBudget lambda S : ℝ) := by
  have h := fixedRateSlotBudget_lt_cast_add_one lambda S
  linarith

/-- Half of the natural slot budget loses less than one half from the ideal
real shrink. -/
theorem fixedRate_halfSlotBudget_cast_gt_sub_half (lambda S : ℕ) :
    (fixedRateKappa * (S : ℝ) / (20 * (lambda : ℝ))) / 2 - 1 / 2 <
      (fixedRateSlotBudget lambda S : ℝ) / 2 := by
  have h := fixedRateSlotBudget_lt_cast_add_one lambda S
  linarith

/-- After the natural division by two, the guaranteed slot shrink loses less
than one from half of the ideal real budget. -/
theorem fixedRateSlotBudget_div_two_cast_gt_sub_one (lambda S : ℕ) :
    (fixedRateKappa * (S : ℝ) / (20 * (lambda : ℝ))) / 2 - 1 <
      (fixedRateSlotBudget lambda S / 2 : ℕ) := by
  have hfloor := fixedRateSlotBudget_lt_cast_add_one lambda S
  have hdivNat : fixedRateSlotBudget lambda S ≤
      2 * (fixedRateSlotBudget lambda S / 2) + 1 := by omega
  have hdiv : (fixedRateSlotBudget lambda S : ℝ) ≤
      2 * ((fixedRateSlotBudget lambda S / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hdivNat
  linarith

/-- Non-strict one-unit upper estimate for the ceiling budget. -/
theorem fixedRateJobBudget_cast_le_add_one (lambda S : ℕ) :
    (fixedRateJobBudget lambda S : ℝ) ≤
      8 * fixedRateKappa * (S : ℝ) / (lambda : ℝ) + 1 :=
  (fixedRateJobBudget_cast_lt_add_one lambda S).le

/-- The slot budget is at most the current slot cap. -/
theorem fixedRateSlotBudget_le_slotBound
    (lambda S : ℕ) (hlambda : 0 < lambda) :
    fixedRateSlotBudget lambda S ≤ S := by
  have hcast := fixedRateSlotBudget_cast_le lambda S
  have hlambdaR : (0 : ℝ) < (lambda : ℝ) := by positivity
  have hk : fixedRateKappa ≤ 20 * (lambda : ℝ) := by
    have : (1 : ℝ) ≤ (lambda : ℝ) := by exact_mod_cast hlambda
    norm_num [fixedRateKappa]
    linarith
  have hx : fixedRateKappa * (S : ℝ) / (20 * (lambda : ℝ)) ≤ S := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 20 * (lambda : ℝ))]
    calc
      fixedRateKappa * (S : ℝ) ≤
          (20 * (lambda : ℝ)) * (S : ℝ) :=
        mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg S)
      _ = (S : ℝ) * (20 * (lambda : ℝ)) := by ring
  exact_mod_cast hcast.trans hx

/-- The chosen half threshold satisfies the inactive-slot premise of
`residualSlotDegree_le_of_active_shrink`. -/
theorem fixedRateSlotThreshold_le_next_add_one
    (lambda S : ℕ) (hlambda : 0 < lambda) :
    fixedRateSlotThreshold S ≤ fixedRateNextSlotBound lambda S + 1 := by
  have hb := fixedRateSlotBudget_le_slotBound lambda S hlambda
  simp only [fixedRateSlotThreshold, fixedRateNextSlotBound]
  omega

/-- The next cap and the floor budget satisfy the active-slot shrink
arithmetic premise exactly. -/
theorem fixedRate_two_mul_slotBound_le_next_add_budget
    (lambda S : ℕ) (hlambda : 0 < lambda) :
    2 * S ≤ 2 * fixedRateNextSlotBound lambda S +
      fixedRateSlotBudget lambda S := by
  have hb := fixedRateSlotBudget_le_slotBound lambda S hlambda
  simp only [fixedRateNextSlotBound]
  omega

theorem fixedRateNextSlotBound_le (lambda S : ℕ) :
    fixedRateNextSlotBound lambda S ≤ S := by
  simp [fixedRateNextSlotBound]

/-- Real recurrence estimate for the next slot cap, including the single
unit lost by the two nested floors. -/
theorem fixedRateNextSlotBound_cast_lt
    (lambda S : ℕ) (hlambda : 0 < lambda) :
    (fixedRateNextSlotBound lambda S : ℝ) <
      (S : ℝ) -
        (fixedRateKappa * (S : ℝ) / (20 * (lambda : ℝ))) / 2 + 1 := by
  have hb := fixedRateSlotBudget_le_slotBound lambda S hlambda
  have hq : fixedRateSlotBudget lambda S / 2 ≤ S :=
    (Nat.div_le_self _ _).trans hb
  have hshrink := fixedRateSlotBudget_div_two_cast_gt_sub_one lambda S
  rw [fixedRateNextSlotBound, Nat.cast_sub hq]
  linarith

/-- The lower natural budget is admissible for the half-mean lower tail. -/
theorem fixedRate_lowerSlotBudget_threshold
    (lambda J S kMin m dJob : ℕ) (hlambda : 0 < lambda) (hJ : 0 < J)
    (hgroupSize : S ≤ 10 * lambda * kMin)
    (hjobHalf : J ≤ 2 * dJob) (hcodegree : 6 * lambda ≤ J)
    (hsupport : kMin * dJob ≤ m) :
    ((fixedRateSlotBudget lambda S : ℕ) : ℝ) /
        (3 * lambda : ℕ) ≤
      RankThreeOptionSystem.activeSlotUniformLowerMean
        (fixedRateRho lambda J) m dJob (fixedRateSlotThreshold S) lambda / 2 := by
  have hslotHalf : S ≤ 2 * fixedRateSlotThreshold S := by
    simp only [fixedRateSlotThreshold]
    omega
  have hmean := fixedRate_lower_floor_le_activeSlotMean
    lambda J S kMin m dJob (fixedRateSlotThreshold S)
    hlambda hJ hgroupSize hjobHalf hslotHalf hcodegree hsupport
  have hbudget := fixedRateSlotBudget_cast_le lambda S
  have hlambdaR : (0 : ℝ) < (lambda : ℝ) := by positivity
  have hmain : (fixedRateSlotBudget lambda S : ℝ) /
      (3 * (lambda : ℝ)) ≤
      RankThreeOptionSystem.activeSlotUniformLowerMean
        (fixedRateRho lambda J) m dJob (fixedRateSlotThreshold S) lambda / 2 := by
    calc
      (fixedRateSlotBudget lambda S : ℝ) / (3 * (lambda : ℝ)) ≤
        (fixedRateKappa * (S : ℝ) / (20 * (lambda : ℝ))) /
          (3 * (lambda : ℝ)) :=
        div_le_div_of_nonneg_right hbudget
          (by positivity : (0 : ℝ) ≤ 3 * (lambda : ℝ))
      _ ≤ (fixedRateKappa * fixedRateScale lambda S / 20) / 2 := by
        simp only [fixedRateScale]
        field_simp
        have hks : 0 ≤ fixedRateKappa * (S : ℝ) :=
          mul_nonneg fixedRateKappa_nonneg (Nat.cast_nonneg S)
        nlinarith
      _ ≤ RankThreeOptionSystem.activeSlotUniformLowerMean
            (fixedRateRho lambda J) m dJob (fixedRateSlotThreshold S) lambda / 2 :=
        div_le_div_of_nonneg_right hmean (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmain

/-- The upper natural job budget is large enough for the lambda-one upper
tail used by the active-slot theorem. -/
theorem fixedRate_upperJobBudget_threshold
    (lambda J S : ℕ) (hlambda : 0 < lambda) (hJ : 0 < J) :
    4 * (fixedRateRho lambda J *
        ((J : ℝ) * (S : ℝ) / (lambda : ℝ))) ≤
      ((fixedRateJobBudget lambda S : ℕ) : ℝ) / (2 * lambda : ℕ) := by
  rw [fixedRate_muUpper_eq lambda J S hlambda hJ]
  have hbudget := fixedRateJobBudget_cast_ge lambda S
  have hlambdaR : (0 : ℝ) < (lambda : ℝ) := by positivity
  have hmain : 4 * (fixedRateKappa * fixedRateScale lambda S) ≤
      (fixedRateJobBudget lambda S : ℝ) / (2 * (lambda : ℝ)) := by
    apply le_trans ?_ (div_le_div_of_nonneg_right hbudget
      (by positivity : (0 : ℝ) ≤ 2 * (lambda : ℝ)))
    simp only [fixedRateScale]
    field_simp
    have heq : 4 * fixedRateKappa * (S : ℝ) * 2 =
        fixedRateKappa * (S : ℝ) * 8 := by ring
    exact heq.le
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmain

namespace RankThreeOptionSystem

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

/-- One fixed-rate active-slot round with all scalar parameters and natural
budgets instantiated.  Only structural graph hypotheses, block bounds, and
the single asymptotic scale inequality remain. -/
theorem exists_oneRound_activeSlot_fixedRate
    (members : Group → Finset Job)
    (lambda J S dJob R Kmax kMin m : ℕ)
    (hlambda : 0 < lambda) (hJ : 0 < J)
    (hSJ : S ≤ J) (hRJ : R ≤ J) (hKmaxS : Kmax ≤ S)
    (hgroupSize : S ≤ 10 * lambda * kMin)
    (hjobHalf : J ≤ 2 * dJob) (hcodegreeScale : 6 * lambda ≤ J)
    (hsupportArithmetic : kMin * dJob ≤ m)
    (hjobDegreeLower : ∀ o, dJob ≤ (H.fiber (H.owner o)).card)
    (hjobDegreeUpper : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegreeUpper : ∀ s, H.slotDegree s ≤ S)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hmembers : ∀ g, (members g).card ≤ Kmax)
    (hgroupSupportLower : ∀ g,
      m ≤ (linearRowSupport
        (H.jobGroupCoverageWeight members) g).card)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (hscale : Real.exp
      (-(fixedRateKappa * fixedRateScale lambda S / 320)) ≤
        fixedRateLLLWeight lambda J) :
    ∃ A : Finset Option,
      H.IsPartialMatching A ∧
      (∀ g,
        RankThreeOptionSystem.activeSlotUniformLowerMean
            (fixedRateRho lambda J) m dJob
              (fixedRateSlotThreshold S) lambda / 2 <
          (H.coveredGroupJobs members g A).card) ∧
      (∀ s, H.residualSlotDegree A s ≤
        fixedRateNextSlotBound lambda S) ∧
      (∀ j, ¬ H.Covers A j →
        H.residualJobDegree ∅ j ≤ H.residualJobDegree A j +
          fixedRateJobBudget lambda S) := by
  have hnumeric := fixedRate_activeSlot_numeric_package
    lambda J S R Kmax kMin m dJob (fixedRateSlotThreshold S)
    hlambda hJ hSJ hRJ hKmaxS hgroupSize hjobHalf
    (by simp [fixedRateSlotThreshold]; omega)
    hcodegreeScale hsupportArithmetic hscale
  rcases hnumeric with ⟨hpairNumeric, hlowerNumeric, hupperNumeric⟩
  have hrho0 := fixedRateRho_nonneg lambda J
  have hrho1 : fixedRateRho lambda J ≤ 1 :=
    (fixedRateRho_le_half lambda J hlambda hJ).trans (by norm_num)
  have hweight0 := fixedRateLLLWeight_nonneg lambda J
  have hweightHalf := fixedRateLLLWeight_le_half lambda J hlambda hJ
  have hlowerThreshold : ∀ s : H.ActiveSlot (fixedRateSlotThreshold S),
      (fixedRateSlotBudget lambda S : ℝ) / (3 * lambda : ℕ) ≤
        RankThreeOptionSystem.activeSlotUniformLowerMean
          (fixedRateRho lambda J) m dJob
            (fixedRateSlotThreshold S) lambda / 2 := by
    intro _s
    exact fixedRate_lowerSlotBudget_threshold
      lambda J S kMin m dJob hlambda hJ hgroupSize hjobHalf
      hcodegreeScale hsupportArithmetic
  have hupperThreshold : ∀ _j : Job,
      4 * (fixedRateRho lambda J *
        ((J : ℝ) * (S : ℝ) / (lambda : ℝ))) ≤
          (fixedRateJobBudget lambda S : ℝ) / (2 * lambda : ℕ) := by
    intro _j
    exact fixedRate_upperJobBudget_threshold lambda J S hlambda hJ
  rcases H.exists_oneRound_activeSlot_uniform_exponential
      (fixedRateRho lambda J) members lambda hlambda
      (fun _ ↦ fixedRateSlotBudget lambda S)
      (fun _ ↦ fixedRateJobBudget lambda S)
      J S dJob (fixedRateSlotThreshold S) R Kmax m
      (fixedRateLLLWeight lambda J) (fixedRateLLLWeight lambda J)
      (fixedRateLLLWeight lambda J)
      hrho0 hrho1 hjobDegreeLower hjobDegreeUpper hslotDegreeUpper
      hjobSlot hslotPair hmembers hgroupSupportLower hgroupIncidence
      hweight0 hweight0 le_rfl le_rfl hweightHalf
      hlowerThreshold hupperThreshold hpairNumeric hlowerNumeric hupperNumeric with
    ⟨A, hA, hgroup, hslotShrink, hjob⟩
  have hslotNext : ∀ s, H.residualSlotDegree A s ≤
      fixedRateNextSlotBound lambda S :=
    H.residualSlotDegree_le_of_active_shrink A
      (fixedRateSlotThreshold S) (fixedRateSlotBudget lambda S)
      S (fixedRateNextSlotBound lambda S) hslotDegreeUpper
      (fixedRateSlotThreshold_le_next_add_one lambda S hlambda)
      (fixedRate_two_mul_slotBound_le_next_add_budget lambda S hlambda)
      hslotShrink
  exact ⟨A, hA, hgroup, hslotNext, hjob⟩

end RankThreeOptionSystem

end WeightedEdgeColoring
