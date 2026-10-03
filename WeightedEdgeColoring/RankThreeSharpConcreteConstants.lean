import WeightedEdgeColoring.RankThreeSharpFixedSlackNumeric
import WeightedEdgeColoring.RankThreeFixedSlackGapPreservation

/-!
# One concrete fixed-slack parameter choice

The sharp rank-three round is easiest to iterate with fixed small constants.
This file makes one such choice once and proves all elementary inequalities
which do not involve the current degree, the codegree, or an exponential
tail.  Later files may therefore concentrate only on the genuinely
asymptotic estimates.
-/

namespace WeightedEdgeColoring

/-- Proposal numerator in every sharp round. -/
noncomputable def sharpConcreteA : ℝ := 1 / 10000

/-- The maintained slot/job gap. -/
noncomputable def sharpConcreteGamma : ℝ := 1 / 4

/-- Each of the three error budgets receives the same small allowance. -/
noncomputable def sharpConcreteEta : ℝ := sharpConcreteA / 64

/-- A fixed half-mean loss in every endpoint block. -/
noncomputable def sharpConcreteDelta : ℝ := 1 / 2

/-- Robust proposal numerator.  Dividing this small absolute constant by
the codegree pays the cubic Harris cost in the lower slot rows. -/
noncomputable def sharpScaledAlpha : ℝ := 1 / 10000000000

noncomputable def sharpScaledA (lambda : ℕ) : ℝ :=
  sharpScaledAlpha / (lambda : ℝ)

noncomputable def sharpScaledEta (lambda : ℕ) : ℝ := sharpScaledA lambda / 64

theorem sharpScaled_constants (lambda : ℕ) (hlambda : 0 < lambda) :
    0 < sharpScaledA lambda ∧
      0 < sharpScaledEta lambda ∧
      (1 - sharpConcreteGamma) * sharpScaledEta lambda +
          sharpScaledEta lambda + sharpScaledEta lambda ≤
        sharpScaledA lambda * sharpConcreteGamma *
          (1 - sharpConcreteGamma) ∧
      0 < fixedSlackJobRetention (sharpScaledA lambda)
          sharpConcreteGamma - sharpScaledEta lambda ∧
      0 < fixedSlackSlotRetention (sharpScaledA lambda)
          sharpConcreteGamma * (1 - sharpConcreteGamma) +
        sharpScaledEta lambda + sharpScaledEta lambda ∧
      18 * sharpScaledA lambda ^ 2 ≤ sharpScaledEta lambda := by
  have hlambdaR : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
  have haPos : 0 < sharpScaledA lambda := by
    unfold sharpScaledA sharpScaledAlpha
    positivity
  have haSmall : sharpScaledA lambda ≤ 1 / 10000000000 := by
    unfold sharpScaledA sharpScaledAlpha
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < lambda)).2 (by
      nlinarith)
  refine ⟨haPos, div_pos haPos (by norm_num), ?_, ?_, ?_, ?_⟩
  · dsimp [sharpScaledEta, sharpConcreteGamma]
    nlinarith [haPos.le]
  · unfold fixedSlackJobRetention
    norm_num [sharpScaledEta, sharpConcreteGamma]
    nlinarith
  · unfold fixedSlackSlotRetention
    norm_num [sharpScaledEta, sharpConcreteGamma]
    nlinarith
  · unfold sharpScaledEta
    have : 18 * sharpScaledA lambda ≤ 1 / 64 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this haPos.le]

theorem sharpScaled_rho_bounds (lambda d : ℕ)
    (hlambda : 0 < lambda) (hd : 0 < d) :
    0 ≤ sharpScaledA lambda / (d : ℝ) ∧
      sharpScaledA lambda / (d : ℝ) ≤ 1 ∧
      SharpFixedSlackNumeric.increasingCap
        (sharpScaledA lambda / (d : ℝ)) ≤ 1 / 2 := by
  have ha := sharpScaled_constants lambda hlambda
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdPos : (0 : ℝ) < d := by exact_mod_cast hd
  have ha1 : sharpScaledA lambda ≤ 1 := by
    have hlambdaR : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
    unfold sharpScaledA sharpScaledAlpha
    have hlambdaPos : (0 : ℝ) < lambda := by positivity
    apply (div_le_iff₀ hlambdaPos).2
    nlinarith
  have hrhoA : sharpScaledA lambda / (d : ℝ) ≤ sharpScaledA lambda := by
    exact (div_le_iff₀ hdPos).2 (by nlinarith)
  have hrho0 : 0 ≤ sharpScaledA lambda / (d : ℝ) :=
    div_nonneg ha.1.le hdPos.le
  refine ⟨hrho0, hrhoA.trans ha1, ?_⟩
  apply SharpFixedSlackNumeric.increasingCap_le_half
  have hsq : (sharpScaledA lambda / (d : ℝ)) ^ 2 ≤
      sharpScaledA lambda ^ 2 := by nlinarith
  calc
    (sharpScaledA lambda / (d : ℝ)) ^ 2 ≤
        sharpScaledA lambda ^ 2 := hsq
    _ ≤ 1 / 8 := by
      have hlambdaR : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
      have hden : (1 : ℝ) ≤ (lambda : ℝ) ^ 2 := by nlinarith
      calc
        sharpScaledA lambda ^ 2 =
            sharpScaledAlpha ^ 2 / (lambda : ℝ) ^ 2 := by
          rw [sharpScaledA, div_pow]
        _ ≤ sharpScaledAlpha ^ 2 :=
          div_le_self (sq_nonneg sharpScaledAlpha) hden
        _ ≤ 1 / 8 := by norm_num [sharpScaledAlpha]

theorem sharpScaled_collisionThreshold_pos (lambda d : ℕ)
    (hlambda : 0 < lambda) (hd : 0 < d) :
    0 < 2 * sharpScaledEta lambda * d := by
  have heta := (sharpScaled_constants lambda hlambda).2.1
  positivity

theorem sharpConcrete_constants :
    0 < sharpConcreteA ∧
      0 < sharpConcreteGamma ∧ sharpConcreteGamma ≤ 1 / 2 ∧
      0 < sharpConcreteEta ∧
      0 ≤ sharpConcreteDelta ∧ sharpConcreteDelta ≤ 1 ∧
      (1 - sharpConcreteGamma) * sharpConcreteEta +
          sharpConcreteEta + sharpConcreteEta ≤
        sharpConcreteA * sharpConcreteGamma * (1 - sharpConcreteGamma) ∧
      sharpConcreteA / 8 ≤
        sharpConcreteA * sharpConcreteGamma * (1 - sharpConcreteGamma) -
          ((1 - sharpConcreteGamma) * sharpConcreteEta +
            sharpConcreteEta + sharpConcreteEta) ∧
      0 < fixedSlackJobRetention sharpConcreteA sharpConcreteGamma -
        sharpConcreteEta ∧
      0 < fixedSlackSlotRetention sharpConcreteA sharpConcreteGamma *
          (1 - sharpConcreteGamma) + sharpConcreteEta + sharpConcreteEta ∧
      18 * sharpConcreteA ^ 2 ≤ sharpConcreteEta ∧
      (1 - sharpConcreteDelta) * sharpConcreteA / 8 ≤ 1 := by
  norm_num [sharpConcreteA, sharpConcreteGamma, sharpConcreteEta,
    sharpConcreteDelta, fixedSlackJobRetention, fixedSlackSlotRetention]

theorem sharpConcrete_error_fits :
    (1 - sharpConcreteGamma) * sharpConcreteEta +
          sharpConcreteEta + sharpConcreteEta ≤
      sharpConcreteA * sharpConcreteGamma * (1 - sharpConcreteGamma) :=
  sharpConcrete_constants.2.2.2.2.2.2.1

theorem sharpConcrete_jobRate_pos :
    0 < fixedSlackJobRetention sharpConcreteA sharpConcreteGamma -
      sharpConcreteEta :=
  sharpConcrete_constants.2.2.2.2.2.2.2.2.1

theorem sharpConcrete_slotRate_pos :
    0 < fixedSlackSlotRetention sharpConcreteA sharpConcreteGamma *
        (1 - sharpConcreteGamma) + sharpConcreteEta + sharpConcreteEta :=
  sharpConcrete_constants.2.2.2.2.2.2.2.2.2.1

theorem sharpConcrete_collision_mean_fits :
    18 * sharpConcreteA ^ 2 ≤ sharpConcreteEta :=
  sharpConcrete_constants.2.2.2.2.2.2.2.2.2.2.1

theorem sharpConcrete_rho_bounds (d : ℕ) (hd : 0 < d) :
    0 ≤ sharpConcreteA / (d : ℝ) ∧
      sharpConcreteA / (d : ℝ) ≤ 1 ∧
      SharpFixedSlackNumeric.increasingCap
          (sharpConcreteA / (d : ℝ)) ≤ 1 / 2 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ha0 : 0 ≤ sharpConcreteA := sharpConcrete_constants.1.le
  have ha1 : sharpConcreteA ≤ 1 := by
    norm_num [sharpConcreteA]
  have hrho0 : 0 ≤ sharpConcreteA / (d : ℝ) := by positivity
  have hrhoA : sharpConcreteA / (d : ℝ) ≤ sharpConcreteA := by
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < d)).2
      (by nlinarith)
  have hrho1 : sharpConcreteA / (d : ℝ) ≤ 1 := hrhoA.trans ha1
  refine ⟨hrho0, hrho1, ?_⟩
  apply SharpFixedSlackNumeric.increasingCap_le_half
  have hprod : 0 ≤
      (sharpConcreteA - sharpConcreteA / (d : ℝ)) *
        (sharpConcreteA + sharpConcreteA / (d : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hrhoA) (add_nonneg ha0 hrho0)
  have hsq : (sharpConcreteA / (d : ℝ)) ^ 2 ≤ sharpConcreteA ^ 2 := by
    nlinarith
  calc
    (sharpConcreteA / (d : ℝ)) ^ 2 ≤ sharpConcreteA ^ 2 := hsq
    _ ≤ 1 / 8 := by norm_num [sharpConcreteA]

theorem sharpConcrete_nextScale_pos (d : ℕ) (hd : 0 < d) :
    0 <
      (fixedSlackJobRetention sharpConcreteA sharpConcreteGamma -
        sharpConcreteEta) * d := by
  exact mul_pos sharpConcrete_jobRate_pos (by exact_mod_cast hd)

theorem sharpConcrete_collisionThreshold_pos (d : ℕ) (hd : 0 < d) :
    0 < 2 * sharpConcreteEta * d := by
  have heta : 0 < sharpConcreteEta :=
    sharpConcrete_constants.2.2.2.1
  positivity

theorem sharpConcrete_same_gap :
    fixedSlackSlotRetention sharpConcreteA sharpConcreteGamma *
          (1 - sharpConcreteGamma) +
        sharpConcreteEta + sharpConcreteEta ≤
      (1 - sharpConcreteGamma) *
        (fixedSlackJobRetention sharpConcreteA sharpConcreteGamma -
          sharpConcreteEta) := by
  have herr :
      (1 - sharpConcreteGamma) * sharpConcreteEta +
          (sharpConcreteEta + sharpConcreteEta) ≤
        sharpConcreteA * sharpConcreteGamma *
          (1 - sharpConcreteGamma) := by
    simpa [add_assoc] using sharpConcrete_error_fits
  have h := fixedSlack_preserves_same_gap_of_separate_errors
    sharpConcreteA sharpConcreteGamma sharpConcreteEta
      (sharpConcreteEta + sharpConcreteEta) herr
  simpa [add_assoc] using h

/-- A fixed number of sharp rounds, depending only on the requested error,
makes the geometric active-star term arbitrarily small. -/
theorem exists_sharpConcrete_steps (eta : ℝ) (heta : 0 < eta) :
    ∃ steps : ℕ,
      (1 - (1 - sharpConcreteDelta) * sharpConcreteA / 8) ^ steps ≤ eta := by
  let r : ℝ := 1 - (1 - sharpConcreteDelta) * sharpConcreteA / 8
  have hr0 : 0 < r := by
    norm_num [r, sharpConcreteA, sharpConcreteDelta]
  have hr1 : r < 1 := by
    norm_num [r, sharpConcreteA, sharpConcreteDelta]
  obtain ⟨steps, hsteps⟩ := exists_pow_lt_of_lt_one heta hr1
  exact ⟨steps, hsteps.le⟩

end WeightedEdgeColoring
