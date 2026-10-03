import WeightedEdgeColoring.RankThreeResidualParameterRegime
import WeightedEdgeColoring.RankThreeResidualActiveSlotUniform

/-!
# A fixed-rate parameter package for the active-slot round

This file discharges the three scalar local-lemma inequalities in the exact
form used by the separate job/slot-scale active-slot theorem.  It is purely
numeric and can therefore be reused at every step of a finite iteration.
-/

namespace WeightedEdgeColoring

noncomputable def fixedRateKappa : ℝ := 1 / 1000000

noncomputable def fixedRateRho (lambda J : ℕ) : ℝ :=
  fixedRateKappa / ((lambda : ℝ) * (J : ℝ))

noncomputable def fixedRateLLLWeight (lambda J : ℕ) : ℝ :=
  2 * fixedRateRho lambda J ^ 2

noncomputable def fixedRateScale (lambda S : ℕ) : ℝ :=
  (S : ℝ) / (lambda : ℝ) ^ 2

theorem fixedRateKappa_nonneg : 0 ≤ fixedRateKappa := by
  norm_num [fixedRateKappa]

theorem fixedRateKappa_lower_small :
    96 * fixedRateKappa ≤ 1 / 320 := by
  norm_num [fixedRateKappa]

theorem fixedRateKappa_upper_small :
    56 * fixedRateKappa ≤ 1 := by
  norm_num [fixedRateKappa]

theorem fixedRate_maxSupport_le
    (J S K : ℕ) (hSJ : S ≤ J) (hKS : K ≤ S) :
    Nat.max (K * J) (S * (J + 2 * S)) ≤ 3 * S * J := by
  rw [Nat.max_le]
  constructor
  · calc
      K * J ≤ S * J := Nat.mul_le_mul_right J hKS
      _ ≤ (3 * S) * J := Nat.mul_le_mul_right J (by omega)
      _ = 3 * S * J := by ring
  · calc
      S * (J + 2 * S) ≤ S * (J + 2 * J) := by
        gcongr
      _ = 3 * S * J := by ring

theorem fixedRate_lower_product_le
    (J S K : ℕ) (hSJ : S ≤ J) (hKS : K ≤ S) :
    Nat.max (K * J) (S * (J + 2 * S)) * (2 * J + 6 * S) ≤
      24 * S * J * J := by
  calc
    Nat.max (K * J) (S * (J + 2 * S)) * (2 * J + 6 * S) ≤
        (3 * S * J) * (2 * J + 6 * S) :=
      Nat.mul_le_mul_right _ (fixedRate_maxSupport_le J S K hSJ hKS)
    _ ≤ (3 * S * J) * (2 * J + 6 * J) := by gcongr
    _ = 24 * S * J * J := by ring

theorem fixedRate_upper_product_le
    (J S R : ℕ) (hSJ : S ≤ J) (hRJ : R ≤ J) :
    (2 * J * S) * (R + (2 * J + 4 * S)) ≤ 14 * S * J * J := by
  calc
    (2 * J * S) * (R + (2 * J + 4 * S)) ≤
        (2 * J * S) * (J + (2 * J + 4 * J)) := by gcongr
    _ = 14 * S * J * J := by ring

theorem fixedRate_pair_count_le
    (J S R : ℕ) (hSJ : S ≤ J) (hRJ : R ≤ J) :
    2 * (R + (2 * J + 4 * S)) ≤ 14 * J := by omega

/-- The half-scale degree and block-size assumptions imply the two integer
cross-product inequalities used by the common lower mean. -/
theorem fixedRate_lower_mean_cross_products
    (lambda J S kMin m dJob dSlot : ℕ)
    (hgroupSize : S ≤ 10 * lambda * kMin)
    (hjobHalf : J ≤ 2 * dJob) (hslotHalf : S ≤ 2 * dSlot)
    (hcodegree : 6 * lambda ≤ J) (hsupport : kMin * dJob ≤ m) :
    S * J ≤ 20 * lambda * m ∧
      3 * S * J ≤ 20 * dSlot * (dJob - lambda) := by
  have hjobSub : J ≤ 3 * (dJob - lambda) := by omega
  constructor
  · calc
      S * J ≤ (10 * lambda * kMin) * (2 * dJob) :=
        Nat.mul_le_mul hgroupSize hjobHalf
      _ = 20 * lambda * (kMin * dJob) := by ring
      _ ≤ 20 * lambda * m := Nat.mul_le_mul_left (20 * lambda) hsupport
  · calc
      3 * S * J ≤ 3 * (2 * dSlot) * (3 * (dJob - lambda)) := by
        gcongr
      _ = 18 * dSlot * (dJob - lambda) := by ring
      _ ≤ 20 * dSlot * (dJob - lambda) := by
        gcongr
        omega

/-- The planned block size and half-scale degree bounds put the concrete
floor `kappa*S/(20*lambda^2)` below the exact `min` lower mean. -/
theorem fixedRate_lower_floor_le_activeSlotMean
    (lambda J S kMin m dJob dSlot : ℕ)
    (hlambda : 0 < lambda) (hJ : 0 < J)
    (hgroupSize : S ≤ 10 * lambda * kMin)
    (hjobHalf : J ≤ 2 * dJob) (hslotHalf : S ≤ 2 * dSlot)
    (hcodegree : 6 * lambda ≤ J) (hsupport : kMin * dJob ≤ m) :
    fixedRateKappa * fixedRateScale lambda S / 20 ≤
      RankThreeOptionSystem.activeSlotUniformLowerMean
        (fixedRateRho lambda J) m dJob dSlot lambda := by
  rcases fixedRate_lower_mean_cross_products lambda J S kMin m dJob dSlot
    hgroupSize hjobHalf hslotHalf hcodegree hsupport with ⟨hgroup, hslot⟩
  rw [RankThreeOptionSystem.activeSlotUniformLowerMean]
  apply le_min
  · have hgroupR : ((S * J : ℕ) : ℝ) ≤ ((20 * lambda * m : ℕ) : ℝ) := by
      exact_mod_cast hgroup
    simp only [fixedRateScale, fixedRateRho]
    have hlambdaR : (lambda : ℝ) ≠ 0 := by positivity
    have hJR : (J : ℝ) ≠ 0 := by positivity
    push_cast at hgroupR ⊢
    field_simp
    nlinarith [fixedRateKappa_nonneg]
  · have hslotR : ((3 * S * J : ℕ) : ℝ) ≤
        ((20 * dSlot * (dJob - lambda) : ℕ) : ℝ) := by
      exact_mod_cast hslot
    simp only [fixedRateScale, fixedRateRho]
    have hlambdaR : (lambda : ℝ) ≠ 0 := by positivity
    have hJR : (J : ℝ) ≠ 0 := by positivity
    push_cast at hslotR ⊢
    field_simp
    nlinarith [fixedRateKappa_nonneg]

theorem fixedRate_muUpper_eq
    (lambda J S : ℕ) (hlambda : 0 < lambda) (hJ : 0 < J) :
    fixedRateRho lambda J *
        ((J : ℝ) * (S : ℝ) / (lambda : ℝ)) =
      fixedRateKappa * fixedRateScale lambda S := by
  simp only [fixedRateRho, fixedRateScale]
  have hlambdaR : (lambda : ℝ) ≠ 0 := by positivity
  have hJR : (J : ℝ) ≠ 0 := by positivity
  field_simp

theorem fixedRate_lower_penalty_le
    (lambda J S K : ℕ) (hlambda : 0 < lambda) (hJ : 0 < J)
    (hSJ : S ≤ J) (hKS : K ≤ S) :
    2 * fixedRateLLLWeight lambda J *
        (((Nat.max (K * J) (S * (J + 2 * S))) *
          (2 * J + 6 * S) : ℕ) : ℝ) ≤
      96 * fixedRateKappa ^ 2 * fixedRateScale lambda S := by
  have hp := fixedRate_lower_product_le J S K hSJ hKS
  have hpR : (((Nat.max (K * J) (S * (J + 2 * S))) *
          (2 * J + 6 * S) : ℕ) : ℝ) ≤
      ((24 * S * J * J : ℕ) : ℝ) := by exact_mod_cast hp
  calc
    2 * fixedRateLLLWeight lambda J *
        (((Nat.max (K * J) (S * (J + 2 * S))) *
          (2 * J + 6 * S) : ℕ) : ℝ) ≤
      2 * fixedRateLLLWeight lambda J *
        ((24 * S * J * J : ℕ) : ℝ) := by
          exact mul_le_mul_of_nonneg_left hpR (by
            simp only [fixedRateLLLWeight]
            positivity)
    _ = 96 * fixedRateKappa ^ 2 * fixedRateScale lambda S := by
      simp only [fixedRateLLLWeight, fixedRateRho, fixedRateScale]
      have hlambdaR : (lambda : ℝ) ≠ 0 := by positivity
      have hJR : (J : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem fixedRate_upper_penalty_le
    (lambda J S R : ℕ) (hlambda : 0 < lambda) (hJ : 0 < J)
    (hSJ : S ≤ J) (hRJ : R ≤ J) :
    2 * fixedRateLLLWeight lambda J *
        ((((2 * J * S) * (R + (2 * J + 4 * S)) : ℕ) : ℝ)) ≤
      56 * fixedRateKappa ^ 2 * fixedRateScale lambda S := by
  have hp := fixedRate_upper_product_le J S R hSJ hRJ
  have hpR : ((((2 * J * S) * (R + (2 * J + 4 * S)) : ℕ) : ℝ)) ≤
      ((14 * S * J * J : ℕ) : ℝ) := by exact_mod_cast hp
  calc
    2 * fixedRateLLLWeight lambda J *
        ((((2 * J * S) * (R + (2 * J + 4 * S)) : ℕ) : ℝ)) ≤
      2 * fixedRateLLLWeight lambda J *
        ((14 * S * J * J : ℕ) : ℝ) := by
          exact mul_le_mul_of_nonneg_left hpR (by
            simp only [fixedRateLLLWeight]
            positivity)
    _ = 56 * fixedRateKappa ^ 2 * fixedRateScale lambda S := by
      simp only [fixedRateLLLWeight, fixedRateRho, fixedRateScale]
      have hlambdaR : (lambda : ℝ) ≠ 0 := by positivity
      have hJR : (J : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem fixedRateRho_nonneg (lambda J : ℕ) :
    0 ≤ fixedRateRho lambda J := by
  simp only [fixedRateRho]
  exact div_nonneg fixedRateKappa_nonneg
    (mul_nonneg (Nat.cast_nonneg lambda) (Nat.cast_nonneg J))

theorem fixedRateLLLWeight_nonneg (lambda J : ℕ) :
    0 ≤ fixedRateLLLWeight lambda J := by
  simp only [fixedRateLLLWeight]
  positivity

theorem fixedRateRho_le_half
    (lambda J : ℕ) (hlambda : 0 < lambda) (hJ : 0 < J) :
    fixedRateRho lambda J ≤ 1 / 2 := by
  simp only [fixedRateRho]
  have hden : (0 : ℝ) < (lambda : ℝ) * (J : ℝ) := by positivity
  apply (div_le_iff₀ hden).2
  have hnat : 1 ≤ lambda * J := Nat.one_le_iff_ne_zero.mpr (by
    exact Nat.mul_ne_zero (Nat.ne_of_gt hlambda) (Nat.ne_of_gt hJ))
  have hcast : (1 : ℝ) ≤ (lambda : ℝ) * (J : ℝ) := by exact_mod_cast hnat
  norm_num [fixedRateKappa]
  nlinarith

theorem fixedRateLLLWeight_le_half
    (lambda J : ℕ) (hlambda : 0 < lambda) (hJ : 0 < J) :
    fixedRateLLLWeight lambda J ≤ 1 / 2 := by
  have hrho0 := fixedRateRho_nonneg lambda J
  have hrhoHalf := fixedRateRho_le_half lambda J hlambda hJ
  simp only [fixedRateLLLWeight]
  nlinarith [sq_nonneg (fixedRateRho lambda J)]

/-- The exponent in the pair-event neighbor product is at most one half. -/
theorem fixedRate_pair_exponent_le_half
    (lambda J S R : ℕ) (hlambda : 0 < lambda) (hJ : 0 < J)
    (hSJ : S ≤ J) (hRJ : R ≤ J) :
    2 * fixedRateLLLWeight lambda J *
        ((2 * (R + (2 * J + 4 * S)) : ℕ) : ℝ) ≤ 1 / 2 := by
  have hc := fixedRate_pair_count_le J S R hSJ hRJ
  have hcR : ((2 * (R + (2 * J + 4 * S)) : ℕ) : ℝ) ≤
      ((14 * J : ℕ) : ℝ) := by exact_mod_cast hc
  calc
    2 * fixedRateLLLWeight lambda J *
        ((2 * (R + (2 * J + 4 * S)) : ℕ) : ℝ) ≤
      2 * fixedRateLLLWeight lambda J * ((14 * J : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hcR
          (mul_nonneg (by norm_num) (fixedRateLLLWeight_nonneg lambda J))
    _ = 56 * fixedRateKappa ^ 2 /
        ((lambda : ℝ) ^ 2 * (J : ℝ)) := by
      simp only [fixedRateLLLWeight, fixedRateRho]
      have hlambdaR : (lambda : ℝ) ≠ 0 := by positivity
      have hJR : (J : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    _ ≤ 1 / 2 := by
      have hden : (0 : ℝ) < (lambda : ℝ) ^ 2 * (J : ℝ) := by positivity
      apply (div_le_iff₀ hden).2
      have hnat : 1 ≤ lambda ^ 2 * J := by
        have hl : 1 ≤ lambda := hlambda
        have hj : 1 ≤ J := hJ
        nlinarith
      have hcast : (1 : ℝ) ≤ (lambda : ℝ) ^ 2 * (J : ℝ) := by
        exact_mod_cast hnat
      norm_num [fixedRateKappa]
      nlinarith

/-- Pair-event scalar inequality for the fixed choice. -/
theorem fixedRate_pair_numeric
    (lambda J S R : ℕ) (hlambda : 0 < lambda) (hJ : 0 < J)
    (hSJ : S ≤ J) (hRJ : R ≤ J) :
    fixedRateRho lambda J * fixedRateRho lambda J ≤
      fixedRateLLLWeight lambda J *
        Real.exp (-2 * fixedRateLLLWeight lambda J *
          ((2 * (R + (2 * J + 4 * S)) : ℕ) : ℝ)) := by
  have h := doubled_pair_weight_pays_small_exponent
    (fixedRateRho lambda J)
    (2 * fixedRateLLLWeight lambda J *
      ((2 * (R + (2 * J + 4 * S)) : ℕ) : ℝ))
    (fixedRate_pair_exponent_le_half lambda J S R hlambda hJ hSJ hRJ)
  simpa [fixedRateLLLWeight, pow_two] using h

/-- Lower-row scalar inequality.  The one transparent scale assumption is
the expected asymptotic condition `exp(-kappa*S/(320*lambda^2)) ≤ rowX`. -/
theorem fixedRate_lower_numeric
    (lambda J S K : ℕ) (eta : ℝ)
    (hlambda : 0 < lambda) (hJ : 0 < J)
    (hSJ : S ≤ J) (hKS : K ≤ S)
    (heta : fixedRateKappa * fixedRateScale lambda S / 20 ≤ eta)
    (hscale : Real.exp
      (-(fixedRateKappa * fixedRateScale lambda S / 320)) ≤
        fixedRateLLLWeight lambda J) :
    Real.exp (-(1 / 8 : ℝ) * eta) ≤
      fixedRateLLLWeight lambda J *
        Real.exp (-2 * fixedRateLLLWeight lambda J *
          (((Nat.max (K * J) (S * (J + 2 * S))) *
            (2 * J + 6 * S) : ℕ) : ℝ)) := by
  let Z := fixedRateScale lambda S
  have hZ0 : 0 ≤ Z := by
    dsimp [Z, fixedRateScale]
    positivity
  have hetaExp : Real.exp (-(1 / 8 : ℝ) * eta) ≤
      Real.exp (-(fixedRateKappa * Z / 160)) := by
    apply Real.exp_le_exp.mpr
    dsimp [Z] at heta ⊢
    linarith
  have hbase := tight_lower_exp_le fixedRateKappa Z
    (fixedRateLLLWeight lambda J) fixedRateKappa_nonneg hZ0
    fixedRateKappa_lower_small (by simpa [Z] using hscale)
  have hpenalty := fixedRate_lower_penalty_le
    lambda J S K hlambda hJ hSJ hKS
  have hexpPenalty : Real.exp (-(96 * fixedRateKappa ^ 2 * Z)) ≤
      Real.exp (-2 * fixedRateLLLWeight lambda J *
        (((Nat.max (K * J) (S * (J + 2 * S))) *
          (2 * J + 6 * S) : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    dsimp [Z] at hpenalty ⊢
    linarith
  calc
    Real.exp (-(1 / 8 : ℝ) * eta) ≤
        Real.exp (-(fixedRateKappa * Z / 160)) := hetaExp
    _ ≤ fixedRateLLLWeight lambda J *
        Real.exp (-(96 * fixedRateKappa ^ 2 * Z)) := hbase
    _ ≤ fixedRateLLLWeight lambda J *
        Real.exp (-2 * fixedRateLLLWeight lambda J *
          (((Nat.max (K * J) (S * (J + 2 * S))) *
            (2 * J + 6 * S) : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hexpPenalty
        (fixedRateLLLWeight_nonneg lambda J)

/-- Upper-job scalar inequality for the fixed choice. -/
theorem fixedRate_upper_numeric
    (lambda J S R : ℕ) (hlambda : 0 < lambda) (hJ : 0 < J)
    (hSJ : S ≤ J) (hRJ : R ≤ J)
    (hscale : Real.exp
      (-(fixedRateKappa * fixedRateScale lambda S / 320)) ≤
        fixedRateLLLWeight lambda J) :
    Real.exp (-2 *
        (fixedRateRho lambda J *
          ((J : ℝ) * (S : ℝ) / (lambda : ℝ)))) ≤
      fixedRateLLLWeight lambda J *
        Real.exp (-2 * fixedRateLLLWeight lambda J *
          (((2 * J * S) * (R + (2 * J + 4 * S)) : ℕ) : ℝ)) := by
  let Z := fixedRateScale lambda S
  have hZ0 : 0 ≤ Z := by
    dsimp [Z, fixedRateScale]
    positivity
  have hscaleUpper : Real.exp (-(fixedRateKappa * Z)) ≤
      fixedRateLLLWeight lambda J := by
    apply le_trans ?_ (by simpa [Z] using hscale)
    apply Real.exp_le_exp.mpr
    have hkZ : 0 ≤ fixedRateKappa * Z :=
      mul_nonneg fixedRateKappa_nonneg hZ0
    linarith
  have hbase := tight_upper_exp_le fixedRateKappa Z
    (fixedRateLLLWeight lambda J) fixedRateKappa_nonneg hZ0
    fixedRateKappa_upper_small hscaleUpper
  have hpenalty := fixedRate_upper_penalty_le
    lambda J S R hlambda hJ hSJ hRJ
  have hexpPenalty : Real.exp (-(56 * fixedRateKappa ^ 2 * Z)) ≤
      Real.exp (-2 * fixedRateLLLWeight lambda J *
        (((2 * J * S) * (R + (2 * J + 4 * S)) : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    dsimp [Z] at hpenalty ⊢
    linarith
  rw [fixedRate_muUpper_eq lambda J S hlambda hJ]
  simpa [Z, mul_assoc] using
    hbase.trans (mul_le_mul_of_nonneg_left hexpPenalty
      (fixedRateLLLWeight_nonneg lambda J))

/-- All three scalar hypotheses required by the separate-scale active-slot
round, packaged for direct use in an iteration. -/
theorem fixedRate_numeric_package
    (lambda J S R K : ℕ) (eta : ℝ)
    (hlambda : 0 < lambda) (hJ : 0 < J)
    (hSJ : S ≤ J) (hRJ : R ≤ J) (hKS : K ≤ S)
    (heta : fixedRateKappa * fixedRateScale lambda S / 20 ≤ eta)
    (hscale : Real.exp
      (-(fixedRateKappa * fixedRateScale lambda S / 320)) ≤
        fixedRateLLLWeight lambda J) :
    (fixedRateRho lambda J * fixedRateRho lambda J ≤
      fixedRateLLLWeight lambda J *
        Real.exp (-2 * fixedRateLLLWeight lambda J *
          ((2 * (R + (2 * J + 4 * S)) : ℕ) : ℝ))) ∧
    (Real.exp (-(1 / 8 : ℝ) * eta) ≤
      fixedRateLLLWeight lambda J *
        Real.exp (-2 * fixedRateLLLWeight lambda J *
          (((Nat.max (K * J) (S * (J + 2 * S))) *
            (2 * J + 6 * S) : ℕ) : ℝ))) ∧
    (Real.exp (-2 *
        (fixedRateRho lambda J *
          ((J : ℝ) * (S : ℝ) / (lambda : ℝ)))) ≤
      fixedRateLLLWeight lambda J *
        Real.exp (-2 * fixedRateLLLWeight lambda J *
          (((2 * J * S) * (R + (2 * J + 4 * S)) : ℕ) : ℝ))) := by
  exact ⟨fixedRate_pair_numeric lambda J S R hlambda hJ hSJ hRJ,
    fixedRate_lower_numeric lambda J S K eta hlambda hJ hSJ hKS heta hscale,
    fixedRate_upper_numeric lambda J S R hlambda hJ hSJ hRJ hscale⟩

/-- The same package with `eta` instantiated by the exact common lower mean.
Its hypotheses are the integer conditions naturally maintained by the
iteration. -/
theorem fixedRate_activeSlot_numeric_package
    (lambda J S R Kmax kMin m dJob dSlot : ℕ)
    (hlambda : 0 < lambda) (hJ : 0 < J)
    (hSJ : S ≤ J) (hRJ : R ≤ J) (hKS : Kmax ≤ S)
    (hgroupSize : S ≤ 10 * lambda * kMin)
    (hjobHalf : J ≤ 2 * dJob) (hslotHalf : S ≤ 2 * dSlot)
    (hcodegree : 6 * lambda ≤ J) (hsupport : kMin * dJob ≤ m)
    (hscale : Real.exp
      (-(fixedRateKappa * fixedRateScale lambda S / 320)) ≤
        fixedRateLLLWeight lambda J) :
    let eta := RankThreeOptionSystem.activeSlotUniformLowerMean
      (fixedRateRho lambda J) m dJob dSlot lambda
    (fixedRateRho lambda J * fixedRateRho lambda J ≤
      fixedRateLLLWeight lambda J *
        Real.exp (-2 * fixedRateLLLWeight lambda J *
          ((2 * (R + (2 * J + 4 * S)) : ℕ) : ℝ))) ∧
    (Real.exp (-(1 / 8 : ℝ) * eta) ≤
      fixedRateLLLWeight lambda J *
        Real.exp (-2 * fixedRateLLLWeight lambda J *
          (((Nat.max (Kmax * J) (S * (J + 2 * S))) *
            (2 * J + 6 * S) : ℕ) : ℝ))) ∧
    (Real.exp (-2 *
        (fixedRateRho lambda J *
          ((J : ℝ) * (S : ℝ) / (lambda : ℝ)))) ≤
      fixedRateLLLWeight lambda J *
        Real.exp (-2 * fixedRateLLLWeight lambda J *
          (((2 * J * S) * (R + (2 * J + 4 * S)) : ℕ) : ℝ))) := by
  dsimp only
  apply fixedRate_numeric_package lambda J S R Kmax
    (RankThreeOptionSystem.activeSlotUniformLowerMean
      (fixedRateRho lambda J) m dJob dSlot lambda)
    hlambda hJ hSJ hRJ hKS
  · exact fixedRate_lower_floor_le_activeSlotMean
      lambda J S kMin m dJob dSlot hlambda hJ hgroupSize
      hjobHalf hslotHalf hcodegree hsupport
  · exact hscale

end WeightedEdgeColoring
