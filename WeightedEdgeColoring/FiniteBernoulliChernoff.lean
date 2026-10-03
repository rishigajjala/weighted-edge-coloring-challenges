import WeightedEdgeColoring.FiniteLocalLemma

/-!
# Finite weighted Bernoulli concentration

This file proves a Chernoff bound directly by finite sums.  A Bernoulli
outcome is represented by the finset of active coordinates.  Thus no
measurability or almost-everywhere side conditions enter applications.
-/

namespace WeightedEdgeColoring.FiniteBernoulliChernoff

open scoped BigOperators

variable {Omega I : Type*}

/-- The event on which a real-valued statistic is at least `r`. -/
noncomputable def upperTail [Fintype Omega] [DecidableEq Omega]
    (X : Omega → ℝ) (r : ℝ) : Finset Omega :=
  Finset.univ.filter fun omega ↦ r ≤ X omega

/-- The event on which a real-valued statistic is at most `r`. -/
noncomputable def lowerTail [Fintype Omega] [DecidableEq Omega]
    (X : Omega → ℝ) (r : ℝ) : Finset Omega :=
  Finset.univ.filter fun omega ↦ X omega ≤ r

/-- Finite exponential Markov inequality, in a form ready for an MGF bound. -/
theorem exponential_markov [Fintype Omega] [DecidableEq Omega]
    (mass : Omega → ℝ) (X : Omega → ℝ) (r lambda : ℝ)
    (hmass : ∀ omega, 0 ≤ mass omega) (hlambda : 0 ≤ lambda) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass mass (upperTail X r) ≤
      Real.exp (-lambda * r) * ∑ omega, mass omega * Real.exp (lambda * X omega) := by
  have hexp : 0 < Real.exp (lambda * r) := Real.exp_pos _
  have hneg : -lambda * r = -(lambda * r) := by ring
  rw [hneg, Real.exp_neg, inv_mul_eq_div]
  apply (le_div_iff₀ hexp).2
  rw [WeightedEdgeColoring.FiniteLocalLemma.eventMass, Finset.sum_mul]
  calc
    ∑ omega ∈ upperTail X r, mass omega * Real.exp (lambda * r) ≤
        ∑ omega ∈ upperTail X r, mass omega * Real.exp (lambda * X omega) := by
      apply Finset.sum_le_sum
      intro omega homega
      apply mul_le_mul_of_nonneg_left _ (hmass omega)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp homega).2 hlambda
    _ ≤ ∑ omega, mass omega * Real.exp (lambda * X omega) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro omega _ _
      exact mul_nonneg (hmass omega) (Real.exp_pos _).le

section Bernoulli

variable [Fintype I] [DecidableEq I]

/-- Product mass of a Bernoulli outcome, represented by its active coordinates. -/
def bernoulliMass (q : I → ℝ) (S : Finset I) : ℝ :=
  (∏ i ∈ S, q i) * ∏ i ∈ (Finset.univ \ S), (1 - q i)

/-- Weighted sum of the active Bernoulli coordinates. -/
def weightedSum (a : I → ℝ) (S : Finset I) : ℝ :=
  ∑ i ∈ S, a i

/-- Mean of the weighted Bernoulli sum. -/
def mean (q a : I → ℝ) : ℝ :=
  ∑ i, q i * a i

omit [Fintype I] in
private theorem sum_powerset_product (s : Finset I) (f g : I → ℝ) :
    (∑ T ∈ s.powerset, (∏ i ∈ T, f i) * ∏ i ∈ (s \ T), g i) =
      ∏ i ∈ s, (f i + g i) := by
  simpa using (Finset.prod_add f g s).symm

theorem bernoulliMass_nonneg (q : I → ℝ)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_le_one : ∀ i, q i ≤ 1) (S : Finset I) :
    0 ≤ bernoulliMass q S := by
  exact mul_nonneg
    (Finset.prod_nonneg fun i _ ↦ hq_nonneg i)
    (Finset.prod_nonneg fun i _ ↦ sub_nonneg.mpr (hq_le_one i))

theorem sum_bernoulliMass (q : I → ℝ) :
    ∑ S : Finset I, bernoulliMass q S = 1 := by
  classical
  have huniv : (Finset.univ : Finset (Finset I)) =
      (Finset.univ : Finset I).powerset := by ext S; simp
  change (∑ S ∈ (Finset.univ : Finset (Finset I)), bernoulliMass q S) = 1
  rw [huniv]
  simpa [bernoulliMass] using
    sum_powerset_product (Finset.univ : Finset I) q (fun i ↦ 1 - q i)

private theorem exp_mul_le_secant {lambda a : ℝ}
    (ha_nonneg : 0 ≤ a) (ha_le_one : a ≤ 1) :
    Real.exp (lambda * a) ≤ 1 + a * (Real.exp lambda - 1) := by
  have hconvex := convexOn_exp.2 (Set.mem_univ lambda) (Set.mem_univ 0)
    ha_nonneg (sub_nonneg.mpr ha_le_one) (by ring : a + (1 - a) = 1)
  have hconvex' : Real.exp (lambda * a) ≤
      a * Real.exp lambda + (1 - a) := by
    simpa [smul_eq_mul, mul_comm] using hconvex
  calc
    Real.exp (lambda * a) ≤ a * Real.exp lambda + (1 - a) := hconvex'
    _ = 1 + a * (Real.exp lambda - 1) := by ring

private theorem bernoulli_mgf_exact (q a : I → ℝ) (lambda : ℝ) :
    (∑ S : Finset I, bernoulliMass q S * Real.exp (lambda * weightedSum a S)) =
      ∏ i, (q i * Real.exp (lambda * a i) + (1 - q i)) := by
  classical
  have huniv : (Finset.univ : Finset (Finset I)) =
      (Finset.univ : Finset I).powerset := by ext S; simp
  change (∑ S ∈ (Finset.univ : Finset (Finset I)),
    bernoulliMass q S * Real.exp (lambda * weightedSum a S)) = _
  rw [huniv]
  calc
    (∑ S ∈ (Finset.univ : Finset I).powerset,
        bernoulliMass q S * Real.exp (lambda * weightedSum a S)) =
        ∑ S ∈ (Finset.univ : Finset I).powerset,
          (∏ i ∈ S, q i * Real.exp (lambda * a i)) *
            ∏ i ∈ (Finset.univ \ S), (1 - q i) := by
      apply Finset.sum_congr rfl
      intro S _
      have hexp : Real.exp (lambda * weightedSum a S) =
          ∏ i ∈ S, Real.exp (lambda * a i) := by
        rw [weightedSum, Finset.mul_sum, Real.exp_sum]
      rw [bernoulliMass, hexp]
      calc
        ((∏ i ∈ S, q i) * ∏ i ∈ (Finset.univ \ S), (1 - q i)) *
            ∏ i ∈ S, Real.exp (lambda * a i) =
            ((∏ i ∈ S, q i) * ∏ i ∈ S, Real.exp (lambda * a i)) *
              ∏ i ∈ (Finset.univ \ S), (1 - q i) := by ring
        _ = (∏ i ∈ S, q i * Real.exp (lambda * a i)) *
              ∏ i ∈ (Finset.univ \ S), (1 - q i) := by
          rw [Finset.prod_mul_distrib]
    _ = ∏ i, (q i * Real.exp (lambda * a i) + (1 - q i)) := by
      simpa using sum_powerset_product (Finset.univ : Finset I)
        (fun i ↦ q i * Real.exp (lambda * a i)) (fun i ↦ 1 - q i)

/-- Exponential-moment estimate for a weighted sum of independent Bernoulli coordinates. -/
theorem bernoulli_mgf_le (q a : I → ℝ) (lambda : ℝ)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_le_one : ∀ i, q i ≤ 1)
    (ha_nonneg : ∀ i, 0 ≤ a i) (ha_le_one : ∀ i, a i ≤ 1) :
    (∑ S : Finset I, bernoulliMass q S * Real.exp (lambda * weightedSum a S)) ≤
      Real.exp ((Real.exp lambda - 1) * mean q a) := by
  rw [bernoulli_mgf_exact]
  calc
    (∏ i, (q i * Real.exp (lambda * a i) + (1 - q i))) ≤
        ∏ i, Real.exp ((Real.exp lambda - 1) * (q i * a i)) := by
      apply Finset.prod_le_prod
      · intro i _
        have hexp_nonneg : 0 ≤ Real.exp (lambda * a i) := (Real.exp_pos _).le
        nlinarith [hq_nonneg i, hq_le_one i]
      · intro i _
        have hsecant := exp_mul_le_secant
          (lambda := lambda) (a := a i) (ha_nonneg i) (ha_le_one i)
        have hone_exp : 1 + (Real.exp lambda - 1) * (q i * a i) ≤
            Real.exp ((Real.exp lambda - 1) * (q i * a i)) :=
          by simpa [add_comm] using
            (Real.add_one_le_exp ((Real.exp lambda - 1) * (q i * a i)))
        nlinarith [hq_nonneg i]
    _ = Real.exp ((Real.exp lambda - 1) * mean q a) := by
      rw [← Real.exp_sum]
      congr 1
      simp [mean, Finset.mul_sum]

/--
Chernoff upper-tail bound for a weighted sum of independent Bernoulli
coordinates.  The free parameter `lambda ≥ 0` can be optimized by an
application; the exponent depends only on the exact mean `μ = ∑ i, q i a i`.
-/
theorem bernoulli_upperTail_le (q a : I → ℝ) (r lambda : ℝ)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_le_one : ∀ i, q i ≤ 1)
    (ha_nonneg : ∀ i, 0 ≤ a i) (ha_le_one : ∀ i, a i ≤ 1)
    (hlambda : 0 ≤ lambda) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (upperTail (weightedSum a) r) ≤
      Real.exp (-lambda * r + (Real.exp lambda - 1) * mean q a) := by
  calc
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (upperTail (weightedSum a) r) ≤
        Real.exp (-lambda * r) *
          ∑ S, bernoulliMass q S * Real.exp (lambda * weightedSum a S) :=
      exponential_markov _ _ _ _
        (bernoulliMass_nonneg q hq_nonneg hq_le_one) hlambda
    _ ≤ Real.exp (-lambda * r) *
        Real.exp ((Real.exp lambda - 1) * mean q a) :=
      mul_le_mul_of_nonneg_left
        (bernoulli_mgf_le q a lambda hq_nonneg hq_le_one ha_nonneg ha_le_one)
        (Real.exp_pos _).le
    _ = Real.exp (-lambda * r + (Real.exp lambda - 1) * mean q a) :=
      (Real.exp_add _ _).symm

/-- Lower-tail companion, obtained by applying exponential Markov to `-X`. -/
theorem bernoulli_lowerTail_le (q a : I → ℝ) (r lambda : ℝ)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_le_one : ∀ i, q i ≤ 1)
    (ha_nonneg : ∀ i, 0 ≤ a i) (ha_le_one : ∀ i, a i ≤ 1)
    (hlambda : 0 ≤ lambda) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (lowerTail (weightedSum a) r) ≤
      Real.exp (lambda * r + (Real.exp (-lambda) - 1) * mean q a) := by
  have htail : lowerTail (weightedSum a) r =
      upperTail (fun S ↦ -weightedSum a S) (-r) := by
    ext S
    simp [lowerTail, upperTail]
  rw [htail]
  calc
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (upperTail (fun S ↦ -weightedSum a S) (-r)) ≤
        Real.exp (-lambda * (-r)) *
          ∑ S, bernoulliMass q S * Real.exp (lambda * (-weightedSum a S)) :=
      exponential_markov _ _ _ _
        (bernoulliMass_nonneg q hq_nonneg hq_le_one) hlambda
    _ = Real.exp (lambda * r) *
          ∑ S, bernoulliMass q S * Real.exp ((-lambda) * weightedSum a S) := by
      simp only [neg_mul, mul_neg, neg_neg]
    _ ≤ Real.exp (lambda * r) *
        Real.exp ((Real.exp (-lambda) - 1) * mean q a) :=
      mul_le_mul_of_nonneg_left
        (bernoulli_mgf_le q a (-lambda) hq_nonneg hq_le_one ha_nonneg ha_le_one)
        (Real.exp_pos _).le
    _ = Real.exp (lambda * r + (Real.exp (-lambda) - 1) * mean q a) :=
      (Real.exp_add _ _).symm

end Bernoulli

end WeightedEdgeColoring.FiniteBernoulliChernoff
