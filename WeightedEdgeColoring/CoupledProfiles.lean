import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# Coupling the two endpoint profile choices

This file formalizes the algebraic part of the whole-edge rounding proof.
An edge has the same retained mass `y` at its two endpoints.  If `aU` and
`aV` split that mass among profile slots, the product construction below
couples the two splits without paying for the edge twice.
-/

section Pairing

variable {PU PV IU IV : Type*}

/-- Fractional mass assigned to the option using the indicated profile slot
at each endpoint.  The two profile probabilities occur in the denominator
because profiles are sampled independently. -/
noncomputable def pairedOption
    (rho y : ℝ) (lambdaU : PU → ℝ) (lambdaV : PV → ℝ)
    (aU : PU → IU → ℝ) (aV : PV → IV → ℝ)
    (p : PU) (q : PV) (i : IU) (j : IV) : ℝ :=
  if y = 0 then 0 else
    rho * aU p i * aV q j / (y * lambdaU p * lambdaV q)

variable [Fintype PU] [Fintype PV] [Fintype IU] [Fintype IV]

/-- Averaging over the independently sampled profile at the right endpoint
recovers the left assigned fraction, with exactly one factor of `y` canceled.
This is the local identity used in the slot-load calculation. -/
theorem sum_pairedOption_right
    (rho y : ℝ) (lambdaU : PU → ℝ) (lambdaV : PV → ℝ)
    (aU : PU → IU → ℝ) (aV : PV → IV → ℝ)
    (p : PU) (i : IU)
    (hy : y ≠ 0) (hU : lambdaU p ≠ 0)
    (hV : ∀ q, lambdaV q ≠ 0)
    (hmassV : ∑ q, ∑ j, aV q j = y) :
    (∑ q, lambdaV q * ∑ j,
      pairedOption rho y lambdaU lambdaV aU aV p q i j) =
      rho * aU p i / lambdaU p := by
  have hpoint : ∀ q j,
      lambdaV q * pairedOption rho y lambdaU lambdaV aU aV p q i j =
        (rho * aU p i / (y * lambdaU p)) * aV q j := by
    intro q j
    simp only [pairedOption, if_neg hy]
    field_simp [hU, hV q, hy]
  calc
    (∑ q, lambdaV q * ∑ j,
        pairedOption rho y lambdaU lambdaV aU aV p q i j)
        = ∑ q, ∑ j,
            lambdaV q * pairedOption rho y lambdaU lambdaV aU aV p q i j := by
              apply Finset.sum_congr rfl
              intro q _hq
              rw [Finset.mul_sum]
    _ = ∑ q, ∑ j,
          (rho * aU p i / (y * lambdaU p)) * aV q j := by
            apply Finset.sum_congr rfl
            intro q _hq
            apply Finset.sum_congr rfl
            intro j _hj
            exact hpoint q j
    _ = (rho * aU p i / (y * lambdaU p)) *
          (∑ q, ∑ j, aV q j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q _hq
            rw [Finset.mul_sum]
    _ = rho * aU p i / lambdaU p := by
          rw [hmassV]
          field_simp [hU, hy]

/-- Symmetric form of `sum_pairedOption_right`. -/
theorem sum_pairedOption_left
    (rho y : ℝ) (lambdaU : PU → ℝ) (lambdaV : PV → ℝ)
    (aU : PU → IU → ℝ) (aV : PV → IV → ℝ)
    (q : PV) (j : IV)
    (hy : y ≠ 0) (hU : ∀ p, lambdaU p ≠ 0)
    (hV : lambdaV q ≠ 0)
    (hmassU : ∑ p, ∑ i, aU p i = y) :
    (∑ p, lambdaU p * ∑ i,
      pairedOption rho y lambdaU lambdaV aU aV p q i j) =
      rho * aV q j / lambdaV q := by
  have hpoint : ∀ p i,
      lambdaU p * pairedOption rho y lambdaU lambdaV aU aV p q i j =
        (rho * aV q j / (y * lambdaV q)) * aU p i := by
    intro p i
    simp only [pairedOption, if_neg hy]
    field_simp [hU p, hV, hy]
  calc
    (∑ p, lambdaU p * ∑ i,
        pairedOption rho y lambdaU lambdaV aU aV p q i j)
        = ∑ p, ∑ i,
            lambdaU p * pairedOption rho y lambdaU lambdaV aU aV p q i j := by
              apply Finset.sum_congr rfl
              intro p _hp
              rw [Finset.mul_sum]
    _ = ∑ p, ∑ i,
          (rho * aV q j / (y * lambdaV q)) * aU p i := by
            apply Finset.sum_congr rfl
            intro p _hp
            apply Finset.sum_congr rfl
            intro i _hi
            exact hpoint p i
    _ = (rho * aV q j / (y * lambdaV q)) *
          (∑ p, ∑ i, aU p i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p _hp
            rw [Finset.mul_sum]
    _ = rho * aV q j / lambdaV q := by
          rw [hmassU]
          field_simp [hV, hy]

/-- After averaging both independent endpoint profiles, the total option
mass is `rho * y`, not `rho * y^2`. -/
theorem sum_pairedOption
    (rho y : ℝ) (lambdaU : PU → ℝ) (lambdaV : PV → ℝ)
    (aU : PU → IU → ℝ) (aV : PV → IV → ℝ)
    (hy : y ≠ 0) (hU : ∀ p, lambdaU p ≠ 0)
    (hV : ∀ q, lambdaV q ≠ 0)
    (hmassU : ∑ p, ∑ i, aU p i = y)
    (hmassV : ∑ q, ∑ j, aV q j = y) :
    (∑ p, lambdaU p * ∑ i,
      ∑ q, lambdaV q * ∑ j,
        pairedOption rho y lambdaU lambdaV aU aV p q i j) = rho * y := by
  calc
    (∑ p, lambdaU p * ∑ i,
      ∑ q, lambdaV q * ∑ j,
        pairedOption rho y lambdaU lambdaV aU aV p q i j)
        = ∑ p, lambdaU p * ∑ i, (rho * aU p i / lambdaU p) := by
            apply Finset.sum_congr rfl
            intro p _hp
            congr 1
            apply Finset.sum_congr rfl
            intro i _hi
            exact sum_pairedOption_right rho y lambdaU lambdaV aU aV p i
              hy (hU p) hV hmassV
    _ = ∑ p, ∑ i, rho * aU p i := by
          apply Finset.sum_congr rfl
          intro p _hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          field_simp [hU p]
    _ = rho * (∑ p, ∑ i, aU p i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _hp
          rw [Finset.mul_sum]
    _ = rho * y := by rw [hmassU]

end Pairing

section Load

variable {E PU PV IU IV : Type*}
variable [Fintype E] [Fintype PU] [Fintype PV]
variable [Fintype IU] [Fintype IV]

/-- The exact expected-load identity for one fixed left profile slot and a
finite family of edges.  This is equation `(meanload)` before applying the
slot-capacity bound. -/
theorem coupled_slot_expected_load
    (rho : ℝ) (y d : E → ℝ)
    (lambdaU : PU → ℝ) (lambdaV : E → PV → ℝ)
    (aU : E → PU → IU → ℝ) (aV : E → PV → IV → ℝ)
    (p : PU) (i : IU)
    (hy : ∀ e, y e ≠ 0) (hU : lambdaU p ≠ 0)
    (hV : ∀ e q, lambdaV e q ≠ 0)
    (hmassV : ∀ e, ∑ q, ∑ j, aV e q j = y e) :
    (∑ e, d e * (∑ q, lambdaV e q * ∑ j,
      pairedOption rho (y e) lambdaU (lambdaV e) (aU e) (aV e)
        p q i j)) =
      (rho / lambdaU p) * ∑ e, d e * aU e p i := by
  calc
    (∑ e, d e * (∑ q, lambdaV e q * ∑ j,
      pairedOption rho (y e) lambdaU (lambdaV e) (aU e) (aV e)
        p q i j))
        = ∑ e, d e * (rho * aU e p i / lambdaU p) := by
            apply Finset.sum_congr rfl
            intro e _he
            rw [sum_pairedOption_right rho (y e) lambdaU (lambdaV e)
              (aU e) (aV e) p i (hy e) hU (hV e) (hmassV e)]
    _ = (rho / lambdaU p) * ∑ e, d e * aU e p i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _he
          field_simp [hU]

/-- A capacity bound on assigned fractions immediately gives the expected
load bound used by the profile-rounding proof. -/
theorem coupled_slot_expected_load_le
    (rho : ℝ) (y d : E → ℝ)
    (lambdaU : PU → ℝ) (lambdaV : E → PV → ℝ)
    (aU : E → PU → IU → ℝ) (aV : E → PV → IV → ℝ)
    (p : PU) (i : IU) (h : ℝ)
    (hy : ∀ e, y e ≠ 0) (hU : 0 < lambdaU p)
    (hV : ∀ e q, lambdaV e q ≠ 0)
    (hmassV : ∀ e, ∑ q, ∑ j, aV e q j = y e)
    (hrho : 0 ≤ rho)
    (hcap : ∑ e, d e * aU e p i ≤ lambdaU p * h) :
    (∑ e, d e * (∑ q, lambdaV e q * ∑ j,
      pairedOption rho (y e) lambdaU (lambdaV e) (aU e) (aV e)
        p q i j)) ≤ rho * h := by
  rw [coupled_slot_expected_load rho y d lambdaU lambdaV aU aV p i
    hy hU.ne' hV hmassV]
  calc
    (rho / lambdaU p) * ∑ e, d e * aU e p i
        ≤ (rho / lambdaU p) * (lambdaU p * h) := by
          exact mul_le_mul_of_nonneg_left hcap (div_nonneg hrho hU.le)
    _ = rho * h := by field_simp [hU.ne']

end Load

end WeightedEdgeColoring
