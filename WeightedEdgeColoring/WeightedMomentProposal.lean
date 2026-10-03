import WeightedEdgeColoring.KempeComponentEndpoints
import WeightedEdgeColoring.WeightedMomentPaletteMixing
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# From common-palette moments to a clipped proposal

This file is the deterministic second half of the weighted-moment mixing
argument.  It does not choose any Kempe switches.  Given the resulting
missing palettes, it defines

`lambda e = q * |F_u ∩ F_v| / (|F_u| |F_v|)`

and spreads mass uniformly over the common colors, clipping the total mass
at one.  A squared-error estimate for `lambda` then bounds all uncovered
charge by weighted Cauchy--Schwarz.  A first-moment pressure estimate bounds
every vertex--color row.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Real size of the missing palette at one vertex. -/
def momentMissingSize {q : ℕ} (F : Finset G.E) (color : G.E → Fin q)
    (v : G.V) : ℝ :=
  (G.missingColorsAt F color v).card

/-- Colors missing at both ends of an indexed edge. -/
def momentCommonMissingColors {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (e : G.E) :
    Finset (Fin q) :=
  G.missingColorsAt F color (G.fst e) ∩
    G.missingColorsAt F color (G.snd e)

/-- Normalized common-palette size.  A perfectly mixed pair has value close
to one. -/
noncomputable def momentLambda {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (e : G.E) : ℝ :=
  (q : ℝ) * (G.momentCommonMissingColors F color e).card /
    (G.momentMissingSize F color (G.fst e) *
      G.momentMissingSize F color (G.snd e))

/-- Uniform common-color mass, divided by `max 1 lambda` so that every edge
has total proposal mass at most one. -/
noncomputable def momentProposal {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (e : G.E) (c : Fin q) : ℝ :=
  if c ∈ G.momentCommonMissingColors F color e then
    ((q : ℝ) /
      (G.momentMissingSize F color (G.fst e) *
        G.momentMissingSize F color (G.snd e))) /
      max 1 (G.momentLambda F color e)
  else 0

/-! ## Scalar clipping -/

theorem lambda_div_max_nonneg {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    0 ≤ lambda / max 1 lambda := by
  exact div_nonneg hlambda (by positivity)

theorem lambda_div_max_le_one {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    lambda / max 1 lambda ≤ 1 := by
  have hmax : 0 < max 1 lambda := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [div_le_one hmax]
  exact le_max_right _ _

theorem one_sub_lambda_div_max_le_abs {lambda : ℝ}
    (hlambda : 0 ≤ lambda) :
    1 - lambda / max 1 lambda ≤ |lambda - 1| := by
  by_cases hle : lambda ≤ 1
  · rw [max_eq_left hle]
    simp only [div_one]
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  · have hone : 1 ≤ lambda := le_of_not_ge hle
    rw [max_eq_right hone]
    have hlambdaPos : 0 < lambda := zero_lt_one.trans_le hone
    rw [div_self (ne_of_gt hlambdaPos)]
    simpa using abs_nonneg (lambda - 1)

/-! ## Elementary proposal identities -/

theorem momentLambda_nonneg {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ v, 0 < G.momentMissingSize F color v) (e : G.E) :
    0 ≤ G.momentLambda F color e := by
  unfold momentLambda
  exact div_nonneg
    (mul_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg _))
    (mul_nonneg (hmissing _).le (hmissing _).le)

theorem momentProposal_nonneg {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ v, 0 < G.momentMissingSize F color v)
    (e : G.E) (c : Fin q) :
    0 ≤ G.momentProposal F color e c := by
  unfold momentProposal
  split
  · exact div_nonneg
      (div_nonneg (Nat.cast_nonneg q)
        (mul_nonneg (hmissing _).le (hmissing _).le))
      (le_trans zero_le_one (le_max_left _ _))
  · exact le_rfl

theorem momentProposal_pos_support {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    {e : G.E} {c : Fin q} (hpos : 0 < G.momentProposal F color e c) :
    c ∈ G.missingColorsAt F color (G.fst e) ∧
      c ∈ G.missingColorsAt F color (G.snd e) := by
  unfold momentProposal at hpos
  split at hpos
  · exact Finset.mem_inter.mp (by assumption)
  · simp at hpos

/-- Exact total mass of the clipped common-palette proposal. -/
theorem sum_momentProposal_eq_lambda_div_max {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (e : G.E) :
    (∑ c, G.momentProposal F color e c) =
      G.momentLambda F color e / max 1 (G.momentLambda F color e) := by
  classical
  let S := G.momentCommonMissingColors F color e
  calc
    (∑ c, G.momentProposal F color e c) =
        ∑ _c ∈ S,
          (((q : ℝ) /
            (G.momentMissingSize F color (G.fst e) *
              G.momentMissingSize F color (G.snd e))) /
            max 1 (G.momentLambda F color e)) := by
      simp [momentProposal, S]
    _ = (S.card : ℝ) *
          (((q : ℝ) /
            (G.momentMissingSize F color (G.fst e) *
              G.momentMissingSize F color (G.snd e))) /
            max 1 (G.momentLambda F color e)) := by simp
    _ = G.momentLambda F color e /
          max 1 (G.momentLambda F color e) := by
      unfold momentLambda
      dsimp [S]
      ring

theorem sum_momentProposal_le_one {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ v, 0 < G.momentMissingSize F color v) (e : G.E) :
    (∑ c, G.momentProposal F color e c) ≤ 1 := by
  rw [G.sum_momentProposal_eq_lambda_div_max F color e]
  exact lambda_div_max_le_one
    (G.momentLambda_nonneg F color hmissing e)

theorem one_sub_sum_momentProposal_le_abs {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ v, 0 < G.momentMissingSize F color v) (e : G.E) :
    1 - ∑ c, G.momentProposal F color e c ≤
      |G.momentLambda F color e - 1| := by
  rw [G.sum_momentProposal_eq_lambda_div_max F color e]
  exact one_sub_lambda_div_max_le_abs
    (G.momentLambda_nonneg F color hmissing e)

/-- Dropping the clipping denominator can only increase one proposal
entry. -/
theorem momentProposal_le_unclipped {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ v, 0 < G.momentMissingSize F color v)
    (e : G.E) (c : Fin q) :
    G.momentProposal F color e c ≤
      (q : ℝ) /
        (G.momentMissingSize F color (G.fst e) *
          G.momentMissingSize F color (G.snd e)) := by
  unfold momentProposal
  split
  · have hbase : 0 ≤ (q : ℝ) /
        (G.momentMissingSize F color (G.fst e) *
          G.momentMissingSize F color (G.snd e)) := by
      exact div_nonneg (Nat.cast_nonneg q)
        (mul_nonneg (hmissing _).le (hmissing _).le)
    have hmax : 1 ≤ max 1 (G.momentLambda F color e) :=
      le_max_left _ _
    exact (div_le_iff₀ (by positivity : (0 : ℝ) <
      max 1 (G.momentLambda F color e))).2
        (by nlinarith)
  · exact div_nonneg (Nat.cast_nonneg q)
      (mul_nonneg (hmissing _).le (hmissing _).le)

/-! ## Vertex--color row pressure -/

/-- The denominator seen from an incident vertex is the product of its own
missing-palette size and the size at the opposite endpoint. -/
theorem momentMissingSize_mul_otherEndpoint {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    {v : G.V} {e : G.E} (hinc : G.Inc v e) :
    G.momentMissingSize F color v *
        G.momentMissingSize F color (G.kempeOtherEndpoint v e) =
      G.momentMissingSize F color (G.fst e) *
        G.momentMissingSize F color (G.snd e) := by
  rcases hinc with hfst | hsnd
  · simp [kempeOtherEndpoint, hfst]
  · have hne : G.fst e ≠ v := by
      intro hfst
      exact G.noLoop e (hfst.trans hsnd.symm)
    simp [kempeOtherEndpoint, hne, hsnd, mul_comm]

/-- A common missing color belongs to the missing palette at an incident
vertex and at the opposite endpoint. -/
theorem mem_missing_and_other_of_mem_momentCommonMissingColors {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    {v : G.V} {e : G.E} (hinc : G.Inc v e) {c : Fin q}
    (hc : c ∈ G.momentCommonMissingColors F color e) :
    c ∈ G.missingColorsAt F color v ∧
      c ∈ G.missingColorsAt F color (G.kempeOtherEndpoint v e) := by
  have hcends := Finset.mem_inter.mp hc
  rcases hinc with hfst | hsnd
  · simpa [momentCommonMissingColors, kempeOtherEndpoint, hfst] using hcends
  · have hne : G.fst e ≠ v := by
      intro hfst
      exact G.noLoop e (hfst.trans hsnd.symm)
    simpa [momentCommonMissingColors, kempeOtherEndpoint, hne, hsnd,
      and_comm] using hcends

/-- First-moment pressure at a vertex and color, looking at missing colors
at the opposite endpoints. -/
noncomputable def momentNeighborPressure {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (v : G.V) (c : Fin q) : ℝ :=
  ∑ e ∈ R,
    if G.Inc v e then
      charge e *
        (if c ∈ G.missingColorsAt F color (G.kempeOtherEndpoint v e) then
          1 / G.momentMissingSize F color (G.kempeOtherEndpoint v e)
        else 0)
    else 0

/-- Pointwise inequality behind the row-pressure bound. -/
theorem momentProposal_le_neighborPressureTerm {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ v, 0 < G.momentMissingSize F color v)
    {v : G.V} (e : G.E) (hinc : G.Inc v e) (c : Fin q) :
    G.momentProposal F color e c ≤
      (q : ℝ) / G.momentMissingSize F color v *
        (if c ∈ G.missingColorsAt F color (G.kempeOtherEndpoint v e) then
          1 / G.momentMissingSize F color (G.kempeOtherEndpoint v e)
        else 0) := by
  classical
  by_cases hc : c ∈ G.momentCommonMissingColors F color e
  · have hother :=
      (G.mem_missing_and_other_of_mem_momentCommonMissingColors
        F color hinc hc).2
    rw [if_pos hother]
    calc
      G.momentProposal F color e c ≤
          (q : ℝ) /
            (G.momentMissingSize F color (G.fst e) *
              G.momentMissingSize F color (G.snd e)) :=
        G.momentProposal_le_unclipped F color hmissing e c
      _ = (q : ℝ) /
          (G.momentMissingSize F color v *
            G.momentMissingSize F color (G.kempeOtherEndpoint v e)) := by
        rw [G.momentMissingSize_mul_otherEndpoint F color hinc]
      _ = (q : ℝ) / G.momentMissingSize F color v *
          (1 / G.momentMissingSize F color (G.kempeOtherEndpoint v e)) := by
        field_simp [ne_of_gt (hmissing v),
          ne_of_gt (hmissing (G.kempeOtherEndpoint v e))]
  · rw [show G.momentProposal F color e c = 0 by
      simp [momentProposal, hc]]
    apply mul_nonneg
    · exact div_nonneg (Nat.cast_nonneg q) (hmissing v).le
    · split
      · exact one_div_nonneg.mpr (hmissing _).le
      · exact le_rfl

/-- Every proposal row is bounded by `q / |F_v|` times its opposite-end
first-moment pressure. -/
theorem proposalChargeLoad_momentProposal_le_pressure {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ v, 0 < G.momentMissingSize F color v)
    (v : G.V) (c : Fin q) :
    G.proposalChargeLoad R charge (G.momentProposal F color) v c ≤
      (q : ℝ) / G.momentMissingSize F color v *
        G.momentNeighborPressure R charge F color v c := by
  unfold proposalChargeLoad momentNeighborPressure
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  by_cases hinc : G.Inc v e
  · simp only [hinc, if_true]
    calc
      charge e * G.momentProposal F color e c ≤
          charge e *
            ((q : ℝ) / G.momentMissingSize F color v *
              (if c ∈ G.missingColorsAt F color
                    (G.kempeOtherEndpoint v e) then
                1 / G.momentMissingSize F color
                    (G.kempeOtherEndpoint v e)
              else 0)) :=
        mul_le_mul_of_nonneg_left
          (G.momentProposal_le_neighborPressureTerm
            F color hmissing e hinc c) (hcharge e he)
      _ = (q : ℝ) / G.momentMissingSize F color v *
          (charge e *
            (if c ∈ G.missingColorsAt F color
                  (G.kempeOtherEndpoint v e) then
              1 / G.momentMissingSize F color
                  (G.kempeOtherEndpoint v e)
            else 0)) := by ring
  · simp [hinc]

/-- A pressure estimate centered at the uniform value gives the row bound
used by `WeightedMomentPaletteMixing`. -/
theorem proposalChargeLoad_momentProposal_le_uniform_add {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ v, 0 < G.momentMissingSize F color v)
    (hq : 0 < q) (v : G.V) (c : Fin q) {delta : ℝ}
    (hpressure :
      G.momentNeighborPressure R charge F color v c ≤
        G.restrictedCharge R charge v / q + delta) :
    G.proposalChargeLoad R charge (G.momentProposal F color) v c ≤
      G.restrictedCharge R charge v /
          G.momentMissingSize F color v +
        (q : ℝ) / G.momentMissingSize F color v * delta := by
  have hfactor : 0 ≤ (q : ℝ) / G.momentMissingSize F color v := by
    exact div_nonneg (Nat.cast_nonneg q) (hmissing v).le
  have hrow := G.proposalChargeLoad_momentProposal_le_pressure
    R charge F color hcharge hmissing v c
  calc
    _ ≤ (q : ℝ) / G.momentMissingSize F color v *
          G.momentNeighborPressure R charge F color v c := hrow
    _ ≤ (q : ℝ) / G.momentMissingSize F color v *
          (G.restrictedCharge R charge v / q + delta) :=
      mul_le_mul_of_nonneg_left hpressure hfactor
    _ = G.restrictedCharge R charge v /
          G.momentMissingSize F color v +
        (q : ℝ) / G.momentMissingSize F color v * delta := by
      have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
      field_simp [hqreal, ne_of_gt (hmissing v)]

/-! ## Diffuseness from linear palette sizes -/

theorem div_mul_div_le_linear_diffuse
    {K alpha C n fu fv : ℝ}
    (hK0 : 0 ≤ K) (halpha : 0 < alpha) (hC : 0 < C) (hn : 0 < n)
    (hK : K ≤ C * n) (hfu : alpha * n ≤ fu)
    (hfv : alpha * n ≤ fv) :
    K / (fu * fv) ≤ C / (alpha ^ 2 * n) := by
  have hfu0 : 0 < fu := lt_of_lt_of_le (mul_pos halpha hn) hfu
  have hfv0 : 0 < fv := lt_of_lt_of_le (mul_pos halpha hn) hfv
  have hden0 : 0 < alpha ^ 2 * n := by positivity
  rw [div_le_div_iff₀ (mul_pos hfu0 hfv0) hden0]
  have hprod : alpha ^ 2 * n ^ 2 ≤ fu * fv := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hfu) (sub_nonneg.mpr hfv)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hK) hden0.le,
    mul_nonneg hC.le (sub_nonneg.mpr hprod)]

theorem momentProposal_le_linear_diffuse {q n : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (alpha C : ℝ) (halpha : 0 < alpha) (hC : 0 < C) (hn : 0 < n)
    (hmissing : ∀ v, alpha * n ≤ G.momentMissingSize F color v)
    (hpalette : (q : ℝ) ≤ C * n) (e : G.E) (c : Fin q) :
    G.momentProposal F color e c ≤ C / (alpha ^ 2 * n) := by
  have hmissingPos : ∀ v, 0 < G.momentMissingSize F color v := by
    intro v
    exact lt_of_lt_of_le (mul_pos halpha (by exact_mod_cast hn)) (hmissing v)
  exact (G.momentProposal_le_unclipped F color hmissingPos e c).trans
    (div_mul_div_le_linear_diffuse (K := (q : ℝ))
      (fu := G.momentMissingSize F color (G.fst e))
      (fv := G.momentMissingSize F color (G.snd e))
      (n := n) (Nat.cast_nonneg q) halpha hC (by exact_mod_cast hn)
      hpalette (hmissing _) (hmissing _))

/-! ## Weighted Cauchy--Schwarz and uncovered charge -/

/-- Weighted Cauchy--Schwarz with an absolute error. -/
theorem weighted_abs_error_sq_le
    {I : Type*} [Fintype I]
    (S : Finset I) (weight error : I → ℝ)
    (hweight : ∀ i ∈ S, 0 ≤ weight i) :
    (∑ i ∈ S, weight i * |error i|) ^ 2 ≤
      (∑ i ∈ S, weight i) *
        ∑ i ∈ S, weight i * (error i) ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    (s := S)
    (r := fun i ↦ weight i * |error i|)
    (f := weight)
    (g := fun i ↦ weight i * (error i) ^ 2)
  · exact hweight
  · intro i hi
    exact mul_nonneg (hweight i hi) (sq_nonneg _)
  · intro i hi
    rw [mul_pow, sq_abs]
    ring

/-- Absolute lambda error charged at one vertex. -/
noncomputable def momentAbsoluteError {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (v : G.V) : ℝ :=
  ∑ e ∈ R,
    if G.Inc v e then
      charge e * |G.momentLambda F color e - 1| else 0

/-- Squared lambda error charged at one vertex. -/
noncomputable def momentSquaredError {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (v : G.V) : ℝ :=
  ∑ e ∈ R,
    if G.Inc v e then
      charge e * (G.momentLambda F color e - 1) ^ 2 else 0

theorem momentAbsoluteError_sq_le {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e) (v : G.V) :
    (G.momentAbsoluteError R charge F color v) ^ 2 ≤
      G.restrictedCharge R charge v *
        G.momentSquaredError R charge F color v := by
  let w : G.E → ℝ := fun e ↦ if G.Inc v e then charge e else 0
  have hw : ∀ e ∈ R, 0 ≤ w e := by
    intro e he
    dsimp [w]
    split
    · exact hcharge e he
    · exact le_rfl
  have hcs := weighted_abs_error_sq_le R w
    (fun e ↦ G.momentLambda F color e - 1) hw
  simpa only [momentAbsoluteError, momentSquaredError, restrictedCharge,
    w, ite_mul, zero_mul] using hcs

/-- A bound on weighted squared error gives the familiar square-root bound
on weighted absolute error. -/
theorem momentAbsoluteError_le_sqrt {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e) (v : G.V)
    {W sigma : ℝ} (hW0 : 0 ≤ W) (hsigma0 : 0 ≤ sigma)
    (hW : G.restrictedCharge R charge v ≤ W)
    (hsigma : G.momentSquaredError R charge F color v ≤ sigma) :
    G.momentAbsoluteError R charge F color v ≤ Real.sqrt (W * sigma) := by
  apply Real.le_sqrt_of_sq_le
  calc
    (G.momentAbsoluteError R charge F color v) ^ 2 ≤
        G.restrictedCharge R charge v *
          G.momentSquaredError R charge F color v :=
      G.momentAbsoluteError_sq_le R charge F color hcharge v
    _ ≤ W * sigma := by
      apply mul_le_mul hW hsigma
      · exact Finset.sum_nonneg fun e _he ↦ by
          split
          · exact mul_nonneg (hcharge e (by assumption)) (sq_nonneg _)
          · exact le_rfl
      · exact hW0

/-- The clipped proposal leaves no more charge uncovered than the absolute
lambda error. -/
theorem uncoveredProposalCharge_momentProposal_le_absoluteError {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ v, 0 < G.momentMissingSize F color v) (v : G.V) :
    G.uncoveredProposalCharge R charge
        (G.momentProposal F color) v ≤
      G.momentAbsoluteError R charge F color v := by
  unfold uncoveredProposalCharge momentAbsoluteError
  apply Finset.sum_le_sum
  intro e he
  by_cases hinc : G.Inc v e
  · simp only [hinc, if_true]
    exact mul_le_mul_of_nonneg_left
      (G.one_sub_sum_momentProposal_le_abs F color hmissing e)
      (hcharge e he)
  · simp [hinc]

theorem uncoveredProposalCharge_momentProposal_le_sqrt {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ v, 0 < G.momentMissingSize F color v)
    (v : G.V) {W sigma : ℝ} (hW0 : 0 ≤ W) (hsigma0 : 0 ≤ sigma)
    (hW : G.restrictedCharge R charge v ≤ W)
    (hsigma : G.momentSquaredError R charge F color v ≤ sigma) :
    G.uncoveredProposalCharge R charge
        (G.momentProposal F color) v ≤ Real.sqrt (W * sigma) :=
  (G.uncoveredProposalCharge_momentProposal_le_absoluteError
    R charge F color hcharge hmissing v).trans
    (G.momentAbsoluteError_le_sqrt R charge F color hcharge v
      hW0 hsigma0 hW hsigma)

/-- Convenient epsilon form: squared error at most `eps^2 n` and charge at
most `n` leave at most `eps n` uncovered. -/
theorem uncoveredProposalCharge_momentProposal_le_eps_mul {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ v, 0 < G.momentMissingSize F color v)
    (v : G.V) {n eps : ℝ} (hn : 0 ≤ n) (heps : 0 ≤ eps)
    (hW : G.restrictedCharge R charge v ≤ n)
    (hsigma : G.momentSquaredError R charge F color v ≤ eps ^ 2 * n) :
    G.uncoveredProposalCharge R charge
        (G.momentProposal F color) v ≤ eps * n := by
  have hsqrt := G.uncoveredProposalCharge_momentProposal_le_sqrt
    R charge F color hcharge hmissing v hn
      (mul_nonneg (sq_nonneg eps) hn) hW hsigma
  calc
    _ ≤ Real.sqrt (n * (eps ^ 2 * n)) := hsqrt
    _ = eps * n := by
      rw [show n * (eps ^ 2 * n) = (eps * n) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg heps hn)]

end WeightedMultigraph
end WeightedEdgeColoring
