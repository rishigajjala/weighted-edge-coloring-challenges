import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic

/-!
# Numerical contraction in the weighted-moment pairing argument

This file isolates the linear-algebra arithmetic in the first part of the
Kempe palette-mixing proof.  A uniformly random perfect pairing, followed by
independent exchanges inside its pairs, has three transition coefficients on
unordered pairs: `pairP K`, `pairQ K`, and `pairR K`.  The two nonconstant
eigenvalues are recorded below and proved to be at most one half.

The statements are deliberately independent of the graph and of the
realization of a pairing by Kempe switches.  Thus the structural switch file
only has to prove that its finite average has these coefficients.  The final
section gives the finite deterministic iteration principle which turns an
average one-stage contraction into one fixed short list of stages.
-/

namespace WeightedEdgeColoring.WeightedMomentPairingContraction

open scoped BigOperators

noncomputable section

/-- The contraction factor for one-color lists. -/
def singleEigenvalue (K : ℕ) : ℝ :=
  ((K : ℝ) - 2) / (2 * ((K : ℝ) - 1))

/-- Diagonal entry of the averaged two-color operator. -/
def pairP (K : ℕ) : ℝ :=
  ((K : ℝ) + 2) / (4 * ((K : ℝ) - 1))

/-- Entry between two unordered pairs meeting in one color. -/
def pairQ (K : ℕ) : ℝ :=
  1 / (4 * ((K : ℝ) - 1))

/-- Entry between two disjoint unordered pairs. -/
def pairR (K : ℕ) : ℝ :=
  1 / (2 * ((K : ℝ) - 1) * ((K : ℝ) - 3))

/-- Eigenvalue on arrays of the form `b i + b j` with `sum b = 0`. -/
def pairVertexEigenvalue (K : ℕ) : ℝ :=
  pairP K + ((K : ℝ) - 4) * pairQ K -
    ((K : ℝ) - 3) * pairR K

/-- Eigenvalue on symmetric arrays all of whose row sums vanish. -/
def pairRowZeroEigenvalue (K : ℕ) : ℝ :=
  pairP K - 2 * pairQ K + pairR K

theorem pairP_nonneg {K : ℕ} (hK : 4 ≤ K) : 0 ≤ pairP K := by
  have hKreal : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  unfold pairP
  apply div_nonneg <;> nlinarith

theorem pairQ_nonneg {K : ℕ} (hK : 4 ≤ K) : 0 ≤ pairQ K := by
  have hKreal : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  unfold pairQ
  apply div_nonneg <;> nlinarith

theorem pairR_nonneg {K : ℕ} (hK : 4 ≤ K) : 0 ≤ pairR K := by
  have hKreal : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have h1 : (0 : ℝ) ≤ (K : ℝ) - 1 := by linarith
  have h3 : (0 : ℝ) ≤ (K : ℝ) - 3 := by linarith
  unfold pairR
  exact div_nonneg (by norm_num)
    (mul_nonneg (mul_nonneg (by norm_num) h1) h3)

/-- One row of the averaged unordered-pair kernel has one diagonal entry,
`2(K-2)` entries meeting it in one color, and `(K-2)(K-3)/2` disjoint
entries.  The manuscript coefficients therefore have row sum one. -/
theorem pairKernel_rowSum {K : ℕ} (hK : 4 ≤ K) :
    pairP K + (2 * ((K : ℝ) - 2)) * pairQ K +
      (((K : ℝ) - 2) * ((K : ℝ) - 3) / 2) * pairR K = 1 := by
  have hKreal : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have h1 : ((K : ℝ) - 1) ≠ 0 := by
    exact ne_of_gt (by linarith)
  have h3 : ((K : ℝ) - 3) ≠ 0 := by
    exact ne_of_gt (by linarith)
  unfold pairP pairQ pairR
  field_simp
  ring

theorem singleEigenvalue_eq {K : ℕ} (hK : 2 ≤ K) :
    singleEigenvalue K = ((K : ℝ) - 2) / (2 * ((K : ℝ) - 1)) := by
  rfl

theorem singleEigenvalue_nonneg {K : ℕ} (hK : 2 ≤ K) :
    0 ≤ singleEigenvalue K := by
  have hKreal : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  unfold singleEigenvalue
  apply div_nonneg <;> nlinarith

theorem singleEigenvalue_le_half {K : ℕ} (hK : 2 ≤ K) :
    singleEigenvalue K ≤ 1 / 2 := by
  have hKreal : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hden : (0 : ℝ) < (K : ℝ) - 1 := by linarith
  unfold singleEigenvalue
  rw [div_le_iff₀ (mul_pos (by norm_num) hden)]
  nlinarith

/-- Exact one-color quadratic identity.  If a symmetric averaging kernel has
diagonal coefficient `1/2` and every off-diagonal coefficient
`1/(2(K-1))`, its quadratic form on a zero-sum vector is
`singleEigenvalue K` times the squared norm. -/
theorem singleKernel_quadratic_of_sum_zero {Color : Type*}
    [Fintype Color] {h : Color → ℝ}
    (hcard : 2 ≤ Fintype.card Color) (hsum : ∑ i, h i = 0) :
    (1 / 2 : ℝ) * (∑ i, (h i) ^ 2) +
        1 / (2 * ((Fintype.card Color : ℝ) - 1)) *
          ((∑ i, h i) ^ 2 - ∑ i, (h i) ^ 2) =
      singleEigenvalue (Fintype.card Color) * ∑ i, (h i) ^ 2 := by
  have hcardReal : (2 : ℝ) ≤ (Fintype.card Color : ℝ) := by
    exact_mod_cast hcard
  have hden : ((Fintype.card Color : ℝ) - 1) ≠ 0 := by
    exact ne_of_gt (by linarith)
  rw [hsum]
  unfold singleEigenvalue
  field_simp
  ring

theorem pairVertexEigenvalue_eq {K : ℕ} (hK : 4 ≤ K) :
    pairVertexEigenvalue K = singleEigenvalue K := by
  have hKreal : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have h1 : ((K : ℝ) - 1) ≠ 0 := by
    exact ne_of_gt (by linarith)
  have h3 : ((K : ℝ) - 3) ≠ 0 := by
    exact ne_of_gt (by linarith)
  unfold pairVertexEigenvalue pairP pairQ pairR singleEigenvalue
  field_simp
  ring

theorem pairRowZeroEigenvalue_eq {K : ℕ} (hK : 4 ≤ K) :
    pairRowZeroEigenvalue K =
      ((K : ℝ) - 2) / (4 * ((K : ℝ) - 3)) := by
  have hKreal : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have h1 : ((K : ℝ) - 1) ≠ 0 := by
    exact ne_of_gt (by linarith)
  have h3 : ((K : ℝ) - 3) ≠ 0 := by
    exact ne_of_gt (by linarith)
  unfold pairRowZeroEigenvalue pairP pairQ pairR
  field_simp
  ring

theorem pairVertexEigenvalue_nonneg {K : ℕ} (hK : 4 ≤ K) :
    0 ≤ pairVertexEigenvalue K := by
  rw [pairVertexEigenvalue_eq hK]
  exact singleEigenvalue_nonneg (by omega)

theorem pairVertexEigenvalue_le_half {K : ℕ} (hK : 4 ≤ K) :
    pairVertexEigenvalue K ≤ 1 / 2 := by
  rw [pairVertexEigenvalue_eq hK]
  exact singleEigenvalue_le_half (by omega)

theorem pairRowZeroEigenvalue_nonneg {K : ℕ} (hK : 4 ≤ K) :
    0 ≤ pairRowZeroEigenvalue K := by
  rw [pairRowZeroEigenvalue_eq hK]
  have hKreal : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  apply div_nonneg <;> nlinarith

theorem pairRowZeroEigenvalue_le_half {K : ℕ} (hK : 4 ≤ K) :
    pairRowZeroEigenvalue K ≤ 1 / 2 := by
  rw [pairRowZeroEigenvalue_eq hK]
  have hKreal : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hden : (0 : ℝ) < (K : ℝ) - 3 := by linarith
  rw [div_le_iff₀ (mul_pos (by norm_num) hden)]
  nlinarith

/-! ## The two invariant subspaces -/

/-- On the direct sum of the vertex and row-zero subspaces, the averaged
two-color energy contracts by one half.  `vertexEnergy` and `rowZeroEnergy`
are the squared norms of the two orthogonal components. -/
theorem pairEnergy_le_half_of_orthogonal_split {K : ℕ}
    (hK : 4 ≤ K) {vertexEnergy rowZeroEnergy : ℝ}
    (hvertex : 0 ≤ vertexEnergy) (hrow : 0 ≤ rowZeroEnergy) :
    pairVertexEigenvalue K * vertexEnergy +
        pairRowZeroEigenvalue K * rowZeroEnergy ≤
      (vertexEnergy + rowZeroEnergy) / 2 := by
  have hv := mul_le_mul_of_nonneg_right
    (pairVertexEigenvalue_le_half hK) hvertex
  have hr := mul_le_mul_of_nonneg_right
    (pairRowZeroEigenvalue_le_half hK) hrow
  linarith

/-- The exact quadratic-form reduction used for a symmetric off-diagonal
array.  If `E = E_vertex + E_rowZero`, the two averaged eigenspaces give the
displayed contraction.  This form is convenient for a later file proving the
orthogonal decomposition by finite sums. -/
theorem pairEnergy_le_half {K : ℕ} (hK : 4 ≤ K)
    {energy vertexEnergy rowZeroEnergy averagedEnergy : ℝ}
    (hvertex : 0 ≤ vertexEnergy) (hrow : 0 ≤ rowZeroEnergy)
    (hsplit : energy = vertexEnergy + rowZeroEnergy)
    (haverage : averagedEnergy =
      pairVertexEigenvalue K * vertexEnergy +
        pairRowZeroEigenvalue K * rowZeroEnergy) :
    averagedEnergy ≤ energy / 2 := by
  rw [hsplit, haverage]
  exact pairEnergy_le_half_of_orthogonal_split hK hvertex hrow

/-! ## Deterministically choosing contracting stages -/

variable {State Choice : Type*}
variable [Fintype Choice] [Nonempty Choice]

/-- If the average next energy is at most half of the present energy, one
choice attains that bound.  No probability space is left in the conclusion. -/
theorem exists_choice_contracts
    (energy : State → ℝ) (step : Choice → State → State)
    (x : State)
    (haverage :
      (∑ choice : Choice, energy (step choice x)) /
          (Fintype.card Choice : ℝ) ≤ energy x / 2) :
    ∃ choice : Choice, energy (step choice x) ≤ energy x / 2 := by
  classical
  have hcard : (0 : ℝ) < Fintype.card Choice := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Choice)
  have hsum :
      (∑ choice : Choice, energy (step choice x)) ≤
        ∑ _choice : Choice, energy x / 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [div_le_iff₀ hcard] at haverage
    simpa [mul_comm] using haverage
  obtain ⟨choice, _hmem, hchoice⟩ :=
    Finset.exists_le_of_sum_le
      (s := (Finset.univ : Finset Choice)) Finset.univ_nonempty hsum
  exact ⟨choice, by simpa using hchoice⟩

/-- Apply a finite list of stage choices, in list order. -/
def applyChoiceList (step : Choice → State → State) :
    List Choice → State → State
  | [], x => x
  | choice :: choices, x =>
      applyChoiceList step choices (step choice x)

@[simp] theorem applyChoiceList_nil
    (step : Choice → State → State) (x : State) :
    applyChoiceList step [] x = x := rfl

@[simp] theorem applyChoiceList_cons
    (step : Choice → State → State) (choice : Choice)
    (choices : List Choice) (x : State) :
    applyChoiceList step (choice :: choices) x =
      applyChoiceList step choices (step choice x) := rfl

/-- A one-stage average contraction can be derandomized successively.  After
`s` stages one fixed list has energy at most `2^{-s}` times the initial
energy. -/
theorem exists_choiceList_contracts
    (energy : State → ℝ) (step : Choice → State → State)
    (haverage : ∀ x,
      (∑ choice : Choice, energy (step choice x)) /
          (Fintype.card Choice : ℝ) ≤ energy x / 2)
    (s : ℕ) (x : State) :
    ∃ choices : List Choice,
      choices.length = s ∧
      energy (applyChoiceList step choices x) ≤
        (1 / 2 : ℝ) ^ s * energy x := by
  induction s generalizing x with
  | zero =>
      exact ⟨[], rfl, by simp⟩
  | succ s ih =>
      obtain ⟨choice, hchoice⟩ :=
        exists_choice_contracts energy step x (haverage x)
      obtain ⟨choices, hlength, henergy⟩ := ih (step choice x)
      refine ⟨choice :: choices, by simp [hlength], ?_⟩
      simp only [applyChoiceList_cons, Nat.cast_ofNat]
      calc
        energy (applyChoiceList step choices (step choice x)) ≤
            (1 / 2 : ℝ) ^ s * energy (step choice x) := henergy
        _ ≤ (1 / 2 : ℝ) ^ s * (energy x / 2) := by
          exact mul_le_mul_of_nonneg_left hchoice (by positivity)
        _ = (1 / 2 : ℝ) ^ (Nat.succ s) * energy x := by
          rw [pow_succ]
          ring

end

end WeightedEdgeColoring.WeightedMomentPairingContraction
