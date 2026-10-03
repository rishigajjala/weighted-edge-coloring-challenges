import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileBlockCapacityVarianceSelection

/-!
# Fixed-multiplicity asymptotics for the color-dependent block selector

The fixed endpoint multiplicity scales candidate capacity and both variance
influence families.  The estimates below absorb that fixed factor into the
choice of block width and the sublinear deviation threshold.
-/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

open scoped BigOperators

def colorDependentBlockCombinedColumnCoefficient
    (k : ℕ) (β q r : ℝ) : ℝ :=
  k * extendedProfileStateBound β q r *
      (explicitLargeSlotBound β q r / β + 1) +
    (extendedProfileStateBound β q r : ℝ) ^ k + 1

theorem colorDependentBlockCombinedColumnCoefficient_nonneg
    (k : ℕ) {β q r : ℝ} (hβ : 0 < β) :
    0 ≤ colorDependentBlockCombinedColumnCoefficient k β q r := by
  unfold colorDependentBlockCombinedColumnCoefficient
  positivity

theorem colorDependentBlockCombinedColumnBound_le_linear
    {β q r : ℝ} (k : ℕ) (hβ : 0 < β) {n : ℕ} (hn : 1 ≤ n) :
    colorDependentBlockCombinedColumnBound n k β q r ≤
      colorDependentBlockCombinedColumnCoefficient k β q r * n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold colorDependentBlockCombinedColumnBound
    colorDependentCandidatePerColorColumnBound
    colorDependentBlockSparseVarianceColumnBound
    colorDependentBlockCombinedColumnCoefficient
  have hslot : 0 ≤ (explicitLargeSlotBound β q r : ℝ) / β + 1 := by
    positivity
  have hstate : 0 ≤ (extendedProfileStateBound β q r : ℝ) := by positivity
  have hpow : 0 ≤ (extendedProfileStateBound β q r : ℝ) ^ k := by positivity
  nlinarith

theorem colorDependentBlockNaturalDeviation_sublinear
    {β q r : ℝ} (k : ℕ) (hβ : 0 < β) (delta : ℝ) :
    0 < delta → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      FinitePartialResamplingNumerics.packingDeviation n
          (colorDependentBlockCombinedColumnBound n k β q r) ≤ delta * n := by
  intro hdelta
  obtain ⟨N, hN⟩ :=
    FinitePartialResamplingNumerics.packingDeviation_sublinear_of_linear_row_polynomial_column
      (A := 1) (C0 := colorDependentBlockCombinedColumnCoefficient k β q r)
      (by norm_num) (colorDependentBlockCombinedColumnCoefficient_nonneg k hβ)
      1 delta hdelta
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := (Nat.le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (Nat.le_max_right _ _).trans hn
  apply hN n hnN n (colorDependentBlockCombinedColumnBound n k β q r)
  · positivity
  · unfold colorDependentBlockCombinedColumnBound
      colorDependentCandidatePerColorColumnBound
      colorDependentBlockSparseVarianceColumnBound
    positivity
  · norm_num
  · simpa using colorDependentBlockCombinedColumnBound_le_linear k hβ hn1

/-- A convenient upper envelope for the selector's quadratic error.  The
factor `4*k+16` is the result of using `B*k ≤ 4*n` in the self and pair
variance terms. -/
def colorDependentBlockNaturalSigma
    (mult : ℕ) (B n k : ℕ)
    (rho s omega β q r C0 : ℝ) : ℝ :=
  let D := FinitePartialResamplingNumerics.packingDeviation n
    (colorDependentBlockCombinedColumnBound n k β q r)
  let T := 2 * colorDependentCandidateCapacityScale rho s omega β q r C0 +
    rho * s * C0
  B * colorDependentBlockSharpVarianceMean n rho s omega β q r C0 +
    mult * (4 * k + 16) * T ^ 2 * D

/-- The exact variance expression returned by the selector is bounded by
`colorDependentBlockNaturalSigma` under the product-palette size bound. -/
theorem colorDependentBlockVarianceExpression_le_naturalSigma
    {mult B n k : ℕ} {rho s omega β q r C0 : ℝ}
    (hβ : 0 < β) (hn : 0 < n) (hk : 0 < k) (hpalette : B * k ≤ 4 * n) :
    let D := FinitePartialResamplingNumerics.packingDeviation n
      (colorDependentBlockCombinedColumnBound n k β q r)
    B * (colorDependentBlockSharpVarianceMean n rho s omega β q r C0 +
        mult * colorDependentBlockVarianceSelfScale n k rho s omega β q r C0 * D +
        B * (mult * colorDependentBlockVariancePairScale n k rho s omega β q r C0) * D) ≤
      colorDependentBlockNaturalSigma mult B n k rho s omega β q r C0 := by
  dsimp only
  let A := colorDependentCandidateCapacityScale rho s omega β q r C0
  let T := 2 * A + rho * s * C0
  let D := FinitePartialResamplingNumerics.packingDeviation n
    (colorDependentBlockCombinedColumnBound n k β q r)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hBk : (B : ℝ) * k ≤ 4 * n := by exact_mod_cast hpalette
  have hD : 0 ≤ D := by
    unfold D FinitePartialResamplingNumerics.packingDeviation
    have hC : 0 ≤ colorDependentBlockCombinedColumnBound n k β q r := by
      unfold colorDependentBlockCombinedColumnBound
        colorDependentCandidatePerColorColumnBound
        colorDependentBlockSparseVarianceColumnBound
      positivity
    have := FinitePartialResamplingNumerics.packingLog_nonneg hC
    positivity
  have hmult : 0 ≤ (mult : ℝ) := by positivity
  have hpair : colorDependentBlockVariancePairScale n k rho s omega β q r C0 =
      ((k : ℝ) / n * T) ^ 2 := by
    unfold colorDependentBlockVariancePairScale colorDependentBlockOptionUpper
      colorDependentBlockTargetUpper T A
    field_simp [hnR.ne']
    <;> ring
  have hself : colorDependentBlockVarianceSelfScale n k rho s omega β q r C0 =
      n * (((k : ℝ) / n * T) ^ 2) := by
    rw [colorDependentBlockVarianceSelfScale, hpair]
  rw [hpair, hself]
  have hratio : (B : ℝ) * k / n ≤ 4 := by
    exact (div_le_iff₀ hnR).2 (by simpa using hBk)
  have hratio0 : 0 ≤ (B : ℝ) * k / n := by positivity
  have hQ : 0 ≤ T ^ 2 * D := mul_nonneg (sq_nonneg T) hD
  have hselfBound :
      (B : ℝ) * mult * (n * ((k : ℝ) / n * T) ^ 2) * D ≤
        (mult : ℝ) * (4 * k) * T ^ 2 * D := by
    calc
      (B : ℝ) * mult * (n * ((k : ℝ) / n * T) ^ 2) * D =
          (mult : ℝ) * (((B : ℝ) * k / n) * k) * (T ^ 2 * D) := by
        field_simp [hnR.ne']
        <;> ring
      _ ≤ (mult : ℝ) * (4 * k) * (T ^ 2 * D) := by
        gcongr
      _ = (mult : ℝ) * (4 * k) * T ^ 2 * D := by ring
  have hpairBound :
      (B : ℝ) * (B * (mult * (((k : ℝ) / n * T) ^ 2)) * D) ≤
        (mult : ℝ) * 16 * T ^ 2 * D := by
    have hsquare : (((B : ℝ) * k / n) ^ 2) ≤ 16 := by
      nlinarith [sq_nonneg (4 - (B : ℝ) * k / n)]
    calc
      (B : ℝ) * (B * (mult * (((k : ℝ) / n * T) ^ 2)) * D) =
          (mult : ℝ) * (((B : ℝ) * k / n) ^ 2) * (T ^ 2 * D) := by
        field_simp [hnR.ne']
        <;> ring
      _ ≤ (mult : ℝ) * 16 * (T ^ 2 * D) := by
        gcongr
      _ = (mult : ℝ) * 16 * T ^ 2 * D := by ring
  unfold colorDependentBlockNaturalSigma
  dsimp only
  calc
    (B : ℝ) * (colorDependentBlockSharpVarianceMean n rho s omega β q r C0 +
        mult * (n * ((k : ℝ) / n * T) ^ 2) * D +
        B * (mult * ((k : ℝ) / n * T) ^ 2) * D) =
      B * colorDependentBlockSharpVarianceMean n rho s omega β q r C0 +
        (B * mult * (n * ((k : ℝ) / n * T) ^ 2) * D) +
        B * (B * (mult * ((k : ℝ) / n * T) ^ 2) * D) := by ring
    _ ≤ B * colorDependentBlockSharpVarianceMean n rho s omega β q r C0 +
        (mult * (4 * k) * T ^ 2 * D) +
        mult * 16 * T ^ 2 * D := by
      gcongr
    _ = B * colorDependentBlockSharpVarianceMean n rho s omega β q r C0 +
        mult * (4 * k + 16) * T ^ 2 * D := by ring

private theorem sharpVarianceMean_eq
    {n : ℕ} {rho s omega β q r C0 : ℝ} (hn : 0 < n) :
    colorDependentBlockSharpVarianceMean n rho s omega β q r C0 =
      2 * colorDependentCandidateCapacityScale rho s omega β q r C0 * rho * s := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold colorDependentBlockSharpVarianceMean colorDependentBlockOptionUpper
  field_simp [hnR.ne']
  <;> ring

theorem exists_colorDependentBlockNaturalScales_small
    {mult : ℕ} {β s omega rho C0 q r : ℝ}
    (hmult : 0 < mult)
    (hβ : 0 < β) (hs : 0 < s) (homega : 0 < omega)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ k N : ℕ, 4 ≤ k ∧ ∀ n B : ℕ, N ≤ n → B * k ≤ 4 * n →
      colorDependentBlockNaturalSigma mult B n k rho s omega β q r C0 ≤
          eps ^ 2 * n ∧
      (mult : ℝ) * colorDependentCandidateCapacityScale rho s omega β q r C0 / n *
          FinitePartialResamplingNumerics.packingDeviation n
            (colorDependentBlockCombinedColumnBound n k β q r) ≤ eps := by
  let A := colorDependentCandidateCapacityScale rho s omega β q r C0
  let M := 2 * A * rho * s
  have hA : 0 < A := colorDependentCandidateCapacityScale_pos hrho hs hC0 homega
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨k0, hk0⟩ := exists_nat_gt (8 * M / eps ^ 2)
  let k := max 4 k0
  have hk4 : 4 ≤ k := Nat.le_max_left _ _
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk4
  have hklarge : 8 * M / eps ^ 2 < (k : ℝ) :=
    hk0.trans_le (by exact_mod_cast Nat.le_max_right 4 k0)
  let T := 2 * A + rho * s * C0
  let V : ℝ := (mult : ℝ) * (4 * (k : ℝ) + 16) * T ^ 2
  have hmultR : (0 : ℝ) < mult := by exact_mod_cast hmult
  have hT : 0 < T := by dsimp [T]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  let delta := min (eps / ((mult : ℝ) * A)) (eps ^ 2 / (2 * V))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (div_pos heps (mul_pos hmultR hA))
      (div_pos (sq_pos_of_pos heps) (mul_pos (by norm_num) hV))
  obtain ⟨N0, hN0⟩ := colorDependentBlockNaturalDeviation_sublinear
    k hβ delta hdelta
  refine ⟨k, max N0 1, hk4, ?_⟩
  intro n B hn hpalette
  have hnN : N0 ≤ n := (Nat.le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (Nat.le_max_right _ _).trans hn
  have hn0 : 0 < n := hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let D := FinitePartialResamplingNumerics.packingDeviation n
    (colorDependentBlockCombinedColumnBound n k β q r)
  have hD0 : 0 ≤ D := by
    unfold D FinitePartialResamplingNumerics.packingDeviation
    have hC : 0 ≤ colorDependentBlockCombinedColumnBound n k β q r := by
      unfold colorDependentBlockCombinedColumnBound
        colorDependentCandidatePerColorColumnBound
        colorDependentBlockSparseVarianceColumnBound
      positivity
    have := FinitePartialResamplingNumerics.packingLog_nonneg hC
    positivity
  have hD : D ≤ delta * n := hN0 n hnN
  have hBk : (B : ℝ) * k ≤ 4 * n := by exact_mod_cast hpalette
  have hmean : colorDependentBlockSharpVarianceMean n rho s omega β q r C0 = M := by
    simpa [M, A] using (sharpVarianceMean_eq (rho := rho) (s := s)
      (omega := omega) (β := β) (q := q) (r := r) (C0 := C0) hn0)
  have hmeanTerm : (B : ℝ) * M ≤ eps ^ 2 / 2 * n := by
    have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
    have hkbound : 8 * M < eps ^ 2 * k := by
      apply (div_lt_iff₀ heps2).mp at hklarge
      simpa [mul_comm, mul_left_comm, mul_assoc] using hklarge
    have hBbound : (B : ℝ) ≤ 4 * n / k := by
      exact (le_div_iff₀ (by exact_mod_cast hkpos)).2 (by simpa [mul_comm] using hBk)
    calc
      (B : ℝ) * M ≤ (4 * n / k) * M :=
        mul_le_mul_of_nonneg_right hBbound hM.le
      _ = (4 * n * M) / k := by ring
      _ ≤ eps ^ 2 / 2 * n := by
        apply (div_le_iff₀ (by exact_mod_cast hkpos)).2
        nlinarith [hnR.le]
  have hdeltaCap : delta ≤ eps / ((mult : ℝ) * A) := min_le_left _ _
  have hdeltaVar : delta ≤ eps ^ 2 / (2 * V) := min_le_right _ _
  constructor
  · unfold colorDependentBlockNaturalSigma
    dsimp only
    rw [hmean]
    have hvar : V * D ≤ eps ^ 2 / 2 * n := by
      calc
        V * D ≤ V * (delta * n) := mul_le_mul_of_nonneg_left hD hV.le
        _ ≤ V * (eps ^ 2 / (2 * V) * n) := by
          gcongr
        _ = eps ^ 2 / 2 * n := by field_simp [hV.ne']
    change (B : ℝ) * M + V * D ≤ _
    nlinarith
  · have hcap : (mult : ℝ) * A * D ≤ eps * n := by
      calc
        (mult : ℝ) * A * D ≤ (mult : ℝ) * A * (delta * n) := by
          gcongr
        _ ≤ (mult : ℝ) * A * (eps / ((mult : ℝ) * A) * n) := by
          gcongr
        _ = eps * n := by field_simp [hmultR.ne', hA.ne']
    dsimp [A] at hcap ⊢
    calc
      (mult : ℝ) * colorDependentCandidateCapacityScale rho s omega β q r C0 / n * D =
          ((mult : ℝ) * colorDependentCandidateCapacityScale rho s omega β q r C0 * D) / n := by ring
      _ ≤ (eps * n) / n := div_le_div_of_nonneg_right hcap hnR.le
      _ = eps := by field_simp [hnR.ne']

end WeightedMultigraph

end

end WeightedEdgeColoring
