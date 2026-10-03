import WeightedEdgeColoring.MultigraphExtendedProfileBlockPackingSelection
import WeightedEdgeColoring.MultigraphSelectedProfileTinyGlobal

/-!
# Candidate block-variance rows

Whole-edge option masses are clipped edge by edge.  To bound the clipping
loss, colours are grouped into fixed blocks and the weighted square of each
block error is selected simultaneously.  A candidate row fixes the complete
state block at its centre and reads the block state at the opposite endpoint.
Simplicity makes this an additive source--row coefficient.

This file gives the concrete rows and the deterministic two-level
conditioning algebra.  Pointwise envelopes and asymptotic choices of the
two normalization scales are deliberately separate.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- Total unnormalised option mass in one colour coordinate of a block. -/
def extendedProfileBlockCoordinateOptionMass
    (rho omega : ℝ) (e : G.E)
    (fstCode sndCode : ExtendedProfilePackedBlockState k β q r)
    (j : Fin k) : ℝ :=
  (∑ i, ∑ l,
      G.extendedProfileProductOptionMass R0 rho omega e
        (G.decodeExtendedProfileBlock R0 (G.fst e) fstCode j)
        (G.decodeExtendedProfileBlock R0 (G.snd e) sndCode j) i l) +
    G.extendedProfileTinyProductOptionMass R0 rho omega e
      (G.decodeExtendedProfileBlock R0 (G.fst e) fstCode j)
      (G.decodeExtendedProfileBlock R0 (G.snd e) sndCode j)

/-- Total option mass of one edge in one `k`-colour block. -/
def extendedProfileBlockOptionMass
    (rho omega : ℝ) (e : G.E)
    (fstCode sndCode : ExtendedProfilePackedBlockState k β q r) : ℝ :=
  ∑ j, G.extendedProfileBlockCoordinateOptionMass R0 rho omega e
    fstCode sndCode j

/-- The deterministic target mass of one full block.  Since the palette has
`B*k` colours, the expectation of each coordinate is `rho*s/(B*k)` and the
block target is `rho*s/B`. -/
def extendedProfileBlockTarget (rho s : ℝ) (B : ℕ) : ℝ :=
  rho * s / B

/-- Weighted squared block error on one edge. -/
def extendedProfileBlockVariance
    (rho omega : ℝ) (e : G.E)
    (fstCode sndCode : ExtendedProfilePackedBlockState k β q r) : ℝ :=
  G.weight e *
    (G.extendedProfileBlockOptionMass R0 rho omega e fstCode sndCode -
      extendedProfileBlockTarget rho s B) ^ 2

theorem extendedProfileBlockVariance_nonneg
    (rho omega : ℝ) (e : G.E)
    (fstCode sndCode : ExtendedProfilePackedBlockState k β q r) :
    0 ≤ G.extendedProfileBlockVariance R0 rho omega e fstCode sndCode := by
  exact mul_nonneg (G.weight_nonneg e) (sq_nonneg _)

/-- A block-variance row fixes a centre, a block, and the candidate block
state at that centre. -/
abbrev ExtendedProfileBlockVarianceCandidateRow :=
  G.V × Fin B × ExtendedProfilePackedBlockState k β q r

/-- Contribution of one edge to a candidate variance row. -/
def extendedProfileBlockVarianceCandidateEdgeUse
    (rho omega : ℝ) (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (e : G.E)
    (row : G.ExtendedProfileBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) : ℝ :=
  if source.2 = row.2.1 then
    if row.1 = G.fst e ∧ source.1 = G.snd e then
      G.extendedProfileBlockVariance R0 rho omega e row.2.2 sourceCode
    else if row.1 = G.snd e ∧ source.1 = G.fst e then
      G.extendedProfileBlockVariance R0 rho omega e sourceCode row.2.2
    else 0
  else 0

/-- Raw additive variance load of the opposite block sources. -/
def rawExtendedProfileBlockVarianceCandidateUse
    (rho omega : ℝ) (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) : ℝ :=
  ∑ e, G.extendedProfileBlockVarianceCandidateEdgeUse R0 rho omega
    source sourceCode e row

/-- Candidate variance use after division by its pointwise envelope. -/
def scaledExtendedProfileBlockVarianceCandidateUse
    (rho omega pairScale : ℝ) (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) : ℝ :=
  G.rawExtendedProfileBlockVarianceCandidateUse R0 rho omega
    source sourceCode row / pairScale

/-- Conditional raw block variance after fixing the centre candidate. -/
def conditionalExtendedProfileBlockVariance
    (rho omega : ℝ)
    (row : G.ExtendedProfileBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) : ℝ :=
  FiniteCategoricalSelection.rowMean
    (fun source a ↦
      G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
    (G.rawExtendedProfileBlockVarianceCandidateUse R0 rho omega) row

/-- The aggregate self row at `v`: source `(v,b)` contributes the
conditional variance of its selected candidate block, divided by a second
envelope. -/
def scaledExtendedProfileBlockVarianceSelfUse
    (rho omega selfScale : ℝ) (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (v : G.V) : ℝ :=
  if source.1 = v then
    G.conditionalExtendedProfileBlockVariance R0 rho omega
      (v, source.2, sourceCode) / selfScale
  else 0

/-- Candidate rows and aggregate self rows used in one PRA call. -/
abbrev ExtendedProfileBlockVarianceRow :=
  G.ExtendedProfileBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r) ⊕ G.V

def scaledExtendedProfileBlockVarianceUse
    (rho omega pairScale selfScale : ℝ)
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileBlockVarianceRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) : ℝ :=
  match row with
  | Sum.inl candidate =>
      G.scaledExtendedProfileBlockVarianceCandidateUse R0 rho omega pairScale
        source sourceCode candidate
  | Sum.inr v =>
      G.scaledExtendedProfileBlockVarianceSelfUse R0 rho omega selfScale
        source sourceCode v

/-- Selected raw variance in one block at one centre. -/
def selectedRawExtendedProfileBlockVariance
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (v : G.V) (b : Fin B) : ℝ :=
  FiniteCategoricalSelection.rowLoad
    (G.rawExtendedProfileBlockVarianceCandidateUse R0 rho omega)
    (v, b, choice (v, b)) choice

def selectedTotalRawExtendedProfileBlockVariance
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (v : G.V) : ℝ :=
  ∑ b, G.selectedRawExtendedProfileBlockVariance R0 rho omega choice v b

/-- Sum of the conditional block variances at the selected centre states. -/
def selectedConditionalExtendedProfileBlockVariance
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (v : G.V) : ℝ :=
  ∑ b, G.conditionalExtendedProfileBlockVariance R0 rho omega
    (v, b, choice (v, b))

/-- Fully averaged total block variance at one vertex. -/
def meanTotalExtendedProfileBlockVariance
    (rho omega : ℝ) (v : G.V) : ℝ :=
  ∑ b, ∑ a,
    G.paddedExtendedProfileBlockProbability R0 omega v a *
      G.conditionalExtendedProfileBlockVariance R0 rho omega (v, b, a)

theorem rowLoad_scaledBlockVarianceCandidate_eq
    (rho omega pairScale : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (v : G.V) (b : Fin B) :
    FiniteCategoricalSelection.rowLoad
        (G.scaledExtendedProfileBlockVarianceCandidateUse R0 rho omega pairScale)
        (v, b, choice (v, b)) choice =
      G.selectedRawExtendedProfileBlockVariance R0 rho omega choice v b /
        pairScale := by
  unfold selectedRawExtendedProfileBlockVariance
    scaledExtendedProfileBlockVarianceCandidateUse
    FiniteCategoricalSelection.rowLoad
  rw [← Finset.sum_div]

theorem rowMean_scaledBlockVarianceCandidate_eq
    (rho omega pairScale : ℝ)
    (row : G.ExtendedProfileBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
        (fun source a ↦
          G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
        (G.scaledExtendedProfileBlockVarianceCandidateUse
          R0 rho omega pairScale) row =
      G.conditionalExtendedProfileBlockVariance R0 rho omega row /
        pairScale := by
  unfold conditionalExtendedProfileBlockVariance
    scaledExtendedProfileBlockVarianceCandidateUse
    FiniteCategoricalSelection.rowMean
  simp only [div_eq_mul_inv, mul_assoc, Finset.sum_mul]

theorem rowLoad_scaledBlockVarianceSelf_eq
    (rho omega selfScale : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (v : G.V) :
    FiniteCategoricalSelection.rowLoad
        (G.scaledExtendedProfileBlockVarianceSelfUse
          R0 rho omega selfScale) v choice =
      G.selectedConditionalExtendedProfileBlockVariance
          R0 rho omega choice v / selfScale := by
  classical
  unfold FiniteCategoricalSelection.rowLoad
    selectedConditionalExtendedProfileBlockVariance
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single v]
  · simp only [scaledExtendedProfileBlockVarianceSelfUse, if_pos,
      Finset.sum_div]
  · intro u _hu huv
    simp [scaledExtendedProfileBlockVarianceSelfUse, huv]
  · simp

theorem rowMean_scaledBlockVarianceSelf_eq
    (rho omega selfScale : ℝ) (v : G.V) :
    FiniteCategoricalSelection.rowMean
        (fun source a ↦
          G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
        (G.scaledExtendedProfileBlockVarianceSelfUse
          R0 rho omega selfScale) v =
      G.meanTotalExtendedProfileBlockVariance R0 rho omega v / selfScale := by
  classical
  unfold meanTotalExtendedProfileBlockVariance
    FiniteCategoricalSelection.rowMean
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single v]
  · simp only [scaledExtendedProfileBlockVarianceSelfUse, if_pos]
    simp only [div_eq_mul_inv, mul_assoc, Finset.sum_mul]
  · intro u _hu huv
    simp [scaledExtendedProfileBlockVarianceSelfUse, huv]
  · simp

/-- The two row families convert their simultaneous mean-relative bounds
into a bound on the selected total raw block variance. -/
theorem selectedTotalRawBlockVariance_le_of_rowBounds
    (rho omega pairScale selfScale deviation : ℝ)
    (hpair : 0 < pairScale) (hself : 0 < selfScale)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (hrows : ∀ row : G.ExtendedProfileBlockVarianceRow
        (B := B) (k := k) (β := β) (q := q) (r := r),
      FiniteCategoricalSelection.rowLoad
          (G.scaledExtendedProfileBlockVarianceUse R0 rho omega
            pairScale selfScale) row choice ≤
        FiniteCategoricalSelection.rowMean
          (fun source a ↦
            G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
          (G.scaledExtendedProfileBlockVarianceUse R0 rho omega
            pairScale selfScale) row + deviation) :
    ∀ v,
      G.selectedTotalRawExtendedProfileBlockVariance R0 rho omega choice v ≤
        G.meanTotalExtendedProfileBlockVariance R0 rho omega v +
          selfScale * deviation + B * pairScale * deviation := by
  intro v
  have hcandidate : ∀ b : Fin B,
      G.selectedRawExtendedProfileBlockVariance R0 rho omega choice v b ≤
        G.conditionalExtendedProfileBlockVariance R0 rho omega
          (v, b, choice (v, b)) + pairScale * deviation := by
    intro b
    have h := hrows (Sum.inl (v, b, choice (v, b)))
    change FiniteCategoricalSelection.rowLoad
        (G.scaledExtendedProfileBlockVarianceCandidateUse
          R0 rho omega pairScale) (v, b, choice (v, b)) choice ≤
      FiniteCategoricalSelection.rowMean
        (fun source a ↦
          G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
        (G.scaledExtendedProfileBlockVarianceCandidateUse
          R0 rho omega pairScale) (v, b, choice (v, b)) + deviation at h
    rw [G.rowLoad_scaledBlockVarianceCandidate_eq R0,
      G.rowMean_scaledBlockVarianceCandidate_eq R0] at h
    calc
      G.selectedRawExtendedProfileBlockVariance R0 rho omega choice v b ≤
          (G.conditionalExtendedProfileBlockVariance R0 rho omega
              (v, b, choice (v, b)) / pairScale + deviation) *
            pairScale := (div_le_iff₀ hpair).mp h
      _ = G.conditionalExtendedProfileBlockVariance R0 rho omega
            (v, b, choice (v, b)) + pairScale * deviation := by
        rw [add_mul, div_mul_cancel₀ _ hpair.ne']
        ring
  have hcandidateSum :
      G.selectedTotalRawExtendedProfileBlockVariance R0 rho omega choice v ≤
        G.selectedConditionalExtendedProfileBlockVariance
            R0 rho omega choice v + B * pairScale * deviation := by
    unfold selectedTotalRawExtendedProfileBlockVariance
      selectedConditionalExtendedProfileBlockVariance
    calc
      (∑ b, G.selectedRawExtendedProfileBlockVariance
          R0 rho omega choice v b) ≤
          ∑ b, (G.conditionalExtendedProfileBlockVariance R0 rho omega
            (v, b, choice (v, b)) + pairScale * deviation) :=
        Finset.sum_le_sum fun b _hb ↦ hcandidate b
      _ = (∑ b, G.conditionalExtendedProfileBlockVariance R0 rho omega
            (v, b, choice (v, b))) + B * pairScale * deviation := by
        simp [Finset.sum_add_distrib]
        ring
  have hselfRow := hrows (Sum.inr v)
  change FiniteCategoricalSelection.rowLoad
      (G.scaledExtendedProfileBlockVarianceSelfUse
        R0 rho omega selfScale) v choice ≤
    FiniteCategoricalSelection.rowMean
      (fun source a ↦
        G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
      (G.scaledExtendedProfileBlockVarianceSelfUse
        R0 rho omega selfScale) v + deviation at hselfRow
  rw [G.rowLoad_scaledBlockVarianceSelf_eq R0,
    G.rowMean_scaledBlockVarianceSelf_eq R0] at hselfRow
  have hselfRaw :
      G.selectedConditionalExtendedProfileBlockVariance
          R0 rho omega choice v ≤
        G.meanTotalExtendedProfileBlockVariance R0 rho omega v +
          selfScale * deviation := by
    calc
      G.selectedConditionalExtendedProfileBlockVariance
          R0 rho omega choice v ≤
          (G.meanTotalExtendedProfileBlockVariance R0 rho omega v /
              selfScale + deviation) * selfScale :=
        (div_le_iff₀ hself).mp hselfRow
      _ = G.meanTotalExtendedProfileBlockVariance R0 rho omega v +
          selfScale * deviation := by
        rw [add_mul, div_mul_cancel₀ _ hself.ne']
        ring
  exact hcandidateSum.trans (by linarith)

end WeightedMultigraph

end

end WeightedEdgeColoring
