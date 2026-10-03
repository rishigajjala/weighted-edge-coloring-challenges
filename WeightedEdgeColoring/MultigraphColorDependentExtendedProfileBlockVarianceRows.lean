import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileBlockVarianceSelection
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Weighted-square rows for colour-dependent profile blocks

The target of a block is its actual proposal mass, rather than a uniform
`1/B`.  This is the form required by whole-edge rounding.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- Total raw option mass in one colour coordinate. -/
def colorDependentCoordinateOptionMass
    (rho omega : ℝ) (e : G.E) (c : Fin B × Fin k)
    (P : G.ColorDependentExtendedProfileState R (G.fst e) c)
    (Q : G.ColorDependentExtendedProfileState R (G.snd e) c) : ℝ :=
  (∑ i, ∑ j, G.colorDependentExtendedProfileLargeProductMass
    proposal R rho omega e c P Q i j) +
  G.colorDependentExtendedProfileTinyProductMass
    proposal R rho omega e c P Q

/-- Selected option mass on edge `e` inside block `b`. -/
def colorDependentBlockOptionMass
    (rho omega : ℝ) (e : G.E) (b : Fin B)
    (left right : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) : ℝ :=
  ∑ i, G.colorDependentCoordinateOptionMass proposal R rho omega e (b, i)
    (G.decodeColorDependentExtendedProfileBlock proposal R
      (G.fst e, b) left i)
    (G.decodeColorDependentExtendedProfileBlock proposal R
      (G.snd e, b) right i)

/-- Exact expected option mass of one block. -/
def colorDependentBlockTarget (rho s : ℝ) (e : G.E) (b : Fin B) : ℝ :=
  rho * s * ∑ i : Fin k, proposal e (b, i)

/-- Weighted squared error of one edge in one block. -/
def colorDependentBlockVariance
    (rho omega : ℝ) (e : G.E) (b : Fin B)
    (left right : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) : ℝ :=
  G.weight e *
    (G.colorDependentBlockOptionMass proposal R rho omega e b left right -
      G.colorDependentBlockTarget proposal rho s e b) ^ 2

theorem colorDependentBlockVariance_nonneg
    (rho omega : ℝ) (e : G.E) (b : Fin B)
    (left right : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) :
    0 ≤ G.colorDependentBlockVariance proposal R rho omega e b left right := by
  exact mul_nonneg (G.weight_nonneg e) (sq_nonneg _)

abbrev ColorDependentBlockVarianceCandidateRow :=
  G.V × Fin B ×
    G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)

def colorDependentBlockVarianceCandidateEdgeUse
    (rho omega : ℝ) (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r))
    (e : G.E)
    (row : G.ColorDependentBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) : ℝ :=
  if source.2 = row.2.1 then
    if row.1 = G.fst e ∧ source.1 = G.snd e then
      G.colorDependentBlockVariance proposal R rho omega e row.2.1
        row.2.2 sourceCode
    else if row.1 = G.snd e ∧ source.1 = G.fst e then
      G.colorDependentBlockVariance proposal R rho omega e row.2.1
        sourceCode row.2.2
    else 0
  else 0

def rawColorDependentBlockVarianceCandidateUse
    (rho omega : ℝ) (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r))
    (row : G.ColorDependentBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) : ℝ :=
  ∑ e, G.colorDependentBlockVarianceCandidateEdgeUse proposal R rho omega
    source sourceCode e row

theorem rawColorDependentBlockVarianceCandidateUse_nonneg
    (rho omega : ℝ) (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r))
    (row : G.ColorDependentBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    0 ≤ G.rawColorDependentBlockVarianceCandidateUse
      proposal R rho omega source sourceCode row := by
  unfold rawColorDependentBlockVarianceCandidateUse
  apply Finset.sum_nonneg
  intro e _he
  unfold colorDependentBlockVarianceCandidateEdgeUse
  split <;> try exact le_rfl
  split
  · exact G.colorDependentBlockVariance_nonneg proposal R _ _ _ _ _ _
  · split
    · exact G.colorDependentBlockVariance_nonneg proposal R _ _ _ _ _ _
    · exact le_rfl

def scaledColorDependentBlockVarianceCandidateUse
    (rho omega pairScale : ℝ) (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r))
    (row : G.ColorDependentBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) : ℝ :=
  G.rawColorDependentBlockVarianceCandidateUse proposal R rho omega
    source sourceCode row / pairScale

def conditionalColorDependentBlockVariance
    (rho omega : ℝ)
    (row : G.ColorDependentBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) : ℝ :=
  FiniteCategoricalSelection.rowMean
    (G.paddedColorDependentExtendedProfileBlockProbability proposal R omega)
    (G.rawColorDependentBlockVarianceCandidateUse proposal R rho omega) row

theorem conditionalColorDependentBlockVariance_nonneg
    (rho omega : ℝ)
    (hprob0 : ∀ src a,
      0 ≤ G.paddedColorDependentExtendedProfileBlockProbability
        proposal R omega src a)
    (row : G.ColorDependentBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    0 ≤ G.conditionalColorDependentBlockVariance
      proposal R rho omega row := by
  unfold conditionalColorDependentBlockVariance
    FiniteCategoricalSelection.rowMean
  exact Finset.sum_nonneg fun src _hsrc ↦
    Finset.sum_nonneg fun a _ha ↦ mul_nonneg (hprob0 src a)
      (G.rawColorDependentBlockVarianceCandidateUse_nonneg
        proposal R rho omega src a row)

def scaledColorDependentBlockVarianceSelfUse
    (rho omega selfScale : ℝ) (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) (v : G.V) : ℝ :=
  if source.1 = v then
    G.conditionalColorDependentBlockVariance proposal R rho omega
      (v, source.2, sourceCode) / selfScale
  else 0

abbrev ColorDependentBlockVarianceRow :=
  G.ColorDependentBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r) ⊕ G.V

def scaledColorDependentBlockVarianceUse
    (rho omega pairScale selfScale : ℝ) (source : G.V × Fin B)
    (sourceCode : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r))
    (row : G.ColorDependentBlockVarianceRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) : ℝ :=
  match row with
  | Sum.inl candidate =>
      G.scaledColorDependentBlockVarianceCandidateUse proposal R rho omega
        pairScale source sourceCode candidate
  | Sum.inr v =>
      G.scaledColorDependentBlockVarianceSelfUse proposal R rho omega
        selfScale source sourceCode v

def selectedRawColorDependentBlockVariance
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (v : G.V) (b : Fin B) : ℝ :=
  FiniteCategoricalSelection.rowLoad
    (G.rawColorDependentBlockVarianceCandidateUse proposal R rho omega)
    (v, b, choice (v, b)) choice

def selectedTotalRawColorDependentBlockVariance
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (v : G.V) : ℝ :=
  ∑ b, G.selectedRawColorDependentBlockVariance
    proposal R rho omega choice v b

def selectedConditionalColorDependentBlockVariance
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (v : G.V) : ℝ :=
  ∑ b, G.conditionalColorDependentBlockVariance proposal R rho omega
    (v, b, choice (v, b))

def meanTotalColorDependentBlockVariance
    (rho omega : ℝ) (v : G.V) : ℝ :=
  ∑ b, ∑ a,
    G.paddedColorDependentExtendedProfileBlockProbability
        proposal R omega (v, b) a *
      G.conditionalColorDependentBlockVariance proposal R rho omega (v, b, a)

theorem rowLoad_scaledColorDependentBlockVarianceCandidate_eq
    (rho omega pairScale : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (v : G.V) (b : Fin B) :
    FiniteCategoricalSelection.rowLoad
      (G.scaledColorDependentBlockVarianceCandidateUse
        proposal R rho omega pairScale)
      (v, b, choice (v, b)) choice =
    G.selectedRawColorDependentBlockVariance
      proposal R rho omega choice v b / pairScale := by
  unfold selectedRawColorDependentBlockVariance
    scaledColorDependentBlockVarianceCandidateUse
    FiniteCategoricalSelection.rowLoad
  rw [← Finset.sum_div]

theorem rowMean_scaledColorDependentBlockVarianceCandidate_eq
    (rho omega pairScale : ℝ)
    (row : G.ColorDependentBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
      (G.paddedColorDependentExtendedProfileBlockProbability proposal R omega)
      (G.scaledColorDependentBlockVarianceCandidateUse
        proposal R rho omega pairScale) row =
    G.conditionalColorDependentBlockVariance proposal R rho omega row /
      pairScale := by
  unfold conditionalColorDependentBlockVariance
    scaledColorDependentBlockVarianceCandidateUse
    FiniteCategoricalSelection.rowMean
  simp only [div_eq_mul_inv, mul_assoc, Finset.sum_mul]

theorem rowLoad_scaledColorDependentBlockVarianceSelf_eq
    (rho omega selfScale : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r)) (v : G.V) :
    FiniteCategoricalSelection.rowLoad
      (G.scaledColorDependentBlockVarianceSelfUse
        proposal R rho omega selfScale) v choice =
    G.selectedConditionalColorDependentBlockVariance
      proposal R rho omega choice v / selfScale := by
  classical
  unfold FiniteCategoricalSelection.rowLoad
    selectedConditionalColorDependentBlockVariance
  rw [Fintype.sum_prod_type, Finset.sum_eq_single v]
  · simp only [scaledColorDependentBlockVarianceSelfUse, if_pos,
      Finset.sum_div]
  · intro u _hu huv
    simp [scaledColorDependentBlockVarianceSelfUse, huv]
  · simp

theorem rowMean_scaledColorDependentBlockVarianceSelf_eq
    (rho omega selfScale : ℝ) (v : G.V) :
    FiniteCategoricalSelection.rowMean
      (G.paddedColorDependentExtendedProfileBlockProbability proposal R omega)
      (G.scaledColorDependentBlockVarianceSelfUse
        proposal R rho omega selfScale) v =
    G.meanTotalColorDependentBlockVariance proposal R rho omega v /
      selfScale := by
  classical
  unfold meanTotalColorDependentBlockVariance
    FiniteCategoricalSelection.rowMean
  rw [Fintype.sum_prod_type, Finset.sum_eq_single v]
  · simp only [scaledColorDependentBlockVarianceSelfUse, if_pos]
    simp only [div_eq_mul_inv, mul_assoc, Finset.sum_mul]
  · intro u _hu huv
    simp [scaledColorDependentBlockVarianceSelfUse, huv]
  · simp

/-- Sharp reduction of all normalized variance-row envelopes to the three
raw estimates used by the analytic moment calculation. -/
theorem scaledColorDependentBlockVarianceUse_envelopes
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho pairScale selfScale meanBound : ℝ)
    (hpair : 0 < pairScale) (hself : 0 < selfScale)
    (hpairSelf : meanBound * pairScale ≤ selfScale)
    (hrawPair : ∀ src a row,
      G.rawColorDependentBlockVarianceCandidateUse
        proposal R rho omega src a row ≤ pairScale)
    (hconditionalPair : ∀ row,
      G.conditionalColorDependentBlockVariance proposal R rho omega row ≤
        meanBound * pairScale)
    (hmeanSelf : ∀ v,
      G.meanTotalColorDependentBlockVariance proposal R rho omega v ≤
        meanBound * selfScale) :
    (∀ src a row,
      0 ≤ G.scaledColorDependentBlockVarianceUse proposal R rho omega
        pairScale selfScale src a row) ∧
    (∀ src a row,
      G.scaledColorDependentBlockVarianceUse proposal R rho omega
        pairScale selfScale src a row ≤ 1) ∧
    ∀ row,
      FiniteCategoricalSelection.rowMean
        (G.paddedColorDependentExtendedProfileBlockProbability proposal R omega)
        (G.scaledColorDependentBlockVarianceUse proposal R rho omega
          pairScale selfScale) row ≤ meanBound := by
  have hprob0 :=
    G.paddedColorDependentExtendedProfileBlockProbability_nonneg
      proposal R hs hq hr0 hleft homega0 homega1
  constructor
  · intro src a row
    rcases row with row | v
    · change 0 ≤
          G.rawColorDependentBlockVarianceCandidateUse
            proposal R rho omega src a row / pairScale
      exact div_nonneg
        (G.rawColorDependentBlockVarianceCandidateUse_nonneg
          proposal R rho omega src a row) hpair.le
    · change 0 ≤ G.scaledColorDependentBlockVarianceSelfUse
          proposal R rho omega selfScale src a v
      unfold scaledColorDependentBlockVarianceSelfUse
      split
      · exact div_nonneg
          (G.conditionalColorDependentBlockVariance_nonneg
            proposal R rho omega hprob0 _) hself.le
      · norm_num
  constructor
  · intro src a row
    rcases row with row | v
    · change
          G.rawColorDependentBlockVarianceCandidateUse
            proposal R rho omega src a row / pairScale ≤ 1
      exact (div_le_one hpair).2 (hrawPair src a row)
    · change G.scaledColorDependentBlockVarianceSelfUse
          proposal R rho omega selfScale src a v ≤ 1
      unfold scaledColorDependentBlockVarianceSelfUse
      split
      · exact (div_le_one hself).2 (by
          exact (hconditionalPair _).trans hpairSelf)
      · norm_num
  · intro row
    rcases row with row | v
    · change FiniteCategoricalSelection.rowMean
          (G.paddedColorDependentExtendedProfileBlockProbability
            proposal R omega)
          (G.scaledColorDependentBlockVarianceCandidateUse
            proposal R rho omega pairScale) row ≤ meanBound
      rw [G.rowMean_scaledColorDependentBlockVarianceCandidate_eq]
      exact (div_le_iff₀ hpair).2 (hconditionalPair row)
    · change FiniteCategoricalSelection.rowMean
          (G.paddedColorDependentExtendedProfileBlockProbability
            proposal R omega)
          (G.scaledColorDependentBlockVarianceSelfUse
            proposal R rho omega selfScale) v ≤ meanBound
      rw [G.rowMean_scaledColorDependentBlockVarianceSelf_eq]
      exact (div_le_iff₀ hself).2 (hmeanSelf v)

/-- The two conditional row levels turn simultaneous row bounds into a
bound on the selected total weighted block square. -/
theorem selectedTotalRawColorDependentBlockVariance_le_of_rowBounds
    (rho omega pairScale selfScale deviation : ℝ)
    (hpair : 0 < pairScale) (hself : 0 < selfScale)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (hrows : ∀ row : G.ColorDependentBlockVarianceRow
        (B := B) (k := k) (β := β) (q := q) (r := r),
      FiniteCategoricalSelection.rowLoad
        (G.scaledColorDependentBlockVarianceUse proposal R rho omega
          pairScale selfScale) row choice ≤
      FiniteCategoricalSelection.rowMean
        (G.paddedColorDependentExtendedProfileBlockProbability proposal R omega)
        (G.scaledColorDependentBlockVarianceUse proposal R rho omega
          pairScale selfScale) row + deviation) :
    ∀ v,
      G.selectedTotalRawColorDependentBlockVariance
          proposal R rho omega choice v ≤
        G.meanTotalColorDependentBlockVariance proposal R rho omega v +
          selfScale * deviation + B * pairScale * deviation := by
  intro v
  have hcandidate : ∀ b : Fin B,
      G.selectedRawColorDependentBlockVariance
          proposal R rho omega choice v b ≤
        G.conditionalColorDependentBlockVariance proposal R rho omega
          (v, b, choice (v, b)) + pairScale * deviation := by
    intro b
    have h := hrows (Sum.inl (v, b, choice (v, b)))
    change FiniteCategoricalSelection.rowLoad
      (G.scaledColorDependentBlockVarianceCandidateUse
        proposal R rho omega pairScale)
      (v, b, choice (v, b)) choice ≤
      FiniteCategoricalSelection.rowMean
        (G.paddedColorDependentExtendedProfileBlockProbability proposal R omega)
        (G.scaledColorDependentBlockVarianceCandidateUse
          proposal R rho omega pairScale)
        (v, b, choice (v, b)) + deviation at h
    rw [G.rowLoad_scaledColorDependentBlockVarianceCandidate_eq,
      G.rowMean_scaledColorDependentBlockVarianceCandidate_eq] at h
    calc
      G.selectedRawColorDependentBlockVariance
            proposal R rho omega choice v b =
          (G.selectedRawColorDependentBlockVariance
              proposal R rho omega choice v b / pairScale) * pairScale := by
            field_simp
      _ ≤ (G.conditionalColorDependentBlockVariance
            proposal R rho omega (v, b, choice (v, b)) / pairScale +
            deviation) * pairScale := mul_le_mul_of_nonneg_right h hpair.le
      _ = G.conditionalColorDependentBlockVariance
            proposal R rho omega (v, b, choice (v, b)) +
            pairScale * deviation := by field_simp
  have hsum :
      G.selectedTotalRawColorDependentBlockVariance
          proposal R rho omega choice v ≤
        G.selectedConditionalColorDependentBlockVariance
          proposal R rho omega choice v + B * pairScale * deviation := by
    unfold selectedTotalRawColorDependentBlockVariance
      selectedConditionalColorDependentBlockVariance
    calc
      (∑ b, G.selectedRawColorDependentBlockVariance
          proposal R rho omega choice v b) ≤
        ∑ b, (G.conditionalColorDependentBlockVariance proposal R rho omega
          (v, b, choice (v, b)) + pairScale * deviation) :=
            Finset.sum_le_sum fun b _hb ↦ hcandidate b
      _ = _ := by simp [Finset.sum_add_distrib, mul_assoc]
  have hselfRow := hrows (Sum.inr v)
  change FiniteCategoricalSelection.rowLoad
      (G.scaledColorDependentBlockVarianceSelfUse
        proposal R rho omega selfScale) v choice ≤
    FiniteCategoricalSelection.rowMean
      (G.paddedColorDependentExtendedProfileBlockProbability proposal R omega)
      (G.scaledColorDependentBlockVarianceSelfUse
        proposal R rho omega selfScale) v + deviation at hselfRow
  rw [G.rowLoad_scaledColorDependentBlockVarianceSelf_eq,
    G.rowMean_scaledColorDependentBlockVarianceSelf_eq] at hselfRow
  have hselfBound :
      G.selectedConditionalColorDependentBlockVariance
          proposal R rho omega choice v ≤
        G.meanTotalColorDependentBlockVariance proposal R rho omega v +
          selfScale * deviation := by
    calc
      _ = (G.selectedConditionalColorDependentBlockVariance
          proposal R rho omega choice v / selfScale) * selfScale := by
            field_simp
      _ ≤ (G.meanTotalColorDependentBlockVariance
          proposal R rho omega v / selfScale + deviation) * selfScale :=
            mul_le_mul_of_nonneg_right hselfRow hself.le
      _ = _ := by field_simp
  linarith

/-- Whole-edge selected option mass, before clipping. -/
def selectedColorDependentTotalOptionMass
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) : ℝ :=
  ∑ b, G.colorDependentBlockOptionMass proposal R rho omega e b
    (choice (G.fst e, b)) (choice (G.snd e, b))

def colorDependentTotalTarget
    (rho s : ℝ) (e : G.E) : ℝ :=
  rho * s * ∑ c : Fin B × Fin k, proposal e c

/-- The candidate-row load is the direct block-variance sum over the star. -/
theorem selectedRawColorDependentBlockVariance_eq_star_sum
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (v : G.V) (b : Fin B) :
    G.selectedRawColorDependentBlockVariance
        proposal R rho omega choice v b =
      ∑ e : G.StarEdge v,
        G.colorDependentBlockVariance proposal R rho omega e.1 b
          (choice (G.fst e.1, b)) (choice (G.snd e.1, b)) := by
  classical
  unfold selectedRawColorDependentBlockVariance
    FiniteCategoricalSelection.rowLoad
    rawColorDependentBlockVarianceCandidateUse
  rw [Finset.sum_comm]
  calc
    (∑ e : G.E, ∑ source : G.V × Fin B,
      G.colorDependentBlockVarianceCandidateEdgeUse proposal R rho omega
        source (choice source) e (v, b, choice (v, b))) =
      ∑ e : G.E, if G.Inc v e then
        G.colorDependentBlockVariance proposal R rho omega e b
          (choice (G.fst e, b)) (choice (G.snd e, b)) else 0 := by
        apply Finset.sum_congr rfl
        intro e _he
        rw [Fintype.sum_prod_type]
        by_cases hfst : v = G.fst e
        · subst v
          have hne : G.fst e ≠ G.snd e := G.noLoop e
          simp [colorDependentBlockVarianceCandidateEdgeUse,
            WeightedMultigraph.Inc, hne]
        · by_cases hsnd : v = G.snd e
          · subst v
            have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
            simp [colorDependentBlockVarianceCandidateEdgeUse,
              WeightedMultigraph.Inc, hne, hfst]
          · have hfst' : G.fst e ≠ v := Ne.symm hfst
            have hsnd' : G.snd e ≠ v := Ne.symm hsnd
            simp [colorDependentBlockVarianceCandidateEdgeUse,
              WeightedMultigraph.Inc, hfst, hsnd, hfst', hsnd']
    _ = ∑ e ∈ Finset.univ.filter (G.Inc v),
        G.colorDependentBlockVariance proposal R rho omega e b
          (choice (G.fst e, b)) (choice (G.snd e, b)) := by
      rw [Finset.sum_filter]
    _ = _ := by
      exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
        (by intro e; simp)
        (fun e ↦ G.colorDependentBlockVariance proposal R rho omega e b
          (choice (G.fst e, b)) (choice (G.snd e, b)))

theorem selectedTotalRawColorDependentBlockVariance_eq_star_sum
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (v : G.V) :
    G.selectedTotalRawColorDependentBlockVariance
        proposal R rho omega choice v =
      ∑ b : Fin B, ∑ e : G.StarEdge v,
        G.colorDependentBlockVariance proposal R rho omega e.1 b
          (choice (G.fst e.1, b)) (choice (G.snd e.1, b)) := by
  unfold selectedTotalRawColorDependentBlockVariance
  apply Finset.sum_congr rfl
  intro b _hb
  exact G.selectedRawColorDependentBlockVariance_eq_star_sum
    proposal R rho omega choice v b

theorem sum_colorDependentBlockTarget_eq_totalTarget
    (rho s : ℝ) (e : G.E) :
    (∑ b, G.colorDependentBlockTarget proposal rho s e b) =
      G.colorDependentTotalTarget proposal rho s e := by
  unfold colorDependentBlockTarget colorDependentTotalTarget
  rw [Fintype.sum_prod_type, Finset.mul_sum]

/-- Deterministic Cauchy bridge from selected block squares to the complete
whole-edge squared error at every star. -/
theorem selectedColorDependentTotalOptionMass_weightedSquare_le
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (rho omega : ℝ) (v : G.V) :
    (∑ e : G.StarEdge v, G.weight e.1 *
      (G.selectedColorDependentTotalOptionMass
          proposal R rho omega choice e.1 -
        G.colorDependentTotalTarget proposal rho s e.1) ^ 2) ≤
      B * G.selectedTotalRawColorDependentBlockVariance
        proposal R rho omega choice v := by
  classical
  have hB : ∀ e : G.StarEdge v,
      (G.selectedColorDependentTotalOptionMass
          proposal R rho omega choice e.1 -
        G.colorDependentTotalTarget proposal rho s e.1) ^ 2 ≤
      B * ∑ b,
        (G.colorDependentBlockOptionMass proposal R rho omega e.1 b
            (choice (G.fst e.1, b)) (choice (G.snd e.1, b)) -
          G.colorDependentBlockTarget proposal rho s e.1 b) ^ 2 := by
    intro e
    rw [← G.sum_colorDependentBlockTarget_eq_totalTarget proposal rho s e.1]
    unfold selectedColorDependentTotalOptionMass
    rw [← Finset.sum_sub_distrib]
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ)
        (f := fun b : Fin B ↦
          G.colorDependentBlockOptionMass proposal R rho omega e.1 b
              (choice (G.fst e.1, b)) (choice (G.snd e.1, b)) -
            G.colorDependentBlockTarget proposal rho s e.1 b))
  calc
    _ ≤ ∑ e : G.StarEdge v, G.weight e.1 *
        (B * ∑ b,
          (G.colorDependentBlockOptionMass proposal R rho omega e.1 b
              (choice (G.fst e.1, b)) (choice (G.snd e.1, b)) -
            G.colorDependentBlockTarget proposal rho s e.1 b) ^ 2) := by
      exact Finset.sum_le_sum fun e _he ↦
        mul_le_mul_of_nonneg_left (hB e) (G.weight_nonneg e.1)
    _ = B * G.selectedTotalRawColorDependentBlockVariance
        proposal R rho omega choice v := by
      rw [G.selectedTotalRawColorDependentBlockVariance_eq_star_sum]
      simp_rw [colorDependentBlockVariance]
      calc
        (∑ e : G.StarEdge v, G.weight e.1 *
          (B * ∑ b,
            (G.colorDependentBlockOptionMass proposal R rho omega e.1 b
                (choice (G.fst e.1, b)) (choice (G.snd e.1, b)) -
              G.colorDependentBlockTarget proposal rho s e.1 b) ^ 2)) =
            B * ∑ e : G.StarEdge v, ∑ b,
              G.weight e.1 *
                (G.colorDependentBlockOptionMass proposal R rho omega e.1 b
                    (choice (G.fst e.1, b)) (choice (G.snd e.1, b)) -
                  G.colorDependentBlockTarget proposal rho s e.1 b) ^ 2 := by
          conv_rhs => rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _he
          calc
            G.weight e.1 *
                (B * ∑ b,
                  (G.colorDependentBlockOptionMass proposal R rho omega e.1 b
                      (choice (G.fst e.1, b)) (choice (G.snd e.1, b)) -
                    G.colorDependentBlockTarget proposal rho s e.1 b) ^ 2) =
              B * (G.weight e.1 * ∑ b,
                (G.colorDependentBlockOptionMass proposal R rho omega e.1 b
                    (choice (G.fst e.1, b)) (choice (G.snd e.1, b)) -
                  G.colorDependentBlockTarget proposal rho s e.1 b) ^ 2) := by
                ring
            _ = B * ∑ b, G.weight e.1 *
                (G.colorDependentBlockOptionMass proposal R rho omega e.1 b
                    (choice (G.fst e.1, b)) (choice (G.snd e.1, b)) -
                  G.colorDependentBlockTarget proposal rho s e.1 b) ^ 2 := by
                rw [Finset.mul_sum]
        _ = B * ∑ b, ∑ e : G.StarEdge v,
              G.weight e.1 *
                (G.colorDependentBlockOptionMass proposal R rho omega e.1 b
                    (choice (G.fst e.1, b)) (choice (G.snd e.1, b)) -
                  G.colorDependentBlockTarget proposal rho s e.1 b) ^ 2 := by
          rw [Finset.sum_comm]

/-- Weighted Cauchy--Schwarz for the signed clipping deficit. -/
theorem colorDependentWeightedSignedDeficit_sq_le
    {I : Type*} [Fintype I]
    (weight error : I → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    (∑ i, weight i * error i) ^ 2 ≤
      (∑ i, weight i) * ∑ i, weight i * (error i) ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    (s := Finset.univ)
    (r := fun i ↦ weight i * error i)
    (f := weight)
    (g := fun i ↦ weight i * (error i) ^ 2)
  · intro i _hi
    exact hweight i
  · intro i _hi
    exact mul_nonneg (hweight i) (sq_nonneg _)
  · intro i _hi
    ring_nf

end WeightedMultigraph

end

end WeightedEdgeColoring
