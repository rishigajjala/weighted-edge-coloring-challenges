import WeightedEdgeColoring.FinitePartialResamplingFiniteRun
import WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial

/-!
# Positive traces use nonempty patches

The witness construction needs every recorded patch to mention a source.
This file extracts that fact directly from positivity of the adaptive trace
mass whenever the empty patch has hitting weight zero.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingNonemptyTrace

open WeightedEdgeColoring.FinitePartialResamplingExponential
open WeightedEdgeColoring.FinitePartialResamplingProcess
open WeightedEdgeColoring.FinitePartialResamplingFiniteRun
open WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial

noncomputable section

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- A finite partial assignment mentions a source exactly when it is not the
empty partial assignment. -/
theorem nonemptyPartial_iff_ne_emptyPartial
    {Y : PartialAssignment Source State} :
    NonemptyPartial Y ↔ Y ≠ emptyPartial := by
  constructor
  · rintro ⟨i, hi⟩ hY
    apply hi
    simpa [emptyPartial] using congrFun hY i
  · intro hY
    by_contra hnone
    apply hY
    funext i
    by_contra hi
    exact hnone ⟨i, hi⟩

/-- If the empty patch has weight zero, then its normalized weight is zero
at every complete state. -/
theorem normalizedPatchWeight_emptyPartial_eq_zero
    (weight : Row → PartialAssignment Source State → ℝ)
    (hempty : ∀ r, weight r emptyPartial = 0)
    (r : Row) (z : Source → State) :
    normalizedPatchWeight weight r z emptyPartial = 0 := by
  have hcompat : Compatible (emptyPartial : PartialAssignment Source State) z := by
    intro i j hij
    simp [emptyPartial] at hij
  simp [normalizedPatchWeight, compatiblePatchWeight, hcompat, hempty]

/-- Positive adaptive trace mass forces every selected patch to mention at
least one source, provided the empty patch has hitting weight zero. -/
theorem trace_nonempty_of_traceMass_pos
    {weight : Row → PartialAssignment Source State → ℝ}
    (hweight : ∀ r Y, 0 ≤ weight r Y)
    (hempty : ∀ r, weight r emptyPartial = 0)
    (rowPolicy : (Source → State) → Row)
    (htotal : ∀ z, 1 ≤ compatiblePatchTotal weight (rowPolicy z) z)
    (T : ResamplingTable Source State) (p : Pointer Source) :
    ∀ (n : ℕ) (trace : PatchTrace Source State n),
      0 < traceMass weight rowPolicy T p n trace →
        ∀ time, NonemptyPartial (trace time) := by
  intro n
  induction n generalizing p with
  | zero =>
      intro trace _hpos time
      exact Fin.elim0 time
  | succ n ih =>
      intro trace hpos
      let z := tableChoice T p
      let Y := trace 0
      let headMass := normalizedPatchWeight weight (rowPolicy z) z Y
      let tailMass := traceMass weight rowPolicy T
        (advancePointer p Y) n (Fin.tail trace)
      have htotalPos : 0 < compatiblePatchTotal weight (rowPolicy z) z :=
        lt_of_lt_of_le zero_lt_one (htotal z)
      have hhead0 : 0 ≤ headMass :=
        normalizedPatchWeight_nonneg hweight htotalPos Y
      have htail0 : 0 ≤ tailMass :=
        traceMass_nonneg hweight rowPolicy htotal T
          (advancePointer p Y) n (Fin.tail trace)
      have hproduct : 0 < headMass * tailMass := by
        simpa [traceMass, z, Y, headMass, tailMass] using hpos
      have hheadPos : 0 < headMass := by
        by_contra hnot
        have hheadZero : headMass = 0 :=
          le_antisymm (le_of_not_gt hnot) hhead0
        rw [hheadZero, zero_mul] at hproduct
        exact lt_irrefl 0 hproduct
      have htailPos : 0 < tailMass := by
        by_contra hnot
        have htailZero : tailMass = 0 :=
          le_antisymm (le_of_not_gt hnot) htail0
        rw [htailZero, mul_zero] at hproduct
        exact lt_irrefl 0 hproduct
      have hY : NonemptyPartial Y := by
        rw [nonemptyPartial_iff_ne_emptyPartial]
        intro hYempty
        have hzero : headMass = 0 := by
          unfold headMass
          rw [hYempty]
          exact normalizedPatchWeight_emptyPartial_eq_zero
            weight hempty (rowPolicy z) z
        rw [hzero] at hheadPos
        exact lt_irrefl 0 hheadPos
      intro time
      refine Fin.cases hY ?_ time
      intro tailTime
      exact ih (p := advancePointer p Y) (Fin.tail trace) htailPos tailTime

/-- Finite-prefix specialization of
`trace_nonempty_of_traceMass_pos`. -/
theorem finiteTrace_nonempty_of_mass_pos
    {weight : Row → PartialAssignment Source State → ℝ}
    (hweight : ∀ r Y, 0 ≤ weight r Y)
    (hempty : ∀ r, weight r emptyPartial = 0)
    (rowPolicy : (Source → State) → Row)
    (htotal : ∀ z, 1 ≤ compatiblePatchTotal weight (rowPolicy z) z)
    (fallback : Source → State) {n : ℕ}
    (T : FiniteResamplingTable Source State n)
    (trace : PatchTrace Source State n)
    (hpos : 0 < finiteTraceMass weight rowPolicy fallback T trace) :
    ∀ time, NonemptyPartial (trace time) := by
  exact trace_nonempty_of_traceMass_pos hweight hempty rowPolicy htotal
    (extendFiniteTable fallback T) initialPointer n trace hpos

end

end WeightedEdgeColoring.FinitePartialResamplingNonemptyTrace
