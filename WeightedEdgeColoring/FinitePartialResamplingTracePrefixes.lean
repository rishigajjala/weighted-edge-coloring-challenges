import WeightedEdgeColoring.FinitePartialResamplingFiniteRun

/-!
# Prefix requirements for adaptive partial-resampling traces

A witness tree fixes, for every row, an initial list of patches which must
have been selected on the successive visits to that row.  Visits to other
rows may be interleaved arbitrarily.  This file proves the finite adaptive
estimate needed for that situation.

The proof uses only the chain rule.  When the current row still has a
required head patch, the normalized probability of choosing that patch is
at most its unnormalized hitting weight.  When its requirement list is
empty, all possible head patches sum to one.  Consequently the total mass
of traces which consume every prescribed row-prefix is at most the product
of the prescribed hitting weights.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingTracePrefixes

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential
open WeightedEdgeColoring.FinitePartialResamplingProcess
open WeightedEdgeColoring.FinitePartialResamplingFiniteRun

noncomputable section

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- A row requirement is the chronological prefix of patches prescribed for
that row. -/
abbrev RowRequirements (Source State Row : Type*) :=
  Row → List (PartialAssignment Source State)

/-- Delete the first outstanding requirement at one row.  It is used only
in the nonempty-list branch of the trace predicate below. -/
def consumeHead
    (requirements : RowRequirements Source State Row) (r : Row) :
    RowRequirements Source State Row :=
  Function.update requirements r (requirements r).tail

/-- Product of all unnormalized hitting weights in all outstanding row
prefixes.  List products deliberately retain multiplicity. -/
def requirementsWeight
    (weight : Row → PartialAssignment Source State → ℝ)
    (requirements : RowRequirements Source State Row) : ℝ :=
  ∏ r, ((requirements r).map (weight r)).prod

/-- A trace consumes the prescribed prefixes.  At a visit to a row with a
nonempty outstanding list, the chosen patch must equal the head and that
head is removed.  At the horizon every list must be empty. -/
def ConsumesRequirements
    (rowPolicy : (Source → State) → Row)
    (T : ResamplingTable Source State) :
    RowRequirements Source State Row → Pointer Source →
      (n : ℕ) → PatchTrace Source State n → Prop
  | requirements, _p, 0, _trace => ∀ r, requirements r = []
  | requirements, p, n + 1, trace =>
      let r := rowPolicy (tableChoice T p)
      match requirements r with
      | [] =>
          ConsumesRequirements rowPolicy T requirements
            (advancePointer p (trace 0)) n (Fin.tail trace)
      | required :: _rest =>
          trace 0 = required ∧
            ConsumesRequirements rowPolicy T
              (consumeHead requirements r)
              (advancePointer p (trace 0)) n (Fin.tail trace)

noncomputable instance consumesRequirementsDecidable
    (rowPolicy : (Source → State) → Row)
    (T : ResamplingTable Source State)
    (requirements : RowRequirements Source State Row)
    (p : Pointer Source) (n : ℕ) (trace : PatchTrace Source State n) :
    Decidable (ConsumesRequirements rowPolicy T requirements p n trace) :=
  Classical.propDecidable _

/-- Every outstanding-prefix weight is nonnegative when the hitting weights
are nonnegative. -/
theorem requirementsWeight_nonneg
    {weight : Row → PartialAssignment Source State → ℝ}
    (hweight : ∀ r Y, 0 ≤ weight r Y)
    (requirements : RowRequirements Source State Row) :
    0 ≤ requirementsWeight weight requirements := by
  unfold requirementsWeight
  apply Finset.prod_nonneg
  intro r _hr
  apply List.prod_nonneg
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨Y, _hY, rfl⟩ := hx
  exact hweight r Y

/-- Removing the head of one nonempty row list removes exactly its one
weight factor from the total product. -/
theorem requirementsWeight_cons
    (weight : Row → PartialAssignment Source State → ℝ)
    (requirements : RowRequirements Source State Row)
    (r : Row) (required : PartialAssignment Source State)
    (rest : List (PartialAssignment Source State))
    (hrow : requirements r = required :: rest) :
    requirementsWeight weight requirements =
      weight r required *
        requirementsWeight weight (consumeHead requirements r) := by
  classical
  let factor : Row → ℝ :=
    fun s ↦ ((requirements s).map (weight s)).prod
  have hfactor : factor r =
      weight r required * ((rest.map (weight r)).prod) := by
    simp [factor, hrow]
  have hconsumeAt :
      ((consumeHead requirements r r).map (weight r)).prod =
        (rest.map (weight r)).prod := by
    simp [consumeHead, hrow]
  have hconsumeOff : ∀ s, s ≠ r →
      ((consumeHead requirements r s).map (weight s)).prod = factor s := by
    intro s hsr
    simp [consumeHead, factor, hsr]
  have hupdated :
      requirementsWeight weight (consumeHead requirements r) =
        (rest.map (weight r)).prod *
          ∏ s ∈ (Finset.univ : Finset Row) \ {r}, factor s := by
    unfold requirementsWeight
    rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ r)]
    rw [hconsumeAt]
    congr 1
    apply Finset.prod_congr rfl
    intro s hs
    have hsr : s ≠ r := by
      intro heq
      subst s
      simpa using hs
    exact hconsumeOff s hsr
  calc
    requirementsWeight weight requirements =
        factor r *
          ∏ s ∈ (Finset.univ : Finset Row) \ {r}, factor s := by
      unfold requirementsWeight factor
      rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ r)]
    _ = weight r required *
          ((rest.map (weight r)).prod *
            ∏ s ∈ (Finset.univ : Finset Row) \ {r}, factor s) := by
      rw [hfactor]
      ring
    _ = weight r required *
          requirementsWeight weight (consumeHead requirements r) := by
      rw [hupdated]

/-- If the current row has no outstanding prefix, consuming a step leaves
the required product unchanged. -/
theorem requirementsWeight_consumeHead_of_nil
    (weight : Row → PartialAssignment Source State → ℝ)
    (requirements : RowRequirements Source State Row)
    (r : Row) (hrow : requirements r = []) :
    requirementsWeight weight (consumeHead requirements r) =
      requirementsWeight weight requirements := by
  have hsame : consumeHead requirements r = requirements := by
    funext s
    by_cases hsr : s = r
    · subst s
      simp [consumeHead, hrow]
    · simp [consumeHead, hsr]
  rw [hsame]

/-- Mass of the adaptive traces which consume all prescribed row-prefixes. -/
def consumingTraceMass
    (weight : Row → PartialAssignment Source State → ℝ)
    (rowPolicy : (Source → State) → Row)
    (T : ResamplingTable Source State)
    (requirements : RowRequirements Source State Row)
    (p : Pointer Source) (n : ℕ) : ℝ :=
  ∑ trace : PatchTrace Source State n,
    if ConsumesRequirements rowPolicy T requirements p n trace then
      traceMass weight rowPolicy T p n trace
    else 0

/-- Adaptive row-prefix bound.  The estimate is uniform in the table, the
starting source pointer, the deterministic row policy, and the amount of
interleaving between rows. -/
theorem consumingTraceMass_le_requirementsWeight
    {weight : Row → PartialAssignment Source State → ℝ}
    (hweight : ∀ r Y, 0 ≤ weight r Y)
    (rowPolicy : (Source → State) → Row)
    (htotal : ∀ z, 1 ≤ compatiblePatchTotal weight (rowPolicy z) z)
    (T : ResamplingTable Source State) :
    ∀ (n : ℕ) (requirements : RowRequirements Source State Row)
      (p : Pointer Source),
      consumingTraceMass weight rowPolicy T requirements p n ≤
        requirementsWeight weight requirements := by
  intro n
  induction n with
  | zero =>
      intro requirements p
      unfold consumingTraceMass
      simp only [ConsumesRequirements, traceMass]
      by_cases hall : ∀ r, requirements r = []
      · have hweightOne : requirementsWeight weight requirements = 1 := by
          unfold requirementsWeight
          apply Finset.prod_eq_one
          intro r _hr
          simp [hall r]
        simp [hall, hweightOne]
      · have hzero :
            ∀ trace : PatchTrace Source State 0,
              ¬ ConsumesRequirements rowPolicy T requirements p 0 trace := by
          intro trace hconsumes
          exact hall hconsumes
        simpa [hall] using
          (requirementsWeight_nonneg hweight requirements)
  | succ n ih =>
      intro requirements p
      let z := tableChoice T p
      let r := rowPolicy z
      have htotalHere : 1 ≤ compatiblePatchTotal weight r z := by
        simpa [r, z] using htotal z
      have htotalPos : 0 < compatiblePatchTotal weight r z :=
        lt_of_lt_of_le zero_lt_one htotalHere
      unfold consumingTraceMass
      rw [sum_patchTrace_succ]
      by_cases hrow : requirements r = []
      · have hstep : ∀ head : PartialAssignment Source State,
            (∑ tail : PatchTrace Source State n,
              if ConsumesRequirements rowPolicy T requirements p (n + 1)
                  (Fin.cons head tail) then
                traceMass weight rowPolicy T p (n + 1)
                  (Fin.cons head tail)
              else 0) ≤
            normalizedPatchWeight weight r z head *
              requirementsWeight weight requirements := by
          intro head
          have hi := ih requirements (advancePointer p head)
          have hnorm0 : 0 ≤ normalizedPatchWeight weight r z head :=
            normalizedPatchWeight_nonneg hweight htotalPos head
          calc
            (∑ tail : PatchTrace Source State n,
                if ConsumesRequirements rowPolicy T requirements p (n + 1)
                    (Fin.cons head tail) then
                  traceMass weight rowPolicy T p (n + 1)
                    (Fin.cons head tail)
                else 0) =
                normalizedPatchWeight weight r z head *
                  consumingTraceMass weight rowPolicy T requirements
                    (advancePointer p head) n := by
              unfold consumingTraceMass
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro tail _htail
              simp only [ConsumesRequirements, traceMass, Fin.cons_zero,
                Fin.tail_cons, r, z, hrow]
              split <;> ring
            _ ≤ normalizedPatchWeight weight r z head *
                  requirementsWeight weight requirements :=
              mul_le_mul_of_nonneg_left hi hnorm0
        calc
          (∑ head : PartialAssignment Source State,
              ∑ tail : PatchTrace Source State n,
                if ConsumesRequirements rowPolicy T requirements p (n + 1)
                    (Fin.cons head tail) then
                  traceMass weight rowPolicy T p (n + 1)
                    (Fin.cons head tail)
                else 0) ≤
              ∑ head : PartialAssignment Source State,
                normalizedPatchWeight weight r z head *
                  requirementsWeight weight requirements :=
            Finset.sum_le_sum fun head _hhead ↦ hstep head
          _ = requirementsWeight weight requirements := by
            rw [← Finset.sum_mul, sum_normalizedPatchWeight weight
              (ne_of_gt htotalPos), one_mul]
      · obtain ⟨required, rest, hrowCons⟩ :
            ∃ required rest, requirements r = required :: rest := by
          cases hlist : requirements r with
          | nil => exact (hrow hlist).elim
          | cons required rest => exact ⟨required, rest, rfl⟩
        have hi := ih (consumeHead requirements r)
          (advancePointer p required)
        have hnorm0 :
            0 ≤ normalizedPatchWeight weight r z required :=
          normalizedPatchWeight_nonneg hweight htotalPos required
        have hnormLe :
            normalizedPatchWeight weight r z required ≤
              weight r required :=
          normalizedPatchWeight_le_weight hweight htotalHere required
        calc
          (∑ head : PartialAssignment Source State,
              ∑ tail : PatchTrace Source State n,
                if ConsumesRequirements rowPolicy T requirements p (n + 1)
                    (Fin.cons head tail) then
                  traceMass weight rowPolicy T p (n + 1)
                    (Fin.cons head tail)
                else 0) =
              ∑ tail : PatchTrace Source State n,
                if ConsumesRequirements rowPolicy T requirements p (n + 1)
                    (Fin.cons required tail) then
                  traceMass weight rowPolicy T p (n + 1)
                    (Fin.cons required tail)
                else 0 := by
            apply Finset.sum_eq_single required
            · intro head _hhead hne
              have hheadNe : head ≠ required := hne
              apply Finset.sum_eq_zero
              intro tail _htail
              simp [ConsumesRequirements, r, z, hrowCons, hheadNe]
            · intro hnot
              exact (hnot (Finset.mem_univ required)).elim
          _ = normalizedPatchWeight weight r z required *
                consumingTraceMass weight rowPolicy T
                  (consumeHead requirements r)
                  (advancePointer p required) n := by
            unfold consumingTraceMass
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro tail _htail
            simp only [ConsumesRequirements, traceMass, Fin.cons_zero,
              Fin.tail_cons, r, z, hrowCons, true_and]
            split <;> ring
          _ ≤ normalizedPatchWeight weight r z required *
                requirementsWeight weight (consumeHead requirements r) :=
            mul_le_mul_of_nonneg_left hi hnorm0
          _ ≤ weight r required *
                requirementsWeight weight (consumeHead requirements r) := by
            exact mul_le_mul_of_nonneg_right hnormLe
              (requirementsWeight_nonneg hweight
                (consumeHead requirements r))
          _ = requirementsWeight weight requirements :=
            (requirementsWeight_cons weight requirements r required rest
              hrowCons).symm

end

end WeightedEdgeColoring.FinitePartialResamplingTracePrefixes
