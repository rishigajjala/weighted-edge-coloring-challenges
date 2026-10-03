import WeightedEdgeColoring.RankThreeMatching
import WeightedEdgeColoring.OptionNormalization
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# Integer copies of fractional rank-three options

The whole-edge construction first produces nonnegative real masses on
options and then replaces an option of mass `x` by `floor (N*x)` distinct
copies.  This file makes that passage exact.  It is independent of the
probabilistic matching theorem: the statements below are the deterministic
degree and codegree estimates needed in order to invoke such a theorem.
-/

noncomputable section

universe u v w

/-! ## Explicit copies and their finite degrees -/

/-- `IntegerCopy Option mult` contains exactly `mult o` labelled copies of
the base option `o`.  The labels make repeated hyperedges honest elements of
a finite type, so all subsequent matching statements can count them without
using a multiset convention. -/
abbrev IntegerCopy (Option : Type w) (mult : Option → ℕ) :=
  Sigma fun o : Option ↦ Fin (mult o)

namespace IntegerCopy

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]

/-- Replacing every base option by `mult o` labelled copies preserves its
owner and the slots that it uses. -/
def system (H : RankThreeOptionSystem Job Slot Option)
    (mult : Option → ℕ) :
    RankThreeOptionSystem Job Slot (IntegerCopy Option mult) where
  owner q := H.owner q.1
  slots q := H.slots q.1
  slots_card_le_two q := H.slots_card_le_two q.1

@[simp] theorem system_owner
    (H : RankThreeOptionSystem Job Slot Option) (mult : Option → ℕ)
    (q : IntegerCopy Option mult) :
    (system H mult).owner q = H.owner q.1 := rfl

@[simp] theorem system_slots
    (H : RankThreeOptionSystem Job Slot Option) (mult : Option → ℕ)
    (q : IntegerCopy Option mult) :
    (system H mult).slots q = H.slots q.1 := rfl

/-- Filtering labelled copies by a property of the base option is the same
as first filtering the base options and then taking all their labels. -/
def predicateSubtypeEquiv (mult : Option → ℕ) (p : Option → Prop)
    [DecidablePred p] :
    {q : IntegerCopy Option mult // p q.1} ≃
      Sigma fun o : {o : Option // p o} ↦ Fin (mult o.1) where
  toFun q := ⟨⟨q.1.1, q.2⟩, q.1.2⟩
  invFun q := ⟨⟨q.1.1, q.2⟩, q.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Cardinality formula for a property-filtered family of labelled copies. -/
theorem card_filter_fst_eq_sum_ite (mult : Option → ℕ)
    (p : Option → Prop) [DecidablePred p] :
    ((Finset.univ : Finset (IntegerCopy Option mult)).filter
        (fun q ↦ p q.1)).card =
      ∑ o : Option, if p o then mult o else 0 := by
  classical
  calc
    ((Finset.univ : Finset (IntegerCopy Option mult)).filter
        (fun q ↦ p q.1)).card =
        Fintype.card {q : IntegerCopy Option mult // p q.1} := by
          rw [Fintype.card_subtype]
    _ = Fintype.card
        (Sigma fun o : {o : Option // p o} ↦ Fin (mult o.1)) :=
      Fintype.card_congr (predicateSubtypeEquiv mult p)
    _ = ∑ o : {o : Option // p o}, mult o.1 := by
      rw [Fintype.card_sigma]
      simp
    _ = ∑ o : Option, if p o then mult o else 0 := by
      symm
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter p) (by simp) mult

/-- Copies in one job fibre are the dependent sum of the copies of its base
options.  This equivalence is the bookkeeping bridge used in all degree
calculations below. -/
def fiberSubtypeEquiv
    (H : RankThreeOptionSystem Job Slot Option) (mult : Option → ℕ)
    (j : Job) :
    {q : IntegerCopy Option mult // (system H mult).owner q = j} ≃
      Sigma fun o : {o : Option // H.owner o = j} ↦ Fin (mult o.1) where
  toFun q := ⟨⟨q.1.1, q.2⟩, q.1.2⟩
  invFun q := ⟨⟨q.1.1, q.2⟩, q.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The copied degree of a job is the sum of the chosen multiplicities of
its base options. -/
theorem fiber_card_eq_sum
    (H : RankThreeOptionSystem Job Slot Option) (mult : Option → ℕ)
    (j : Job) :
    ((system H mult).fiber j).card = ∑ o ∈ H.fiber j, mult o := by
  classical
  calc
    ((system H mult).fiber j).card =
        Fintype.card {q : IntegerCopy Option mult //
          (system H mult).owner q = j} := by
            rw [Fintype.card_subtype]
            rfl
    _ = Fintype.card
        (Sigma fun o : {o : Option // H.owner o = j} ↦ Fin (mult o.1)) :=
      Fintype.card_congr (fiberSubtypeEquiv H mult j)
    _ = ∑ o : {o : Option // H.owner o = j}, mult o.1 := by
      rw [Fintype.card_sigma]
      simp
    _ = ∑ o ∈ H.fiber j, mult o := by
      rw [Finset.sum_subtype (H.fiber j)]
      intro o
      simp [RankThreeOptionSystem.mem_fiber]

/-- Copies of options of job `j` that use slot `s` are a dependent sum over
the corresponding base options. -/
def jobSlotSubtypeEquiv
    (H : RankThreeOptionSystem Job Slot Option) (mult : Option → ℕ)
    (j : Job) (s : Slot) :
    {q : IntegerCopy Option mult //
        (system H mult).owner q = j ∧ s ∈ (system H mult).slots q} ≃
      Sigma fun o : {o : Option // H.owner o = j ∧ s ∈ H.slots o} ↦
        Fin (mult o.1) where
  toFun q := ⟨⟨q.1.1, q.2⟩, q.1.2⟩
  invFun q := ⟨⟨q.1.1, q.2⟩, q.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact copied job-slot codegree. -/
theorem jobSlotCodegree_eq_sum
    (H : RankThreeOptionSystem Job Slot Option) (mult : Option → ℕ)
    (j : Job) (s : Slot) :
    (system H mult).jobSlotCodegree j s =
      ∑ o ∈ H.fiber j, if s ∈ H.slots o then mult o else 0 := by
  classical
  calc
    (system H mult).jobSlotCodegree j s =
        Fintype.card {q : IntegerCopy Option mult //
          (system H mult).owner q = j ∧ s ∈ (system H mult).slots q} := by
            rw [Fintype.card_subtype]
            unfold RankThreeOptionSystem.jobSlotCodegree
            congr 1
            ext q
            simp [RankThreeOptionSystem.fiber]
    _ = Fintype.card
        (Sigma fun o : {o : Option // H.owner o = j ∧ s ∈ H.slots o} ↦
          Fin (mult o.1)) :=
      Fintype.card_congr (jobSlotSubtypeEquiv H mult j s)
    _ = ∑ o : {o : Option // H.owner o = j ∧ s ∈ H.slots o}, mult o.1 := by
      rw [Fintype.card_sigma]
      simp
    _ = ∑ o : Option,
        if H.owner o = j ∧ s ∈ H.slots o then mult o else 0 := by
      symm
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype
        (Finset.univ.filter fun o : Option ↦
          H.owner o = j ∧ s ∈ H.slots o) (by simp) mult
    _ = ∑ o ∈ H.fiber j, if s ∈ H.slots o then mult o else 0 := by
      rw [RankThreeOptionSystem.fiber, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro o _ho
      by_cases hj : H.owner o = j <;>
        by_cases hs : s ∈ H.slots o <;> simp [hj, hs]

end IntegerCopy

/-- The number of integer copies obtained by scaling a nonnegative mass. -/
def quantizedMultiplicity (N : ℕ) (x : ℝ) : ℕ :=
  ⌊(N : ℝ) * x⌋₊

/-- Distinct integer copies of a finite family of fractional options. -/
abbrev QuantizedCopy {Option : Type u} (N : ℕ) (x : Option → ℝ) :=
  IntegerCopy Option (fun o ↦ quantizedMultiplicity N (x o))

namespace RankThreeOptionSystem

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]

/-- Replace every option by `floor (N*x)` distinct copies.  Copies retain
their owner's job and their original set of at most two slots. -/
def quantized (H : RankThreeOptionSystem Job Slot Option)
    (N : ℕ) (x : Option → ℝ) :
    RankThreeOptionSystem Job Slot (QuantizedCopy N x) :=
  IntegerCopy.system H (fun o ↦ quantizedMultiplicity N (x o))

/-- The number of quantized copies belonging to one job. -/
def quantizedJobDegree (H : RankThreeOptionSystem Job Slot Option)
    (N : ℕ) (x : Option → ℝ) (j : Job) : ℕ :=
  ∑ o, if H.owner o = j then quantizedMultiplicity N (x o) else 0

/-- The number of quantized copies of one job that use one slot. -/
def quantizedJobSlotCodegree (H : RankThreeOptionSystem Job Slot Option)
    (N : ℕ) (x : Option → ℝ) (j : Job) (s : Slot) : ℕ :=
  ∑ o, if H.owner o = j ∧ s ∈ H.slots o then
    quantizedMultiplicity N (x o) else 0

/-- Number of options using a slot.  This is the degree of a `B`-vertex in
the rank-three hypergraph. -/
def slotDegree (H : RankThreeOptionSystem Job Slot Option) (s : Slot) : ℕ :=
  ((Finset.univ : Finset Option).filter fun o ↦ s ∈ H.slots o).card

/-- Number of options simultaneously using two given slots.  Together with
`jobSlotCodegree`, this accounts for every nonzero pair-codegree in the
rank-three representation. -/
def slotPairCodegree (H : RankThreeOptionSystem Job Slot Option)
    (s t : Slot) : ℕ :=
  ((Finset.univ : Finset Option).filter fun o ↦
    s ∈ H.slots o ∧ t ∈ H.slots o).card

/-- The actual copied job degree agrees with the explicit floor sum. -/
theorem quantized_fiber_card
    (H : RankThreeOptionSystem Job Slot Option)
    (N : ℕ) (x : Option → ℝ) (j : Job) :
    ((H.quantized N x).fiber j).card = H.quantizedJobDegree N x j := by
  classical
  change ((IntegerCopy.system H
    (fun o ↦ quantizedMultiplicity N (x o))).fiber j).card = _
  rw [IntegerCopy.fiber_card_eq_sum]
  unfold quantizedJobDegree
  rw [RankThreeOptionSystem.fiber, Finset.sum_filter]

/-- The actual copied job-slot codegree agrees with the explicit floor sum. -/
theorem quantized_jobSlotCodegree
    (H : RankThreeOptionSystem Job Slot Option)
    (N : ℕ) (x : Option → ℝ) (j : Job) (s : Slot) :
    (H.quantized N x).jobSlotCodegree j s =
      H.quantizedJobSlotCodegree N x j s := by
  classical
  change (IntegerCopy.system H
    (fun o ↦ quantizedMultiplicity N (x o))).jobSlotCodegree j s = _
  rw [IntegerCopy.jobSlotCodegree_eq_sum]
  unfold quantizedJobSlotCodegree
  rw [RankThreeOptionSystem.fiber, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro o _ho
  by_cases hj : H.owner o = j <;>
    by_cases hs : s ∈ H.slots o <;> simp [hj, hs]

/-- Exact degree of a slot after replacing masses by labelled copies. -/
theorem quantized_slotDegree
    (H : RankThreeOptionSystem Job Slot Option)
    (N : ℕ) (x : Option → ℝ) (s : Slot) :
    (H.quantized N x).slotDegree s =
      ∑ o, if s ∈ H.slots o then quantizedMultiplicity N (x o) else 0 := by
  classical
  unfold slotDegree quantized
  exact IntegerCopy.card_filter_fst_eq_sum_ite
    (fun o ↦ quantizedMultiplicity N (x o)) (fun o ↦ s ∈ H.slots o)

/-- Exact slot-pair codegree after replacing masses by labelled copies. -/
theorem quantized_slotPairCodegree
    (H : RankThreeOptionSystem Job Slot Option)
    (N : ℕ) (x : Option → ℝ) (s t : Slot) :
    (H.quantized N x).slotPairCodegree s t =
      ∑ o, if s ∈ H.slots o ∧ t ∈ H.slots o then
        quantizedMultiplicity N (x o) else 0 := by
  classical
  unfold slotPairCodegree quantized
  exact IntegerCopy.card_filter_fst_eq_sum_ite
    (fun o ↦ quantizedMultiplicity N (x o))
    (fun o ↦ s ∈ H.slots o ∧ t ∈ H.slots o)

end RankThreeOptionSystem

/-- Taking floors can only decrease a finite scaled sum. -/
theorem sum_quantizedMultiplicity_le
    {I : Type*} [Fintype I] (N : ℕ) (x : I → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    ((∑ i, quantizedMultiplicity N (x i) : ℕ) : ℝ) ≤
      (N : ℝ) * ∑ i, x i := by
  rw [Nat.cast_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _hi ↦
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (hx i))

/-- A floor loses at most one unit per term.  The weak inequality is the
form convenient for lower degree estimates. -/
theorem mul_sum_sub_card_le_sum_quantizedMultiplicity
    {I : Type*} [Fintype I] (N : ℕ) (x : I → ℝ) :
    (N : ℝ) * (∑ i, x i) - Fintype.card I ≤
      ((∑ i, quantizedMultiplicity N (x i) : ℕ) : ℝ) := by
  rw [Nat.cast_sum, Finset.mul_sum]
  have hterm : ∀ i : I,
      (N : ℝ) * x i - 1 ≤ (quantizedMultiplicity N (x i) : ℝ) := by
    intro i
    exact (sub_le_iff_le_add).2 (Nat.lt_floor_add_one ((N : ℝ) * x i)).le
  calc
    (∑ i, (N : ℝ) * x i) - Fintype.card I =
        ∑ i, ((N : ℝ) * x i - 1) := by
          rw [Finset.sum_sub_distrib]
          simp
    _ ≤ ∑ i, (quantizedMultiplicity N (x i) : ℝ) :=
      Finset.sum_le_sum fun i _hi ↦ hterm i

/-- Finset form of `sum_quantizedMultiplicity_le`. -/
theorem sum_quantizedMultiplicity_finset_le
    {I : Type*} [Fintype I] (S : Finset I) (N : ℕ) (x : I → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) :
    ((∑ i ∈ S, quantizedMultiplicity N (x i) : ℕ) : ℝ) ≤
      (N : ℝ) * ∑ i ∈ S, x i := by
  rw [Nat.cast_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi ↦
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (hx i hi))

/-- Finset form of the one-unit-per-term lower floor estimate. -/
theorem mul_sum_sub_card_le_sum_quantizedMultiplicity_finset
    {I : Type*} [Fintype I] (S : Finset I) (N : ℕ) (x : I → ℝ) :
    (N : ℝ) * (∑ i ∈ S, x i) - S.card ≤
      ((∑ i ∈ S, quantizedMultiplicity N (x i) : ℕ) : ℝ) := by
  rw [Nat.cast_sum, Finset.mul_sum]
  have hterm : ∀ i ∈ S,
      (N : ℝ) * x i - 1 ≤ (quantizedMultiplicity N (x i) : ℝ) := by
    intro i _hi
    exact (sub_le_iff_le_add).2
      (Nat.lt_floor_add_one ((N : ℝ) * x i)).le
  calc
    (∑ i ∈ S, (N : ℝ) * x i) - S.card =
        ∑ i ∈ S, ((N : ℝ) * x i - 1) := by
          rw [Finset.sum_sub_distrib]
          simp
    _ ≤ ∑ i ∈ S, (quantizedMultiplicity N (x i) : ℝ) :=
      Finset.sum_le_sum hterm

/-- Predicate form of the upper floor estimate. -/
theorem sum_ite_quantizedMultiplicity_le
    {I : Type*} [Fintype I] (p : I → Prop) [DecidablePred p]
    (N : ℕ) (x : I → ℝ) (hx : ∀ i, p i → 0 ≤ x i) :
    ((∑ i, if p i then quantizedMultiplicity N (x i) else 0 : ℕ) : ℝ) ≤
      (N : ℝ) * ∑ i, if p i then x i else 0 := by
  have h := sum_quantizedMultiplicity_finset_le
    ((Finset.univ : Finset I).filter p) N x (by
      intro i hi
      exact hx i (Finset.mem_filter.mp hi).2)
  simpa [Finset.sum_filter] using h

namespace RankThreeOptionSystem

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]

/-- Lower degree estimate for a quantized job fibre.  The only loss is one
copy for each base option owned by the job. -/
theorem quantizedJobDegree_lower
    (H : RankThreeOptionSystem Job Slot Option)
    (N : ℕ) (x : Option → ℝ) (j : Job) :
    (N : ℝ) * (∑ o ∈ H.fiber j, x o) - (H.fiber j).card ≤
      (H.quantizedJobDegree N x j : ℝ) := by
  rw [← H.quantized_fiber_card N x j]
  change (N : ℝ) * (∑ o ∈ H.fiber j, x o) - (H.fiber j).card ≤
    (((IntegerCopy.system H
      (fun o ↦ quantizedMultiplicity N (x o))).fiber j).card : ℝ)
  rw [IntegerCopy.fiber_card_eq_sum]
  exact mul_sum_sub_card_le_sum_quantizedMultiplicity_finset (H.fiber j) N x

/-- Upper degree estimate for a quantized job fibre. -/
theorem quantizedJobDegree_upper
    (H : RankThreeOptionSystem Job Slot Option)
    (N : ℕ) (x : Option → ℝ) (j : Job)
    (hx : ∀ o ∈ H.fiber j, 0 ≤ x o) :
    (H.quantizedJobDegree N x j : ℝ) ≤
      (N : ℝ) * (∑ o ∈ H.fiber j, x o) := by
  rw [← H.quantized_fiber_card N x j]
  change ((((IntegerCopy.system H
      (fun o ↦ quantizedMultiplicity N (x o))).fiber j).card : ℕ) : ℝ) ≤
    (N : ℝ) * (∑ o ∈ H.fiber j, x o)
  rw [IntegerCopy.fiber_card_eq_sum]
  exact sum_quantizedMultiplicity_finset_le (H.fiber j) N x hx

/-- Quantization cannot increase a slot load after scaling by `N`. -/
theorem quantizedSlotDegree_upper
    (H : RankThreeOptionSystem Job Slot Option)
    (N : ℕ) (x : Option → ℝ) (s : Slot)
    (hx : ∀ o, s ∈ H.slots o → 0 ≤ x o) :
    ((H.quantized N x).slotDegree s : ℝ) ≤
      (N : ℝ) * ∑ o, if s ∈ H.slots o then x o else 0 := by
  rw [H.quantized_slotDegree N x s]
  exact sum_ite_quantizedMultiplicity_le
    (fun o ↦ s ∈ H.slots o) N x hx

/-- Quantization cannot increase a job-slot codegree after scaling by `N`. -/
theorem quantizedJobSlotCodegree_upper
    (H : RankThreeOptionSystem Job Slot Option)
    (N : ℕ) (x : Option → ℝ) (j : Job) (s : Slot)
    (hx : ∀ o, H.owner o = j ∧ s ∈ H.slots o → 0 ≤ x o) :
    ((H.quantized N x).jobSlotCodegree j s : ℝ) ≤
      (N : ℝ) * ∑ o,
        if H.owner o = j ∧ s ∈ H.slots o then x o else 0 := by
  rw [H.quantized_jobSlotCodegree N x j s]
  unfold quantizedJobSlotCodegree
  exact sum_ite_quantizedMultiplicity_le
    (fun o ↦ H.owner o = j ∧ s ∈ H.slots o) N x hx

/-- Quantization cannot increase a slot-pair codegree after scaling by `N`. -/
theorem quantizedSlotPairCodegree_upper
    (H : RankThreeOptionSystem Job Slot Option)
    (N : ℕ) (x : Option → ℝ) (s t : Slot)
    (hx : ∀ o, s ∈ H.slots o ∧ t ∈ H.slots o → 0 ≤ x o) :
    ((H.quantized N x).slotPairCodegree s t : ℝ) ≤
      (N : ℝ) * ∑ o,
        if s ∈ H.slots o ∧ t ∈ H.slots o then x o else 0 := by
  rw [H.quantized_slotPairCodegree N x s t]
  exact sum_ite_quantizedMultiplicity_le
    (fun o ↦ s ∈ H.slots o ∧ t ∈ H.slots o) N x hx

/-- The existing elementary rank-three theorem can be applied directly to
the explicit quantized copy system.  This is not the fixed-slack theorem—the
last inequality still depends on the number of jobs—but it verifies that the
copy construction exposes exactly the degree parameters expected by the
matching layer. -/
theorem exists_quantized_covering_of_codegree
    (H : RankThreeOptionSystem Job Slot Option)
    (N : ℕ) (x : Option → ℝ) (m lambda : ℕ)
    (hdegree : ∀ j, m ≤ H.quantizedJobDegree N x j)
    (hcodeg : ∀ j s, H.quantizedJobSlotCodegree N x j s ≤ lambda)
    (hroom : Fintype.card Job * (2 * lambda) < m) :
    ∃ M : Finset (QuantizedCopy N x),
      (H.quantized N x).IsPartialMatching M ∧
        ∀ j, (H.quantized N x).Covers M j := by
  apply (H.quantized N x).exists_covering_partialMatching_of_codegree
    m lambda
  · intro j
    simpa [H.quantized_fiber_card N x j] using hdegree j
  · intro j s
    simpa [H.quantized_jobSlotCodegree N x j s] using hcodeg j s
  · exact hroom

end RankThreeOptionSystem

end

end WeightedEdgeColoring
