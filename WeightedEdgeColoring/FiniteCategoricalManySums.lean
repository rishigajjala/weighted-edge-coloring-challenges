import WeightedEdgeColoring.FiniteCategoricalBernstein
import WeightedEdgeColoring.FiniteCategoricalEventLLL
import WeightedEdgeColoring.ColumnMassSelection

/-!
# A count-independent categorical Bernstein--LLL selector

This file proves a simultaneous categorical assignment theorem whose error
does not depend on the number of sources, states, or rows.  If every row has
fractional mean at most `R` and the support-overlap graph of the row events
has degree at most `d`, one can select one state at every source with additive
row error

`2 * sqrt (R * log (4(d+1))) + 2 * log (4(d+1))`.

The first part extends the finite categorical Bernstein estimate to every
deviation, including deviations larger than twice the mean bound.  The second
part supplies all numerical details for the finite support-overlap local
lemma.

This is a genuine simultaneous, count-independent theorem, but it does not
yet derive the overlap degree `d` from a weighted column-sum bound alone.
That implication is false for the ordinary support graph: one column may have
arbitrarily many nonzero entries of arbitrarily small size while its total
mass stays bounded.  Replacing `d` by weighted column mass therefore needs a
mass-sensitive local lemma or partial-resampling theorem; this is the exact
remaining Harris--Srinivasan step.
-/

namespace WeightedEdgeColoring.FiniteCategoricalSelection

open scoped BigOperators

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- Full-range categorical Bernstein bound.  For small deviations this is
the quadratic estimate already proved in `FiniteCategoricalBernstein`; for
deviations above `2M`, choosing exponential parameter one gives linear
decay. -/
theorem categorical_centered_upperTail_mass_le_all
    (prob : Source → State → ℝ) (use : Source → State → Row → ℝ)
    (r : Row) (M t : ℝ)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huse1 : ∀ s a r, use s a r ≤ 1)
    (hmeanM : rowMean prob use r ≤ M)
    (hM : 0 < M) (ht0 : 0 ≤ t) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (categoricalMass prob)
        (badRow use (fun _ ↦ rowMean prob use r + t) r) ≤
      Real.exp (-min (t ^ 2 / (4 * M)) (t / 2)) := by
  have hmean0 : 0 ≤ rowMean prob use r := by
    unfold rowMean
    exact Finset.sum_nonneg fun s _ ↦
      Finset.sum_nonneg fun a _ ↦ mul_nonneg (hprob0 s a) (huse0 s a r)
  by_cases htM : t ≤ 2 * M
  · have hquad : t ^ 2 / (4 * M) ≤ t / 2 := by
      apply (div_le_iff₀ (show (0 : ℝ) < 4 * M by positivity)).2
      nlinarith
    calc
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (categoricalMass prob)
          (badRow use (fun _ ↦ rowMean prob use r + t) r) ≤
          Real.exp (-(t ^ 2) / (4 * M)) :=
        categorical_centered_upperTail_mass_le prob use r M t
          hprob0 hprobSum huse0 huse1 hmeanM hM ht0 htM
      _ = Real.exp (-min (t ^ 2 / (4 * M)) (t / 2)) := by
        rw [min_eq_left hquad]
        congr 1
        ring
  · have hrem0 : 0 ≤ Real.exp (1 : ℝ) - 1 - 1 := by
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have hrem1 : Real.exp (1 : ℝ) - 1 - 1 ≤ 1 := by
      simpa using
        (exp_sub_one_sub_id_le_sq (x := (1 : ℝ)) (by norm_num) (by norm_num))
    have hlinear :
        -1 * (rowMean prob use r + t) +
            (Real.exp 1 - 1) * rowMean prob use r ≤ -t / 2 := by
      calc
        -1 * (rowMean prob use r + t) +
            (Real.exp 1 - 1) * rowMean prob use r =
            -t + (Real.exp 1 - 1 - 1) * rowMean prob use r := by ring
        _ ≤ -t + (Real.exp 1 - 1 - 1) * M := by
          gcongr
        _ ≤ -t + M := by
          simpa [add_comm] using add_le_add_left
            ((mul_le_mul_of_nonneg_right hrem1 hM.le).trans_eq (one_mul M)) (-t)
        _ ≤ -t / 2 := by linarith
    have hhalf : t / 2 ≤ t ^ 2 / (4 * M) := by
      apply (le_div_iff₀ (show (0 : ℝ) < 4 * M by positivity)).2
      nlinarith
    calc
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (categoricalMass prob)
          (badRow use (fun _ ↦ rowMean prob use r + t) r) ≤
          Real.exp (-1 * (rowMean prob use r + t) +
            (Real.exp 1 - 1) * rowMean prob use r) :=
        categorical_badRow_mass_le prob use
          (fun _ ↦ rowMean prob use r + t) r 1
          hprob0 hprobSum huse0 huse1 (by norm_num)
      _ ≤ Real.exp (-t / 2) := Real.exp_le_exp.mpr hlinear
      _ = Real.exp (-min (t ^ 2 / (4 * M)) (t / 2)) := by
        rw [min_eq_right hhalf]
        congr 1
        ring

/-- Deviation used by the simultaneous selector. -/
noncomputable def manySumsDeviation (R L : ℝ) : ℝ :=
  2 * Real.sqrt (R * L) + 2 * L

theorem manySumsDeviation_nonneg
    {R L : ℝ} (hL : 0 ≤ L) :
    0 ≤ manySumsDeviation R L := by
  unfold manySumsDeviation
  positivity

/-- Substituting `2 sqrt(RL) + 2L` in the full-range Bernstein exponent
makes the tail at most `exp(-L)`. -/
theorem exp_neg_min_at_manySumsDeviation_le
    {R L : ℝ} (hR : 0 < R) (hL : 0 ≤ L) :
    Real.exp (-min
        ((manySumsDeviation R L) ^ 2 / (4 * R))
        (manySumsDeviation R L / 2)) ≤
      Real.exp (-L) := by
  have hRL : 0 ≤ R * L := mul_nonneg hR.le hL
  have hsqrt0 : 0 ≤ Real.sqrt (R * L) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (R * L)) ^ 2 = R * L :=
    Real.sq_sqrt hRL
  have hquad : L ≤ (manySumsDeviation R L) ^ 2 / (4 * R) := by
    apply (le_div_iff₀ (show (0 : ℝ) < 4 * R by positivity)).2
    unfold manySumsDeviation
    nlinarith
  have hlinear : L ≤ manySumsDeviation R L / 2 := by
    unfold manySumsDeviation
    linarith
  exact Real.exp_le_exp.mpr (neg_le_neg (le_min hquad hlinear))

/-- Categorical Bernstein with the deviation already chosen in the form
needed by a simultaneous local-lemma application. -/
theorem categorical_centered_upperTail_mass_le_exp_neg
    (prob : Source → State → ℝ) (use : Source → State → Row → ℝ)
    (r : Row) (R L : ℝ)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huse1 : ∀ s a r, use s a r ≤ 1)
    (hmeanR : rowMean prob use r ≤ R)
    (hR : 0 < R) (hL : 0 ≤ L) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (categoricalMass prob)
        (badRow use
          (fun _ ↦ rowMean prob use r + manySumsDeviation R L) r) ≤
      Real.exp (-L) := by
  exact (categorical_centered_upperTail_mass_le_all prob use r R
      (manySumsDeviation R L) hprob0 hprobSum huse0 huse1 hmeanR hR
      (manySumsDeviation_nonneg hL)).trans
    (exp_neg_min_at_manySumsDeviation_le hR hL)

/-- The elementary numerical witness for the symmetric local lemma. -/
theorem quarter_inv_degree_le_lllWitness (d : ℕ) :
    1 / (4 * (d + 1 : ℝ)) ≤
      (1 / (2 * (d + 1 : ℝ))) *
        (1 - 1 / (2 * (d + 1 : ℝ))) ^ d := by
  let x : ℝ := 1 / (2 * (d + 1 : ℝ))
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have hx0 : 0 ≤ x := by unfold x; positivity
  have hxHalf : x ≤ 1 / 2 := by
    unfold x
    apply (div_le_iff₀ (show (0 : ℝ) < 2 * (d + 1 : ℝ) by positivity)).2
    have : (1 : ℝ) ≤ d + 1 := by exact_mod_cast Nat.le_add_left 1 d
    nlinarith
  have hbern := one_add_mul_le_pow (a := -x) (by linarith) d
  have hpower : (1 / 2 : ℝ) ≤ (1 - x) ^ d := by
    calc
      (1 / 2 : ℝ) ≤ 1 + (d : ℝ) * (-x) := by
        unfold x
        field_simp
        have hd0 : (0 : ℝ) ≤ d := by positivity
        linarith
      _ ≤ (1 + -x) ^ d := hbern
      _ = (1 - x) ^ d := by ring
  have hmul := mul_le_mul_of_nonneg_left hpower hx0
  calc
    1 / (4 * (d + 1 : ℝ)) =
        (1 / (2 * (d + 1 : ℝ))) * (1 / 2) := by
      field_simp
      ring
    _ ≤ (1 / (2 * (d + 1 : ℝ))) *
        (1 - 1 / (2 * (d + 1 : ℝ))) ^ d := by
      simpa [x] using hmul

/-- Logarithmic parameter used by the support-degree theorem. -/
noncomputable def supportDegreeLog (d : ℕ) : ℝ :=
  Real.log (4 * (d + 1 : ℝ))

theorem supportDegreeLog_nonneg (d : ℕ) : 0 ≤ supportDegreeLog d := by
  unfold supportDegreeLog
  apply Real.log_nonneg
  have hd0 : (0 : ℝ) ≤ d := by positivity
  linarith

theorem exp_neg_supportDegreeLog (d : ℕ) :
    Real.exp (-supportDegreeLog d) = 1 / (4 * (d + 1 : ℝ)) := by
  unfold supportDegreeLog
  rw [Real.exp_neg, Real.exp_log (show (0 : ℝ) < 4 * (d + 1 : ℝ) by positivity)]
  simp [div_eq_mul_inv]

/-! ## Converting a column bound to ordinary support degree under granularity -/

omit [DecidableEq Source] [DecidableEq State] [Fintype Row] [DecidableEq Row] in
/-- A positive lower bound on probabilities and nonzero entries converts a
row-mean bound into a bound on the number of sources read by that row. -/
theorem rowSupport_card_le_of_mean_and_min_entry
    (prob : Source → State → ℝ) (use : Source → State → Row → ℝ)
    (r : Row) (R p tau : ℝ) (A : ℕ)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobLower : ∀ s a, p ≤ prob s a)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huseMin : ∀ s a r, use s a r ≠ 0 → tau ≤ use s a r)
    (hp : 0 < p) (htau : 0 < tau)
    (hmeanR : rowMean prob use r ≤ R)
    (hA : R < ((A + 1 : ℕ) : ℝ) * p * tau) :
    (rowSupport use r).card ≤ A := by
  let K := rowSupport use r
  have hsource : ∀ s ∈ K,
      p * tau ≤ ∑ a, prob s a * use s a r := by
    intro s hs
    have hex : ∃ a, use s a r ≠ 0 := by
      simpa [K, rowSupport] using hs
    obtain ⟨a, ha⟩ := hex
    have hterm : p * tau ≤ prob s a * use s a r := by
      calc
        p * tau ≤ prob s a * tau :=
          mul_le_mul_of_nonneg_right (hprobLower s a) htau.le
        _ ≤ prob s a * use s a r :=
          mul_le_mul_of_nonneg_left (huseMin s a r ha) (hprob0 s a)
    exact hterm.trans (Finset.single_le_sum
      (fun b _ ↦ mul_nonneg (hprob0 s b) (huse0 s b r))
      (Finset.mem_univ a))
  have htotal : ((K.card : ℕ) : ℝ) * p * tau ≤ R := by
    calc
      ((K.card : ℕ) : ℝ) * p * tau = ∑ _s ∈ K, p * tau := by
        simp [mul_assoc]
      _ ≤ ∑ s ∈ K, ∑ a, prob s a * use s a r :=
        Finset.sum_le_sum hsource
      _ ≤ ∑ s, ∑ a, prob s a * use s a r := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun _ _ ↦ Finset.mem_univ _)
          (fun s _ _ ↦ Finset.sum_nonneg fun a _ ↦
            mul_nonneg (hprob0 s a) (huse0 s a r))
      _ = rowMean prob use r := rfl
      _ ≤ R := hmeanR
  change K.card ≤ A
  by_contra hnot
  have hcard : A + 1 ≤ K.card := by omega
  have hcast : (((A + 1 : ℕ) : ℝ)) ≤ (K.card : ℝ) := by
    exact_mod_cast hcard
  have hscale : (((A + 1 : ℕ) : ℝ)) * p * tau ≤
      (K.card : ℝ) * p * tau := by
    gcongr
  linarith

omit [DecidableEq State] [DecidableEq Row] in
/-- If every nonzero entry has size at least `tau`, a weighted column bound
controls the number of rows read by one source.  The factor `|State|` pays for
the union of the supports of its possible states. -/
theorem supportIncidence_card_le_of_columnMass_and_min_entry
    (use : Source → State → Row → ℝ) (s : Source)
    (C tau : ℝ) (B : ℕ)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huseMin : ∀ s a r, use s a r ≠ 0 → tau ≤ use s a r)
    (hcolumn : ∀ s a, ∑ r, use s a r ≤ C)
    (htau : 0 < tau)
    (hB : ((Fintype.card State : ℕ) : ℝ) * C <
      ((B + 1 : ℕ) : ℝ) * tau) :
    (WeightedEdgeColoring.FiniteCategoricalEventLLL.supportIncidence
      (rowSupport use) s).card ≤ B := by
  let I := WeightedEdgeColoring.FiniteCategoricalEventLLL.supportIncidence
    (rowSupport use) s
  have hrow : ∀ r ∈ I, tau ≤ ∑ a, use s a r := by
    intro r hr
    have hrs : s ∈ rowSupport use r := by
      simpa [I, WeightedEdgeColoring.FiniteCategoricalEventLLL.supportIncidence] using hr
    have hex : ∃ a, use s a r ≠ 0 := by
      simpa [rowSupport] using hrs
    obtain ⟨a, ha⟩ := hex
    exact (huseMin s a r ha).trans
      (Finset.single_le_sum (fun b _ ↦ huse0 s b r) (Finset.mem_univ a))
  have htotal : ((I.card : ℕ) : ℝ) * tau ≤
      ((Fintype.card State : ℕ) : ℝ) * C := by
    calc
      ((I.card : ℕ) : ℝ) * tau = ∑ _r ∈ I, tau := by simp
      _ ≤ ∑ r ∈ I, ∑ a, use s a r := Finset.sum_le_sum hrow
      _ ≤ ∑ r, ∑ a, use s a r := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun _ _ ↦ Finset.mem_univ _)
          (fun r _ _ ↦ Finset.sum_nonneg fun a _ ↦ huse0 s a r)
      _ = ∑ a, ∑ r, use s a r := by rw [Finset.sum_comm]
      _ ≤ ∑ _a : State, C := Finset.sum_le_sum fun a _ ↦ hcolumn s a
      _ = ((Fintype.card State : ℕ) : ℝ) * C := by simp
  change I.card ≤ B
  by_contra hnot
  have hcard : B + 1 ≤ I.card := by omega
  have hcast : (((B + 1 : ℕ) : ℝ)) ≤ (I.card : ℝ) := by
    exact_mod_cast hcard
  have hscale : (((B + 1 : ℕ) : ℝ)) * tau ≤
      (I.card : ℝ) * tau := mul_le_mul_of_nonneg_right hcast htau.le
  linarith

omit [DecidableEq State] in
/-- Granularity converts the row-mean and column-mass estimates into a
support-overlap degree bound. -/
theorem rowSupport_overlapNeighbor_card_le_of_mean_column_min_entry
    (prob : Source → State → ℝ) (use : Source → State → Row → ℝ)
    (R p C tau : ℝ) (A B : ℕ)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobLower : ∀ s a, p ≤ prob s a)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huseMin : ∀ s a r, use s a r ≠ 0 → tau ≤ use s a r)
    (hcolumn : ∀ s a, ∑ r, use s a r ≤ C)
    (hp : 0 < p) (htau : 0 < tau)
    (hmeanR : ∀ r, rowMean prob use r ≤ R)
    (hA : R < ((A + 1 : ℕ) : ℝ) * p * tau)
    (hB : ((Fintype.card State : ℕ) : ℝ) * C <
      ((B + 1 : ℕ) : ℝ) * tau)
    (r : Row) :
    (WeightedEdgeColoring.FiniteCategoricalEventLLL.overlapNeighbor
      (rowSupport use) r).card ≤ A * B := by
  apply WeightedEdgeColoring.FiniteCategoricalEventLLL.overlapNeighbor_card_le
    (rowSupport use) A B
  · intro q
    exact rowSupport_card_le_of_mean_and_min_entry
      prob use q R p tau A hprob0 hprobLower huse0 huseMin hp htau
      (hmeanR q) hA
  · intro s
    exact supportIncidence_card_le_of_columnMass_and_min_entry
      use s C tau B huse0 huseMin hcolumn htau hB

/-- Simultaneous categorical selection with a Bernstein-size error.  The
conclusion is independent of the cardinalities of all three finite types.
Only the support-overlap degree `d` appears. -/
theorem exists_choice_rowLoad_lt_mean_add_manySumsDeviation
    (prob : Source → State → ℝ) (use : Source → State → Row → ℝ)
    (R : ℝ) (d : ℕ)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huse1 : ∀ s a r, use s a r ≤ 1)
    (hmeanR : ∀ r, rowMean prob use r ≤ R)
    (hR : 0 < R)
    (hdegree : ∀ r,
      (WeightedEdgeColoring.FiniteCategoricalEventLLL.overlapNeighbor
        (rowSupport use) r).card ≤ d) :
    ∃ choice : Source → State, ∀ r,
      rowLoad use r choice <
        rowMean prob use r + manySumsDeviation R (supportDegreeLog d) := by
  let L := supportDegreeLog d
  let t := manySumsDeviation R L
  let threshold : Row → ℝ := fun r ↦ rowMean prob use r + t
  let p : ℝ := 1 / (4 * (d + 1 : ℝ))
  let x : ℝ := 1 / (2 * (d + 1 : ℝ))
  obtain ⟨choice, hchoice⟩ :=
    WeightedEdgeColoring.FiniteCategoricalEventLLL.exists_avoids_of_support_overlap
      prob (badRow use threshold) (rowSupport use) p x d
      hprob0 hprobSum
      (fun r ↦ badRow_dependsOn_rowSupport use threshold r)
      hdegree
      (by dsimp [x]; positivity)
      (by
        dsimp [x]
        have hd1 : (1 : ℝ) ≤ d + 1 := by
          exact_mod_cast Nat.le_add_left 1 d
        have hden : (0 : ℝ) < 2 * (d + 1 : ℝ) := by positivity
        apply (div_lt_one hden).2
        nlinarith)
      (by simpa [p, x] using quarter_inv_degree_le_lllWitness d)
      (by
        intro r
        have htail := categorical_centered_upperTail_mass_le_exp_neg
          prob use r R L hprob0 hprobSum huse0 huse1 (hmeanR r) hR
          (by simpa [L] using supportDegreeLog_nonneg d)
        simpa [badRow, threshold, t, L, p, exp_neg_supportDegreeLog d] using htail)
  refine ⟨choice, ?_⟩
  intro r
  have := hchoice r
  simpa [badRow, threshold, t, L, not_le] using this

/-- Column-mass specialization when probabilities and nonzero entries have
positive granularity.  The two elementary scale inequalities define support
bounds `A` and `B`; the resulting error is logarithmic in their product. -/
theorem exists_choice_rowLoad_lt_mean_add_manySumsDeviation_of_column_min_entry
    (prob : Source → State → ℝ) (use : Source → State → Row → ℝ)
    (R p C tau : ℝ) (A B : ℕ)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (hprobLower : ∀ s a, p ≤ prob s a)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huse1 : ∀ s a r, use s a r ≤ 1)
    (huseMin : ∀ s a r, use s a r ≠ 0 → tau ≤ use s a r)
    (hcolumn : ∀ s a, ∑ r, use s a r ≤ C)
    (hmeanR : ∀ r, rowMean prob use r ≤ R)
    (hR : 0 < R) (hp : 0 < p) (htau : 0 < tau)
    (hA : R < ((A + 1 : ℕ) : ℝ) * p * tau)
    (hB : ((Fintype.card State : ℕ) : ℝ) * C <
      ((B + 1 : ℕ) : ℝ) * tau) :
    ∃ choice : Source → State, ∀ r,
      rowLoad use r choice < rowMean prob use r +
        manySumsDeviation R (supportDegreeLog (A * B)) := by
  apply exists_choice_rowLoad_lt_mean_add_manySumsDeviation
    prob use R (A * B) hprob0 hprobSum huse0 huse1 hmeanR hR
  intro r
  exact rowSupport_overlapNeighbor_card_le_of_mean_column_min_entry
    prob use R p C tau A B hprob0 hprobLower huse0 huseMin hcolumn
    hp htau hmeanR hA hB r

/-- Finset form of the simultaneous selector: the selected pairs contain
exactly one state for every source. -/
theorem exists_stateSelection_load_lt_mean_add_manySumsDeviation
    (prob : Source → State → ℝ) (use : Source → State → Row → ℝ)
    (R : ℝ) (d : ℕ)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huse1 : ∀ s a r, use s a r ≤ 1)
    (hmeanR : ∀ r, rowMean prob use r ≤ R)
    (hR : 0 < R)
    (hdegree : ∀ r,
      (WeightedEdgeColoring.FiniteCategoricalEventLLL.overlapNeighbor
        (rowSupport use) r).card ≤ d) :
    ∃ selected : Finset (Source × State),
      WeightedEdgeColoring.IsStateSelection selected ∧
      ∀ r, (∑ o ∈ selected, use o.1 o.2 r) <
        rowMean prob use r + manySumsDeviation R (supportDegreeLog d) := by
  obtain ⟨choice, hchoice⟩ :=
    exists_choice_rowLoad_lt_mean_add_manySumsDeviation
      prob use R d hprob0 hprobSum huse0 huse1 hmeanR hR hdegree
  let selected : Finset (Source × State) :=
    Finset.univ.filter fun o ↦ o.2 = choice o.1
  have hselection : WeightedEdgeColoring.IsStateSelection selected := by
    intro s
    refine ⟨choice s, by simp [selected], ?_⟩
    intro a ha
    simpa [selected] using ha
  refine ⟨selected, hselection, ?_⟩
  intro r
  have hload : (∑ o ∈ selected, use o.1 o.2 r) = rowLoad use r choice := by
    simp only [selected, Finset.sum_filter, rowLoad, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _hs
    simp
  rw [hload]
  exact hchoice r

/-- Hybrid of count-independent support-degree selection and deterministic
column-mass rounding.  When both hypotheses are available, the additive
error is the smaller of the column mass and the Bernstein--LLL deviation.

The theorem deliberately retains `d`: bounded column mass by itself does not
bound the ordinary support-overlap degree. -/
theorem exists_stateSelection_load_le_mean_add_min_column_deviation
    (prob : Source → State → ℝ) (use : Source → State → Row → ℝ)
    (R C : ℝ) (d : ℕ)
    (hC : 0 < C)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huse1 : ∀ s a r, use s a r ≤ 1)
    (hcolumn : ∀ s a, ∑ r, use s a r ≤ C)
    (hmeanR : ∀ r, rowMean prob use r ≤ R)
    (hR : 0 < R)
    (hdegree : ∀ r,
      (WeightedEdgeColoring.FiniteCategoricalEventLLL.overlapNeighbor
        (rowSupport use) r).card ≤ d) :
    ∃ selected : Finset (Source × State),
      WeightedEdgeColoring.IsStateSelection selected ∧
      ∀ r, (∑ o ∈ selected, use o.1 o.2 r) ≤
        rowMean prob use r +
          min C (manySumsDeviation R (supportDegreeLog d)) := by
  by_cases hsmall : C ≤ manySumsDeviation R (supportDegreeLog d)
  · obtain ⟨selected, hselection, hload⟩ :=
      WeightedEdgeColoring.exists_columnMass_profile_selection
        prob use C hC hprob0 hprobSum huse0 hcolumn
    refine ⟨selected, hselection, ?_⟩
    intro r
    have hr := hload r
    simpa [WeightedEdgeColoring.profileRowMean, rowMean, min_eq_left hsmall] using hr
  · have hdeviation : manySumsDeviation R (supportDegreeLog d) ≤ C :=
      le_of_not_ge hsmall
    obtain ⟨selected, hselection, hload⟩ :=
      exists_stateSelection_load_lt_mean_add_manySumsDeviation
        prob use R d hprob0 hprobSum huse0 huse1 hmeanR hR hdegree
    refine ⟨selected, hselection, ?_⟩
    intro r
    have hr := (hload r).le
    simpa [min_eq_right hdeviation] using hr

end WeightedEdgeColoring.FiniteCategoricalSelection
