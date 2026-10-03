import WeightedEdgeColoring.ExtraSlotBudget
import WeightedEdgeColoring.ExtraSlotOptions
import WeightedEdgeColoring.SimpleExtraPairUnique
import WeightedEdgeColoring.WeightedGraph

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# Graph-indexed extra-slot budgets

The generic Cartesian extra-slot construction is parameterized by a number
of slots at every vertex and weight class.  Here that number is instantiated
with the manuscript's residual budget

`ceil (R(v,h)/(1-gamma)) + t`.

The main theorem turns the scalar estimate from `ExtraSlotBudget` into the
copied degree bound for every concrete extra slot.
-/

noncomputable section

universe u w

namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]

/-- Total unused option mass incident with `(v,h)`, counting the two endpoint
orientations explicitly.  Looplessness ensures an edge never contributes to
both terms at the same vertex. -/
def classResidual (bucket : G.E → Class) (residual : G.E → ℝ)
    (v : G.V) (h : Class) : ℝ :=
  ∑ e,
    ((if (G.fst e, bucket e) = (v, h) then residual e else 0) +
      (if (G.snd e, bucket e) = (v, h) then residual e else 0))

theorem classResidual_nonneg (bucket : G.E → Class) (residual : G.E → ℝ)
    (hr : ∀ e, 0 ≤ residual e) (v : G.V) (h : Class) :
    0 ≤ G.classResidual bucket residual v h := by
  unfold classResidual
  apply Finset.sum_nonneg
  intro e _
  by_cases hl : (G.fst e, bucket e) = (v, h) <;>
    by_cases hr' : (G.snd e, bucket e) = (v, h) <;>
      simp [hl, hr', hr]

/-- Number of graph-indexed extra slots. -/
def graphExtraSlotCount (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) (t : ℕ) (v : G.V) (h : Class) : ℕ :=
  extraSlotCount (G.classResidual bucket residual v h) gamma t

theorem graphExtraSlotCount_pos
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) {t : ℕ} (ht : 0 < t) (v : G.V) (h : Class) :
    0 < G.graphExtraSlotCount bucket residual gamma t v h :=
  extraSlotCount_pos _ _ ht

/-- Every graph-indexed extra-slot count contains the additive reserve. -/
theorem graphExtraSlotCount_ge_reserve
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) (t : ℕ) (v : G.V) (h : Class) :
    t ≤ G.graphExtraSlotCount bucket residual gamma t v h :=
  extraSlotCount_ge_reserve _ _ _

/-- A single edge contributes at most `1/t` to any endpoint slot when its
residual is at most one. -/
theorem edgeResidual_div_graphExtraSlotCount_le_inv_reserve
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (hresidual_one : ∀ e, residual e ≤ 1)
    (gamma : ℝ) {t : ℕ} (ht : 0 < t) (e : G.E) (v : G.V) (h : Class) :
    residual e / G.graphExtraSlotCount bucket residual gamma t v h ≤
      1 / (t : ℝ) := by
  exact residual_div_count_le_inv_reserve (residual e)
    (hresidual_one e) ht
    (G.graphExtraSlotCount_ge_reserve bucket residual gamma t v h)

/-- Every Cartesian extra option has mass at most `1/t^2`. -/
theorem graphExtraMass_le_inv_reserve_sq
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (hresidual_one : ∀ e, residual e ≤ 1)
    (gamma : ℝ) {t : ℕ} (ht : 0 < t)
    (q : ExtraSlotChoice G.E G.V Class G.fst G.snd bucket
      (G.graphExtraSlotCount bucket residual gamma t)) :
    ExtraSlotChoice.mass G.fst G.snd bucket
        (G.graphExtraSlotCount bucket residual gamma t) residual q ≤
      1 / (t : ℝ) ^ 2 := by
  exact residual_div_mul_counts_le_inv_reserve_sq (residual q.1)
    (hresidual_one q.1) ht
    (G.graphExtraSlotCount_ge_reserve bucket residual gamma t
      (G.fst q.1) (bucket q.1))
    (G.graphExtraSlotCount_ge_reserve bucket residual gamma t
      (G.snd q.1) (bucket q.1))

/-- The endpoint-share expression seen by a concrete slot is exactly the
class residual divided by the number of slots in that class. -/
theorem sum_endpointShares_eq_classResidual_div
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) (t : ℕ) (v : G.V) (h : Class) :
    (∑ e,
      ((if (v, h) = (G.fst e, bucket e) then
          residual e /
            G.graphExtraSlotCount bucket residual gamma t v h else 0) +
        (if (v, h) = (G.snd e, bucket e) then
          residual e /
            G.graphExtraSlotCount bucket residual gamma t v h else 0))) =
      G.classResidual bucket residual v h /
        G.graphExtraSlotCount bucket residual gamma t v h := by
  unfold classResidual
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hl : (v, h) = (G.fst e, bucket e)
  · have hl' : (G.fst e, bucket e) = (v, h) := hl.symm
    by_cases hr : (v, h) = (G.snd e, bucket e)
    · have hr' : (G.snd e, bucket e) = (v, h) := hr.symm
      rw [if_pos hl, if_pos hr, if_pos hl', if_pos hr', add_div]
    · have hr' : (G.snd e, bucket e) ≠ (v, h) := by
        exact fun heq ↦ hr heq.symm
      rw [if_pos hl, if_neg hr, if_pos hl', if_neg hr']
      simp
  · have hl' : (G.fst e, bucket e) ≠ (v, h) := by
      exact fun heq ↦ hl heq.symm
    by_cases hr : (v, h) = (G.snd e, bucket e)
    · have hr' : (G.snd e, bucket e) = (v, h) := hr.symm
      rw [if_neg hl, if_pos hr, if_neg hl', if_pos hr']
      simp
    · have hr' : (G.snd e, bucket e) ≠ (v, h) := by
        exact fun heq ↦ hr heq.symm
      rw [if_neg hl, if_neg hr, if_neg hl', if_neg hr']
      simp

/-- An indicator lets its denominator be written at either of two equal
labels.  Keeping this small rewrite separate avoids exposing dependent slot
indices to the simplifier. -/
private theorem if_div_pair_apply_eq
    {Vertex Class' : Type*} [DecidableEq Vertex] [DecidableEq Class']
    (D : Vertex → Class' → ℕ) (x y : Vertex × Class') (r : ℝ) :
    (if x = y then r / (D y.1 y.2 : ℕ) else 0) =
      if x = y then r / (D x.1 x.2 : ℕ) else 0 := by
  by_cases hxy : x = y
  · subst y
    rfl
  · simp [hxy]

/-- In the endpoint form used by `ExtraSlotChoice`, the denominator is
written at the matching endpoint.  On the support of either indicator it is
the same graph-indexed slot count. -/
theorem sum_endpointShares_variable_eq_classResidual_div
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) (t : ℕ) (v : G.V) (h : Class) :
    (∑ e,
      ((if (v, h) = (G.fst e, bucket e) then
          residual e /
            G.graphExtraSlotCount bucket residual gamma t
              (G.fst e) (bucket e) else 0) +
        (if (v, h) = (G.snd e, bucket e) then
          residual e /
            G.graphExtraSlotCount bucket residual gamma t
              (G.snd e) (bucket e) else 0))) =
      G.classResidual bucket residual v h /
        G.graphExtraSlotCount bucket residual gamma t v h := by
  let D : G.V → Class → ℕ :=
    G.graphExtraSlotCount bucket residual gamma t
  calc
    _ = ∑ e,
        ((if (v, h) = (G.fst e, bucket e) then
            residual e / D v h else 0) +
          (if (v, h) = (G.snd e, bucket e) then
            residual e / D v h else 0)) := by
      apply Finset.sum_congr rfl
      intro e _
      congr 1
      · exact if_div_pair_apply_eq D (v, h)
          (G.fst e, bucket e) (residual e)
      · exact if_div_pair_apply_eq D (v, h)
          (G.snd e, bucket e) (residual e)
    _ = G.classResidual bucket residual v h / D v h := by
      simpa [D] using
        (G.sum_endpointShares_eq_classResidual_div
          bucket residual gamma t v h)
    _ = _ := by rfl

/-- Every copied graph-indexed extra slot has the fixed degree slack
`1-gamma`. -/
theorem quantized_graphExtraSlotDegree_le
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (hr : ∀ e, 0 ≤ residual e)
    (gamma : ℝ) (t N : ℕ)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (ht : 0 < t)
    (s : ExtraSlot G.V Class
      (G.graphExtraSlotCount bucket residual gamma t)) :
    ((((ExtraSlotChoice.system G.fst G.snd bucket
        (G.graphExtraSlotCount bucket residual gamma t)).quantized N
      (ExtraSlotChoice.mass G.fst G.snd bucket
        (G.graphExtraSlotCount bucket residual gamma t) residual)).slotDegree s : ℕ) : ℝ) ≤
      (1 - gamma) * N := by
  let B : G.V → Class → ℕ :=
    G.graphExtraSlotCount bucket residual gamma t
  have hB : ∀ v h, 0 < B v h := fun v h ↦
    G.graphExtraSlotCount_pos bucket residual gamma ht v h
  have hdegree := ExtraSlotChoice.quantized_slotDegree_upper
    G.fst G.snd bucket B residual hr
    (fun e ↦ hB (G.fst e) (bucket e))
    (fun e ↦ hB (G.snd e) (bucket e)) N s
  rcases s with ⟨⟨v, h⟩, k⟩
  change _ ≤ (1 - gamma) * N
  have hshares :
      (∑ e,
        ((if (v, h) = (G.fst e, bucket e) then
            residual e / B (G.fst e) (bucket e) else 0) +
          (if (v, h) = (G.snd e, bucket e) then
            residual e / B (G.snd e) (bucket e) else 0))) =
        G.classResidual bucket residual v h / B v h := by
    simpa [B] using
      (G.sum_endpointShares_variable_eq_classResidual_div
        bucket residual gamma t v h)
  rw [hshares] at hdegree
  exact hdegree.trans (scaled_residual_div_extraSlotCount_le
    (G.classResidual bucket residual v h) gamma t N
    (G.classResidual_nonneg bucket residual hr v h)
    hgamma0 hgamma1 ht)

/-- Every copied job--extra-slot codegree is at most `N/t`.  The no-loop
condition makes a concrete slot belong to at most one endpoint of the job. -/
theorem quantized_graphExtraJobSlotCodegree_le
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (hr0 : ∀ e, 0 ≤ residual e) (hr1 : ∀ e, residual e ≤ 1)
    (gamma : ℝ) {t : ℕ} (ht : 0 < t) (N : ℕ)
    (e : G.E)
    (s : ExtraSlot G.V Class
      (G.graphExtraSlotCount bucket residual gamma t)) :
    (((ExtraSlotChoice.system G.fst G.snd bucket
        (G.graphExtraSlotCount bucket residual gamma t)).quantized N
      (ExtraSlotChoice.mass G.fst G.snd bucket
        (G.graphExtraSlotCount bucket residual gamma t) residual)).jobSlotCodegree
          e s : ℝ) ≤
      (N : ℝ) * (1 / (t : ℝ)) := by
  let B : G.V → Class → ℕ :=
    G.graphExtraSlotCount bucket residual gamma t
  have hB : ∀ v h, 0 < B v h := fun v h ↦
    G.graphExtraSlotCount_pos bucket residual gamma ht v h
  have hbase := ExtraSlotChoice.quantized_jobSlotCodegree_upper_oneEndpoint
    G.fst G.snd bucket B residual hr0
    (fun k ↦ hB (G.fst k) (bucket k))
    (fun k ↦ hB (G.snd k) (bucket k)) G.noLoop N e s
  have hshare :
      (if s.1 = (G.fst e, bucket e) then
          residual e / B (G.fst e) (bucket e)
        else if s.1 = (G.snd e, bucket e) then
          residual e / B (G.snd e) (bucket e) else 0) ≤
        1 / (t : ℝ) := by
    by_cases hl : s.1 = (G.fst e, bucket e)
    · rw [if_pos hl]
      exact residual_div_count_le_inv_reserve (residual e) (hr1 e) ht
        (by simpa [B] using
          (G.graphExtraSlotCount_ge_reserve bucket residual gamma t
            (G.fst e) (bucket e)))
    · rw [if_neg hl]
      by_cases hr : s.1 = (G.snd e, bucket e)
      · rw [if_pos hr]
        exact residual_div_count_le_inv_reserve (residual e) (hr1 e) ht
          (by simpa [B] using
            (G.graphExtraSlotCount_ge_reserve bucket residual gamma t
              (G.snd e) (bucket e)))
      · rw [if_neg hr]
        positivity
  simpa [B] using
    hbase.trans (mul_le_mul_of_nonneg_left hshare (Nat.cast_nonneg N))

/-- Pair uniqueness and the `1/t^2` point-mass estimate give the same bound
for every copied pair of distinct extra slots. -/
theorem quantized_graphExtraSlotPairCodegree_le
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (hr0 : ∀ e, 0 ≤ residual e) (hr1 : ∀ e, residual e ≤ 1)
    (gamma : ℝ) {t : ℕ} (ht : 0 < t) (N : ℕ)
    {s r : ExtraSlot G.V Class
      (G.graphExtraSlotCount bucket residual gamma t)} (hsr : s ≠ r) :
    ((((ExtraSlotChoice.system G.fst G.snd bucket
        (G.graphExtraSlotCount bucket residual gamma t)).quantized N
      (ExtraSlotChoice.mass G.fst G.snd bucket
        (G.graphExtraSlotCount bucket residual gamma t) residual)).slotPairCodegree
          s r : ℕ) : ℝ) ≤
      (N : ℝ) * (1 / (t : ℝ) ^ 2) := by
  apply (ExtraSlotChoice.system G.fst G.snd bucket
    (G.graphExtraSlotCount bucket residual gamma t)).quantized_slotPairCodegree_le
      (G.extraSlotChoice_pairUnique bucket
        (G.graphExtraSlotCount bucket residual gamma t)) N
      (ExtraSlotChoice.mass G.fst G.snd bucket
        (G.graphExtraSlotCount bucket residual gamma t) residual)
      (1 / (t : ℝ) ^ 2)
  · positivity
  · exact ExtraSlotChoice.mass_nonneg G.fst G.snd bucket
      (G.graphExtraSlotCount bucket residual gamma t) residual hr0
  · exact G.graphExtraMass_le_inv_reserve_sq bucket residual hr1 gamma ht
  · exact hsr

end WeightedSimpleGraph

end

end WeightedEdgeColoring
