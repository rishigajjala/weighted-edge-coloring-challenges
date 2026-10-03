import WeightedEdgeColoring.CyclicProfilePairAveraging
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# One global choice of cyclic shifts

Give every vertex a word indexed by `Fin n`.  We may rotate each vertex word
independently.  For an edge with distinct endpoints, the relative rotation of
its two endpoint words is uniform when all vertex rotations are averaged.
Linearity then gives one global choice of vertex rotations whose total edge
cost is at most the sum of the separate edge averages.

No sign condition on the costs is needed for this averaging argument.  In
particular, the final theorem applies to nonnegative profile-pair costs.
-/

noncomputable section

universe u v w

variable {V : Type u} {E : Type v} {State : Type w}
variable [Fintype V] [DecidableEq V]
variable [Fintype E]

/-- Subtracting a fixed element permutes `Fin n`. -/
theorem sum_cyclic_sub_right {n : ℕ} (hn : 0 < n) (c : Fin n)
    (g : Fin n → ℝ) :
    ∑ t : Fin n, g (t - c) = ∑ d : Fin n, g d := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  simpa [finCycle_apply, sub_eq_add_neg] using
    (Equiv.sum_comp (finCycle (-c)) g)

/-- Exact uniformity of the relative shift across all assignments of one
cyclic shift to every vertex.  The multiplier counts assignments on all
vertices except `y`. -/
theorem sum_relativeShift_eq_card_mul {n : ℕ} (hn : 0 < n)
    {x y : V} (hxy : x ≠ y) (g : Fin n → ℝ) :
    (∑ shift : V → Fin n, g (shift y - shift x)) =
      (Fintype.card ({z : V // z ≠ y} → Fin n) : ℝ) *
        ∑ t : Fin n, g t := by
  classical
  let split := Equiv.funSplitAt y (Fin n)
  let x' : {z : V // z ≠ y} := ⟨x, hxy⟩
  have hsplit := Equiv.sum_comp split
    (fun p : Fin n × ({z : V // z ≠ y} → Fin n) ↦
      g (p.1 - p.2 x'))
  have hreindex :
      (∑ shift : V → Fin n, g (shift y - shift x)) =
        ∑ p : Fin n × ({z : V // z ≠ y} → Fin n),
          g (p.1 - p.2 x') := by
    simpa [split, x'] using hsplit
  rw [hreindex, Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [sum_cyclic_sub_right hn]
  simp

/-- The average of any function of the relative shift is the uniform average
on `Fin n`. -/
theorem average_relativeShift {n : ℕ} (hn : 0 < n)
    {x y : V} (hxy : x ≠ y) (g : Fin n → ℝ) :
    (∑ shift : V → Fin n, g (shift y - shift x)) /
        (Fintype.card (V → Fin n) : ℝ) =
      (∑ t : Fin n, g t) / (n : ℝ) := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [sum_relativeShift_eq_card_mul hn hxy]
  have hcard :
      Fintype.card (V → Fin n) =
        n * Fintype.card ({z : V // z ≠ y} → Fin n) := by
    calc
      Fintype.card (V → Fin n) =
          Fintype.card (Fin n × ({z : V // z ≠ y} → Fin n)) :=
        Fintype.card_congr (Equiv.funSplitAt y (Fin n))
      _ = n * Fintype.card ({z : V // z ≠ y} → Fin n) := by simp
  rw [hcard]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hrest :
      (Fintype.card ({z : V // z ≠ y} → Fin n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  push_cast
  field_simp

/-- Total cost of a global assignment of cyclic shifts to the vertices. -/
def globalRelativeShiftCost {n : ℕ}
    (left right : E → V) (edgeCost : E → Fin n → ℝ)
    (shift : V → Fin n) : ℝ :=
  ∑ e : E, edgeCost e (shift (right e) - shift (left e))

/-- The average total cost of a global shift assignment is the sum of the
separate relative-shift averages of the edges. -/
theorem average_globalRelativeShiftCost {n : ℕ} (hn : 0 < n)
    (left right : E → V) (hloop : ∀ e, left e ≠ right e)
    (edgeCost : E → Fin n → ℝ) :
    (∑ shift : V → Fin n,
        globalRelativeShiftCost left right edgeCost shift) /
          (Fintype.card (V → Fin n) : ℝ) =
      ∑ e : E, (∑ t : Fin n, edgeCost e t) / (n : ℝ) := by
  classical
  unfold globalRelativeShiftCost
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _he
  exact average_relativeShift hn (hloop e) (edgeCost e)

/-- One global shift assignment is no more expensive than the sum of the
individual edge averages. -/
theorem exists_globalShift_cost_le_average {n : ℕ} (hn : 0 < n)
    (left right : E → V) (hloop : ∀ e, left e ≠ right e)
    (edgeCost : E → Fin n → ℝ) :
    ∃ shift : V → Fin n,
      globalRelativeShiftCost left right edgeCost shift ≤
        ∑ e : E, (∑ t : Fin n, edgeCost e t) / (n : ℝ) := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let target := ∑ e : E, (∑ t : Fin n, edgeCost e t) / (n : ℝ)
  have hcard_pos : 0 < (Fintype.card (V → Fin n) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (V → Fin n))
  have havg := average_globalRelativeShiftCost hn left right hloop edgeCost
  have hsum :
      (∑ shift : V → Fin n,
          globalRelativeShiftCost left right edgeCost shift) ≤
        ∑ _shift : V → Fin n, target := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [div_eq_iff hcard_pos.ne'] at havg
    simpa [target, mul_comm] using havg.le
  obtain ⟨shift, _hmem, hshift⟩ :=
    Finset.exists_le_of_sum_le
      (s := (Finset.univ : Finset (V → Fin n))) Finset.univ_nonempty hsum
  exact ⟨shift, by simpa [target] using hshift⟩

/-- The edge cost obtained by cyclically pairing two endpoint words. -/
def profileEdgeShiftCost {n : ℕ} (word : V → Fin n → State)
    (left right : E → V) (pairCost : E → State → State → ℝ)
    (e : E) (t : Fin n) : ℝ :=
  cyclicPairCost (word (left e)) (word (right e)) (pairCost e) t

/-- Rotating both words only changes their relative shift. -/
theorem shifted_pair_sum_eq_cyclicPairCost {n : ℕ} (hn : 0 < n)
    (a b : Fin n → State) (f : State → State → ℝ)
    (sa sb : Fin n) :
    (∑ c : Fin n, f (a (c + sa)) (b (c + sb))) =
      cyclicPairCost a b f (sb - sa) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hind (c : Fin n) :
      (sa + c) + (sb - sa) = c + sb := by
    calc
      (sa + c) + (sb - sa) = c + ((sb - sa) + sa) := by ac_rfl
      _ = c + sb := by rw [sub_add_cancel]
  calc
    (∑ c : Fin n, f (a (c + sa)) (b (c + sb))) =
        ∑ c : Fin n,
          f (a (sa + c)) (b ((sa + c) + (sb - sa))) := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [add_comm c sa, hind]
    _ = ∑ d : Fin n, f (a d) (b (d + (sb - sa))) :=
      sum_cyclic_add_left sa
        (fun d ↦ f (a d) (b (d + (sb - sa))))
    _ = cyclicPairCost a b f (sb - sa) := by
      rfl

/-- Literal total cost after rotating the word at every vertex by its chosen
shift. -/
def globalProfileShiftCost {n : ℕ} (word : V → Fin n → State)
    (left right : E → V) (pairCost : E → State → State → ℝ)
    (shift : V → Fin n) : ℝ :=
  ∑ e : E, ∑ c : Fin n,
    pairCost e
      (word (left e) (c + shift (left e)))
      (word (right e) (c + shift (right e)))

omit [Fintype V] [DecidableEq V] in
/-- The literal shifted-word cost is the corresponding relative-shift cost. -/
theorem globalProfileShiftCost_eq_relative {n : ℕ} (hn : 0 < n)
    (word : V → Fin n → State)
    (left right : E → V) (pairCost : E → State → State → ℝ)
    (shift : V → Fin n) :
    globalProfileShiftCost word left right pairCost shift =
      globalRelativeShiftCost left right
        (profileEdgeShiftCost word left right pairCost) shift := by
  classical
  unfold globalProfileShiftCost globalRelativeShiftCost profileEdgeShiftCost
  apply Finset.sum_congr rfl
  intro e _he
  exact shifted_pair_sum_eq_cyclicPairCost hn
    (word (left e)) (word (right e)) (pairCost e)
    (shift (left e)) (shift (right e))

/-- Global cyclic synchronization for vertex words.  A single rotation is
chosen at every vertex, and its total edge cost is bounded by the sum of the
per-edge cyclic averages. -/
theorem exists_globalProfileShift_cost_le_average {n : ℕ} (hn : 0 < n)
    (word : V → Fin n → State)
    (left right : E → V) (hloop : ∀ e, left e ≠ right e)
    (pairCost : E → State → State → ℝ) :
    ∃ shift : V → Fin n,
      globalProfileShiftCost word left right pairCost shift ≤
        ∑ e : E,
          (∑ t : Fin n,
            cyclicPairCost (word (left e)) (word (right e)) (pairCost e) t) /
              (n : ℝ) := by
  obtain ⟨shift, hshift⟩ :=
    exists_globalShift_cost_le_average hn left right hloop
      (profileEdgeShiftCost word left right pairCost)
  refine ⟨shift, ?_⟩
  rw [globalProfileShiftCost_eq_relative hn]
  simpa [profileEdgeShiftCost] using hshift

/-- Full-pair form of global cyclic synchronization.  The right side is the
sum, over edges, of the average over all ordered pairs of positions. -/
theorem exists_globalProfileShift_cost_le_fullPairAverage
    {n : ℕ} (hn : 0 < n)
    (word : V → Fin n → State)
    (left right : E → V) (hloop : ∀ e, left e ≠ right e)
    (pairCost : E → State → State → ℝ) :
    ∃ shift : V → Fin n,
      globalProfileShiftCost word left right pairCost shift ≤
        ∑ e : E,
          (∑ c : Fin n, ∑ d : Fin n,
            pairCost e (word (left e) c) (word (right e) d)) / (n : ℝ) := by
  obtain ⟨shift, hshift⟩ :=
    exists_globalProfileShift_cost_le_average hn word left right hloop pairCost
  refine ⟨shift, ?_⟩
  calc
    globalProfileShiftCost word left right pairCost shift ≤
        ∑ e : E,
          (∑ t : Fin n,
            cyclicPairCost (word (left e)) (word (right e)) (pairCost e) t) /
              (n : ℝ) := hshift
    _ = ∑ e : E,
          (∑ c : Fin n, ∑ d : Fin n,
            pairCost e (word (left e) c) (word (right e) d)) / (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [sum_cyclicPairCost]

end

end WeightedEdgeColoring
