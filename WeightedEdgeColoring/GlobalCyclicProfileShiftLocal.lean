import WeightedEdgeColoring.GlobalCyclicProfileShift
import WeightedEdgeColoring.FiniteCategoricalEventLLL

open scoped BigOperators

namespace WeightedEdgeColoring.GlobalCyclicProfileShiftLocal

/-!
# Simultaneous local control for cyclic vertex shifts

Every vertex independently receives a uniform shift in `Fin n`.  The bad
event at a vertex is that the total cost of its incident edges exceeds its
cyclic-average incident cost by more than a chosen threshold.  This event
only reads the closed neighbourhood of the vertex.  A support-overlap local
lemma therefore makes all vertex bounds hold simultaneously.

The scalar tail estimate is supplied conditionally on the shift at the
centre vertex.  This is the useful form for Hoeffding or Chernoff: after the
centre is fixed, the remaining summands are functions of the neighbouring
vertex shifts, while their cyclic means do not change with the fixed centre.
-/

noncomputable section

universe u v

variable {V : Type u} {E : Type v}
variable [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E]

/-- Two vertices are joined by one of the endpoint-indexed edges. -/
def Adjacent (left right : E → V) (x y : V) : Prop :=
  ∃ e : E,
    (left e = x ∧ right e = y) ∨
    (left e = y ∧ right e = x)

theorem adjacent_comm (left right : E → V) (x y : V) :
    Adjacent left right x y ↔ Adjacent left right y x := by
  constructor <;> rintro ⟨e, h | h⟩
  · exact ⟨e, Or.inr h⟩
  · exact ⟨e, Or.inl h⟩
  · exact ⟨e, Or.inr h⟩
  · exact ⟨e, Or.inl h⟩

/-- Edges incident with a vertex. -/
def incidentSet (left right : E → V) (x : V) : Finset E :=
  Finset.univ.filter fun e ↦ left e = x ∨ right e = x

@[simp] theorem mem_incidentSet (left right : E → V) (x : V) (e : E) :
    e ∈ incidentSet left right x ↔ left e = x ∨ right e = x := by
  simp [incidentSet]

/-- The set of neighbours of a vertex. -/
noncomputable def neighborSet (left right : E → V) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter fun y ↦ Adjacent left right x y

@[simp] theorem mem_neighborSet (left right : E → V) (x y : V) :
    y ∈ neighborSet left right x ↔ Adjacent left right x y := by
  simp [neighborSet]

/-- The coordinates read by the incident-cost event at a vertex. -/
def closedSupport (left right : E → V) (x : V) : Finset V :=
  insert x (neighborSet left right x)

theorem left_mem_closedSupport_of_incident
    (left right : E → V) {x : V} {e : E}
    (he : e ∈ incidentSet left right x) :
    left e ∈ closedSupport left right x := by
  rcases (mem_incidentSet left right x e).mp he with h | h
  · simp [closedSupport, h]
  · apply Finset.mem_insert_of_mem
    rw [mem_neighborSet]
    exact ⟨e, Or.inr ⟨rfl, h⟩⟩

theorem right_mem_closedSupport_of_incident
    (left right : E → V) {x : V} {e : E}
    (he : e ∈ incidentSet left right x) :
    right e ∈ closedSupport left right x := by
  rcases (mem_incidentSet left right x e).mp he with h | h
  · apply Finset.mem_insert_of_mem
    rw [mem_neighborSet]
    exact ⟨e, Or.inl ⟨h, rfl⟩⟩
  · simp [closedSupport, h]

theorem closedSupport_card_le
    (left right : E → V) (D : ℕ)
    (hdegree : ∀ x, (neighborSet left right x).card ≤ D) (x : V) :
    (closedSupport left right x).card ≤ D + 1 := by
  calc
    (closedSupport left right x).card ≤
        (neighborSet left right x).card + 1 := by
      exact Finset.card_insert_le x (neighborSet left right x)
    _ ≤ D + 1 := Nat.add_le_add_right (hdegree x) 1

/-- Closed-neighbourhood incidence is symmetric: a source belongs to the
support at `x` exactly when `x` belongs to the support at that source. -/
theorem supportIncidence_closedSupport_eq
    (left right : E → V) (s : V) :
    WeightedEdgeColoring.FiniteCategoricalEventLLL.supportIncidence
        (closedSupport left right) s =
      closedSupport left right s := by
  classical
  ext x
  simp only [WeightedEdgeColoring.FiniteCategoricalEventLLL.supportIncidence,
    Finset.mem_filter, Finset.mem_univ, true_and, closedSupport,
    Finset.mem_insert, mem_neighborSet]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr ((adjacent_comm left right x s).mp h)
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr ((adjacent_comm left right s x).mp h)

theorem closedSupport_overlapDegree_le
    (left right : E → V) (D : ℕ)
    (hdegree : ∀ x, (neighborSet left right x).card ≤ D) (x : V) :
    (WeightedEdgeColoring.FiniteCategoricalEventLLL.overlapNeighbor
      (closedSupport left right) x).card ≤ (D + 1) * (D + 1) := by
  apply WeightedEdgeColoring.FiniteCategoricalEventLLL.overlapNeighbor_card_le
    (closedSupport left right) (D + 1) (D + 1)
  · exact closedSupport_card_le left right D hdegree
  · intro s
    rw [supportIncidence_closedSupport_eq]
    exact closedSupport_card_le left right D hdegree s

/-- Cost of one edge under a global vertex-shift assignment. -/
def shiftedEdgeCost {n : ℕ} (left right : E → V)
    (edgeCost : E → Fin n → ℝ) (e : E) (shift : V → Fin n) : ℝ :=
  edgeCost e (shift (right e) - shift (left e))

/-- Total shifted cost of the edges incident with one vertex. -/
def vertexIncidentCost {n : ℕ} (left right : E → V)
    (edgeCost : E → Fin n → ℝ) (x : V) (shift : V → Fin n) : ℝ :=
  ∑ e ∈ incidentSet left right x, shiftedEdgeCost left right edgeCost e shift

/-- Sum of the uniform cyclic averages of the edges incident with a vertex. -/
def vertexCyclicAverage {n : ℕ} (left right : E → V)
    (edgeCost : E → Fin n → ℝ) (x : V) : ℝ :=
  ∑ e ∈ incidentSet left right x,
    (∑ t : Fin n, edgeCost e t) / (n : ℝ)

/-- The bad event that the incident cost exceeds its cyclic average plus
`tau`. -/
def badVertex {n : ℕ} (left right : E → V)
    (edgeCost : E → Fin n → ℝ) (tau : ℝ) (x : V) :
    Finset (V → Fin n) :=
  Finset.univ.filter fun shift ↦
    vertexCyclicAverage left right edgeCost x + tau <
      vertexIncidentCost left right edgeCost x shift

theorem badVertex_dependsOn_closedSupport {n : ℕ}
    (left right : E → V) (edgeCost : E → Fin n → ℝ)
    (tau : ℝ) (x : V) :
    WeightedEdgeColoring.FiniteCategoricalSelection.DependsOn
      (closedSupport left right x) (badVertex left right edgeCost tau x) := by
  intro a b hab
  have hcost :
      vertexIncidentCost left right edgeCost x a =
        vertexIncidentCost left right edgeCost x b := by
    unfold vertexIncidentCost shiftedEdgeCost
    apply Finset.sum_congr rfl
    intro e he
    rw [hab (left e) (left_mem_closedSupport_of_incident left right he),
      hab (right e) (right_mem_closedSupport_of_incident left right he)]
  simp [badVertex, hcost]

/-- Uniform law on cyclic shifts. -/
def uniformShiftProb {n : ℕ} : V → Fin n → ℝ :=
  fun _ _ ↦ 1 / (n : ℝ)

theorem uniformShiftProb_nonneg {n : ℕ} (hn : 0 < n) :
    ∀ x : V, ∀ t : Fin n, 0 ≤ uniformShiftProb (V := V) x t := by
  intro x t
  unfold uniformShiftProb
  positivity

theorem sum_uniformShiftProb {n : ℕ} (hn : 0 < n) (x : V) :
    ∑ t : Fin n, uniformShiftProb (V := V) x t = 1 := by
  unfold uniformShiftProb
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [hnR]

/-- A global shift reconstructed after fixing the centre coordinate and all
coordinates outside it. -/
def conditionedShift {n : ℕ} (x : V)
    (center : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Inside ({x} : Finset V) → Fin n)
    (outside : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside ({x} : Finset V) → Fin n) :
    V → Fin n :=
  (WeightedEdgeColoring.FiniteCategoricalSupportSplit.splitEquiv ({x} : Finset V)).symm
    (center, outside)

/-- Conditional overload event after the shift at the centre vertex has been
fixed.  This is the event to which a scalar Hoeffding or Chernoff estimate is
applied. -/
def conditionalBadVertex {n : ℕ}
    (left right : E → V) (edgeCost : E → Fin n → ℝ)
    (tau : ℝ) (x : V)
    (center : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Inside ({x} : Finset V) → Fin n) :
    Finset (WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside
      ({x} : Finset V) → Fin n) :=
  Finset.univ.filter fun outside ↦
    vertexCyclicAverage left right edgeCost x + tau <
      vertexIncidentCost left right edgeCost x
        (conditionedShift x center outside)

/-- The same conditional bad event, before projecting to the outside block. -/
def splitBadVertex {n : ℕ}
    (left right : E → V) (edgeCost : E → Fin n → ℝ)
    (tau : ℝ) (x : V) :
    Finset
      ((WeightedEdgeColoring.FiniteCategoricalSupportSplit.Inside ({x} : Finset V) → Fin n) ×
       (WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside ({x} : Finset V) → Fin n)) :=
  Finset.univ.filter fun p ↦
    vertexCyclicAverage left right edgeCost x + tau <
      vertexIncidentCost left right edgeCost x
        (conditionedShift x p.1 p.2)

theorem badVertex_eq_splitEvent {n : ℕ}
    (left right : E → V) (edgeCost : E → Fin n → ℝ)
    (tau : ℝ) (x : V) :
    badVertex left right edgeCost tau x =
      WeightedEdgeColoring.FiniteCategoricalSupportSplit.splitEvent ({x} : Finset V)
        (splitBadVertex left right edgeCost tau x) := by
  classical
  ext shift
  simp [badVertex, splitBadVertex, conditionedShift]

/-- Exact disintegration of a split bad-event mass over the possible centre
shifts. -/
theorem eventMass_splitBadVertex_eq_sum_conditional {n : ℕ}
    (left right : E → V) (edgeCost : E → Fin n → ℝ)
    (tau : ℝ) (x : V) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteProductCylinder.productMass
          (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
            (WeightedEdgeColoring.FiniteCategoricalSupportSplit.insideProb
              (uniformShiftProb (V := V) (n := n)) ({x} : Finset V)))
          (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
            (WeightedEdgeColoring.FiniteCategoricalSupportSplit.outsideProb
              (uniformShiftProb (V := V) (n := n)) ({x} : Finset V))))
        (splitBadVertex left right edgeCost tau x) =
      ∑ center,
        WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
            (WeightedEdgeColoring.FiniteCategoricalSupportSplit.insideProb
              (uniformShiftProb (V := V) (n := n)) ({x} : Finset V)) center *
          WeightedEdgeColoring.FiniteLocalLemma.eventMass
            (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
              (WeightedEdgeColoring.FiniteCategoricalSupportSplit.outsideProb
                (uniformShiftProb (V := V) (n := n)) ({x} : Finset V)))
            (conditionalBadVertex left right edgeCost tau x center) := by
  classical
  unfold WeightedEdgeColoring.FiniteLocalLemma.eventMass splitBadVertex conditionalBadVertex
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro center _hcenter
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro outside _houtside
  rfl

/-- A conditional scalar tail bound implies the same unconditional bound for
the global product of uniform vertex shifts. -/
theorem badVertex_mass_le_of_conditional {n : ℕ} (hn : 0 < n)
    (left right : E → V) (edgeCost : E → Fin n → ℝ)
    (tau p : ℝ)
    (htail : ∀ (x : V)
      (center : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Inside
        ({x} : Finset V) → Fin n),
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
          (WeightedEdgeColoring.FiniteCategoricalSupportSplit.outsideProb
            (uniformShiftProb (V := V) (n := n)) ({x} : Finset V)))
        (conditionalBadVertex left right edgeCost tau x center) ≤ p) :
    ∀ x : V,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
          (uniformShiftProb (V := V) (n := n)))
        (badVertex left right edgeCost tau x) ≤ p := by
  classical
  intro x
  rw [badVertex_eq_splitEvent,
    WeightedEdgeColoring.FiniteCategoricalSupportSplit.eventMass_splitEvent,
    eventMass_splitBadVertex_eq_sum_conditional]
  calc
    (∑ center,
        WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
            (WeightedEdgeColoring.FiniteCategoricalSupportSplit.insideProb
              (uniformShiftProb (V := V) (n := n)) ({x} : Finset V)) center *
          WeightedEdgeColoring.FiniteLocalLemma.eventMass
            (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
              (WeightedEdgeColoring.FiniteCategoricalSupportSplit.outsideProb
                (uniformShiftProb (V := V) (n := n)) ({x} : Finset V)))
            (conditionalBadVertex left right edgeCost tau x center)) ≤
        ∑ center,
          WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
              (WeightedEdgeColoring.FiniteCategoricalSupportSplit.insideProb
                (uniformShiftProb (V := V) (n := n)) ({x} : Finset V)) center * p := by
      apply Finset.sum_le_sum
      intro center _hcenter
      exact mul_le_mul_of_nonneg_left (htail x center)
        (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass_nonneg
          (WeightedEdgeColoring.FiniteCategoricalSupportSplit.insideProb
            (uniformShiftProb (V := V) (n := n)) ({x} : Finset V))
          (fun s t ↦ uniformShiftProb_nonneg (V := V) hn s t) center)
    _ = p := by
      rw [← Finset.sum_mul]
      rw [WeightedEdgeColoring.FiniteCategoricalSelection.sum_categoricalMass]
      · simp
      · intro s
        exact sum_uniformShiftProb (V := V) hn s

/-- For a fixed right endpoint shift, subtraction from that shift also runs
uniformly through `Fin n`. -/
theorem sum_cyclic_sub_left {n : ℕ} (hn : 0 < n) (c : Fin n)
    (g : Fin n → ℝ) :
    ∑ t : Fin n, g (c - t) = ∑ d : Fin n, g d := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let reflect : Equiv.Perm (Fin n) :=
    { toFun := fun t ↦ c - t
      invFun := fun t ↦ c - t
      left_inv := by intro t; simp
      right_inv := by intro t; simp }
  simpa [reflect] using (Equiv.sum_comp reflect g)

/-- Fixing the left endpoint shift does not change an edge's cyclic mean. -/
theorem edgeMean_invariant_fix_left {n : ℕ} (hn : 0 < n)
    (g : Fin n → ℝ) (center : Fin n) :
    (∑ t : Fin n, g (t - center)) / (n : ℝ) =
      (∑ d : Fin n, g d) / (n : ℝ) := by
  rw [WeightedEdgeColoring.sum_cyclic_sub_right hn]

/-- Fixing the right endpoint shift does not change an edge's cyclic mean. -/
theorem edgeMean_invariant_fix_right {n : ℕ} (hn : 0 < n)
    (g : Fin n → ℝ) (center : Fin n) :
    (∑ t : Fin n, g (center - t)) / (n : ℝ) =
      (∑ d : Fin n, g d) / (n : ℝ) := by
  rw [sum_cyclic_sub_left hn]

/-- Simultaneous local control from a conditional scalar tail estimate and
the symmetric finite local lemma. -/
theorem exists_shift_all_vertexIncidentCost_le
    {n : ℕ} (hn : 0 < n)
    (left right : E → V) (edgeCost : E → Fin n → ℝ)
    (tau p lllWeight : ℝ) (D : ℕ)
    (hdegree : ∀ x, (neighborSet left right x).card ≤ D)
    (hweight0 : 0 ≤ lllWeight) (hweight1 : lllWeight < 1)
    (hnumeric : p ≤
      lllWeight * (1 - lllWeight) ^ ((D + 1) * (D + 1)))
    (htail : ∀ (x : V)
      (center : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Inside
        ({x} : Finset V) → Fin n),
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
          (WeightedEdgeColoring.FiniteCategoricalSupportSplit.outsideProb
            (uniformShiftProb (V := V) (n := n)) ({x} : Finset V)))
        (conditionalBadVertex left right edgeCost tau x center) ≤ p) :
    ∃ shift : V → Fin n, ∀ x : V,
      vertexIncidentCost left right edgeCost x shift ≤
        vertexCyclicAverage left right edgeCost x + tau := by
  classical
  obtain ⟨shift, hshift⟩ :=
    WeightedEdgeColoring.FiniteCategoricalEventLLL.exists_avoids_of_support_overlap
      (uniformShiftProb (V := V) (n := n))
      (badVertex left right edgeCost tau)
      (closedSupport left right)
      p lllWeight ((D + 1) * (D + 1))
      (uniformShiftProb_nonneg (V := V) hn)
      (sum_uniformShiftProb (V := V) hn)
      (badVertex_dependsOn_closedSupport left right edgeCost tau)
      (closedSupport_overlapDegree_le left right D hdegree)
      hweight0 hweight1 hnumeric
      (badVertex_mass_le_of_conditional hn left right edgeCost tau p htail)
  refine ⟨shift, ?_⟩
  intro x
  have hx := hshift x
  simpa [badVertex, not_lt] using hx

/-- The standard square-root scale suggested by Hoeffding for `D` summands
of range at most `B`, with logarithmic parameter `L`. -/
def hoeffdingThreshold (B : ℝ) (D : ℕ) (L : ℝ) : ℝ :=
  B * Real.sqrt ((D : ℝ) * L / 2)

/-- Explicit Hoeffding-form wrapper.  The only probabilistic input is the
conditional scalar bound `exp (-L)`.  All graph locality, dependency
counting, and global synchronization are discharged by this theorem. -/
theorem exists_shift_all_vertexIncidentCost_le_hoeffding
    {n : ℕ} (hn : 0 < n)
    (left right : E → V) (edgeCost : E → Fin n → ℝ)
    (B L lllWeight : ℝ) (D : ℕ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f,
      ((left e = left f ∧ right e = right f) ∨
       (left e = right f ∧ right e = left f)) → e = f)
    (hcost0 : ∀ e t, 0 ≤ edgeCost e t)
    (hcostB : ∀ e t, edgeCost e t ≤ B)
    (hdegree : ∀ x, (neighborSet left right x).card ≤ D)
    (hweight0 : 0 ≤ lllWeight) (hweight1 : lllWeight < 1)
    (hnumeric : Real.exp (-L) ≤
      lllWeight * (1 - lllWeight) ^ ((D + 1) * (D + 1)))
    (htail : ∀ (x : V)
      (center : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Inside
        ({x} : Finset V) → Fin n),
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
          (WeightedEdgeColoring.FiniteCategoricalSupportSplit.outsideProb
            (uniformShiftProb (V := V) (n := n)) ({x} : Finset V)))
        (conditionalBadVertex left right edgeCost
          (hoeffdingThreshold B D L) x center) ≤ Real.exp (-L)) :
    ∃ shift : V → Fin n, ∀ x : V,
      vertexIncidentCost left right edgeCost x shift ≤
        vertexCyclicAverage left right edgeCost x +
          hoeffdingThreshold B D L := by
  have _graphData :
      (∀ e, left e ≠ right e) ∧
      (∀ e f,
        ((left e = left f ∧ right e = right f) ∨
         (left e = right f ∧ right e = left f)) → e = f) :=
    ⟨hloop, hsimple⟩
  have _costData :
      (∀ e t, 0 ≤ edgeCost e t) ∧ (∀ e t, edgeCost e t ≤ B) :=
    ⟨hcost0, hcostB⟩
  exact exists_shift_all_vertexIncidentCost_le hn left right edgeCost
    (hoeffdingThreshold B D L) (Real.exp (-L)) lllWeight D hdegree
    hweight0 hweight1 hnumeric htail

end

end WeightedEdgeColoring.GlobalCyclicProfileShiftLocal
