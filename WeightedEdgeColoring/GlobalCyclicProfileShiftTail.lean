import WeightedEdgeColoring.GlobalCyclicProfileShiftLocal
import WeightedEdgeColoring.FiniteCategoricalBernstein

/-!
# The conditional tail for cyclic vertex shifts

After the shift at one vertex is fixed, a simple graph has one independent
bounded summand for each neighbour.  This file makes that statement literal
in the finite categorical-product model and proves an explicit exponential
tail.  No probability-space or asymptotic axiom is used.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.GlobalCyclicProfileShiftLocal

noncomputable section

universe u v

variable {V : Type u} {E : Type v}
variable [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E]

/-- The endpoint of an incident edge different from the displayed centre. -/
def otherEndpoint (left right : E → V) (x : V) (e : E) : V :=
  if left e = x then right e else left e

theorem otherEndpoint_ne_of_incident
    (left right : E → V) (hloop : ∀ e, left e ≠ right e)
    {x : V} {e : E} (he : e ∈ incidentSet left right x) :
    otherEndpoint left right x e ≠ x := by
  rcases (mem_incidentSet left right x e).mp he with hleft | hright
  · simp only [otherEndpoint, if_pos hleft]
    exact fun h ↦ hloop e (hleft.trans h.symm)
  · by_cases hleft : left e = x
    · exact (hloop e (hleft.trans hright.symm)).elim
    · simp [otherEndpoint, hleft]

theorem otherEndpoint_injective_on_incident
    (left right : E → V)
    (hsimple : ∀ e f,
      ((left e = left f ∧ right e = right f) ∨
       (left e = right f ∧ right e = left f)) → e = f)
    (x : V) :
    Set.InjOn (otherEndpoint left right x)
      (incidentSet left right x) := by
  intro e he f hf hef
  have hei := (mem_incidentSet left right x e).mp he
  have hfi := (mem_incidentSet left right x f).mp hf
  by_cases heL : left e = x
  · by_cases hfL : left f = x
    · apply hsimple e f
      left
      refine ⟨heL.trans hfL.symm, ?_⟩
      simpa [otherEndpoint, heL, hfL] using hef
    · have hfR : right f = x := hfi.resolve_left hfL
      apply hsimple e f
      right
      refine ⟨heL.trans hfR.symm, ?_⟩
      simpa [otherEndpoint, heL, hfL] using hef
  · have heR : right e = x := hei.resolve_left heL
    by_cases hfL : left f = x
    · apply hsimple e f
      right
      refine ⟨?_, heR.trans hfL.symm⟩
      simpa [otherEndpoint, heL, hfL] using hef
    · have hfR : right f = x := hfi.resolve_left hfL
      apply hsimple e f
      left
      refine ⟨?_, heR.trans hfR.symm⟩
      simpa [otherEndpoint, heL, hfL] using hef

/-- Cost of one incident edge as a function of the shift at its other
endpoint, after fixing the shift at `x`. -/
def conditionalEdgeCost {n : ℕ} (left right : E → V)
    (edgeCost : E → Fin n → ℝ) (x : V) (centerShift : Fin n)
    (e : E) (a : Fin n) : ℝ :=
  if left e = x then
    edgeCost e (a - centerShift)
  else
    edgeCost e (centerShift - a)

/-- Normalized contribution of one outside vertex.  On a simple graph at
most one incident edge appears in this sum. -/
def conditionalVertexUse {n : ℕ} (left right : E → V)
    (edgeCost : E → Fin n → ℝ) (B : ℝ) (x : V)
    (centerShift : Fin n)
    (s : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside
      ({x} : Finset V)) (a : Fin n) (_ : Unit) : ℝ :=
  (∑ e ∈ incidentSet left right x,
      if otherEndpoint left right x e = s.1 then
        conditionalEdgeCost left right edgeCost x centerShift e a
      else 0) / B

theorem conditionedShift_center {n : ℕ} (x : V)
    (center : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Inside
      ({x} : Finset V) → Fin n)
    (outside : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside
      ({x} : Finset V) → Fin n) :
    conditionedShift x center outside x = center ⟨x, by simp⟩ := by
  simp [conditionedShift, WeightedEdgeColoring.FiniteCategoricalSupportSplit.splitEquiv]

theorem conditionedShift_outside {n : ℕ} (x y : V) (hy : y ≠ x)
    (center : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Inside
      ({x} : Finset V) → Fin n)
    (outside : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside
      ({x} : Finset V) → Fin n) :
    conditionedShift x center outside y =
      outside ⟨y, by simpa using hy⟩ := by
  simp [conditionedShift, WeightedEdgeColoring.FiniteCategoricalSupportSplit.splitEquiv, hy]

theorem conditionalEdgeCost_nonneg {n : ℕ}
    (left right : E → V) (edgeCost : E → Fin n → ℝ)
    (hcost0 : ∀ e t, 0 ≤ edgeCost e t) (x : V) (centerShift : Fin n)
    (e : E) (a : Fin n) :
    0 ≤ conditionalEdgeCost left right edgeCost x centerShift e a := by
  unfold conditionalEdgeCost
  split <;> exact hcost0 _ _

theorem conditionalEdgeCost_le {n : ℕ}
    (left right : E → V) (edgeCost : E → Fin n → ℝ) (B : ℝ)
    (hcostB : ∀ e t, edgeCost e t ≤ B) (x : V) (centerShift : Fin n)
    (e : E) (a : Fin n) :
    conditionalEdgeCost left right edgeCost x centerShift e a ≤ B := by
  unfold conditionalEdgeCost
  split <;> exact hcostB _ _

theorem conditionalVertexUse_nonneg {n : ℕ}
    (left right : E → V) (edgeCost : E → Fin n → ℝ)
    (B : ℝ) (hB : 0 < B) (hcost0 : ∀ e t, 0 ≤ edgeCost e t)
    (x : V) (centerShift : Fin n) :
    ∀ s a r, 0 ≤ conditionalVertexUse left right edgeCost B x centerShift s a r := by
  intro s a r
  unfold conditionalVertexUse
  apply div_nonneg _ hB.le
  exact Finset.sum_nonneg fun e _he ↦ by
    split
    · exact conditionalEdgeCost_nonneg left right edgeCost hcost0 x centerShift e a
    · exact le_rfl

theorem conditionalVertexUse_le_one {n : ℕ}
    (left right : E → V) (edgeCost : E → Fin n → ℝ)
    (B : ℝ) (hB : 0 < B)
    (hsimple : ∀ e f,
      ((left e = left f ∧ right e = right f) ∨
       (left e = right f ∧ right e = left f)) → e = f)
    (hcostB : ∀ e t, edgeCost e t ≤ B) (x : V) (centerShift : Fin n) :
    ∀ s a r, conditionalVertexUse left right edgeCost B x centerShift s a r ≤ 1 := by
  intro s a r
  unfold conditionalVertexUse
  apply (div_le_one hB).2
  by_cases hex : ∃ e ∈ incidentSet left right x,
      otherEndpoint left right x e = s.1
  · rcases hex with ⟨e, he, hes⟩
    calc
      (∑ f ∈ incidentSet left right x,
          if otherEndpoint left right x f = s.1 then
            conditionalEdgeCost left right edgeCost x centerShift f a else 0) =
          conditionalEdgeCost left right edgeCost x centerShift e a := by
        calc
          (∑ f ∈ incidentSet left right x,
              if otherEndpoint left right x f = s.1 then
                conditionalEdgeCost left right edgeCost x centerShift f a else 0) =
              (if otherEndpoint left right x e = s.1 then
                conditionalEdgeCost left right edgeCost x centerShift e a else 0) := by
            apply Finset.sum_eq_single e
            · intro f hf hfe
              have hother : otherEndpoint left right x f ≠ s.1 := by
                intro hfs
                have hef := otherEndpoint_injective_on_incident
                  left right hsimple x hf he (hfs.trans hes.symm)
                exact hfe hef
              simp [hother]
            · exact fun h ↦ (h he).elim
          _ = conditionalEdgeCost left right edgeCost x centerShift e a :=
            if_pos hes
      _ ≤ B := conditionalEdgeCost_le left right edgeCost B hcostB x centerShift e a
  · apply le_trans (show
        (∑ f ∈ incidentSet left right x,
          if otherEndpoint left right x f = s.1 then
            conditionalEdgeCost left right edgeCost x centerShift f a else 0) = 0 by
          apply Finset.sum_eq_zero
          intro f hf
          have hother : otherEndpoint left right x f ≠ s.1 := by
            intro hfs
            exact hex ⟨f, hf, hfs⟩
          simp [hother]).le
      hB.le

theorem conditionalEdgeCost_eq_shifted {n : ℕ}
    (left right : E → V) (hloop : ∀ e, left e ≠ right e)
    (edgeCost : E → Fin n → ℝ) (x : V)
    (center : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Inside
      ({x} : Finset V) → Fin n)
    (outside : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside
      ({x} : Finset V) → Fin n)
    {e : E} (he : e ∈ incidentSet left right x) :
    conditionalEdgeCost left right edgeCost x (center ⟨x, by simp⟩) e
        (outside ⟨otherEndpoint left right x e,
          by simpa using otherEndpoint_ne_of_incident left right hloop he⟩) =
      shiftedEdgeCost left right edgeCost e
        (conditionedShift x center outside) := by
  let oe : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside
      ({x} : Finset V) :=
    ⟨otherEndpoint left right x e,
      by simpa using otherEndpoint_ne_of_incident left right hloop he⟩
  change conditionalEdgeCost left right edgeCost x (center ⟨x, by simp⟩) e
    (outside oe) = _
  have hi := (mem_incidentSet left right x e).mp he
  by_cases hleft : left e = x
  · have hright : right e ≠ x := by
      intro h
      exact hloop e (hleft.trans h.symm)
    have hother : otherEndpoint left right x e = right e := by
      simp [otherEndpoint, hleft]
    let oRight : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside
        ({x} : Finset V) := ⟨right e, by simpa using hright⟩
    have hoe : oe = oRight := Subtype.ext hother
    rw [hoe]
    unfold conditionalEdgeCost shiftedEdgeCost
    simp only [if_pos hleft]
    rw [hleft, conditionedShift_center x center outside,
      conditionedShift_outside x (right e) hright center outside]
  · have hright : right e = x := hi.resolve_left hleft
    have hother : otherEndpoint left right x e = left e := by
      simp [otherEndpoint, hleft]
    let oLeft : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside
        ({x} : Finset V) := ⟨left e, by simpa using hleft⟩
    have hoe : oe = oLeft := Subtype.ext hother
    rw [hoe]
    unfold conditionalEdgeCost shiftedEdgeCost
    simp only [if_neg hleft]
    rw [hright, conditionedShift_center x center outside,
      conditionedShift_outside x (left e) hleft center outside]

/-- The categorical row load is exactly the conditioned incident cost,
normalized by `B`. -/
theorem conditionalVertexUse_rowLoad {n : ℕ}
    (left right : E → V) (hloop : ∀ e, left e ≠ right e)
    (edgeCost : E → Fin n → ℝ) (B : ℝ) (x : V)
    (center : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Inside
      ({x} : Finset V) → Fin n)
    (outside : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside
      ({x} : Finset V) → Fin n) :
    WeightedEdgeColoring.FiniteCategoricalSelection.rowLoad
        (conditionalVertexUse left right edgeCost B x (center ⟨x, by simp⟩))
        () outside =
      vertexIncidentCost left right edgeCost x
        (conditionedShift x center outside) / B := by
  classical
  unfold WeightedEdgeColoring.FiniteCategoricalSelection.rowLoad conditionalVertexUse
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  let oe : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside
      ({x} : Finset V) :=
    ⟨otherEndpoint left right x e,
      by simpa using otherEndpoint_ne_of_incident left right hloop he⟩
  calc
    (∑ s, if otherEndpoint left right x e = s.1 then
        conditionalEdgeCost left right edgeCost x (center ⟨x, by simp⟩) e
          (outside s) else 0) =
        (if otherEndpoint left right x e = oe.1 then
          conditionalEdgeCost left right edgeCost x (center ⟨x, by simp⟩) e
            (outside oe) else 0) := by
      apply Fintype.sum_eq_single oe
      intro s hse
      have hne : otherEndpoint left right x e ≠ s.1 := by
        intro hs
        apply hse
        apply Subtype.ext
        exact hs.symm
      simp [hne]
    _ = conditionalEdgeCost left right edgeCost x (center ⟨x, by simp⟩) e
          (outside oe) := by
      simp [oe]
    _ = shiftedEdgeCost left right edgeCost e
          (conditionedShift x center outside) := by
      exact conditionalEdgeCost_eq_shifted left right hloop edgeCost x
        center outside he

theorem sum_conditionalEdgeCost {n : ℕ} (hn : 0 < n)
    (left right : E → V) (edgeCost : E → Fin n → ℝ) (x : V)
    (centerShift : Fin n) (e : E) :
    (∑ a : Fin n, conditionalEdgeCost left right edgeCost x centerShift e a) =
      ∑ t : Fin n, edgeCost e t := by
  unfold conditionalEdgeCost
  split
  · exact WeightedEdgeColoring.sum_cyclic_sub_right hn _ _
  · exact sum_cyclic_sub_left hn _ _

theorem sum_outside_conditionalEdgeCost {n : ℕ}
    (left right : E → V) (hloop : ∀ e, left e ≠ right e)
    (edgeCost : E → Fin n → ℝ) (x : V)
    (centerShift : Fin n) {e : E}
    (he : e ∈ incidentSet left right x) (a : Fin n) :
    (∑ s : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside ({x} : Finset V),
      if otherEndpoint left right x e = s.1 then
        conditionalEdgeCost left right edgeCost x centerShift e a else 0) =
      conditionalEdgeCost left right edgeCost x centerShift e a := by
  classical
  let oe : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside
      ({x} : Finset V) :=
    ⟨otherEndpoint left right x e,
      by simpa using otherEndpoint_ne_of_incident left right hloop he⟩
  calc
    (∑ s : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside ({x} : Finset V),
      if otherEndpoint left right x e = s.1 then
        conditionalEdgeCost left right edgeCost x centerShift e a else 0) =
        (if otherEndpoint left right x e = oe.1 then
          conditionalEdgeCost left right edgeCost x centerShift e a else 0) := by
      apply Fintype.sum_eq_single oe
      intro s hse
      have hne : otherEndpoint left right x e ≠ s.1 := by
        intro hs
        apply hse
        apply Subtype.ext
        exact hs.symm
      simp [hne]
    _ = conditionalEdgeCost left right edgeCost x centerShift e a := by
      simp [oe]

/-- A small algebraic reindexing lemma used in the mean calculation below. -/
theorem sum_sum_mul_finset_sum_div_reindex
    {S A I : Type*} [Fintype S] [Fintype A] [DecidableEq I]
    (T : Finset I) (F : S → A → I → ℝ) (c B : ℝ) :
    (∑ s, ∑ a, c * ((∑ i ∈ T, F s a i) / B)) =
      ∑ i ∈ T, ∑ a, ∑ s, c * F s a i / B := by
  simp_rw [Finset.sum_div]
  simp_rw [Finset.mul_sum]
  calc
    (∑ s, ∑ a, ∑ i ∈ T, c * (F s a i / B)) =
        ∑ a, ∑ s, ∑ i ∈ T, c * (F s a i / B) := by
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ i ∈ T, ∑ s, c * (F s a i / B) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_comm]
    _ = ∑ i ∈ T, ∑ a, ∑ s, c * (F s a i / B) := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ T, ∑ a, ∑ s, c * F s a i / B := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro s _hs
      ring

theorem sum_incident_color_outside_collapse {n : ℕ}
    (left right : E → V) (hloop : ∀ e, left e ≠ right e)
    (edgeCost : E → Fin n → ℝ) (B c : ℝ) (x : V)
    (centerShift : Fin n) :
    (∑ e ∈ incidentSet left right x, ∑ a,
      ∑ s : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside ({x} : Finset V),
        c * (if otherEndpoint left right x e = s.1 then
          conditionalEdgeCost left right edgeCost x centerShift e a else 0) / B) =
      ∑ e ∈ incidentSet left right x, ∑ a,
        c * conditionalEdgeCost left right edgeCost x centerShift e a / B := by
  classical
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro a _ha
  rw [← Finset.sum_div, ← Finset.mul_sum,
    sum_outside_conditionalEdgeCost left right hloop edgeCost x
      centerShift he a]

theorem sum_incident_conditionalEdgeCost_average {n : ℕ} (hn : 0 < n)
    (left right : E → V) (edgeCost : E → Fin n → ℝ) (B : ℝ)
    (x : V) (centerShift : Fin n) :
    (∑ e ∈ incidentSet left right x, ∑ a,
      (1 / (n : ℝ)) *
        conditionalEdgeCost left right edgeCost x centerShift e a / B) =
      ∑ e ∈ incidentSet left right x,
        ((∑ t : Fin n, edgeCost e t) / (n : ℝ)) / B := by
  classical
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  apply Finset.sum_congr rfl
  intro e _he
  rw [← Finset.sum_div, ← Finset.mul_sum,
    sum_conditionalEdgeCost hn left right edgeCost x centerShift e]
  field_simp

set_option maxHeartbeats 1000000 in
/-- The categorical mean of the normalized conditioned row is exactly the
cyclic-average incident cost divided by `B`. -/
theorem conditionalVertexUse_rowMean {n : ℕ} (hn : 0 < n)
    (left right : E → V) (hloop : ∀ e, left e ≠ right e)
    (edgeCost : E → Fin n → ℝ) (B : ℝ) (x : V)
    (centerShift : Fin n) :
    WeightedEdgeColoring.FiniteCategoricalSelection.rowMean
        (WeightedEdgeColoring.FiniteCategoricalSupportSplit.outsideProb
          (uniformShiftProb (V := V) (n := n)) ({x} : Finset V))
        (conditionalVertexUse left right edgeCost B x centerShift) () =
      vertexCyclicAverage left right edgeCost x / B  := by
  classical
  unfold WeightedEdgeColoring.FiniteCategoricalSelection.rowMean
    WeightedEdgeColoring.FiniteCategoricalSupportSplit.outsideProb uniformShiftProb
    conditionalVertexUse vertexCyclicAverage
  rw [sum_sum_mul_finset_sum_div_reindex
        (incidentSet left right x)
        (fun (s : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Outside
            ({x} : Finset V)) (a : Fin n) (e : E) ↦
          if otherEndpoint left right x e = s.1 then
          conditionalEdgeCost left right edgeCost x centerShift e a else 0)
        (1 / (n : ℝ)) B]
  rw [sum_incident_color_outside_collapse left right hloop edgeCost B
      (1 / (n : ℝ)) x centerShift,
    sum_incident_conditionalEdgeCost_average hn left right edgeCost B x centerShift,
    Finset.sum_div]

theorem incidentSet_card_le_neighborSet_card
    (left right : E → V)
    (hsimple : ∀ e f,
      ((left e = left f ∧ right e = right f) ∨
       (left e = right f ∧ right e = left f)) → e = f)
    (x : V) :
    (incidentSet left right x).card ≤ (neighborSet left right x).card := by
  classical
  let T := (incidentSet left right x).image (otherEndpoint left right x)
  have hcard : T.card = (incidentSet left right x).card := by
    unfold T
    exact Finset.card_image_iff.mpr
      (otherEndpoint_injective_on_incident left right hsimple x)
  have hsub : T ⊆ neighborSet left right x := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨e, he, rfl⟩
    rw [mem_neighborSet]
    have hi := (mem_incidentSet left right x e).mp he
    by_cases hleft : left e = x
    · exact ⟨e, Or.inl ⟨hleft, by simp [otherEndpoint, hleft]⟩⟩
    · have hright : right e = x := hi.resolve_left hleft
      exact ⟨e, Or.inr ⟨by simp [otherEndpoint, hleft], hright⟩⟩
  rw [← hcard]
  exact Finset.card_le_card hsub

theorem vertexCyclicAverage_le_card_mul {n : ℕ} (hn : 0 < n)
    (left right : E → V) (edgeCost : E → Fin n → ℝ) (B : ℝ)
    (hcostB : ∀ e t, edgeCost e t ≤ B) (x : V) :
    vertexCyclicAverage left right edgeCost x ≤
      ((incidentSet left right x).card : ℝ) * B := by
  unfold vertexCyclicAverage
  calc
    (∑ e ∈ incidentSet left right x,
        (∑ t : Fin n, edgeCost e t) / (n : ℝ)) ≤
        ∑ _e ∈ incidentSet left right x, B := by
      apply Finset.sum_le_sum
      intro e _he
      apply (div_le_iff₀ (by exact_mod_cast hn)).2
      calc
        (∑ t : Fin n, edgeCost e t) ≤ ∑ _t : Fin n, B :=
          Finset.sum_le_sum fun t _ht ↦ hcostB e t
        _ = B * (n : ℝ) := by simp [mul_comm]
    _ = ((incidentSet left right x).card : ℝ) * B := by simp

theorem conditionalVertexUse_rowMean_le_degree {n : ℕ} (hn : 0 < n)
    (left right : E → V) (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f,
      ((left e = left f ∧ right e = right f) ∨
       (left e = right f ∧ right e = left f)) → e = f)
    (edgeCost : E → Fin n → ℝ) (B : ℝ) (hB : 0 < B)
    (hcostB : ∀ e t, edgeCost e t ≤ B) (D : ℕ)
    (hdegree : ∀ x, (neighborSet left right x).card ≤ D)
    (x : V) (centerShift : Fin n) :
    WeightedEdgeColoring.FiniteCategoricalSelection.rowMean
        (WeightedEdgeColoring.FiniteCategoricalSupportSplit.outsideProb
          (uniformShiftProb (V := V) (n := n)) ({x} : Finset V))
        (conditionalVertexUse left right edgeCost B x centerShift) () ≤ D := by
  rw [conditionalVertexUse_rowMean hn left right hloop edgeCost B x centerShift]
  calc
    vertexCyclicAverage left right edgeCost x / B ≤
        (((incidentSet left right x).card : ℝ) * B) / B :=
      div_le_div_of_nonneg_right
        (vertexCyclicAverage_le_card_mul hn left right edgeCost B hcostB x)
        hB.le
    _ = ((incidentSet left right x).card : ℝ) := by field_simp
    _ ≤ ((neighborSet left right x).card : ℝ) := by
      exact_mod_cast incidentSet_card_le_neighborSet_card left right hsimple x
    _ ≤ D := by exact_mod_cast hdegree x

/-- Genuine conditional Bernstein tail for the incident cost at one vertex.
The graph is simple and loopless, every edge cost lies in `[0,B]`, and the
neighbour degree is at most `D`.  The parameter `t` is measured after dividing
costs by `B`. -/
theorem conditionalBadVertex_mass_le_exp_sq {n : ℕ} (hn : 0 < n)
    (left right : E → V) (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f,
      ((left e = left f ∧ right e = right f) ∨
       (left e = right f ∧ right e = left f)) → e = f)
    (edgeCost : E → Fin n → ℝ) (B : ℝ) (hB : 0 < B)
    (hcost0 : ∀ e a, 0 ≤ edgeCost e a)
    (hcostB : ∀ e a, edgeCost e a ≤ B)
    (D : ℕ) (hD : 0 < D)
    (hdegree : ∀ x, (neighborSet left right x).card ≤ D)
    (t : ℝ) (ht0 : 0 ≤ t) (htD : t ≤ 2 * D)
    (x : V)
    (center : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Inside
      ({x} : Finset V) → Fin n) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
          (WeightedEdgeColoring.FiniteCategoricalSupportSplit.outsideProb
            (uniformShiftProb (V := V) (n := n)) ({x} : Finset V)))
        (conditionalBadVertex left right edgeCost (B * t) x center) ≤
      Real.exp (-(t ^ 2) / (4 * D)) := by
  classical
  let prob := WeightedEdgeColoring.FiniteCategoricalSupportSplit.outsideProb
    (uniformShiftProb (V := V) (n := n)) ({x} : Finset V)
  let use := conditionalVertexUse left right edgeCost B x (center ⟨x, by simp⟩)
  have hprob0 : ∀ s a, 0 ≤ prob s a := by
    intro s a
    exact uniformShiftProb_nonneg (V := V) hn s a
  have hprobSum : ∀ s, ∑ a, prob s a = 1 := by
    intro s
    exact sum_uniformShiftProb (V := V) hn s
  have huse0 : ∀ s a r, 0 ≤ use s a r := by
    exact conditionalVertexUse_nonneg left right edgeCost B hB hcost0 x
      (center ⟨x, by simp⟩)
  have huse1 : ∀ s a r, use s a r ≤ 1 := by
    exact conditionalVertexUse_le_one left right edgeCost B hB hsimple hcostB x
      (center ⟨x, by simp⟩)
  have hmeanD : WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob use () ≤ D := by
    exact conditionalVertexUse_rowMean_le_degree hn left right hloop hsimple
      edgeCost B hB hcostB D hdegree x (center ⟨x, by simp⟩)
  have hsubset : conditionalBadVertex left right edgeCost (B * t) x center ⊆
      WeightedEdgeColoring.FiniteCategoricalSelection.badRow use
        (fun _ ↦ WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob use () + t) () := by
    intro outside hout
    have hout' : vertexCyclicAverage left right edgeCost x + B * t <
        vertexIncidentCost left right edgeCost x
          (conditionedShift x center outside) := by
      simpa [conditionalBadVertex] using hout
    have hmean := conditionalVertexUse_rowMean hn left right hloop edgeCost B x
      (center ⟨x, by simp⟩)
    have hload := conditionalVertexUse_rowLoad left right hloop edgeCost B x
      center outside
    have hdiv : (vertexCyclicAverage left right edgeCost x + B * t) / B <
        vertexIncidentCost left right edgeCost x
          (conditionedShift x center outside) / B :=
      (div_lt_div_iff_of_pos_right hB).2 hout'
    have halgebra :
        (vertexCyclicAverage left right edgeCost x + B * t) / B =
          vertexCyclicAverage left right edgeCost x / B + t := by
      field_simp
    rw [halgebra] at hdiv
    simp only [WeightedEdgeColoring.FiniteCategoricalSelection.badRow,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hmean, hload]
    exact hdiv.le
  calc
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass prob)
        (conditionalBadVertex left right edgeCost (B * t) x center) ≤
        WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass prob)
          (WeightedEdgeColoring.FiniteCategoricalSelection.badRow use
            (fun _ ↦ WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob use () + t) ()) :=
      WeightedEdgeColoring.FiniteLocalLemma.eventMass_mono
        (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass_nonneg prob hprob0)
        hsubset
    _ ≤ Real.exp (-(t ^ 2) / (4 * D)) :=
      WeightedEdgeColoring.FiniteCategoricalSelection.categorical_centered_upperTail_mass_le
        prob use () (D : ℝ) t hprob0 hprobSum huse0 huse1 hmeanD
        (by exact_mod_cast hD) ht0 htD


end

end WeightedEdgeColoring.GlobalCyclicProfileShiftLocal
