import WeightedEdgeColoring.FiniteCategoricalSelection

namespace WeightedEdgeColoring.FiniteCategoricalSupportSplit

open scoped BigOperators

variable {Source State : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]

abbrev Inside (K : Finset Source) := {s : Source // s ∈ K}
abbrev Outside (K : Finset Source) := {s : Source // s ∉ K}

/-- Restrict an assignment to `K` and its complement. -/
noncomputable def splitEquiv (K : Finset Source) :
    (Source → State) ≃ ((Inside K → State) × (Outside K → State)) where
  toFun x := (fun s ↦ x s, fun s ↦ x s)
  invFun p s := if hs : s ∈ K then p.1 ⟨s, hs⟩ else p.2 ⟨s, hs⟩
  left_inv x := by
    funext s
    by_cases hs : s ∈ K <;> simp [hs]
  right_inv p := by
    apply Prod.ext <;> funext s
    · simp [s.2]
    · simp [s.2]

def insideProb (prob : Source → State → ℝ) (K : Finset Source) :
    Inside K → State → ℝ := fun s ↦ prob s

def outsideProb (prob : Source → State → ℝ) (K : Finset Source) :
    Outside K → State → ℝ := fun s ↦ prob s

@[simp] theorem splitEquiv_apply_inside (K : Finset Source)
    (x : Source → State) (s : Inside K) :
    (splitEquiv K x).1 s = x s := rfl

@[simp] theorem splitEquiv_apply_outside (K : Finset Source)
    (x : Source → State) (s : Outside K) :
    (splitEquiv K x).2 s = x s := rfl

/-- Categorical product mass factors exactly across a support split. -/
theorem categoricalMass_split (prob : Source → State → ℝ)
    (K : Finset Source) (a : Inside K → State) (b : Outside K → State) :
    WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass prob
        ((splitEquiv K).symm (a, b)) =
      WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass (insideProb prob K) a *
        WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass (outsideProb prob K) b := by
  classical
  unfold WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
  rw [← Finset.prod_sdiff (s₁ := K) (s₂ := Finset.univ)
    (f := fun s ↦ prob s ((splitEquiv K).symm (a, b) s))
    (Finset.subset_univ K)]
  rw [mul_comm]
  congr 1
  · calc
      (∏ s ∈ K, prob s ((splitEquiv K).symm (a, b) s)) =
          ∏ s : Inside K, prob s ((splitEquiv K).symm (a, b) s) :=
        Finset.prod_subtype K (by simp)
          (fun s ↦ prob s ((splitEquiv K).symm (a, b) s))
      _ = ∏ s, insideProb prob K s (a s) := by
        apply Finset.prod_congr rfl
        intro s _
        simp [insideProb, splitEquiv, s.2]
  · calc
      (∏ s ∈ Finset.univ \ K,
          prob s ((splitEquiv K).symm (a, b) s)) =
          ∏ s : Outside K, prob s ((splitEquiv K).symm (a, b) s) :=
        Finset.prod_subtype (Finset.univ \ K) (by simp)
          (fun s ↦ prob s ((splitEquiv K).symm (a, b) s))
      _ = ∏ s, outsideProb prob K s (b s) := by
        apply Finset.prod_congr rfl
        intro s _
        simp [outsideProb, splitEquiv, s.2]

noncomputable def splitEvent (K : Finset Source)
    (event : Finset ((Inside K → State) × (Outside K → State))) :
    Finset (Source → State) :=
  event.map (splitEquiv K).symm.toEmbedding

@[simp] theorem mem_splitEvent (K : Finset Source)
    (event : Finset ((Inside K → State) × (Outside K → State)))
    (x : Source → State) :
    x ∈ splitEvent K event ↔ splitEquiv K x ∈ event := by
  classical
  simp [splitEvent]

/-- Change of variables from global assignments to the two support blocks. -/
theorem eventMass_splitEvent (prob : Source → State → ℝ) (K : Finset Source)
    (event : Finset ((Inside K → State) × (Outside K → State))) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass prob)
        (splitEvent K event) =
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteProductCylinder.productMass
          (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass (insideProb prob K))
          (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass (outsideProb prob K)))
        event := by
  classical
  rw [WeightedEdgeColoring.FiniteLocalLemma.eventMass, splitEvent, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p hp
  exact categoricalMass_split prob K p.1 p.2

noncomputable def insideCylinder (K : Finset Source)
    (event : Finset (Inside K → State)) : Finset (Source → State) :=
  splitEvent K (WeightedEdgeColoring.FiniteProductCylinder.firstCylinder event)

noncomputable def outsideCylinder (K : Finset Source)
    (event : Finset (Outside K → State)) : Finset (Source → State) :=
  splitEvent K (WeightedEdgeColoring.FiniteProductCylinder.secondCylinder event)

@[simp] theorem mem_insideCylinder (K : Finset Source)
    (event : Finset (Inside K → State)) (x : Source → State) :
    x ∈ insideCylinder K event ↔ (splitEquiv K x).1 ∈ event := by
  classical
  simp [insideCylinder]

@[simp] theorem mem_outsideCylinder (K : Finset Source)
    (event : Finset (Outside K → State)) (x : Source → State) :
    x ∈ outsideCylinder K event ↔ (splitEquiv K x).2 ∈ event := by
  classical
  simp [outsideCylinder]

noncomputable def insideProjection (K : Finset Source)
    (event : Finset (Source → State)) : Finset (Inside K → State) :=
  Finset.univ.filter fun a ↦ ∃ b, (splitEquiv K).symm (a, b) ∈ event

noncomputable def outsideProjection (K : Finset Source)
    (event : Finset (Source → State)) : Finset (Outside K → State) :=
  Finset.univ.filter fun b ↦ ∃ a, (splitEquiv K).symm (a, b) ∈ event

/-- Every event supported on `K` is the corresponding first-block cylinder. -/
theorem eq_insideCylinder_of_dependsOn (K : Finset Source)
    (event : Finset (Source → State))
    (hdep : WeightedEdgeColoring.FiniteCategoricalSelection.DependsOn K event) :
    event = insideCylinder K (insideProjection K event) := by
  classical
  ext x
  constructor
  · intro hx
    simp [insideProjection]
    exact ⟨(splitEquiv K x).2, by simpa using hx⟩
  · intro hx
    rcases (by simpa [insideProjection] using hx) with ⟨b, hb⟩
    let y := (splitEquiv K).symm ((splitEquiv K x).1, b)
    have hagree : ∀ s ∈ K, y s = x s := by
      intro s hs
      let hi : Inside K := ⟨s, hs⟩
      have hsplit : (splitEquiv K y).1 = (splitEquiv K x).1 := by
        simp [y]
      exact congrFun hsplit hi
    exact (hdep y x hagree).mp (by simpa [y] using hb)

/-- If an event depends on `L` disjoint from `K`, it is an outside-`K`
cylinder. -/
theorem eq_outsideCylinder_of_dependsOn_disjoint
    (K L : Finset Source) (event : Finset (Source → State))
    (hdisj : Disjoint K L)
    (hdep : WeightedEdgeColoring.FiniteCategoricalSelection.DependsOn L event) :
    event = outsideCylinder K (outsideProjection K event) := by
  classical
  ext x
  constructor
  · intro hx
    simp [outsideProjection]
    exact ⟨(splitEquiv K x).1, by simpa using hx⟩
  · intro hx
    rcases (by simpa [outsideProjection] using hx) with ⟨a, ha⟩
    let y := (splitEquiv K).symm (a, (splitEquiv K x).2)
    have hagree : ∀ s ∈ L, y s = x s := by
      intro s hs
      have hsK : s ∉ K := by
        intro hs'
        exact Finset.disjoint_left.mp hdisj hs' hs
      let ho : Outside K := ⟨s, hsK⟩
      have hsplit : (splitEquiv K y).2 = (splitEquiv K x).2 := by
        simp [y]
      exact congrFun hsplit ho
    exact (hdep y x hagree).mp (by simpa [y] using ha)

/-- Exact independence of events supported on disjoint source sets. -/
theorem independentEvents_of_dependsOn_disjoint
    (prob : Source → State → ℝ)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (K L : Finset Source) (E F : Finset (Source → State))
    (hdisj : Disjoint K L)
    (hE : WeightedEdgeColoring.FiniteCategoricalSelection.DependsOn K E)
    (hF : WeightedEdgeColoring.FiniteCategoricalSelection.DependsOn L F) :
    WeightedEdgeColoring.FiniteProductCylinder.IndependentEvents
      (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass prob) E F := by
  classical
  rw [eq_insideCylinder_of_dependsOn K E hE,
    eq_outsideCylinder_of_dependsOn_disjoint K L F hdisj hF]
  unfold WeightedEdgeColoring.FiniteProductCylinder.IndependentEvents
  rw [show insideCylinder K (insideProjection K E) ∩
      outsideCylinder K (outsideProjection K F) =
      splitEvent K ((insideProjection K E).product (outsideProjection K F)) by
    ext x; simp [insideCylinder, outsideCylinder]]
  rw [eventMass_splitEvent]
  rw [WeightedEdgeColoring.FiniteProductCylinder.eventMass_rectangle]
  have hin : ∀ s : Inside K,
      ∑ a, insideProb prob K s a = 1 := fun s ↦ hprobSum s
  have hout : ∀ s : Outside K,
      ∑ a, outsideProb prob K s a = 1 := fun s ↦ hprobSum s
  have hmassIn :
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass prob)
          (insideCylinder K (insideProjection K E)) =
        WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass (insideProb prob K))
          (insideProjection K E) := by
    unfold insideCylinder
    rw [eventMass_splitEvent]
    unfold WeightedEdgeColoring.FiniteProductCylinder.firstCylinder
    rw [
      WeightedEdgeColoring.FiniteProductCylinder.eventMass_rectangle]
    simp [WeightedEdgeColoring.FiniteLocalLemma.eventMass,
      WeightedEdgeColoring.FiniteCategoricalSelection.sum_categoricalMass _ hout]
  have hmassOut :
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass prob)
          (outsideCylinder K (outsideProjection K F)) =
        WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass (outsideProb prob K))
          (outsideProjection K F) := by
    unfold outsideCylinder
    rw [eventMass_splitEvent]
    unfold WeightedEdgeColoring.FiniteProductCylinder.secondCylinder
    rw [
      WeightedEdgeColoring.FiniteProductCylinder.eventMass_rectangle]
    simp [WeightedEdgeColoring.FiniteLocalLemma.eventMass,
      WeightedEdgeColoring.FiniteCategoricalSelection.sum_categoricalMass _ hin]
  rw [hmassIn, hmassOut]

section RowOverlap

variable {Row : Type*} [Fintype Row] [DecidableEq Row]

/-- Rows adjacent to `r` are exactly the other rows sharing a contributing
source with `r`. -/
noncomputable def overlapNeighbor
    (use : Source → State → Row → ℝ) (r : Row) : Finset Row :=
  Finset.univ.filter fun r' ↦ r' ≠ r ∧
    (WeightedEdgeColoring.FiniteCategoricalSelection.rowSupport use r ∩
      WeightedEdgeColoring.FiniteCategoricalSelection.rowSupport use r').Nonempty

noncomputable def supportsOfRows
    (use : Source → State → Row → ℝ) (T : Finset Row) : Finset Source :=
  T.biUnion (WeightedEdgeColoring.FiniteCategoricalSelection.rowSupport use)

/-- Avoidance of a family of overload events depends only on the union of
their row supports. -/
theorem avoid_badRows_dependsOn_supportsOfRows
    (use : Source → State → Row → ℝ) (threshold : Row → ℝ)
    (T : Finset Row) :
    WeightedEdgeColoring.FiniteCategoricalSelection.DependsOn (supportsOfRows use T)
      (WeightedEdgeColoring.FiniteLocalLemma.avoid
        (WeightedEdgeColoring.FiniteCategoricalSelection.badRow use threshold) T) := by
  intro x y hxy
  simp only [WeightedEdgeColoring.FiniteLocalLemma.avoid, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hx r hr hybad
    have hagree : ∀ s ∈ WeightedEdgeColoring.FiniteCategoricalSelection.rowSupport use r,
        x s = y s := by
      intro s hs
      exact hxy s (Finset.mem_biUnion.mpr ⟨r, hr, hs⟩)
    have hdep := WeightedEdgeColoring.FiniteCategoricalSelection.badRow_dependsOn_rowSupport
      use threshold r x y hagree
    exact hx r hr (hdep.mpr hybad)
  · intro hy r hr hxbad
    have hagree : ∀ s ∈ WeightedEdgeColoring.FiniteCategoricalSelection.rowSupport use r,
        x s = y s := by
      intro s hs
      exact hxy s (Finset.mem_biUnion.mpr ⟨r, hr, hs⟩)
    have hdep := WeightedEdgeColoring.FiniteCategoricalSelection.badRow_dependsOn_rowSupport
      use threshold r x y hagree
    exact hy r hr (hdep.mp hxbad)

/-- Non-neighbour rows have a support union disjoint from the current row. -/
theorem rowSupport_disjoint_supportsOfRows_of_nonNeighbors
    (use : Source → State → Row → ℝ) (r : Row) (T : Finset Row)
    (hT : T ⊆ Finset.univ \ insert r (overlapNeighbor use r)) :
    Disjoint (WeightedEdgeColoring.FiniteCategoricalSelection.rowSupport use r)
      (supportsOfRows use T) := by
  rw [Finset.disjoint_left]
  intro s hsr hsT
  rcases Finset.mem_biUnion.mp hsT with ⟨r', hr'T, hsr'⟩
  have houtside := Finset.mem_sdiff.mp (hT hr'T)
  have hr'ne : r' ≠ r := by
    intro heq
    exact houtside.2 (by simp [heq])
  have hover : r' ∈ overlapNeighbor use r := by
    simp only [overlapNeighbor, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hr'ne, ⟨s, Finset.mem_inter.mpr ⟨hsr, hsr'⟩⟩⟩
  exact houtside.2 (by simp [hover])

/-- Categorical LLL selector with dependency expressed solely by overlap of
row supports. -/
theorem exists_choice_rowLoad_lt_of_support_overlap
    (prob : Source → State → ℝ) (use : Source → State → Row → ℝ)
    (threshold : Row → ℝ) (lambda : Row → ℝ) (p x : ℝ) (d : ℕ)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huse1 : ∀ s a r, use s a r ≤ 1)
    (hlambda : ∀ r, 0 ≤ lambda r)
    (hdegree : ∀ r, (overlapNeighbor use r).card ≤ d)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hnumeric : p ≤ x * (1 - x) ^ d)
    (hchernoff : ∀ r, Real.exp (-lambda r * threshold r +
      (Real.exp (lambda r) - 1) *
        WeightedEdgeColoring.FiniteCategoricalSelection.rowMean prob use r) ≤ p) :
    ∃ choice : Source → State, ∀ r,
      WeightedEdgeColoring.FiniteCategoricalSelection.rowLoad use r choice < threshold r := by
  apply WeightedEdgeColoring.FiniteCategoricalSelection.exists_choice_rowLoad_lt_of_lopsided_local_lemma
    prob use threshold (overlapNeighbor use) lambda p x d hprob0 hprobSum
    huse0 huse1 hlambda hdegree hx0 hx1 hnumeric hchernoff
  intro r T hT
  apply independentEvents_of_dependsOn_disjoint prob hprobSum
    (WeightedEdgeColoring.FiniteCategoricalSelection.rowSupport use r)
    (supportsOfRows use T)
  · exact rowSupport_disjoint_supportsOfRows_of_nonNeighbors use r T hT
  · exact WeightedEdgeColoring.FiniteCategoricalSelection.badRow_dependsOn_rowSupport
      use threshold r
  · exact avoid_badRows_dependsOn_supportsOfRows use threshold T

end RowOverlap

end WeightedEdgeColoring.FiniteCategoricalSupportSplit
