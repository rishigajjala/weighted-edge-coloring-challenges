import WeightedEdgeColoring.SubtwoLabelRounding
import WeightedEdgeColoring.TwoConstraintRounding

/-!
# One endpoint label per boundary color

For one contracted block, each palette color has a fractional distribution
over the block's endpoint labels.  The existing two-constraint rounding
theorem chooses an integral label per color while adding at most two colors
to the expected count of every label.  This constructs disjoint color
classes before physical edge rounding.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo

variable {C L : Type*}
  [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L]

/-- The fractional mass assigned to a label among a finite color palette. -/
def boundaryLabelMean (prob : C → L → ℝ) (l : L) : ℝ :=
  ∑ c : C, prob c l

/-- The count of colors given a label by an integral option array. -/
def boundaryLabelIntegralCount (y : C × L → ℝ) (l : L) : ℝ :=
  ∑ c : C, y (c, l)

/-- A stochastic endpoint-label choice on each color can be rounded with
an additive error of at most two per label.  Positive support is retained,
which later makes each class compatible with the proposal it came from. -/
theorem exists_integral_boundaryLabelAllocation
    (prob : C → L → ℝ)
    (hprob0 : ∀ c l, 0 ≤ prob c l)
    (hprobSum : ∀ c, ∑ l : L, prob c l = 1) :
    ∃ y : C × L → ℝ,
      (∀ o, y o = 0 ∨ y o = 1) ∧
      (∀ c, ∑ l : L, y (c, l) = 1) ∧
      (∀ c l, y (c, l) = 1 → 0 < prob c l) ∧
      ∀ l, boundaryLabelIntegralCount y l ≤ boundaryLabelMean prob l + 2 := by
  let job : C × L → C := Prod.fst
  let use : C × L → L → ℝ := fun o l => if o.2 = l then 1 else 0
  let x : C × L → ℝ := fun o => prob o.1 o.2
  have hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1 := by
    intro ⟨c, l⟩
    constructor
    · exact hprob0 c l
    · calc
        prob c l ≤ ∑ t : L, prob c t :=
          Finset.single_le_sum (fun t _ => hprob0 c t) (Finset.mem_univ l)
        _ = 1 := hprobSum c
  have hjob : ∀ c, WeightedEdgeColoring.optionJobMass job x c = 1 := by
    intro c
    simp [WeightedEdgeColoring.optionJobMass, job, x, Fintype.sum_prod_type, hprobSum]
  have huse0 : ∀ o l, 0 ≤ use o l := by
    intro o l
    dsimp [use]
    split_ifs <;> norm_num
  have huse1 : ∀ o l, use o l ≤ 1 := by
    intro o l
    dsimp [use]
    split_ifs <;> norm_num
  have hsparse : ∀ o : C × L,
      (Finset.univ.filter fun l : L => use o l ≠ 0).card ≤ 2 := by
    intro o
    have hset : (Finset.univ.filter fun l : L => use o l ≠ 0) = {o.2} := by
      ext l
      simp [use, eq_comm]
    rw [hset]
    simp
  obtain ⟨y, hy01, hyjob, hysupport, hyload⟩ :=
    WeightedEdgeColoring.choose_one_option_per_job_indicators_support
      job use 1 x (by norm_num) hx hjob huse0 huse1 hsparse
  refine ⟨y, hy01, ?_, ?_, ?_⟩
  · intro c
    have hmass : WeightedEdgeColoring.optionJobMass job y c =
        ∑ l : L, y (c, l) := by
      simp only [WeightedEdgeColoring.optionJobMass, job, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      simp
    rw [← hmass]
    exact hyjob c
  · intro c l hyl
    exact hysupport (c, l) hyl
  · intro l
    have h := hyload l
    simpa [WeightedEdgeColoring.optionLoad, boundaryLabelIntegralCount,
      boundaryLabelMean, use, x, Fintype.sum_prod_type] using h

/-- An integral one-hot row has a uniquely chosen label. -/
theorem exists_unique_label_of_integral_row
    (y : C × L → ℝ)
    (hy01 : ∀ o, y o = 0 ∨ y o = 1)
    (hysum : ∀ c, ∑ l : L, y (c, l) = 1)
    (c : C) :
    ∃! l : L, y (c, l) = 1 := by
  have hex : ∃ l : L, y (c, l) = 1 := by
    by_contra hnone
    have hz : ∀ l : L, y (c, l) = 0 := by
      intro l
      rcases hy01 (c, l) with h0 | h1
      · exact h0
      · exact False.elim (hnone ⟨l, h1⟩)
    have hzero : (∑ l : L, y (c, l)) = 0 := by simp [hz]
    linarith [hysum c]
  obtain ⟨l, hl⟩ := hex
  refine ⟨l, hl, ?_⟩
  intro m hm
  by_contra hml
  have hnonneg : ∀ t : L, 0 ≤ y (c, t) := by
    intro t
    rcases hy01 (c, t) with h0 | h1
    · simp [h0]
    · simp [h1]
  have hrest : (∑ t ∈ (Finset.univ : Finset L).erase l,
      y (c, t)) = 0 := by
    have h := Finset.add_sum_erase (Finset.univ : Finset L)
      (fun t => y (c, t)) (Finset.mem_univ l)
    change y (c, l) + (∑ t ∈ (Finset.univ : Finset L).erase l,
      y (c, t)) = ∑ t : L, y (c, t) at h
    rw [hl, hysum c] at h
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun t _ => hnonneg t)).mp hrest m
      (Finset.mem_erase.mpr ⟨hml, Finset.mem_univ m⟩)
  linarith

/-- Choose the actual label of every color.  The resulting classes are
disjoint by construction and each uses at most its fractional mean plus two
colors. -/
theorem exists_boundaryLabelClasses
    (prob : C → L → ℝ)
    (hprob0 : ∀ c l, 0 ≤ prob c l)
    (hprobSum : ∀ c, ∑ l : L, prob c l = 1) :
    ∃ assign : C → L,
      (∀ c, 0 < prob c (assign c)) ∧
      ∀ l, ((Finset.univ : Finset C).filter fun c => assign c = l).card ≤
        Nat.floor (boundaryLabelMean prob l + 2) := by
  obtain ⟨y, hy01, hysum, hysupport, hycount⟩ :=
    exists_integral_boundaryLabelAllocation prob hprob0 hprobSum
  have hchoice (c : C) : ∃! l : L, y (c, l) = 1 :=
    exists_unique_label_of_integral_row y hy01 hysum c
  let assign : C → L := fun c => Classical.choose (hchoice c)
  have hchosen (c : C) : y (c, assign c) = 1 :=
    (Classical.choose_spec (hchoice c)).1
  have hzero (c : C) (l : L) (h : assign c ≠ l) : y (c, l) = 0 := by
    rcases hy01 (c, l) with h0 | h1
    · exact h0
    · exact False.elim (h ((Classical.choose_spec (hchoice c)).2 l h1).symm)
  have hindicator (c : C) (l : L) :
      y (c, l) = if assign c = l then 1 else 0 := by
    by_cases h : assign c = l
    · simpa [h] using hchosen c
    · simp [h, hzero c l h]
  refine ⟨assign, ?_, ?_⟩
  · intro c
    exact hysupport c (assign c) (hchosen c)
  · intro l
    have hcount : (boundaryLabelIntegralCount y l) =
        (((Finset.univ : Finset C).filter fun c => assign c = l).card : ℝ) := by
      simp [boundaryLabelIntegralCount, hindicator]
    have hreal := hycount l
    rw [hcount] at hreal
    exact Nat.le_floor hreal

/-- Apply the color-label choice independently at every block.  No bound
on the number of blocks enters the per-block error, because the choice is
made separately for each block's palette. -/
theorem exists_blockBoundaryLabelClasses
    {B : Type*} (prob : B → C → L → ℝ)
    (hprob0 : ∀ b c l, 0 ≤ prob b c l)
    (hprobSum : ∀ b c, ∑ l : L, prob b c l = 1) :
    ∃ assign : B → C → L,
      (∀ b c, 0 < prob b c (assign b c)) ∧
      (∀ b l,
        ((Finset.univ : Finset C).filter fun c => assign b c = l).card ≤
          Nat.floor (boundaryLabelMean (prob b) l + 2)) ∧
      ∀ b l l', l ≠ l' →
        Disjoint ((Finset.univ : Finset C).filter fun c => assign b c = l)
          ((Finset.univ : Finset C).filter fun c => assign b c = l') := by
  classical
  have hchoice (b : B) : ∃ assign : C → L,
      (∀ c, 0 < prob b c (assign c)) ∧
      ∀ l, ((Finset.univ : Finset C).filter fun c => assign c = l).card ≤
        Nat.floor (boundaryLabelMean (prob b) l + 2) :=
    exists_boundaryLabelClasses (prob b) (hprob0 b) (hprobSum b)
  choose assign hsupport hcounts using hchoice
  refine ⟨assign, hsupport, hcounts, ?_⟩
  intro b l l' hne
  rw [Finset.disjoint_left]
  intro c hc hc'
  have hl : assign b c = l := (Finset.mem_filter.mp hc).2
  have hl' : assign b c = l' := (Finset.mem_filter.mp hc').2
  exact hne (hl.symm.trans hl')

end WeightedEdgeColoring.Subtwo

namespace WeightedEdgeColoring.Subtwo

universe u

/-- A color is admissible for an edge when it carries that edge's endpoint
label at every block the edge touches.  This works for edges joining two
blocks, with one constraint at each endpoint block. -/
def BoundaryLabelCompatible
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {B L : Type*} {q : ℕ}
    (assign : B → Fin q → L)
    (touches : B → G.E → Prop) (label : B → G.E → L)
    (e : G.E) (c : Fin q) : Prop :=
  ∀ b, touches b e → assign b c = label b e

/-- Hard-mask a proposal by the chosen endpoint label classes. -/
noncomputable def boundaryLabelMaskedProposal
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {B L : Type*} {q : ℕ}
    (assign : B → Fin q → L)
    (touches : B → G.E → Prop) (label : B → G.E → L)
    (x : G.E → Fin q → ℝ) (e : G.E) (c : Fin q) : ℝ := by
  classical
  exact if BoundaryLabelCompatible assign touches label e c then x e c else 0

theorem boundaryLabelMaskedProposal_nonneg_le
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {B L : Type*} {q : ℕ}
    (assign : B → Fin q → L)
    (touches : B → G.E → Prop) (label : B → G.E → L)
    (x : G.E → Fin q → ℝ) (hx : ∀ e c, 0 ≤ x e c)
    (e : G.E) (c : Fin q) :
    0 ≤ boundaryLabelMaskedProposal assign touches label x e c ∧
      boundaryLabelMaskedProposal assign touches label x e c ≤ x e c := by
  unfold boundaryLabelMaskedProposal
  split_ifs
  · exact ⟨hx e c, le_rfl⟩
  · exact ⟨le_rfl, hx e c⟩

theorem boundaryLabelMaskedProposal_pos_support
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {B L : Type*} {q : ℕ}
    (assign : B → Fin q → L)
    (touches : B → G.E → Prop) (label : B → G.E → L)
    (x : G.E → Fin q → ℝ) (e : G.E) (c : Fin q)
    (hpos : 0 < boundaryLabelMaskedProposal assign touches label x e c) :
    BoundaryLabelCompatible assign touches label e c := by
  by_contra hnot
  simp [boundaryLabelMaskedProposal, hnot] at hpos

theorem boundaryLabelMaskedProposal_sum_le
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {B L : Type*} {q : ℕ}
    (assign : B → Fin q → L)
    (touches : B → G.E → Prop) (label : B → G.E → L)
    (x : G.E → Fin q → ℝ) (hx : ∀ e c, 0 ≤ x e c)
    (e : G.E) :
    (∑ c, boundaryLabelMaskedProposal assign touches label x e c) ≤
      ∑ c, x e c := by
  apply Finset.sum_le_sum
  intro c _
  exact (boundaryLabelMaskedProposal_nonneg_le assign touches label x hx e c).2

/-- Physical incident weight lost when a pre-existing proposal is masked
to one endpoint label per block and color. -/
noncomputable def boundaryLabelDiscardedWeight
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {B L : Type*} {q : ℕ}
    (assign : B → Fin q → L)
    (touches : B → G.E → Prop) (label : B → G.E → L)
    (x : G.E → Fin q → ℝ) (v : G.V) : ℝ :=
  ∑ e : G.E,
    if G.Inc v e then G.weight e *
      (∑ c : Fin q,
        (x e c - boundaryLabelMaskedProposal assign touches label x e c))
    else 0

theorem boundaryLabelDiscardedWeight_nonneg
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {B L : Type*} {q : ℕ}
    (assign : B → Fin q → L)
    (touches : B → G.E → Prop) (label : B → G.E → L)
    (x : G.E → Fin q → ℝ) (hx : ∀ e c, 0 ≤ x e c) (v : G.V) :
    0 ≤ boundaryLabelDiscardedWeight assign touches label x v := by
  unfold boundaryLabelDiscardedWeight
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · apply mul_nonneg (G.weight_nonneg e)
    apply Finset.sum_nonneg
    intro c _
    exact sub_nonneg.mpr
      (boundaryLabelMaskedProposal_nonneg_le assign touches label x hx e c).2
  · exact le_rfl

/-- Exact cost of imposing hard endpoint-label classes on a proposal.
The masked deficit equals the original deficit plus discarded incident
weight.  An `o(n)` bound on that weight at each vertex preserves the
sub-two coefficient. -/
theorem boundaryLabelMaskedProposal_deficit_eq
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {B L : Type*} {q : ℕ}
    (assign : B → Fin q → L)
    (touches : B → G.E → Prop) (label : B → G.E → L)
    (x : G.E → Fin q → ℝ) (v : G.V) :
    G.proposalDeficit
        (boundaryLabelMaskedProposal assign touches label x) v =
      G.proposalDeficit x v +
        boundaryLabelDiscardedWeight assign touches label x v := by
  unfold WeightedEdgeColoring.WeightedMultigraph.proposalDeficit
    boundaryLabelDiscardedWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : G.Inc v e
  · simp only [he, ite_true]
    rw [Finset.sum_sub_distrib]
    ring
  · simp [he]

/-- If the original local feasibility certificate is a harmonic charge row,
hard masking preserves that certificate and hence every local star-packing
polytope constraint.  Its effect on the deficit is quantified separately
by `boundaryLabelMaskedProposal_deficit_eq`. -/
theorem boundaryLabelMaskedProposal_localFeasible_of_charge
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {B L K : Type*} {q : ℕ}
    [Fintype K] [DecidableEq K]
    (assign : B → Fin q → L)
    (touches : B → G.E → Prop) (label : B → G.E → L)
    (x : G.E → Fin q → ℝ)
    (capacity : K → ℕ) (hcapacity : ∀ k, 0 < capacity k)
    (classOf : G.E → K) (M : ℝ)
    (hweight : ∀ e, G.weight e ≤ (1 : ℝ) / capacity (classOf e))
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hM0 : 0 ≤ M) (hxM : ∀ e c, x e c ≤ M)
    (hbudget : ∀ v c,
      (∑ e : G.StarEdge v, x e.1 c / (capacity (classOf e.1) : ℝ)) +
        (Fintype.card K : ℝ) * M ≤ 1) :
    ∀ v c, G.IsAverageOfStarFeasibleSets v
      (fun e => boundaryLabelMaskedProposal assign touches label x e.1 c) := by
  intro v c
  apply G.sizeClasses_isAverageOfStarFeasibleSets_of_charge capacity hcapacity
    (fun e => classOf e.1)
    (fun e => boundaryLabelMaskedProposal assign touches label x e.1 c) M
  · intro e
    exact hweight e.1
  · intro e
    exact (boundaryLabelMaskedProposal_nonneg_le assign touches label x hx0 e.1 c).1
  · exact hM0
  · intro e
    exact (boundaryLabelMaskedProposal_nonneg_le assign touches label x hx0 e.1 c).2.trans
      (hxM e.1 c)
  · calc
      (∑ e : G.StarEdge v,
          boundaryLabelMaskedProposal assign touches label x e.1 c /
            (capacity (classOf e.1) : ℝ)) +
          (Fintype.card K : ℝ) * M ≤
        (∑ e : G.StarEdge v,
          x e.1 c / (capacity (classOf e.1) : ℝ)) +
          (Fintype.card K : ℝ) * M := by
        exact add_le_add
          (Finset.sum_le_sum (fun e _ =>
            div_le_div_of_nonneg_right
              (boundaryLabelMaskedProposal_nonneg_le assign touches label x hx0 e.1 c).2
              (Nat.cast_nonneg _))) le_rfl
      _ ≤ 1 := hbudget v c

/-- Construct disjoint endpoint-label classes at every block, then mask a
charge-certified physical proposal to those classes.  The resulting proposal
is locally feasible and supported on the chosen labels.  The exact deficit
identity expresses its deficit in terms of the discarded incident weight;
an appropriate bound on that weight yields coefficient κ. -/
theorem exists_boundaryLabelClasses_and_localProposal
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {B L K : Type*} {q : ℕ}
    [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K]
    (prob : B → Fin q → L → ℝ)
    (hprob0 : ∀ b c l, 0 ≤ prob b c l)
    (hprobSum : ∀ b c, ∑ l : L, prob b c l = 1)
    (touches : B → G.E → Prop) (label : B → G.E → L)
    (x : G.E → Fin q → ℝ)
    (capacity : K → ℕ) (hcapacity : ∀ k, 0 < capacity k)
    (classOf : G.E → K) (M : ℝ)
    (hweight : ∀ e, G.weight e ≤ (1 : ℝ) / capacity (classOf e))
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hM0 : 0 ≤ M) (hxM : ∀ e c, x e c ≤ M)
    (hbudget : ∀ v c,
      (∑ e : G.StarEdge v, x e.1 c / (capacity (classOf e.1) : ℝ)) +
        (Fintype.card K : ℝ) * M ≤ 1) :
    ∃ assign : B → Fin q → L,
      (∀ b c, 0 < prob b c (assign b c)) ∧
      (∀ b l,
        ((Finset.univ : Finset (Fin q)).filter fun c => assign b c = l).card ≤
          Nat.floor (boundaryLabelMean (prob b) l + 2)) ∧
      (∀ b l l', l ≠ l' →
        Disjoint ((Finset.univ : Finset (Fin q)).filter fun c => assign b c = l)
          ((Finset.univ : Finset (Fin q)).filter fun c => assign b c = l')) ∧
      let x' := boundaryLabelMaskedProposal assign touches label x
      (∀ e c, 0 ≤ x' e c ∧ x' e c ≤ x e c) ∧
      (∀ v c, G.IsAverageOfStarFeasibleSets v (fun e => x' e.1 c)) ∧
      (∀ e c b, 0 < x' e c → touches b e → assign b c = label b e) ∧
      ∀ v, G.proposalDeficit x' v =
        G.proposalDeficit x v +
          boundaryLabelDiscardedWeight assign touches label x v := by
  obtain ⟨assign, hpositive, hcounts, hdisj⟩ :=
    exists_blockBoundaryLabelClasses prob hprob0 hprobSum
  refine ⟨assign, hpositive, hcounts, hdisj, ?_, ?_, ?_, ?_⟩
  · intro e c
    exact boundaryLabelMaskedProposal_nonneg_le assign touches label x hx0 e c
  · exact boundaryLabelMaskedProposal_localFeasible_of_charge
      assign touches label x capacity hcapacity classOf M hweight hx0 hM0 hxM hbudget
  · intro e c b hpos ht
    exact (boundaryLabelMaskedProposal_pos_support
      assign touches label x e c hpos) b ht
  · intro v
    exact boundaryLabelMaskedProposal_deficit_eq assign touches label x v

end WeightedEdgeColoring.Subtwo
