import WeightedEdgeColoring.FinitePartialResamplingWitnessCylinder
import WeightedEdgeColoring.FinitePartialResamplingTracePrefixes

/-!
# Products attached to fixed partial-resampling witnesses

This file rewrites the two finite products attached to a witness as products
over its occurrence nodes.  Source-state requirements contribute the
categorical product of the node patch.  Rank-indexed row requirements
contribute one row weight for each node.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingWitnessProducts

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential
open WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
open WeightedEdgeColoring.FinitePartialResamplingProcess
open WeightedEdgeColoring.FinitePartialResamplingTracePrefixes
open WeightedEdgeColoring.FinitePartialResamplingWitnessStructure
open WeightedEdgeColoring.FinitePartialResamplingWitnessCylinder

noncomputable section

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

section SourceProduct

/-- The product over the states named by one source fiber of a patch is its
single local factor, or one when that source is absent. -/
private theorem prod_stateFiber_eq_partialFactor
    (prob : Source → State → ℝ)
    (Y : PartialAssignment Source State) (i : Source) :
    (∏ a : {a : State // Y i = some a}, prob i a.1) =
      match Y i with
      | none => 1
      | some a => prob i a := by
  classical
  calc
    _ = ∏ a ∈ (Finset.univ.filter fun a : State ↦ Y i = some a),
          prob i a := by
      symm
      exact Finset.prod_subtype
        (Finset.univ.filter fun a : State ↦ Y i = some a)
        (by intro a; simp)
        (fun a ↦ prob i a)
    _ = _ := by
      cases h : Y i with
      | none => simp
      | some value =>
          simp only [h, Option.some.injEq]
          apply Finset.prod_eq_single value
          · intro other hother hne
            have heq : value = other := (Finset.mem_filter.mp hother).2
            exact (hne heq.symm).elim
          · intro hnot
            exact (hnot (Finset.mem_filter.mpr
              ⟨Finset.mem_univ value, rfl⟩)).elim

/-- The source-state cylinder product of a witness is the product of the
categorical patch masses of its occurrence nodes. -/
theorem prod_witnessRequirement_probability_eq
    (prob : Source → State → ℝ)
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    {h : Nat} (hcard : tree.nodes.card < h + 1) :
    (∏ requirement : WitnessRequirement tree,
      prob (witnessRequirementCell tree hcard requirement).1
        (witnessRequirementState tree requirement)) =
      ∏ node : {node : Occurrence Source State Row // node ∈ tree.nodes},
        partialLambdaProduct prob node.1.2.2 := by
  classical
  simp_rw [Fintype.prod_sigma]
  simp only [witnessRequirementCell, witnessRequirementState]
  apply Fintype.prod_congr
  intro node
  unfold partialLambdaProduct partialProduct
  apply Fintype.prod_congr
  intro i
  exact prod_stateFiber_eq_partialFactor prob node.1.2.2 i

/-- Finset-binder form of `prod_witnessRequirement_probability_eq`. -/
theorem prod_witnessRequirement_probability_eq_nodes
    (prob : Source → State → ℝ)
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    {h : Nat} (hcard : tree.nodes.card < h + 1) :
    (∏ requirement : WitnessRequirement tree,
      prob (witnessRequirementCell tree hcard requirement).1
        (witnessRequirementState tree requirement)) =
      ∏ node ∈ tree.nodes, partialLambdaProduct prob node.2.2 := by
  rw [prod_witnessRequirement_probability_eq prob tree hcard]
  exact tree.nodes.prod_coe_sort
    (fun node ↦ partialLambdaProduct prob node.2.2)

end SourceProduct

section RowProduct

/-- Nodes of a witness carrying a fixed row. -/
def rowNodes
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (r : Row) : Finset (Occurrence Source State Row) :=
  tree.nodes.filter fun node ↦ node.2.1 = r

@[simp] theorem mem_rowNodes
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (r : Row) (node : Occurrence Source State Row) :
    node ∈ rowNodes tree r ↔ node ∈ tree.nodes ∧ node.2.1 = r := by
  simp [rowNodes]

/-- A witness occurrence carrying row `r`. -/
abbrev RowNode
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (r : Row) := {node : Occurrence Source State Row // node ∈ rowNodes tree r}

/-- Number of witness occurrences carrying row `r`. -/
def rowNodeCount
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (r : Row) : Nat :=
  (rowNodes tree r).card

/-- Equal rows and equal depths identify nodes. -/
def RowDepthInjective
    (tree : Witness (Source := Source) (State := State) (Row := Row)) : Prop :=
  ∀ {left right : Occurrence Source State Row},
    left ∈ tree.nodes → right ∈ tree.nodes →
    left.2.1 = right.2.1 →
    tree.depth left = tree.depth right → left = right

/-- Canonical backward witnesses have row-injective depth. -/
theorem witnessAt_rowDepthInjective_property {n : Nat}
    (history : Fin n → Label Source State Row) (endpoint : Fin n) :
    RowDepthInjective (witnessAt history endpoint) := by
  intro left right hleft hright hrow hdepth
  exact witnessAt_rowDepthInjective history endpoint hleft hright hrow hdepth

/-- Moving to a deeper node of the same row strictly decreases row rank. -/
theorem rowRank_lt_of_depth_lt
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {shallow deep : Occurrence Source State Row} {r : Row}
    (hshallow : shallow ∈ tree.nodes) (hdeep : deep ∈ tree.nodes)
    (hdeepRow : deep.2.1 = r)
    (hdepth : tree.depth shallow < tree.depth deep) :
    rowRank tree deep r < rowRank tree shallow r := by
  classical
  unfold rowRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro other hother
    have data := Finset.mem_filter.mp hother
    exact Finset.mem_filter.mpr
      ⟨data.1, data.2.1, lt_trans hdepth data.2.2⟩
  · intro heq
    have hlarge : deep ∈ tree.nodes.filter fun other ↦
        other.2.1 = r ∧ tree.depth shallow < tree.depth other :=
      Finset.mem_filter.mpr ⟨hdeep, hdeepRow, hdepth⟩
    have hsmall : deep ∈ tree.nodes.filter fun other ↦
        other.2.1 = r ∧ tree.depth deep < tree.depth other := by
      rw [heq]
      exact hlarge
    exact (Nat.lt_irrefl _ (Finset.mem_filter.mp hsmall).2.2)

/-- Under row-injective depth, same-row ranks identify witness nodes. -/
theorem rowRank_injective_on_row
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : RowDepthInjective tree)
    {left right : Occurrence Source State Row} {r : Row}
    (hleft : left ∈ tree.nodes) (hright : right ∈ tree.nodes)
    (hleftRow : left.2.1 = r) (hrightRow : right.2.1 = r)
    (hrank : rowRank tree left r = rowRank tree right r) :
    left = right := by
  by_cases hdepth : tree.depth left = tree.depth right
  · exact htree hleft hright (hleftRow.trans hrightRow.symm) hdepth
  · rcases lt_or_gt_of_ne hdepth with hlt | hgt
    · have hstrict := rowRank_lt_of_depth_lt hleft hright hrightRow hlt
      omega
    · have hstrict := rowRank_lt_of_depth_lt hright hleft hleftRow hgt
      omega

/-- A row rank lies in the finite set of nodes of that row. -/
theorem rowRank_lt_rowNodeCount
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {r : Row} (node : RowNode tree r) :
    rowRank tree node.1 r < rowNodeCount tree r := by
  classical
  unfold rowRank rowNodeCount
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro other hother
    have data := Finset.mem_filter.mp hother
    exact mem_rowNodes tree r other |>.mpr ⟨data.1, data.2.1⟩
  · intro heq
    have hlarge : node.1 ∈ rowNodes tree r := node.2
    have hsmall : node.1 ∈ tree.nodes.filter fun other ↦
        other.2.1 = r ∧ tree.depth node.1 < tree.depth other := by
      rw [heq]
      exact hlarge
    exact (Nat.lt_irrefl _ (Finset.mem_filter.mp hsmall).2.2)

/-- Intrinsic row rank as a finite index. -/
def rowRankIndex
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (r : Row) (node : RowNode tree r) : Fin (rowNodeCount tree r) :=
  ⟨rowRank tree node.1 r, rowRank_lt_rowNodeCount node⟩

theorem rowRankIndex_injective
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : RowDepthInjective tree) (r : Row) :
    Function.Injective (rowRankIndex tree r) := by
  intro left right heq
  apply Subtype.ext
  have hleft := (mem_rowNodes tree r left.1).mp left.2
  have hright := (mem_rowNodes tree r right.1).mp right.2
  apply rowRank_injective_on_row htree hleft.1 hright.1 hleft.2 hright.2
  exact congrArg Fin.val heq

/-- Row rank lists the nodes of one row without repetition or omission. -/
noncomputable def rowRankEquiv
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : RowDepthInjective tree) (r : Row) :
    RowNode tree r ≃ Fin (rowNodeCount tree r) :=
  Equiv.ofBijective (rowRankIndex tree r)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨rowRankIndex_injective htree r, by simp [rowNodeCount]⟩)

/-- For each row, list its witness patches in increasing intrinsic row rank. -/
def witnessRowRequirements
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : RowDepthInjective tree) :
    RowRequirements Source State Row :=
  fun r ↦ List.ofFn fun rank : Fin (rowNodeCount tree r) ↦
    ((rowRankEquiv tree htree r).symm rank).1.2.2

/-- The disjoint union of the row fibers is the full witness node type. -/
def sigmaRowNodeEquiv
    (tree : Witness (Source := Source) (State := State) (Row := Row)) :
    (Σ r : Row, RowNode tree r) ≃
      {node : Occurrence Source State Row // node ∈ tree.nodes} where
  toFun indexed :=
    ⟨indexed.2.1, (mem_rowNodes tree indexed.1 indexed.2.1).mp indexed.2.2 |>.1⟩
  invFun node :=
    ⟨node.1.2.1, ⟨node.1, (mem_rowNodes tree node.1.2.1 node.1).mpr
      ⟨node.2, rfl⟩⟩⟩
  left_inv indexed := by
    rcases indexed with ⟨r, ⟨node, hnode⟩⟩
    have hrow : node.2.1 = r := (mem_rowNodes tree r node).mp hnode |>.2
    subst r
    rfl
  right_inv node := by
    apply Subtype.ext
    rfl

/-- The weight of the rank-indexed row prefixes is exactly one row weight
per occurrence node. -/
theorem requirementsWeight_witnessRowRequirements
    (q : Row → PartialAssignment Source State → ℝ)
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : RowDepthInjective tree) :
    requirementsWeight q (witnessRowRequirements tree htree) =
      ∏ node : {node : Occurrence Source State Row // node ∈ tree.nodes},
        q node.1.2.1 node.1.2.2 := by
  classical
  unfold requirementsWeight
  calc
    (∏ r,
        (((witnessRowRequirements tree htree) r).map (q r)).prod) =
        ∏ r, ∏ node : RowNode tree r, q r node.1.2.2 := by
      apply Fintype.prod_congr
      intro r
      change
        ((List.ofFn fun rank : Fin (rowNodeCount tree r) ↦
          ((rowRankEquiv tree htree r).symm rank).1.2.2).map (q r)).prod = _
      rw [← List.ofFn_comp', List.prod_ofFn]
      simpa using
        ((rowRankEquiv tree htree r).symm).prod_comp
          (fun node : RowNode tree r ↦ q r node.1.2.2)
    _ = ∏ indexed : Σ r : Row, RowNode tree r,
          q indexed.1 indexed.2.1.2.2 := by
      symm
      exact Fintype.prod_sigma _
    _ = ∏ node : {node : Occurrence Source State Row // node ∈ tree.nodes},
          q node.1.2.1 node.1.2.2 := by
      apply Fintype.prod_equiv (sigmaRowNodeEquiv tree)
      rintro ⟨r, node⟩
      change q r node.1.2.2 = q node.1.2.1 node.1.2.2
      rw [(mem_rowNodes tree r node.1).mp node.2 |>.2]

/-- Finset-binder form of `requirementsWeight_witnessRowRequirements`. -/
theorem requirementsWeight_witnessRowRequirements_nodes
    (q : Row → PartialAssignment Source State → ℝ)
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : RowDepthInjective tree) :
    requirementsWeight q (witnessRowRequirements tree htree) =
      ∏ node ∈ tree.nodes, q node.2.1 node.2.2 := by
  rw [requirementsWeight_witnessRowRequirements q tree htree]
  exact tree.nodes.prod_coe_sort (fun node ↦ q node.2.1 node.2.2)

end RowProduct

end

end WeightedEdgeColoring.FinitePartialResamplingWitnessProducts
