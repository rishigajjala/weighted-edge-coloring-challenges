import WeightedEdgeColoring.FinitePartialResamplingWitnessStructure
import WeightedEdgeColoring.FinitePartialResamplingCoarseCriterion
import Mathlib.Data.Finset.Lattice.Fold

/-!
# From occurrence witnesses to canonical witness trees

The backward construction records occurrences, rather than labels, so that
two uses of one label at different times remain different nodes.  The finite
tree budget is phrased using `ProperRootedTree`, whose children are indexed by
their labels.  This file gives the finite bridge between those two forms.

For a proper occurrence witness, sibling labels are distinct.  We therefore
choose the unique occurrence carrying each child label and recursively unfold
the occurrence tree.  A global maximum depth supplies a common depth budget
for all branches.  The final theorem identifies the canonical tree weight
with the product of the node weights over the original occurrence finset, so
repeated labels retain their full multiplicity.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingWitnessBridge

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
open WeightedEdgeColoring.FinitePartialResamplingTreeWeights
open WeightedEdgeColoring.FinitePartialResamplingWitnessStructure

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- The largest recorded depth of a node of an occurrence witness. -/
def maxDepth
    (tree : Witness (Source := Source) (State := State) (Row := Row)) : Nat :=
  tree.nodes.sup tree.depth

theorem depth_le_maxDepth
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {node : Occurrence Source State Row} (hnode : node ∈ tree.nodes) :
    tree.depth node ≤ maxDepth tree := by
  exact Finset.le_sup hnode

/-- The occurrence carrying one label in the child-label finset.  Properness
will imply that this occurrence is unique. -/
noncomputable def childOccurrence
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (parent : Occurrence Source State Row)
    (child : ↥(childLabels tree parent)) : Occurrence Source State Row :=
  Classical.choose (Finset.mem_image.mp child.property)

theorem childOccurrence_mem_childOccurrences
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (parent : Occurrence Source State Row)
    (child : ↥(childLabels tree parent)) :
    childOccurrence tree parent child ∈ childOccurrences tree parent := by
  classical
  exact (Classical.choose_spec (Finset.mem_image.mp child.property)).1

theorem childOccurrence_label
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (parent : Occurrence Source State Row)
    (child : ↥(childLabels tree parent)) :
    (childOccurrence tree parent child).2 = child.1 := by
  classical
  exact (Classical.choose_spec (Finset.mem_image.mp child.property)).2

theorem childOccurrence_mem_nodes
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (parent : Occurrence Source State Row)
    (child : ↥(childLabels tree parent)) :
    childOccurrence tree parent child ∈ tree.nodes := by
  exact (Finset.mem_filter.mp
    (childOccurrence_mem_childOccurrences tree parent child)).1

theorem childOccurrence_parent
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (parent : Occurrence Source State Row)
    (child : ↥(childLabels tree parent)) :
    tree.parent (childOccurrence tree parent child) = some parent := by
  exact (Finset.mem_filter.mp
    (childOccurrence_mem_childOccurrences tree parent child)).2

/-- Distinct children of a proper occurrence node have distinct labels. -/
theorem child_label_injective
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) {parent : Occurrence Source State Row}
    {left right : Occurrence Source State Row}
    (hleft : left ∈ childOccurrences tree parent)
    (hright : right ∈ childOccurrences tree parent)
    (hlabel : left.2 = right.2) : left = right := by
  by_contra hne
  have hleftData := Finset.mem_filter.mp hleft
  have hrightData := Finset.mem_filter.mp hright
  have hnconflict := htree.siblings_nonconflicting left hleftData.1
    right hrightData.1 parent hleftData.2 hrightData.2 hne
  apply hnconflict
  rw [hlabel]
  exact Or.inl rfl

/-- The chosen occurrence is the inverse of taking the label on the proper
child finset. -/
theorem childOccurrence_of_occurrence
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) {parent child : Occurrence Source State Row}
    (hchild : child ∈ childOccurrences tree parent) :
    childOccurrence tree parent
      ⟨child.2, Finset.mem_image.mpr ⟨child, hchild, rfl⟩⟩ = child := by
  apply child_label_injective htree
  · exact childOccurrence_mem_childOccurrences tree parent _
  · exact hchild
  · exact childOccurrence_label tree parent _

/-- Child occurrences and child labels are equivalent for a proper witness.
The inverse retains the occurrence time, while the forward map is label
erasure. -/
noncomputable def childLabelEquiv
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) (parent : Occurrence Source State Row) :
    ↥(childOccurrences tree parent) ≃ ↥(childLabels tree parent) where
  toFun child :=
    ⟨child.1.2, Finset.mem_image.mpr ⟨child.1, child.2, rfl⟩⟩
  invFun child :=
    ⟨childOccurrence tree parent child,
      childOccurrence_mem_childOccurrences tree parent child⟩
  left_inv child := by
    apply Subtype.ext
    exact childOccurrence_of_occurrence htree child.2
  right_inv child := by
    apply Subtype.ext
    exact childOccurrence_label tree parent child

/-- At maximum depth there can be no child label. -/
theorem childLabels_eq_empty_of_maxDepth_le_depth
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) {node : Occurrence Source State Row}
    (hnode : node ∈ tree.nodes) (hmax : maxDepth tree ≤ tree.depth node) :
    childLabels tree node = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro child hchild
  let indexedChild : ↥(childLabels tree node) := ⟨child, hchild⟩
  let occurrence := childOccurrence tree node indexedChild
  have hoccurrenceMem : occurrence ∈ tree.nodes :=
    childOccurrence_mem_nodes tree node indexedChild
  have hoccurrenceParent : tree.parent occurrence = some node :=
    childOccurrence_parent tree node indexedChild
  have hdepth := htree.parent_depth occurrence hoccurrenceMem node
    hoccurrenceParent
  have hle := depth_le_maxDepth hoccurrenceMem
  omega

/-- Recursively unfold one occurrence node into the canonical label-indexed
tree.  `fuel` is a common remaining depth budget. -/
noncomputable def toProperRootedTreeAt
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : IsProper tree) (node : Occurrence Source State Row)
    (hnode : node ∈ tree.nodes) :
    (fuel : Nat) → maxDepth tree - tree.depth node ≤ fuel →
      ProperRootedTree
        (ProperChildren (Source := Source) (State := State) (Row := Row))
        (fuel + 1) node.2
  | 0, _hfuel => by
      let emptyChildren : {s : Finset (Label Source State Row) //
          ProperChildren node.2 s} := ⟨∅, by simp [ProperChildren]⟩
      refine ⟨emptyChildren, ?_⟩
      intro child
      have hfalse : False := by
        have hmem : child.1 ∈ (∅ : Finset (Label Source State Row)) :=
          child.property
        exact Finset.notMem_empty child.1 hmem
      exact hfalse.elim
  | fuel + 1, hfuel => by
      refine ⟨⟨childLabels tree node, childLabels_proper htree hnode⟩, ?_⟩
      intro child
      let occurrence := childOccurrence tree node child
      have hoccurrenceMem : occurrence ∈ tree.nodes :=
        childOccurrence_mem_nodes tree node child
      have hoccurrenceParent : tree.parent occurrence = some node :=
        childOccurrence_parent tree node child
      have hdepth : tree.depth occurrence = tree.depth node + 1 :=
        htree.parent_depth occurrence hoccurrenceMem node hoccurrenceParent
      have hle : tree.depth occurrence ≤ maxDepth tree :=
        depth_le_maxDepth hoccurrenceMem
      have hchildFuel : maxDepth tree - tree.depth occurrence ≤ fuel := by
        omega
      have subtree :=
        toProperRootedTreeAt tree htree occurrence hoccurrenceMem fuel hchildFuel
      have hlabel : occurrence.2 = child.1 :=
        childOccurrence_label tree node child
      exact hlabel ▸ subtree

/-- The canonical certificate attached to a proper occurrence witness.  Its
depth budget is one more than the largest occurrence depth. -/
noncomputable def toProperRootedTree
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : IsProper tree) :
    ProperRootedTree
      (ProperChildren (Source := Source) (State := State) (Row := Row))
      (maxDepth tree + 1) (rootLabel tree) := by
  have hfuel : maxDepth tree - tree.depth tree.root ≤ maxDepth tree :=
    Nat.sub_le _ _
  have result := toProperRootedTreeAt tree htree tree.root htree.root_mem
    (maxDepth tree) hfuel
  simpa [rootLabel, htree.root_depth] using result

/-- Follow the parent pointer a fixed number of times. -/
def iteratedParent
    (tree : Witness (Source := Source) (State := State) (Row := Row)) :
    Nat → Occurrence Source State Row → Option (Occurrence Source State Row)
  | 0, node => some node
  | steps + 1, node =>
      (iteratedParent tree steps node).bind tree.parent

theorem iteratedParent_add
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (first second : Nat) (node : Occurrence Source State Row) :
    iteratedParent tree (first + second) node =
      (iteratedParent tree first node).bind (iteratedParent tree second) := by
  induction second with
  | zero => simp [iteratedParent]
  | succ second ih =>
      simp [Nat.add_succ, iteratedParent, ih, Option.bind_assoc]

/-- An iterated parent remains a node, and its depth drops by exactly the
number of parent steps. -/
theorem iteratedParent_spec
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) {node ancestor : Occurrence Source State Row}
    (hnode : node ∈ tree.nodes) {steps : Nat}
    (hancestor : iteratedParent tree steps node = some ancestor) :
    ancestor ∈ tree.nodes ∧
      tree.depth node = tree.depth ancestor + steps := by
  induction steps generalizing ancestor with
  | zero =>
      simp [iteratedParent] at hancestor
      subst ancestor
      exact ⟨hnode, by simp⟩
  | succ steps ih =>
      cases hmiddle : iteratedParent tree steps node with
      | none => simp [iteratedParent, hmiddle] at hancestor
      | some middle =>
          have hparent : tree.parent middle = some ancestor := by
            simpa [iteratedParent, hmiddle] using hancestor
          have hmiddleSpec := ih hmiddle
          have hancestorMem := htree.parent_mem middle hmiddleSpec.1 ancestor hparent
          have hdepth := htree.parent_depth middle hmiddleSpec.1 ancestor hparent
          exact ⟨hancestorMem, by omega⟩

/-- Every node reaches the root after exactly its recorded depth. -/
theorem iteratedParent_depth_eq_root
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) {node : Occurrence Source State Row}
    (hnode : node ∈ tree.nodes) :
    iteratedParent tree (tree.depth node) node = some tree.root := by
  generalize hdepthValue : tree.depth node = depthValue
  induction depthValue generalizing node with
  | zero =>
      have hnodeRoot : node = tree.root := by
        by_contra hne
        obtain ⟨parent, hparentMem, hparent⟩ :=
          htree.nonroot_parent node hnode hne
        have hdepth := htree.parent_depth node hnode parent hparent
        omega
      subst node
      simp [iteratedParent, htree.root_depth]
  | succ depthValue ih =>
      have hnodeRoot : node ≠ tree.root := by
        intro heq
        subst node
        rw [htree.root_depth] at hdepthValue
        omega
      obtain ⟨parent, hparentMem, hparent⟩ :=
        htree.nonroot_parent node hnode hnodeRoot
      have hdepth := htree.parent_depth node hnode parent hparent
      have hparentDepth : tree.depth parent = depthValue := by omega
      calc
        iteratedParent tree (depthValue + 1) node =
            iteratedParent tree (1 + depthValue) node := by
              rw [Nat.add_comm]
        _ = (iteratedParent tree 1 node).bind
              (iteratedParent tree depthValue) :=
            iteratedParent_add tree 1 depthValue node
        _ = iteratedParent tree depthValue parent := by
            simp [iteratedParent, hparent]
        _ = some tree.root := ih hparentMem hparentDepth

/-- Nodes below `ancestor`, including `ancestor` itself. -/
noncomputable def descendantNodes
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (ancestor : Occurrence Source State Row) :
    Finset (Occurrence Source State Row) := by
  classical
  exact tree.nodes.filter fun node ↦
    ∃ steps, iteratedParent tree steps node = some ancestor

/-- The subtree rooted at the witness root contains every occurrence. -/
theorem descendantNodes_root
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) :
    descendantNodes tree tree.root = tree.nodes := by
  classical
  apply Finset.ext
  intro node
  simp only [descendantNodes, Finset.mem_filter]
  constructor
  · intro hnode
    exact hnode.1
  · intro hnode
    exact ⟨hnode, ⟨tree.depth node, iteratedParent_depth_eq_root htree hnode⟩⟩

/-- A node belongs to the descendant set rooted at itself. -/
theorem mem_descendantNodes_self
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {node : Occurrence Source State Row} (hnode : node ∈ tree.nodes) :
    node ∈ descendantNodes tree node := by
  classical
  exact Finset.mem_filter.mpr ⟨hnode, ⟨0, rfl⟩⟩

/-- Descending to a child and then to its parent preserves membership in the
larger descendant set. -/
theorem mem_descendantNodes_of_child
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {parent child node : Occurrence Source State Row}
    (hchild : tree.parent child = some parent)
    (hnode : node ∈ descendantNodes tree child) :
    node ∈ descendantNodes tree parent := by
  classical
  have hdata := Finset.mem_filter.mp hnode
  obtain ⟨steps, hsteps⟩ := hdata.2
  refine Finset.mem_filter.mpr ⟨hdata.1, ⟨steps + 1, ?_⟩⟩
  simp [iteratedParent, hsteps, hchild]

/-- Every proper descendant other than the root lies below one immediate
child. -/
theorem exists_child_of_mem_descendantNodes_of_ne
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) {parent node : Occurrence Source State Row}
    (hnode : node ∈ descendantNodes tree parent) (hne : node ≠ parent) :
    ∃ child ∈ childOccurrences tree parent,
      node ∈ descendantNodes tree child := by
  classical
  have hdata := Finset.mem_filter.mp hnode
  obtain ⟨steps, hsteps⟩ := hdata.2
  cases steps with
  | zero =>
      simp [iteratedParent] at hsteps
      exact (hne hsteps).elim
  | succ steps =>
      cases hmiddle : iteratedParent tree steps node with
      | none => simp [iteratedParent, hmiddle] at hsteps
      | some child =>
          have hparent : tree.parent child = some parent := by
            simpa [iteratedParent, hmiddle] using hsteps
          have hchildMem : child ∈ tree.nodes :=
            (iteratedParent_spec htree hdata.1 hmiddle).1
          refine ⟨child, Finset.mem_filter.mpr ⟨hchildMem, hparent⟩, ?_⟩
          exact Finset.mem_filter.mpr ⟨hdata.1, ⟨steps, hmiddle⟩⟩

/-- Descendants split into the root and the descendant sets of its immediate
children. -/
theorem descendantNodes_eq_insert_biUnion
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) {parent : Occurrence Source State Row}
    (hparent : parent ∈ tree.nodes) :
    descendantNodes tree parent =
      insert parent
        ((childOccurrences tree parent).biUnion (descendantNodes tree)) := by
  classical
  apply Finset.ext
  intro node
  constructor
  · intro hnode
    by_cases heq : node = parent
    · simp [heq]
    · obtain ⟨child, hchild, hbelow⟩ :=
        exists_child_of_mem_descendantNodes_of_ne htree hnode heq
      simp only [Finset.mem_insert, Finset.mem_biUnion]
      exact Or.inr ⟨child, hchild, hbelow⟩
  · intro hnode
    simp only [Finset.mem_insert, Finset.mem_biUnion] at hnode
    rcases hnode with rfl | ⟨child, hchild, hbelow⟩
    · exact mem_descendantNodes_self hparent
    · exact mem_descendantNodes_of_child
        (Finset.mem_filter.mp hchild).2 hbelow

/-- Two distinct immediate children have disjoint descendant sets. -/
theorem descendantNodes_disjoint_of_children_ne
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) {parent left right : Occurrence Source State Row}
    (hleft : left ∈ childOccurrences tree parent)
    (hright : right ∈ childOccurrences tree parent) (hne : left ≠ right) :
    Disjoint (descendantNodes tree left) (descendantNodes tree right) := by
  classical
  rw [Finset.disjoint_left]
  intro node hnodeLeft hnodeRight
  have hleftData := Finset.mem_filter.mp hleft
  have hrightData := Finset.mem_filter.mp hright
  have hleftDepth := htree.parent_depth left hleftData.1 parent hleftData.2
  have hrightDepth := htree.parent_depth right hrightData.1 parent hrightData.2
  have hnodeLeftData := Finset.mem_filter.mp hnodeLeft
  have hnodeRightData := Finset.mem_filter.mp hnodeRight
  obtain ⟨leftSteps, hleftSteps⟩ := hnodeLeftData.2
  obtain ⟨rightSteps, hrightSteps⟩ := hnodeRightData.2
  have hleftSpec := iteratedParent_spec htree hnodeLeftData.1 hleftSteps
  have hrightSpec := iteratedParent_spec htree hnodeRightData.1 hrightSteps
  have hsteps : leftSteps = rightSteps := by omega
  apply hne
  apply Option.some.inj
  calc
    some left = iteratedParent tree leftSteps node := hleftSteps.symm
    _ = iteratedParent tree rightSteps node := by rw [hsteps]
    _ = some right := hrightSteps

/-- The immediate-child descendant sets form a pairwise disjoint family. -/
theorem descendantNodes_pairwiseDisjoint
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) (parent : Occurrence Source State Row) :
    Set.PairwiseDisjoint (↑(childOccurrences tree parent))
      (descendantNodes tree) := by
  intro left hleft right hright hne
  exact descendantNodes_disjoint_of_children_ne htree hleft hright hne

/-- A parent is not below any one of its children. -/
theorem parent_not_mem_childDescendants
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) {parent : Occurrence Source State Row}
    (hparent : parent ∈ tree.nodes) :
    parent ∉ (childOccurrences tree parent).biUnion (descendantNodes tree) := by
  classical
  intro hparentBelow
  rw [Finset.mem_biUnion] at hparentBelow
  obtain ⟨child, hchild, hbelow⟩ := hparentBelow
  have hchildData := Finset.mem_filter.mp hchild
  have hchildDepth :=
    htree.parent_depth child hchildData.1 parent hchildData.2
  have hbelowData := Finset.mem_filter.mp hbelow
  obtain ⟨steps, hsteps⟩ := hbelowData.2
  have hspec := iteratedParent_spec htree hparent hsteps
  omega

/-- Product factorization over the root and its pairwise disjoint child
subtrees. -/
theorem prod_descendantNodes
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) {parent : Occurrence Source State Row}
    (hparent : parent ∈ tree.nodes)
    (base : Label Source State Row → ℝ) :
    (∏ node ∈ descendantNodes tree parent, base node.2) =
      base parent.2 *
        ∏ child ∈ childOccurrences tree parent,
          ∏ node ∈ descendantNodes tree child, base node.2 := by
  classical
  rw [descendantNodes_eq_insert_biUnion htree hparent]
  rw [Finset.prod_insert (parent_not_mem_childDescendants htree hparent)]
  rw [Finset.prod_biUnion (descendantNodes_pairwiseDisjoint htree parent)]

/-- Reindex a child-label product by its unique child occurrences. -/
theorem prod_childLabels_eq_prod_childOccurrences
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) (parent : Occurrence Source State Row)
    (f : Occurrence Source State Row → ℝ) :
    (∏ child : ↥(childLabels tree parent),
      f (childOccurrence tree parent child)) =
      ∏ child : ↥(childOccurrences tree parent), f child.1 := by
  classical
  apply Fintype.prod_equiv (childLabelEquiv htree parent).symm
  intro child
  congr 1

/-- Transporting only the root-label index does not change a tree's product
weight. -/
@[simp] theorem treeWeight_transport_root
    {Label' : Type*} [Fintype Label'] [DecidableEq Label']
    {AllowedChildren : Label' → Finset Label' → Prop}
    (base : Label' → ℝ) {depth : Nat} {left right : Label'}
    (h : left = right)
    (tree : ProperRootedTree AllowedChildren depth left) :
    treeWeight base (h ▸ tree) = treeWeight base tree := by
  subst right
  rfl

/-- Product of node weights over the occurrence finset. -/
def witnessWeight (base : Label Source State Row → ℝ)
    (tree : Witness (Source := Source) (State := State) (Row := Row)) : ℝ :=
  ∏ node ∈ tree.nodes, base node.2

/-- The canonical conversion preserves the product of all node-label weights,
including repeated labels at different occurrences. -/
theorem treeWeight_toProperRootedTreeAt
    (base : Label Source State Row → ℝ)
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) (node : Occurrence Source State Row)
    (hnode : node ∈ tree.nodes) (fuel : Nat)
    (hfuel : maxDepth tree - tree.depth node ≤ fuel) :
    treeWeight base (toProperRootedTreeAt tree htree node hnode fuel hfuel) =
      ∏ occurrence ∈ descendantNodes tree node, base occurrence.2 := by
  induction fuel generalizing node with
  | zero =>
      have hmax : maxDepth tree ≤ tree.depth node := by omega
      have hempty := childLabels_eq_empty_of_maxDepth_le_depth htree hnode hmax
      have hchildOccurrences : childOccurrences tree node = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro child hchild
        have hlabelMem : child.2 ∈ childLabels tree node :=
          Finset.mem_image.mpr ⟨child, hchild, rfl⟩
        rw [hempty] at hlabelMem
        exact Finset.notMem_empty child.2 hlabelMem
      rw [descendantNodes_eq_insert_biUnion htree hnode]
      simp [toProperRootedTreeAt, treeWeight, nodeWeight, hchildOccurrences]
  | succ fuel ih =>
      rw [toProperRootedTreeAt, treeWeight, nodeWeight]
      rw [prod_descendantNodes htree hnode base]
      apply congrArg (base node.2 * ·)
      trans
        ∏ child : ↥(childOccurrences tree node),
          ∏ occurrence ∈ descendantNodes tree child.1, base occurrence.2
      · apply Fintype.prod_equiv (childLabelEquiv htree node).symm
        intro child
        let occurrence := childOccurrence tree node child
        have hoccurrenceMem : occurrence ∈ tree.nodes :=
          childOccurrence_mem_nodes tree node child
        have hoccurrenceParent : tree.parent occurrence = some node :=
          childOccurrence_parent tree node child
        have hdepth : tree.depth occurrence = tree.depth node + 1 :=
          htree.parent_depth occurrence hoccurrenceMem node hoccurrenceParent
        have hle : tree.depth occurrence ≤ maxDepth tree :=
          depth_le_maxDepth hoccurrenceMem
        have hchildFuel : maxDepth tree - tree.depth occurrence ≤ fuel := by
          omega
        simpa [childLabelEquiv, toProperRootedTreeAt, occurrence] using
          ih occurrence hoccurrenceMem hchildFuel
      · exact (childOccurrences tree node).prod_coe_sort
          (fun child ↦
            ∏ occurrence ∈ descendantNodes tree child, base occurrence.2)

theorem treeWeight_toProperRootedTree
    (base : Label Source State Row → ℝ)
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : IsProper tree) :
    treeWeight base (toProperRootedTree tree htree) = witnessWeight base tree := by
  unfold toProperRootedTree witnessWeight
  have hfuel : maxDepth tree - tree.depth tree.root ≤ maxDepth tree :=
    Nat.sub_le _ _
  have hweight := treeWeight_toProperRootedTreeAt base htree tree.root
    htree.root_mem (maxDepth tree) hfuel
  rw [descendantNodes_root htree] at hweight
  simpa [rootLabel, htree.root_depth] using hweight

/-- A flattening which retains occurrence times and their structural depths.
The canonical tree is obtained from this finite occurrence set by erasing the
times only after the parent hierarchy has been unfolded. -/
def occurrenceDepthFlattening
    (tree : Witness (Source := Source) (State := State) (Row := Row)) :
    Finset ((Occurrence Source State Row) × Nat) :=
  tree.nodes.image fun node ↦ (node, tree.depth node)

theorem mem_occurrenceDepthFlattening
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {node : Occurrence Source State Row} (hnode : node ∈ tree.nodes) :
    (node, tree.depth node) ∈ occurrenceDepthFlattening tree := by
  exact Finset.mem_image.mpr ⟨node, hnode, rfl⟩

end WeightedEdgeColoring.FinitePartialResamplingWitnessBridge
