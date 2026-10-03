import WeightedEdgeColoring.FinitePartialResamplingWitnessBridge
import WeightedEdgeColoring.FinitePartialResamplingWitnessCylinder
import Mathlib.Data.List.Sort

/-!
# Fixed-depth canonical certificates for history witnesses

Every endpoint witness of a history of length `n` has occurrence depth at
most `n`.  It can therefore be unfolded into a canonical proper rooted tree
with the common depth budget `n + 1`.  This file proves that unfolding
preserves the exact number of nodes and packages the root label with the
tree.  Certificates belonging to distinct history endpoints are distinct:
if their root labels agree, the earlier occurrence witness is a strict
node-set subset of the later one, so their canonical node counts differ.

The final definitions flatten any canonical tree into a list of
label/depth pairs and expose the row and source depth lists in decreasing
order.  Lists, rather than finsets, retain repeated labels and all node
multiplicities.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingWitnessCertificates

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
open WeightedEdgeColoring.FinitePartialResamplingTreeWeights
open WeightedEdgeColoring.FinitePartialResamplingWitnessStructure
open WeightedEdgeColoring.FinitePartialResamplingWitnessBridge
open WeightedEdgeColoring.FinitePartialResamplingWitnessCylinder

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- Every node of a witness has depth at most `bound`. -/
def DepthBound
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (bound : Nat) : Prop :=
  ∀ node ∈ tree.nodes, tree.depth node ≤ bound

theorem depthBound_mono
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {left right : Nat} (hbound : DepthBound tree left)
    (hle : left ≤ right) : DepthBound tree right := by
  intro node hnode
  exact (hbound node hnode).trans hle

theorem singletonWitness_depthBound
    (root : Occurrence Source State Row) :
    DepthBound (singletonWitness root) 0 := by
  intro node hnode
  simp [singletonWitness]

/-- One insertion raises a uniform depth bound by at most one. -/
theorem insertNode_depthBound
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {node parent : Occurrence Source State Row} {bound : Nat}
    (hbound : DepthBound tree bound) (hparent : parent ∈ tree.nodes) :
    DepthBound (insertNode tree node parent) (bound + 1) := by
  intro current hcurrent
  by_cases hcurrentNode : current = node
  · subst current
    simp only [insertNode, if_pos]
    exact Nat.succ_le_succ (hbound parent hparent)
  · have hcurrentOld : current ∈ tree.nodes := by
      simpa [insertNode, hcurrentNode] using hcurrent
    simp only [insertNode, hcurrentNode, if_false]
    exact (hbound current hcurrentOld).trans (Nat.le_succ bound)

/-- Reading one earlier occurrence raises a uniform depth bound by at most
one, whether the occurrence is inserted or ignored. -/
theorem insertEarlier_depthBound
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {node : Occurrence Source State Row} {bound : Nat}
    (hbound : DepthBound tree bound) :
    DepthBound (insertEarlier tree node) (bound + 1) := by
  classical
  by_cases hnode : node ∈ tree.nodes
  · simpa [insertEarlier, hnode] using
      depthBound_mono hbound (Nat.le_succ bound)
  · cases hparent : deepestParent tree node.2 with
    | none =>
        simpa [insertEarlier, hnode, hparent] using
          depthBound_mono hbound (Nat.le_succ bound)
    | some parent =>
        have hparentMem : parent ∈ tree.nodes :=
          (deepestParent_spec hparent).1
        simpa [insertEarlier, hnode, hparent] using
          insertNode_depthBound hbound hparentMem

/-- A backward scan raises a uniform depth bound by at most the length of
the scanned list. -/
theorem scanBackward_depthBound
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (history : List (Occurrence Source State Row)) {bound : Nat}
    (hbound : DepthBound tree bound) :
    DepthBound (scanBackward tree history) (bound + history.length) := by
  induction history generalizing tree bound with
  | nil => simpa using hbound
  | cons node earlier ih =>
      rw [scanBackward_cons]
      have hnext := insertEarlier_depthBound (node := node) hbound
      have hresult := ih (tree := insertEarlier tree node)
        (bound := bound + 1) hnext
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult

theorem maxDepth_le_of_depthBound
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {bound : Nat} (hbound : DepthBound tree bound) :
    maxDepth tree ≤ bound := by
  unfold maxDepth
  rw [Finset.sup_le_iff]
  exact hbound

/-- The endpoint witness has maximum depth at most its endpoint time. -/
theorem witnessAt_maxDepth_le_time {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n) :
    maxDepth (witnessAt history time) ≤ time.1 := by
  apply maxDepth_le_of_depthBound
  have hbound := scanBackward_depthBound
    (singletonWitness (time.1, history time))
    (earlierOccurrences history time)
    (singletonWitness_depthBound (time.1, history time))
  simpa [witnessAt, earlierOccurrences] using hbound

/-- Unfold a proper occurrence witness with any common fuel which dominates
its maximum occurrence depth. -/
noncomputable def toProperRootedTreeWithFuel
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : IsProper tree) (fuel : Nat) (hmax : maxDepth tree ≤ fuel) :
    ProperRootedTree
      (ProperChildren (Source := Source) (State := State) (Row := Row))
      (fuel + 1) (rootLabel tree) := by
  have hfuel : maxDepth tree - tree.depth tree.root ≤ fuel :=
    (Nat.sub_le _ _).trans hmax
  exact toProperRootedTreeAt tree htree tree.root htree.root_mem fuel hfuel

/-- Every endpoint of an `n`-step history is converted at the common depth
budget `n + 1`. -/
noncomputable def witnessAtProperRootedTree {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (time : Fin n) :
    ProperRootedTree
      (ProperChildren (Source := Source) (State := State) (Row := Row))
      (n + 1) (history time) := by
  let tree := witnessAt history time
  have hproper : IsProper tree := witnessAt_isProper history hnonempty time
  have hmax : maxDepth tree ≤ n :=
    (witnessAt_maxDepth_le_time history time).trans
      (Nat.le_of_lt time.2)
  have hroot : rootLabel tree = history time := by
    simp [tree]
  exact hroot ▸ toProperRootedTreeWithFuel tree hproper n hmax

/-- Exact node count of a canonical proper rooted tree. -/
def canonicalNodeCount
    {Label' : Type*} [Fintype Label'] [DecidableEq Label']
    {AllowedChildren : Label' → Finset Label' → Prop} :
    {depth : Nat} → {root : Label'} →
      ProperRootedTree AllowedChildren depth root → Nat
  | 0, _root, tree => nomatch tree
  | _depth + 1, _root, ⟨childset, branches⟩ =>
      1 + ∑ child, canonicalNodeCount (branches child)

/-- Changing only the dependent root index does not change node count. -/
@[simp] theorem canonicalNodeCount_transport_root
    {Label' : Type*} [Fintype Label'] [DecidableEq Label']
    {AllowedChildren : Label' → Finset Label' → Prop}
    {depth : Nat} {left right : Label'} (h : left = right)
    (tree : ProperRootedTree AllowedChildren depth left) :
    canonicalNodeCount (h ▸ tree) = canonicalNodeCount tree := by
  subst right
  rfl

/-- Cardinality factorization over the root and its pairwise disjoint child
subtrees. -/
theorem card_descendantNodes
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) {parent : Occurrence Source State Row}
    (hparent : parent ∈ tree.nodes) :
    (descendantNodes tree parent).card =
      1 + ∑ child ∈ childOccurrences tree parent,
        (descendantNodes tree child).card := by
  classical
  rw [descendantNodes_eq_insert_biUnion htree hparent]
  rw [Finset.card_insert_of_notMem
    (parent_not_mem_childDescendants htree hparent)]
  rw [Finset.card_biUnion (descendantNodes_pairwiseDisjoint htree parent)]
  omega

/-- The canonical conversion preserves the exact number of occurrence
nodes, including repeated labels at different times. -/
theorem canonicalNodeCount_toProperRootedTreeAt
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) (node : Occurrence Source State Row)
    (hnode : node ∈ tree.nodes) (fuel : Nat)
    (hfuel : maxDepth tree - tree.depth node ≤ fuel) :
    canonicalNodeCount
        (toProperRootedTreeAt tree htree node hnode fuel hfuel) =
      (descendantNodes tree node).card := by
  induction fuel generalizing node with
  | zero =>
      have hmax : maxDepth tree ≤ tree.depth node := by omega
      have hempty :=
        childLabels_eq_empty_of_maxDepth_le_depth htree hnode hmax
      have hchildOccurrences : childOccurrences tree node = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro child hchild
        have hlabelMem : child.2 ∈ childLabels tree node :=
          Finset.mem_image.mpr ⟨child, hchild, rfl⟩
        rw [hempty] at hlabelMem
        exact Finset.notMem_empty child.2 hlabelMem
      rw [card_descendantNodes htree hnode]
      simp [toProperRootedTreeAt, canonicalNodeCount, hchildOccurrences]
  | succ fuel ih =>
      rw [toProperRootedTreeAt, canonicalNodeCount]
      rw [card_descendantNodes htree hnode]
      apply congrArg (1 + ·)
      trans
        ∑ child : ↥(childOccurrences tree node),
          (descendantNodes tree child.1).card
      · apply Fintype.sum_equiv (childLabelEquiv htree node).symm
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
      · exact (childOccurrences tree node).sum_coe_sort
          (fun child ↦ (descendantNodes tree child).card)

theorem canonicalNodeCount_toProperRootedTreeWithFuel
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : IsProper tree) (fuel : Nat) (hmax : maxDepth tree ≤ fuel) :
    canonicalNodeCount
        (toProperRootedTreeWithFuel tree htree fuel hmax) =
      tree.nodes.card := by
  have hfuel : maxDepth tree - tree.depth tree.root ≤ fuel :=
    (Nat.sub_le _ _).trans hmax
  have hcount := canonicalNodeCount_toProperRootedTreeAt htree tree.root
    htree.root_mem fuel hfuel
  rw [descendantNodes_root htree] at hcount
  simpa [toProperRootedTreeWithFuel, rootLabel] using hcount

theorem canonicalNodeCount_witnessAtProperRootedTree {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (time : Fin n) :
    canonicalNodeCount
        (witnessAtProperRootedTree history hnonempty time) =
      (witnessAt history time).nodes.card := by
  let tree := witnessAt history time
  have hproper : IsProper tree := witnessAt_isProper history hnonempty time
  have hmax : maxDepth tree ≤ n :=
    (witnessAt_maxDepth_le_time history time).trans
      (Nat.le_of_lt time.2)
  have hcount := canonicalNodeCount_toProperRootedTreeWithFuel
    tree hproper n hmax
  unfold witnessAtProperRootedTree
  simp only [canonicalNodeCount_transport_root]
  exact hcount

/-- If two endpoint root labels agree, every node of the earlier canonical
occurrence witness also belongs to the later one. -/
theorem witnessAt_nodes_subset_of_lt_of_rootLabel_eq {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    {earlier later : Fin n} (hlt : earlier.1 < later.1)
    (hlabel : history earlier = history later) :
    (witnessAt history earlier).nodes ⊆
      (witnessAt history later).nodes := by
  intro node hnode
  let earlyTree := witnessAt history earlier
  have hproper : IsProper earlyTree :=
    witnessAt_isProper history hnonempty earlier
  generalize hdepthValue : earlyTree.depth node = depthValue
  induction depthValue generalizing node with
  | zero =>
      have hnodeRoot : node = earlyTree.root := by
        have hreach := iteratedParent_depth_eq_root hproper hnode
        simpa [iteratedParent, hdepthValue] using hreach
      subst node
      simpa [earlyTree, hlabel] using
        (earlier_root_mem_later_witness history hlt
          (congrArg Prod.fst hlabel))
  | succ depthValue ih =>
      have hnodeRoot : node ≠ earlyTree.root := by
        intro heq
        subst node
        rw [hproper.root_depth] at hdepthValue
        omega
      obtain ⟨parent, hparentMem, hparent⟩ :=
        hproper.nonroot_parent node hnode hnodeRoot
      have hparentDepth :=
        hproper.parent_depth node hnode parent hparent
      have hparentDepthValue : earlyTree.depth parent = depthValue := by
        omega
      have hparentLater := ih hparentMem hparentDepthValue
      obtain ⟨nodeTime, _hnodeLe, hnodeEq⟩ :=
        witnessAt_node_provenance history earlier hnode
      obtain ⟨parentTime, _hparentLe, hparentEq⟩ :=
        witnessAt_node_provenance history earlier hparentMem
      have hconflict : Conflict parent.2 node.2 :=
        hproper.parent_child_conflict node hnode parent hparent
      have htime : nodeTime.1 < parentTime.1 := by
        have hdepthLt : earlyTree.depth parent < earlyTree.depth node := by
          omega
        have hiff := witnessAt_depth_lt_iff_time_gt history earlier
          hparentMem hnode hconflict
        have hoccurrenceTime : node.1 < parent.1 := hiff.mp hdepthLt
        simpa [hnodeEq, hparentEq] using hoccurrenceTime
      subst node
      subst parent
      apply witnessAt_mem_of_earlier_conflict history later htime hparentLater
      exact conflict_symm.mp hconflict

/-- Equal root labels make the earlier endpoint witness a strict subset of
the later endpoint witness. -/
theorem witnessAt_card_lt_of_lt_of_rootLabel_eq {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    {earlier later : Fin n} (hlt : earlier.1 < later.1)
    (hlabel : history earlier = history later) :
    (witnessAt history earlier).nodes.card <
      (witnessAt history later).nodes.card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨witnessAt_nodes_subset_of_lt_of_rootLabel_eq
    history hnonempty hlt hlabel, ?_⟩
  intro heq
  have hlaterRoot : (later.1, history later) ∈
      (witnessAt history later).nodes :=
    by simpa using (witnessAt_isProper history hnonempty later).root_mem
  have hlaterInEarlier : (later.1, history later) ∈
      (witnessAt history earlier).nodes := by
    rw [heq]
    exact hlaterRoot
  obtain ⟨time, htimeLe, htimeEq⟩ :=
    witnessAt_node_provenance history earlier hlaterInEarlier
  have htime : time.1 = later.1 := by
    exact (congrArg Prod.fst htimeEq).symm
  omega

/-- A fixed-depth certificate packages the root label with its dependent
canonical tree. -/
abbrev CanonicalCertificate
    (Source State Row : Type*) [Fintype Source] [DecidableEq Source]
    [Fintype State] [DecidableEq State]
    [Fintype Row] [DecidableEq Row] (depth : Nat) :=
  Σ root : Label Source State Row,
    ProperRootedTree
      (ProperChildren (Source := Source) (State := State) (Row := Row))
      depth root

/-- The common-depth canonical certificate of one history endpoint. -/
noncomputable def endpointCertificate {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (time : Fin n) : CanonicalCertificate Source State Row (n + 1) :=
  ⟨history time, witnessAtProperRootedTree history hnonempty time⟩

/-- Node count as a function on the dependent certificate package. -/
def certificateNodeCount {depth : Nat} :
    CanonicalCertificate Source State Row depth → Nat
  | ⟨_root, tree⟩ => canonicalNodeCount tree

theorem certificateNodeCount_endpointCertificate {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (time : Fin n) :
    certificateNodeCount (endpointCertificate history hnonempty time) =
      (witnessAt history time).nodes.card := by
  exact canonicalNodeCount_witnessAtProperRootedTree history hnonempty time

/-- Distinct endpoints of one nonempty history have distinct fixed-depth
canonical certificates. -/
theorem endpointCertificate_injective {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2) :
    Function.Injective (endpointCertificate history hnonempty) := by
  intro left right heq
  apply Fin.ext
  by_contra htime
  rcases lt_or_gt_of_ne htime with hleftRight | hrightLeft
  · have hlabel : history left = history right := by
      exact congrArg Sigma.fst heq
    have hcard := witnessAt_card_lt_of_lt_of_rootLabel_eq
      history hnonempty hleftRight hlabel
    have hcount := congrArg certificateNodeCount heq
    rw [certificateNodeCount_endpointCertificate,
      certificateNodeCount_endpointCertificate] at hcount
    omega
  · have hlabel : history right = history left := by
      exact congrArg Sigma.fst heq.symm
    have hcard := witnessAt_card_lt_of_lt_of_rootLabel_eq
      history hnonempty hrightLeft hlabel
    have hcount := congrArg certificateNodeCount heq
    rw [certificateNodeCount_endpointCertificate,
      certificateNodeCount_endpointCertificate] at hcount
    omega

/-- Flatten a canonical tree from structural level `level`.  The list keeps
one entry for every node, including repeated labels. -/
noncomputable def canonicalDepthFlatteningAux
    {Label' : Type*} [Fintype Label'] [DecidableEq Label']
    {AllowedChildren : Label' → Finset Label' → Prop}
    (level : Nat) : {depth : Nat} → {root : Label'} →
      ProperRootedTree AllowedChildren depth root → List (Label' × Nat)
  | 0, _root, tree => nomatch tree
  | _depth + 1, root, ⟨childset, branches⟩ =>
      (root, level) ::
        (Finset.univ.toList.flatMap fun child ↦
          canonicalDepthFlatteningAux (level + 1) (branches child))

/-- Structural label/depth flattening, with the root at depth zero. -/
noncomputable def canonicalDepthFlattening
    {Label' : Type*} [Fintype Label'] [DecidableEq Label']
    {AllowedChildren : Label' → Finset Label' → Prop}
    {depth : Nat} {root : Label'}
    (tree : ProperRootedTree AllowedChildren depth root) :
    List (Label' × Nat) :=
  canonicalDepthFlatteningAux 0 tree

/-- Structural depths of all nodes in one row, sorted from deeper to
shallower nodes. -/
noncomputable def canonicalRowDepthList {depth : Nat}
    {root : Label Source State Row}
    (tree : ProperRootedTree
      (ProperChildren (Source := Source) (State := State) (Row := Row))
      depth root)
    (r : Row) : List Nat :=
  ((canonicalDepthFlattening tree).filterMap fun item ↦
      if item.1.1 = r then some item.2 else none).mergeSort (fun a b ↦ b ≤ a)

/-- Structural depths of all nodes using one source, sorted from deeper to
shallower nodes. -/
noncomputable def canonicalSourceDepthList {depth : Nat}
    {root : Label Source State Row}
    (tree : ProperRootedTree
      (ProperChildren (Source := Source) (State := State) (Row := Row))
      depth root)
    (i : Source) : List Nat :=
  ((canonicalDepthFlattening tree).filterMap fun item ↦
      if UsesSource item.1.2 i then some item.2 else none).mergeSort
        (fun a b ↦ b ≤ a)

theorem canonicalRowDepthList_pairwise {depth : Nat}
    {root : Label Source State Row}
    (tree : ProperRootedTree
      (ProperChildren (Source := Source) (State := State) (Row := Row))
      depth root)
    (r : Row) :
    (canonicalRowDepthList tree r).Pairwise (fun a b ↦ b ≤ a) := by
  unfold canonicalRowDepthList
  exact List.pairwise_mergeSort' (fun a b : Nat ↦ b ≤ a) _

theorem canonicalSourceDepthList_pairwise {depth : Nat}
    {root : Label Source State Row}
    (tree : ProperRootedTree
      (ProperChildren (Source := Source) (State := State) (Row := Row))
      depth root)
    (i : Source) :
    (canonicalSourceDepthList tree i).Pairwise (fun a b ↦ b ≤ a) := by
  unfold canonicalSourceDepthList
  exact List.pairwise_mergeSort' (fun a b : Nat ↦ b ≤ a) _

end WeightedEdgeColoring.FinitePartialResamplingWitnessCertificates
