import WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
import WeightedEdgeColoring.FinitePartialResamplingTreeWeights
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.OfFn

/-!
# Finite witness trees for backward partial resampling histories

This file contains only the finite combinatorial part of the witness-tree
construction.  An occurrence remembers both its time and its witness label.
Starting with the last occurrence of a nonempty history prefix, earlier
occurrences are read backwards.  An occurrence which conflicts with the
current tree is attached below a deepest conflicting node.  Ties are broken
by one fixed finite choice.

The resulting occurrence tree has the two properness properties needed by
the neighbor polynomial: a child conflicts with its parent, and two distinct
children of the same parent do not conflict.  The latter follows from the
choice of a deepest conflicting parent.  All statements here are finite and
deterministic after the fixed tie-breaking choice; there is no probabilistic
or existence conclusion.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingWitnessStructure

open WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
open WeightedEdgeColoring.FinitePartialResamplingTreeWeights

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- A node occurrence consists of its time and its label.  Times distinguish
two appearances of the same label in one history. -/
abbrev Occurrence (Source State Row : Type*) :=
  Nat × Label Source State Row

/-- A finite occurrence tree.  The structural conditions are kept in the
separate predicate `IsProper`; this makes backward insertion an ordinary
finite function. -/
structure Witness where
  root : Occurrence Source State Row
  nodes : Finset (Occurrence Source State Row)
  parent : Occurrence Source State Row → Option (Occurrence Source State Row)
  depth : Occurrence Source State Row → Nat

/-- The label at the root of a witness. -/
def rootLabel (tree : Witness (Source := Source) (State := State) (Row := Row)) :
    Label Source State Row :=
  tree.root.2

/-- Nodes whose labels conflict with `a`. -/
def conflictingNodes
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (a : Label Source State Row) :
    Finset (Occurrence Source State Row) :=
  tree.nodes.filter fun occurrence ↦ Conflict occurrence.2 a

/-- A finite nonempty set has an element on which a natural-valued function
is largest. -/
private theorem exists_maximizer
    {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) (value : α → Nat) :
    ∃ a ∈ s, ∀ b ∈ s, value b ≤ value a := by
  let values := s.image value
  have hvalues : values.Nonempty := hs.image value
  let largest := values.max' hvalues
  have hlargest : largest ∈ values := values.max'_mem hvalues
  obtain ⟨a, ha, havalue⟩ := Finset.mem_image.mp hlargest
  refine ⟨a, ha, ?_⟩
  intro b hb
  have hbvalue : value b ∈ values :=
    Finset.mem_image.mpr ⟨b, hb, rfl⟩
  calc
    value b ≤ largest := values.le_max' (value b) hbvalue
    _ = value a := havalue.symm

/-- A deepest conflicting node exists whenever there is a conflicting node. -/
theorem exists_deepestConflictingNode
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (a : Label Source State Row)
    (hne : (conflictingNodes tree a).Nonempty) :
    ∃ parent ∈ conflictingNodes tree a,
      ∀ other ∈ conflictingNodes tree a,
        tree.depth other ≤ tree.depth parent :=
  exists_maximizer (conflictingNodes tree a) hne tree.depth

/-- The fixed parent selected for a new label.  It is absent exactly when
there is no conflicting node. -/
noncomputable def deepestParent
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (a : Label Source State Row) : Option (Occurrence Source State Row) :=
  if hne : (conflictingNodes tree a).Nonempty then
    some (Classical.choose (exists_deepestConflictingNode tree a hne))
  else none

/-- The selected parent is a conflicting node and is at least as deep as
every other conflicting node. -/
theorem deepestParent_spec
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {a : Label Source State Row} {parent : Occurrence Source State Row}
    (hparent : deepestParent tree a = some parent) :
    parent ∈ tree.nodes ∧ Conflict parent.2 a ∧
      ∀ other ∈ tree.nodes, Conflict other.2 a →
        tree.depth other ≤ tree.depth parent := by
  classical
  unfold deepestParent at hparent
  split at hparent
  · rename_i hne
    have hchosen :=
      Classical.choose_spec (exists_deepestConflictingNode tree a hne)
    have heq : Classical.choose
        (exists_deepestConflictingNode tree a hne) = parent :=
      Option.some.inj hparent
    rw [heq] at hchosen
    have hmem := Finset.mem_filter.mp hchosen.1
    refine ⟨hmem.1, hmem.2, ?_⟩
    intro other hother hconflict
    exact hchosen.2 other (Finset.mem_filter.mpr ⟨hother, hconflict⟩)
  · simp at hparent

/-- A conflicting node forces the selected parent to be present. -/
theorem deepestParent_exists_of_conflict
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {a : Label Source State Row} {node : Occurrence Source State Row}
    (hnode : node ∈ tree.nodes) (hconflict : Conflict node.2 a) :
    ∃ parent, deepestParent tree a = some parent := by
  classical
  have hne : (conflictingNodes tree a).Nonempty :=
    ⟨node, Finset.mem_filter.mpr ⟨hnode, hconflict⟩⟩
  refine ⟨Classical.choose (exists_deepestConflictingNode tree a hne), ?_⟩
  simp [deepestParent, hne]

/-- The structural facts maintained by backward insertion. -/
structure IsProper
    (tree : Witness (Source := Source) (State := State) (Row := Row)) : Prop where
  root_mem : tree.root ∈ tree.nodes
  root_parent : tree.parent tree.root = none
  root_depth : tree.depth tree.root = 0
  nonroot_parent : ∀ node ∈ tree.nodes, node ≠ tree.root →
    ∃ parent ∈ tree.nodes, tree.parent node = some parent
  parent_mem : ∀ node ∈ tree.nodes, ∀ parent,
    tree.parent node = some parent → parent ∈ tree.nodes
  parent_depth : ∀ node ∈ tree.nodes, ∀ parent,
    tree.parent node = some parent →
      tree.depth node = tree.depth parent + 1
  parent_child_conflict : ∀ node ∈ tree.nodes, ∀ parent,
    tree.parent node = some parent → Conflict parent.2 node.2
  siblings_nonconflicting : ∀ left ∈ tree.nodes, ∀ right ∈ tree.nodes,
    ∀ parent, tree.parent left = some parent →
      tree.parent right = some parent → left ≠ right →
      ¬ Conflict left.2 right.2
  node_nonempty : ∀ node ∈ tree.nodes, NonemptyPartial node.2.2

/-- The one-node witness rooted at `root`. -/
def singletonWitness (root : Occurrence Source State Row) :
    Witness (Source := Source) (State := State) (Row := Row) where
  root := root
  nodes := {root}
  parent := fun _ ↦ none
  depth := fun _ ↦ 0

/-- A singleton witness is proper when its partial assignment is nonempty. -/
theorem singletonWitness_isProper
    {root : Occurrence Source State Row}
    (hroot : NonemptyPartial root.2.2) :
    IsProper (singletonWitness root) := by
  constructor
  · simp [singletonWitness]
  · simp [singletonWitness]
  · simp [singletonWitness]
  · intro node hnode hne
    simp [singletonWitness] at hnode
    exact (hne hnode).elim
  · intro node hnode parent hparent
    simp [singletonWitness] at hparent
  · intro node hnode parent hparent
    simp [singletonWitness] at hparent
  · intro node hnode parent hparent
    simp [singletonWitness] at hparent
  · intro left hleft right hright parent hleftParent hrightParent hne
    simp [singletonWitness] at hleftParent
  · intro node hnode
    have hnodeEq : node = root := by
      simpa [singletonWitness] using hnode
    simpa [hnodeEq] using hroot

/-- Attach the fresh occurrence `node` below `parent`. -/
def insertNode
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (node parent : Occurrence Source State Row) :
    Witness (Source := Source) (State := State) (Row := Row) where
  root := tree.root
  nodes := insert node tree.nodes
  parent := fun other ↦ if other = node then some parent else tree.parent other
  depth := fun other ↦
    if other = node then tree.depth parent + 1 else tree.depth other

/-- Read one earlier occurrence.  Repeated occurrences are ignored.  A fresh
occurrence is ignored when it has no conflict; otherwise it is attached to a
deepest conflicting node. -/
noncomputable def insertEarlier
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (node : Occurrence Source State Row) :
    Witness (Source := Source) (State := State) (Row := Row) :=
  if node ∈ tree.nodes then tree
  else
    match deepestParent tree node.2 with
    | none => tree
    | some parent => insertNode tree node parent

@[simp] theorem insertEarlier_root
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (node : Occurrence Source State Row) :
    (insertEarlier tree node).root = tree.root := by
  classical
  by_cases hnode : node ∈ tree.nodes
  · simp [insertEarlier, hnode]
  · cases hparent : deepestParent tree node.2 with
    | none => simp [insertEarlier, hnode, hparent]
    | some parent => simp [insertEarlier, hnode, hparent, insertNode]

/-- Backward insertion never removes a node. -/
theorem nodes_subset_insertEarlier
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (node : Occurrence Source State Row) :
    tree.nodes ⊆ (insertEarlier tree node).nodes := by
  classical
  intro old hold
  by_cases hnode : node ∈ tree.nodes
  · simpa [insertEarlier, hnode] using hold
  · cases hparent : deepestParent tree node.2 with
    | none => simpa [insertEarlier, hnode, hparent] using hold
    | some parent =>
        simp only [insertEarlier, hnode, if_false, hparent, insertNode]
        exact Finset.mem_insert_of_mem hold

/-- If `node` conflicts with a current node, it belongs to the result. -/
theorem mem_insertEarlier_of_conflict
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {node old : Occurrence Source State Row}
    (hold : old ∈ tree.nodes) (hconflict : Conflict old.2 node.2) :
    node ∈ (insertEarlier tree node).nodes := by
  classical
  by_cases hnode : node ∈ tree.nodes
  · exact nodes_subset_insertEarlier tree node hnode
  · obtain ⟨parent, hparent⟩ :=
      deepestParent_exists_of_conflict hold hconflict
    simp [insertEarlier, hnode, hparent, insertNode]

/-- Attaching a fresh node below the selected deepest parent preserves every
properness condition. -/
theorem insertNode_isProper
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {node parent : Occurrence Source State Row}
    (htree : IsProper tree) (hfresh : node ∉ tree.nodes)
    (hparent : deepestParent tree node.2 = some parent)
    (hnonempty : NonemptyPartial node.2.2) :
    IsProper (insertNode tree node parent) := by
  classical
  have hparentSpec := deepestParent_spec hparent
  have hparentMem : parent ∈ tree.nodes := hparentSpec.1
  have hparentConflict : Conflict parent.2 node.2 := hparentSpec.2.1
  have hmax := hparentSpec.2.2
  have hroot_ne : tree.root ≠ node := by
    intro heq
    apply hfresh
    simpa [heq] using htree.root_mem
  have hparent_ne : parent ≠ node := by
    intro heq
    apply hfresh
    simpa [heq] using hparentMem
  constructor
  · exact Finset.mem_insert_of_mem htree.root_mem
  · simp [insertNode, hroot_ne, htree.root_parent]
  · simp [insertNode, hroot_ne, htree.root_depth]
  · intro current hcurrent hcurrentRoot
    by_cases hcurrentNode : current = node
    · subst current
      exact ⟨parent, Finset.mem_insert_of_mem hparentMem, by simp [insertNode]⟩
    · have hcurrentOld : current ∈ tree.nodes := by
        simpa [insertNode, hcurrentNode] using hcurrent
      have hcurrentRootOld : current ≠ tree.root := by
        simpa [insertNode] using hcurrentRoot
      obtain ⟨oldParent, holdParentMem, holdParent⟩ :=
        htree.nonroot_parent current hcurrentOld hcurrentRootOld
      exact ⟨oldParent, Finset.mem_insert_of_mem holdParentMem, by
        simpa [insertNode, hcurrentNode] using holdParent⟩
  · intro current hcurrent currentParent hcurrentParent
    by_cases hcurrentNode : current = node
    · subst current
      have heq : currentParent = parent := by
        have hsome : (some parent : Option (Occurrence Source State Row)) =
            some currentParent := by
          simpa [insertNode] using hcurrentParent
        exact (Option.some.inj hsome).symm
      subst currentParent
      exact Finset.mem_insert_of_mem hparentMem
    · have hcurrentOld : current ∈ tree.nodes := by
        simpa [insertNode, hcurrentNode] using hcurrent
      have hparentOld : tree.parent current = some currentParent := by
        simpa [insertNode, hcurrentNode] using hcurrentParent
      exact Finset.mem_insert_of_mem
        (htree.parent_mem current hcurrentOld currentParent hparentOld)
  · intro current hcurrent currentParent hcurrentParent
    by_cases hcurrentNode : current = node
    · subst current
      have heq : currentParent = parent := by
        have hsome : (some parent : Option (Occurrence Source State Row)) =
            some currentParent := by
          simpa [insertNode] using hcurrentParent
        exact (Option.some.inj hsome).symm
      subst currentParent
      simp [insertNode, hparent_ne]
    · have hcurrentOld : current ∈ tree.nodes := by
        simpa [insertNode, hcurrentNode] using hcurrent
      have hparentOld : tree.parent current = some currentParent := by
        simpa [insertNode, hcurrentNode] using hcurrentParent
      have hdepthOld :=
        htree.parent_depth current hcurrentOld currentParent hparentOld
      have hcurrentParentMem :=
        htree.parent_mem current hcurrentOld currentParent hparentOld
      have hcurrentParentNe : currentParent ≠ node := by
        intro heq
        apply hfresh
        simpa [heq] using hcurrentParentMem
      simpa [insertNode, hcurrentNode, hcurrentParentNe] using hdepthOld
  · intro current hcurrent currentParent hcurrentParent
    by_cases hcurrentNode : current = node
    · subst current
      have heq : currentParent = parent := by
        have hsome : (some parent : Option (Occurrence Source State Row)) =
            some currentParent := by
          simpa [insertNode] using hcurrentParent
        exact (Option.some.inj hsome).symm
      simpa [heq] using hparentConflict
    · have hcurrentOld : current ∈ tree.nodes := by
        simpa [insertNode, hcurrentNode] using hcurrent
      have hparentOld : tree.parent current = some currentParent := by
        simpa [insertNode, hcurrentNode] using hcurrentParent
      exact htree.parent_child_conflict current hcurrentOld currentParent hparentOld
  · intro left hleft right hright common hleftParent hrightParent hne
    by_cases hleftNode : left = node
    · subst left
      have hcommon : common = parent := by
        have hsome : (some parent : Option (Occurrence Source State Row)) =
            some common := by
          simpa [insertNode] using hleftParent
        exact (Option.some.inj hsome).symm
      subst common
      have hrightNode : right ≠ node := by
        intro heq
        exact hne heq.symm
      have hrightOld : right ∈ tree.nodes := by
        simpa [insertNode, hrightNode] using hright
      have hrightParentOld : tree.parent right = some parent := by
        simpa [insertNode, hrightNode] using hrightParent
      intro hbad
      have hcandidate : Conflict right.2 node.2 :=
        conflict_symm.mp hbad
      have hle : tree.depth right ≤ tree.depth parent :=
        hmax right hrightOld hcandidate
      have hdepth : tree.depth right = tree.depth parent + 1 :=
        htree.parent_depth right hrightOld parent hrightParentOld
      omega
    · by_cases hrightNode : right = node
      · subst right
        have hcommon : common = parent := by
          have hsome : (some parent : Option (Occurrence Source State Row)) =
              some common := by
            simpa [insertNode] using hrightParent
          exact (Option.some.inj hsome).symm
        subst common
        have hleftOld : left ∈ tree.nodes := by
          simpa [insertNode, hleftNode] using hleft
        have hleftParentOld : tree.parent left = some parent := by
          simpa [insertNode, hleftNode] using hleftParent
        intro hbad
        have hle : tree.depth left ≤ tree.depth parent :=
          hmax left hleftOld hbad
        have hdepth : tree.depth left = tree.depth parent + 1 :=
          htree.parent_depth left hleftOld parent hleftParentOld
        omega
      · have hleftOld : left ∈ tree.nodes := by
          simpa [insertNode, hleftNode] using hleft
        have hrightOld : right ∈ tree.nodes := by
          simpa [insertNode, hrightNode] using hright
        have hleftParentOld : tree.parent left = some common := by
          simpa [insertNode, hleftNode] using hleftParent
        have hrightParentOld : tree.parent right = some common := by
          simpa [insertNode, hrightNode] using hrightParent
        exact htree.siblings_nonconflicting left hleftOld right hrightOld
          common hleftParentOld hrightParentOld hne
  · intro current hcurrent
    by_cases hcurrentNode : current = node
    · simpa [hcurrentNode] using hnonempty
    · have hcurrentOld : current ∈ tree.nodes := by
        simpa [insertNode, hcurrentNode] using hcurrent
      exact htree.node_nonempty current hcurrentOld

/-- Reading one nonempty earlier occurrence preserves properness. -/
theorem insertEarlier_isProper
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {node : Occurrence Source State Row}
    (htree : IsProper tree) (hnonempty : NonemptyPartial node.2.2) :
    IsProper (insertEarlier tree node) := by
  classical
  by_cases hnode : node ∈ tree.nodes
  · simpa [insertEarlier, hnode] using htree
  · cases hparent : deepestParent tree node.2 with
    | none => simpa [insertEarlier, hnode, hparent] using htree
    | some parent =>
        simpa [insertEarlier, hnode, hparent] using
          insertNode_isProper htree hnode hparent hnonempty

/-- Process a list ordered from later occurrences to earlier occurrences. -/
noncomputable def scanBackward :
    Witness (Source := Source) (State := State) (Row := Row) →
      List (Occurrence Source State Row) →
      Witness (Source := Source) (State := State) (Row := Row)
  | tree, [] => tree
  | tree, node :: earlier =>
      scanBackward (insertEarlier tree node) earlier

@[simp] theorem scanBackward_nil
    (tree : Witness (Source := Source) (State := State) (Row := Row)) :
    scanBackward tree [] = tree := rfl

@[simp] theorem scanBackward_cons
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (node : Occurrence Source State Row)
    (earlier : List (Occurrence Source State Row)) :
    scanBackward tree (node :: earlier) =
      scanBackward (insertEarlier tree node) earlier := rfl

/-- A scan does not change its root. -/
@[simp] theorem scanBackward_root
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (history : List (Occurrence Source State Row)) :
    (scanBackward tree history).root = tree.root := by
  induction history generalizing tree with
  | nil => rfl
  | cons node earlier ih =>
      simpa using (ih (tree := insertEarlier tree node)).trans
        (insertEarlier_root tree node)

/-- A scan never removes a node. -/
theorem nodes_subset_scanBackward
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (history : List (Occurrence Source State Row)) :
    tree.nodes ⊆ (scanBackward tree history).nodes := by
  induction history generalizing tree with
  | nil => exact fun _ h ↦ h
  | cons node earlier ih =>
      exact Finset.Subset.trans (nodes_subset_insertEarlier tree node)
        (ih (tree := insertEarlier tree node))

/-- Scanning nonempty patches preserves all properness conditions. -/
theorem scanBackward_isProper
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {history : List (Occurrence Source State Row)}
    (htree : IsProper tree)
    (hnonempty : ∀ node ∈ history, NonemptyPartial node.2.2) :
    IsProper (scanBackward tree history) := by
  induction history generalizing tree with
  | nil => simpa using htree
  | cons node earlier ih =>
      rw [scanBackward_cons]
      apply ih
      · exact insertEarlier_isProper htree (hnonempty node (by simp))
      · intro old hold
        exact hnonempty old (by simp [hold])

/-- An occurrence in the scan list which conflicts with the root is selected
into the final witness. -/
theorem mem_scanBackward_of_mem_of_conflict_root
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {history : List (Occurrence Source State Row)}
    {node : Occurrence Source State Row}
    (hroot : tree.root ∈ tree.nodes) (hnode : node ∈ history)
    (hconflict : Conflict tree.root.2 node.2) :
    node ∈ (scanBackward tree history).nodes := by
  induction history generalizing tree with
  | nil => simp at hnode
  | cons current earlier ih =>
      rcases List.mem_cons.mp hnode with hcurrent | hearlier
      · subst current
        have hinserted : node ∈ (insertEarlier tree node).nodes :=
          mem_insertEarlier_of_conflict hroot hconflict
        exact nodes_subset_scanBackward (insertEarlier tree node) earlier hinserted
      · apply ih (tree := insertEarlier tree current)
        · rw [insertEarlier_root]
          exact nodes_subset_insertEarlier tree current hroot
        · exact hearlier
        · simpa only [insertEarlier_root] using hconflict

/-- The earlier occurrences for endpoint `time`, in the order in which the
backward algorithm reads them. -/
def earlierOccurrences {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n) :
    List (Occurrence Source State Row) :=
  (List.ofFn fun earlier : Fin time.1 ↦
    (earlier.1,
      history ⟨earlier.1, Nat.lt_trans earlier.2 time.2⟩)).reverse

/-- Every strictly earlier history occurrence occurs in `earlierOccurrences`. -/
theorem mem_earlierOccurrences {n : Nat}
    (history : Fin n → Label Source State Row) {earlier time : Fin n}
    (hlt : earlier.1 < time.1) :
    (earlier.1, history earlier) ∈ earlierOccurrences history time := by
  rw [earlierOccurrences, List.mem_reverse, List.mem_ofFn]
  refine ⟨⟨earlier.1, hlt⟩, ?_⟩
  congr

/-- The canonical witness of a nonempty history prefix ending at `time`. -/
noncomputable def witnessAt {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n) :
    Witness (Source := Source) (State := State) (Row := Row) :=
  scanBackward
    (singletonWitness (time.1, history time))
    (earlierOccurrences history time)

@[simp] theorem witnessAt_root {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n) :
    (witnessAt history time).root = (time.1, history time) := by
  simp [witnessAt, singletonWitness]

@[simp] theorem witnessAt_rootLabel {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n) :
    rootLabel (witnessAt history time) = history time := by
  simp [rootLabel]

/-- Every node in every prefix witness is nonempty, and all parent and
sibling conditions hold, provided every patch in the history is nonempty. -/
theorem witnessAt_isProper {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (time : Fin n) : IsProper (witnessAt history time) := by
  apply scanBackward_isProper
  · exact singletonWitness_isProper (hnonempty time)
  · intro node hnode
    rw [earlierOccurrences, List.mem_reverse, List.mem_ofFn] at hnode
    obtain ⟨earlier, rfl⟩ := hnode
    exact hnonempty _

/-- Concrete parent-child conflict statement for a history witness. -/
theorem witnessAt_parent_child_conflict {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (time : Fin n) {node parent : Occurrence Source State Row}
    (hnode : node ∈ (witnessAt history time).nodes)
    (hparent : (witnessAt history time).parent node = some parent) :
    Conflict parent.2 node.2 :=
  (witnessAt_isProper history hnonempty time).parent_child_conflict
    node hnode parent hparent

/-- Concrete sibling nonconflict statement for a history witness. -/
theorem witnessAt_siblings_nonconflicting {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (time : Fin n) {left right parent : Occurrence Source State Row}
    (hleft : left ∈ (witnessAt history time).nodes)
    (hright : right ∈ (witnessAt history time).nodes)
    (hleftParent : (witnessAt history time).parent left = some parent)
    (hrightParent : (witnessAt history time).parent right = some parent)
    (hne : left ≠ right) : ¬ Conflict left.2 right.2 :=
  (witnessAt_isProper history hnonempty time).siblings_nonconflicting
    left hleft right hright parent hleftParent hrightParent hne

/-- Concrete nonempty-patch statement for a history witness. -/
theorem witnessAt_node_nonempty {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (time : Fin n) {node : Occurrence Source State Row}
    (hnode : node ∈ (witnessAt history time).nodes) :
    NonemptyPartial node.2.2 :=
  (witnessAt_isProper history hnonempty time).node_nonempty node hnode

/-- If two endpoints have the same row, the earlier root occurrence is a
node of the later witness.  Equality of the full labels is more than enough,
but the coarse conflict relation only needs equality of rows. -/
theorem earlier_root_mem_later_witness {n : Nat}
    (history : Fin n → Label Source State Row) {earlier later : Fin n}
    (hlt : earlier.1 < later.1)
    (hrow : (history earlier).1 = (history later).1) :
    (earlier.1, history earlier) ∈ (witnessAt history later).nodes := by
  apply mem_scanBackward_of_mem_of_conflict_root
  · simp [singletonWitness]
  · exact mem_earlierOccurrences history hlt
  · exact Or.inl hrow.symm

/-- Witnesses belonging to distinct prefix endpoints are distinct. -/
theorem witnessAt_injective {n : Nat}
    (history : Fin n → Label Source State Row) :
    Function.Injective (witnessAt history) := by
  intro left right heq
  apply Fin.ext
  have hroot := congrArg (fun tree ↦ tree.root.1) heq
  simpa using hroot

/-- The standard two-case certificate for distinct endpoint witnesses.  If
the root labels differ, their labeled roots differ.  If the labels agree,
the earlier root occurrence is selected into the later witness. -/
theorem distinct_endpoint_certificate {n : Nat}
    (history : Fin n → Label Source State Row) {earlier later : Fin n}
    (hlt : earlier.1 < later.1) :
    witnessAt history earlier ≠ witnessAt history later ∧
      (history earlier ≠ history later ∨
        (earlier.1, history earlier) ∈ (witnessAt history later).nodes) := by
  constructor
  · intro heq
    have heqTime : earlier = later := witnessAt_injective history heq
    subst later
    exact (Nat.lt_irrefl _ hlt).elim
  · by_cases hlabel : history earlier = history later
    · right
      apply earlier_root_mem_later_witness history hlt
      simpa [hlabel]
    · exact Or.inl hlabel

/-- Occurrence children of one node. -/
def childOccurrences
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (parent : Occurrence Source State Row) :
    Finset (Occurrence Source State Row) :=
  tree.nodes.filter fun child ↦ tree.parent child = some parent

/-- The set of child labels of one occurrence node. -/
def childLabels
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (parent : Occurrence Source State Row) :
    Finset (Label Source State Row) :=
  (childOccurrences tree parent).image Prod.snd

/-- The child-label set at every proper occurrence node is a
`ProperChildren` set for the neighbor polynomial.  This is the local bridge
from occurrence witnesses to the canonical trees used by `TreeWeights`. -/
theorem childLabels_proper
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) {parent : Occurrence Source State Row}
    (hparent : parent ∈ tree.nodes) :
    ProperChildren parent.2 (childLabels tree parent) := by
  constructor
  · intro child hchild
    rw [childLabels, Finset.mem_image] at hchild
    obtain ⟨occurrence, hoccurrence, rfl⟩ := hchild
    have hoccurrenceData := Finset.mem_filter.mp hoccurrence
    exact ⟨htree.node_nonempty occurrence hoccurrenceData.1,
      htree.parent_child_conflict occurrence hoccurrenceData.1 parent
        hoccurrenceData.2⟩
  · intro left hleft right hright hne
    rw [childLabels, Finset.mem_image] at hleft hright
    obtain ⟨leftOccurrence, hleftOccurrence, hleftLabel⟩ := hleft
    obtain ⟨rightOccurrence, hrightOccurrence, hrightLabel⟩ := hright
    have hleftData := Finset.mem_filter.mp hleftOccurrence
    have hrightData := Finset.mem_filter.mp hrightOccurrence
    have hoccurrenceNe : leftOccurrence ≠ rightOccurrence := by
      intro heq
      apply hne
      calc
        left = leftOccurrence.2 := hleftLabel.symm
        _ = rightOccurrence.2 := by rw [heq]
        _ = right := hrightLabel
    have hnconflict := htree.siblings_nonconflicting
      leftOccurrence hleftData.1 rightOccurrence hrightData.1 parent
      hleftData.2 hrightData.2 hoccurrenceNe
    simpa [hleftLabel, hrightLabel] using hnconflict

end WeightedEdgeColoring.FinitePartialResamplingWitnessStructure
