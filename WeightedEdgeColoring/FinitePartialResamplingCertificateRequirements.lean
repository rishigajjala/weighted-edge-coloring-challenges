import WeightedEdgeColoring.FinitePartialResamplingWitnessProducts
import WeightedEdgeColoring.FinitePartialResamplingWitnessCertificates
import WeightedEdgeColoring.FinitePartialResamplingTablePrefixes
import WeightedEdgeColoring.FinitePartialResamplingCertificateBudget
import Mathlib.Data.Prod.Lex

/-!
# Deterministic requirements carried by canonical certificates

A fixed canonical certificate must determine the row prefixes and table
prefixes used in its probability bound.  We first retain the structural
depth of every flattened node.  Entries are sorted by decreasing depth; an
arbitrary fixed finite order breaks ties.  For endpoint certificates the
tie breaker is immaterial, because two nodes in one row, or two nodes using
one source, have different depths.

The central structural statement says that canonical unfolding preserves
the list of label/depth pairs up to permutation, including multiplicity.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingCertificateRequirements

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential
open WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
open WeightedEdgeColoring.FinitePartialResamplingProcess
open WeightedEdgeColoring.FinitePartialResamplingTracePrefixes
open WeightedEdgeColoring.FinitePartialResamplingTreeWeights
open WeightedEdgeColoring.FinitePartialResamplingWitnessStructure
open WeightedEdgeColoring.FinitePartialResamplingWitnessBridge
open WeightedEdgeColoring.FinitePartialResamplingWitnessCylinder
open WeightedEdgeColoring.FinitePartialResamplingWitnessProducts
open WeightedEdgeColoring.FinitePartialResamplingWitnessCertificates
open WeightedEdgeColoring.FinitePartialResamplingTablePrefixes
open WeightedEdgeColoring.FinitePartialResamplingCertificateBudget
open List

noncomputable section

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

section DeterministicSorting

/-- A fixed, noncomputable linear order on a finite type. -/
noncomputable def finiteLinearOrder (Value : Type*)
    [Fintype Value] [DecidableEq Value] : LinearOrder Value :=
  LinearOrder.lift' (Fintype.equivFin Value)
    (Fintype.equivFin Value).injective

/-- Lexicographic order with decreasing depth as the primary key. -/
noncomputable def valueDepthLinearOrder (Value : Type*)
    [Fintype Value] [DecidableEq Value] : LinearOrder (Value × Nat) := by
  letI : LinearOrder Value := finiteLinearOrder Value
  apply LinearOrder.lift'
    (fun item : Value × Nat ↦
      toLex (OrderDual.toDual item.2, item.1))
  rintro ⟨leftValue, leftDepth⟩ ⟨rightValue, rightDepth⟩ heq
  change (OrderDual.toDual leftDepth, leftValue) =
    (OrderDual.toDual rightDepth, rightValue) at heq
  exact Prod.ext (congrArg Prod.snd heq)
    (OrderDual.toDual_inj.mp (congrArg Prod.fst heq))

/-- Sort value/depth entries by decreasing depth and then by the fixed
finite tie breaker. -/
noncomputable def sortValueDepth {Value : Type*}
    [Fintype Value] [DecidableEq Value]
    (items : List (Value × Nat)) : List (Value × Nat) :=
  letI : LinearOrder (Value × Nat) := valueDepthLinearOrder Value
  items.mergeSort (fun left right ↦ left ≤ right)

theorem sortValueDepth_perm {Value : Type*}
    [Fintype Value] [DecidableEq Value]
    (items : List (Value × Nat)) :
    sortValueDepth items ~ items := by
  letI : LinearOrder (Value × Nat) := valueDepthLinearOrder Value
  exact List.mergeSort_perm items (fun left right ↦ left ≤ right)

theorem sortValueDepth_eq_of_perm {Value : Type*}
    [Fintype Value] [DecidableEq Value]
    {left right : List (Value × Nat)} (hperm : left ~ right) :
    sortValueDepth left = sortValueDepth right := by
  letI : LinearOrder (Value × Nat) := valueDepthLinearOrder Value
  apply List.Perm.eq_of_pairwise'
      (List.pairwise_mergeSort' (fun a b : Value × Nat ↦ a ≤ b) left)
      (List.pairwise_mergeSort' (fun a b : Value × Nat ↦ a ≤ b) right)
  exact (sortValueDepth_perm left).trans
    (hperm.trans (sortValueDepth_perm right).symm)

theorem sortValueDepth_eq_self {Value : Type*}
    [Fintype Value] [DecidableEq Value]
    {items : List (Value × Nat)}
    (hsorted : items.Pairwise
      (@LE.le (Value × Nat) (valueDepthLinearOrder Value).toLE)) :
    sortValueDepth items = items := by
  letI : LinearOrder (Value × Nat) := valueDepthLinearOrder Value
  exact List.mergeSort_eq_self (r := fun a b : Value × Nat ↦ a ≤ b)
    hsorted

theorem valueDepth_le_of_depth_gt {Value : Type*}
    [Fintype Value] [DecidableEq Value]
    {left right : Value × Nat} (hdepth : right.2 < left.2) :
    @LE.le (Value × Nat) (valueDepthLinearOrder Value).toLE left right := by
  letI : LinearOrder Value := finiteLinearOrder Value
  change toLex (OrderDual.toDual left.2, left.1) ≤
    toLex (OrderDual.toDual right.2, right.1)
  exact Prod.Lex.toLex_le_toLex.mpr (Or.inl hdepth)

end DeterministicSorting

section CertificateDefinitions

/-- Patch/depth entries of one row in deterministic decreasing-depth order. -/
noncomputable def certificateRowDepthEntries {depth : Nat}
    (certificate : CanonicalCertificate Source State Row depth) (r : Row) :
    List (PartialAssignment Source State × Nat) :=
  sortValueDepth
    ((canonicalDepthFlattening certificate.2).filterMap fun item ↦
      if item.1.1 = r then some (item.1.2, item.2) else none)

/-- Row-prefix patches determined by a canonical certificate. -/
noncomputable def certificateRowRequirements {depth : Nat}
    (certificate : CanonicalCertificate Source State Row depth) :
    RowRequirements Source State Row :=
  fun r ↦ (certificateRowDepthEntries certificate r).map Prod.fst

/-- State/depth entries named at one source, in deterministic
decreasing-depth order. -/
noncomputable def certificateSourceStateDepthEntries {depth : Nat}
    (certificate : CanonicalCertificate Source State Row depth) (i : Source) :
    List (State × Nat) :=
  sortValueDepth
    ((canonicalDepthFlattening certificate.2).filterMap fun item ↦
      (item.1.2 i).map fun state ↦ (state, item.2))

/-- Source-state prefixes determined by a canonical certificate. -/
noncomputable def certificateSourceStateRequirements {depth : Nat}
    (certificate : CanonicalCertificate Source State Row depth) :
    Source → List State :=
  fun i ↦ (certificateSourceStateDepthEntries certificate i).map Prod.fst

end CertificateDefinitions

section FlatteningBridge

/-- Transporting only the dependent root index leaves the flattened
label/depth list unchanged. -/
@[simp] theorem canonicalDepthFlatteningAux_transport_root
    {Label' : Type*} [Fintype Label'] [DecidableEq Label']
    {AllowedChildren : Label' → Finset Label' → Prop}
    {depth level : Nat} {left right : Label'} (h : left = right)
    (tree : ProperRootedTree AllowedChildren depth left) :
    canonicalDepthFlatteningAux level (h ▸ tree) =
      canonicalDepthFlatteningAux level tree := by
  cases h
  rfl

private theorem univ_toList_map_equiv_perm
    {Left Right : Type*} [Fintype Left] [DecidableEq Left]
    [Fintype Right] [DecidableEq Right] (equiv : Left ≃ Right) :
    ((Finset.univ : Finset Left).toList.map equiv) ~
      (Finset.univ : Finset Right).toList := by
  apply (List.perm_ext_iff_of_nodup
    ((Finset.nodup_toList _).map equiv.injective)
    (Finset.nodup_toList _)).2
  intro item
  obtain ⟨preimage, rfl⟩ := equiv.surjective item
  simp

private theorem toList_biUnion_perm_flatMap
    {Index Value : Type*} [DecidableEq Value]
    (indices : Finset Index) (sets : Index → Finset Value)
    (hdisjoint : Set.PairwiseDisjoint (↑indices) sets) :
    (indices.biUnion sets).toList ~
      indices.toList.flatMap fun index ↦ (sets index).toList := by
  classical
  have hflatNodup :
      (indices.toList.flatMap fun index ↦ (sets index).toList).Nodup := by
    apply List.nodup_flatMap.mpr
    constructor
    · intro index _hindex
      exact Finset.nodup_toList _
    · apply (Finset.nodup_toList indices).pairwise_of_forall_ne
      intro left hleft right hright hne
      change List.Disjoint (sets left).toList (sets right).toList
      rw [List.disjoint_left]
      intro value hvalueLeft hvalueRight
      have hd := hdisjoint
        (Finset.mem_toList.mp hleft) (Finset.mem_toList.mp hright) hne
      exact Finset.disjoint_left.mp hd
        (Finset.mem_toList.mp hvalueLeft)
        (Finset.mem_toList.mp hvalueRight)
  apply (List.perm_ext_iff_of_nodup
    (Finset.nodup_toList _) hflatNodup).2
  intro value
  simp

private theorem descendantNodes_toList_perm
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) {parent : Occurrence Source State Row}
    (hparent : parent ∈ tree.nodes) :
    (descendantNodes tree parent).toList ~
      parent ::
        ((Finset.univ : Finset ↑(childOccurrences tree parent)).toList.flatMap
          fun child ↦ (descendantNodes tree child.1).toList) := by
  classical
  let childUnion : Finset (Occurrence Source State Row) :=
    (Finset.univ : Finset ↑(childOccurrences tree parent)).biUnion
      fun child ↦ descendantNodes tree child.1
  have hchildUnion : childUnion =
      (childOccurrences tree parent).biUnion (descendantNodes tree) := by
    ext node
    simp [childUnion]
  have hpairwise : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset ↑(childOccurrences tree parent)) :
        Set ↑(childOccurrences tree parent))
      (fun child : ↑(childOccurrences tree parent) ↦
        descendantNodes tree child.1) := by
    intro left _hleft right _hright hne
    apply descendantNodes_disjoint_of_children_ne htree left.2 right.2
    intro heq
    apply hne
    exact Subtype.ext heq
  have hunionPerm : childUnion.toList ~
      (Finset.univ : Finset ↑(childOccurrences tree parent)).toList.flatMap
        fun child ↦ (descendantNodes tree child.1).toList :=
    toList_biUnion_perm_flatMap _ _ hpairwise
  rw [descendantNodes_eq_insert_biUnion htree hparent, ← hchildUnion]
  exact (Finset.toList_insert
    (by simpa [childUnion, hchildUnion] using
      parent_not_mem_childDescendants htree hparent)).trans
    (hunionPerm.cons parent)

private theorem depth_le_of_mem_descendantNodes
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) {ancestor node : Occurrence Source State Row}
    (hnode : node ∈ descendantNodes tree ancestor) :
    tree.depth ancestor ≤ tree.depth node := by
  classical
  have hdata := Finset.mem_filter.mp hnode
  obtain ⟨steps, hsteps⟩ := hdata.2
  have hspec := iteratedParent_spec htree hdata.1 hsteps
  omega

private theorem descendantDepthList_child_eq
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree)
    {parent child : Occurrence Source State Row}
    (hchild : child ∈ tree.nodes)
    (hparent : tree.parent child = some parent) (level : Nat) :
    ((descendantNodes tree child).toList.map fun node ↦
        (node.2, (level + 1) + (tree.depth node - tree.depth child))) =
      (descendantNodes tree child).toList.map fun node ↦
        (node.2, level + (tree.depth node - tree.depth parent)) := by
  apply List.map_congr_left
  intro node hnode
  have hparentDepth := htree.parent_depth child hchild parent hparent
  have hnodeDepth := depth_le_of_mem_descendantNodes htree
    (by simpa using hnode)
  congr 1
  omega

theorem canonicalDepthFlatteningAux_toProperRootedTreeAt_perm
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : IsProper tree) (node : Occurrence Source State Row)
    (hnode : node ∈ tree.nodes) (level fuel : Nat)
    (hfuel : maxDepth tree - tree.depth node ≤ fuel) :
    canonicalDepthFlatteningAux level
        (toProperRootedTreeAt tree htree node hnode fuel hfuel) ~
      (descendantNodes tree node).toList.map fun occurrence ↦
        (occurrence.2,
          level + (tree.depth occurrence - tree.depth node)) := by
  induction fuel generalizing node level with
  | zero =>
      have hmax : maxDepth tree ≤ tree.depth node := by omega
      have hempty := childLabels_eq_empty_of_maxDepth_le_depth
        htree hnode hmax
      have hchildOccurrences : childOccurrences tree node = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro child hchild
        have hlabelMem : child.2 ∈ childLabels tree node :=
          Finset.mem_image.mpr ⟨child, hchild, rfl⟩
        rw [hempty] at hlabelMem
        exact Finset.notMem_empty child.2 hlabelMem
      rw [descendantNodes_eq_insert_biUnion htree hnode]
      simp [toProperRootedTreeAt, canonicalDepthFlatteningAux,
        hchildOccurrences]
  | succ fuel ih =>
      let labelChildren :=
        (Finset.univ : Finset ↑(childLabels tree node)).toList
      let occurrenceChildren :=
        (Finset.univ : Finset ↑(childOccurrences tree node)).toList
      have hbranches :
          (labelChildren.flatMap fun child ↦
              canonicalDepthFlatteningAux (level + 1)
                ((toProperRootedTreeAt tree htree node hnode (fuel + 1)
                  hfuel).2 child)) ~
            (labelChildren.flatMap fun child ↦
              (descendantNodes tree
                  ((childLabelEquiv htree node).symm child).1).toList.map
                (fun occurrence ↦
                  (occurrence.2,
                    (level + 1) +
                      (tree.depth occurrence -
                        tree.depth ((childLabelEquiv htree node).symm child).1)))) := by
        apply List.Perm.flatMap_left
        intro child hchild
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
        simpa [labelChildren, childLabelEquiv, toProperRootedTreeAt,
          occurrence] using
          ih occurrence hoccurrenceMem (level + 1) hchildFuel
      have hshift :
          (labelChildren.flatMap fun child ↦
              (descendantNodes tree
                  ((childLabelEquiv htree node).symm child).1).toList.map
                (fun occurrence ↦
                  (occurrence.2,
                    (level + 1) +
                      (tree.depth occurrence -
                        tree.depth ((childLabelEquiv htree node).symm child).1)))) =
            (labelChildren.flatMap fun child ↦
              (descendantNodes tree
                  ((childLabelEquiv htree node).symm child).1).toList.map
                (fun occurrence ↦
                  (occurrence.2,
                    level + (tree.depth occurrence - tree.depth node)))) := by
        apply List.flatMap_congr
        intro child hchild
        let occurrence := ((childLabelEquiv htree node).symm child).1
        have hoccurrenceMem : occurrence ∈ tree.nodes :=
          childOccurrence_mem_nodes tree node child
        have hoccurrenceParent : tree.parent occurrence = some node :=
          childOccurrence_parent tree node child
        exact descendantDepthList_child_eq htree hoccurrenceMem
          hoccurrenceParent level
      have hreindex :
          (labelChildren.flatMap fun child ↦
              (descendantNodes tree
                  ((childLabelEquiv htree node).symm child).1).toList.map
                (fun occurrence ↦
                  (occurrence.2,
                    level + (tree.depth occurrence - tree.depth node)))) ~
            (occurrenceChildren.flatMap fun child ↦
              (descendantNodes tree child.1).toList.map
                (fun occurrence ↦
                  (occurrence.2,
                    level + (tree.depth occurrence - tree.depth node)))) := by
        have hchildren := univ_toList_map_equiv_perm
          (childLabelEquiv htree node).symm
        simpa [labelChildren, occurrenceChildren, List.flatMap_map,
          Function.comp_def] using
          hchildren.flatMap_right
            (fun child : ↑(childOccurrences tree node) ↦
              (descendantNodes tree child.1).toList.map
                (fun occurrence ↦
                  (occurrence.2,
                    level + (tree.depth occurrence - tree.depth node))))
      have hdescendants :=
        (descendantNodes_toList_perm htree hnode).map
          (fun occurrence ↦
            (occurrence.2,
              level + (tree.depth occurrence - tree.depth node)))
      rw [toProperRootedTreeAt, canonicalDepthFlatteningAux]
      have hdecomposition :
          (node.2, level) ::
              (occurrenceChildren.flatMap fun child ↦
                (descendantNodes tree child.1).toList.map
                  (fun occurrence ↦
                    (occurrence.2,
                      level + (tree.depth occurrence - tree.depth node)))) ~
            (descendantNodes tree node).toList.map fun occurrence ↦
              (occurrence.2,
                level + (tree.depth occurrence - tree.depth node)) := by
        simpa [occurrenceChildren, List.map_flatMap] using
          hdescendants.symm
      exact (hbranches.cons (node.2, level)).trans
        ((hshift ▸ hreindex.cons (node.2, level)).trans hdecomposition)

theorem canonicalDepthFlattening_toProperRootedTreeWithFuel_perm
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : IsProper tree) (fuel : Nat) (hmax : maxDepth tree ≤ fuel) :
    canonicalDepthFlattening
        (toProperRootedTreeWithFuel tree htree fuel hmax) ~
      tree.nodes.toList.map fun occurrence ↦
        (occurrence.2, tree.depth occurrence) := by
  have hfuel : maxDepth tree - tree.depth tree.root ≤ fuel :=
    (Nat.sub_le _ _).trans hmax
  have hperm := canonicalDepthFlatteningAux_toProperRootedTreeAt_perm
    htree tree.root htree.root_mem 0 fuel hfuel
  rw [descendantNodes_root htree] at hperm
  simpa [canonicalDepthFlattening, toProperRootedTreeWithFuel,
    htree.root_depth] using hperm

end FlatteningBridge

section IntrinsicSourceRequirements

/-- Nodes of a witness whose patch names a fixed source. -/
def sourceNodes
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (i : Source) : Finset (Occurrence Source State Row) :=
  tree.nodes.filter fun node ↦ UsesSource node.2.2 i

@[simp] theorem mem_sourceNodes
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (i : Source) (node : Occurrence Source State Row) :
    node ∈ sourceNodes tree i ↔
      node ∈ tree.nodes ∧ UsesSource node.2.2 i := by
  simp [sourceNodes]

/-- A witness occurrence whose patch names source `i`. -/
abbrev SourceNode
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (i : Source) :=
  {node : Occurrence Source State Row // node ∈ sourceNodes tree i}

/-- Number of witness occurrences whose patch names source `i`. -/
def sourceNodeCount
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (i : Source) : Nat :=
  (sourceNodes tree i).card

private theorem exists_state_of_sourceNode
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {i : Source} (node : SourceNode tree i) :
    ∃ state, node.1.2.2 i = some state := by
  have huses := (mem_sourceNodes tree i node.1).mp node.2 |>.2
  cases hstate : node.1.2.2 i with
  | none => exact (huses hstate).elim
  | some state => exact ⟨state, rfl⟩

/-- The unique state named at source `i` by a source node. -/
noncomputable def sourceNodeState
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {i : Source} (node : SourceNode tree i) : State :=
  Classical.choose (exists_state_of_sourceNode node)

@[simp] theorem sourceNodeState_spec
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {i : Source} (node : SourceNode tree i) :
    node.1.2.2 i = some (sourceNodeState node) :=
  Classical.choose_spec (exists_state_of_sourceNode node)

/-- A source rank lies in the finite set of nodes naming that source. -/
theorem sourceRank_lt_sourceNodeCount
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {i : Source} (node : SourceNode tree i) :
    sourceRank tree node.1 i < sourceNodeCount tree i := by
  classical
  unfold sourceRank sourceNodeCount
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro other hother
    have data := Finset.mem_filter.mp hother
    exact (mem_sourceNodes tree i other).mpr ⟨data.1, data.2.1⟩
  · intro heq
    have hlarge : node.1 ∈ sourceNodes tree i := node.2
    have hsmall : node.1 ∈ tree.nodes.filter fun other ↦
        UsesSource other.2.2 i ∧ tree.depth node.1 < tree.depth other := by
      rw [heq]
      exact hlarge
    exact (Nat.lt_irrefl _ (Finset.mem_filter.mp hsmall).2.2)

/-- Intrinsic source rank as a finite index. -/
def sourceRankIndex
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (i : Source) (node : SourceNode tree i) :
    Fin (sourceNodeCount tree i) :=
  ⟨sourceRank tree node.1 i, sourceRank_lt_sourceNodeCount node⟩

theorem sourceRankIndex_injective
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : SourceDepthInjective tree) (i : Source) :
    Function.Injective (sourceRankIndex tree i) := by
  intro left right heq
  apply Subtype.ext
  have hleft := (mem_sourceNodes tree i left.1).mp left.2
  have hright := (mem_sourceNodes tree i right.1).mp right.2
  apply sourceRank_injective_on_source htree
    hleft.1 hright.1 hleft.2 hright.2
  exact congrArg Fin.val heq

/-- Source rank lists all nodes naming one source, without repetition or
omission. -/
noncomputable def sourceRankEquiv
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : SourceDepthInjective tree) (i : Source) :
    SourceNode tree i ≃ Fin (sourceNodeCount tree i) :=
  Equiv.ofBijective (sourceRankIndex tree i)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨sourceRankIndex_injective htree i, by simp [sourceNodeCount]⟩)

/-- For each source, list the states named by witness nodes in increasing
intrinsic source rank, hence in decreasing structural depth. -/
noncomputable def witnessSourceStateRequirements
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : SourceDepthInjective tree) :
    SourceRequirements Source State :=
  fun i ↦ List.ofFn fun rank : Fin (sourceNodeCount tree i) ↦
    sourceNodeState ((sourceRankEquiv tree htree i).symm rank)

/-- Row entries with their depths, in intrinsic row-rank order. -/
noncomputable def witnessRowDepthEntries
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : RowDepthInjective tree) (r : Row) :
    List (PartialAssignment Source State × Nat) :=
  List.ofFn fun rank : Fin (rowNodeCount tree r) ↦
    let node := (rowRankEquiv tree htree r).symm rank
    (node.1.2.2, tree.depth node.1)

/-- Source-state entries with their depths, in intrinsic source-rank order. -/
noncomputable def witnessSourceStateDepthEntries
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : SourceDepthInjective tree) (i : Source) :
    List (State × Nat) :=
  List.ofFn fun rank : Fin (sourceNodeCount tree i) ↦
    let node := (sourceRankEquiv tree htree i).symm rank
    (sourceNodeState node, tree.depth node.1)

theorem witnessRowDepthEntries_map_fst
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : RowDepthInjective tree) (r : Row) :
    (witnessRowDepthEntries tree htree r).map Prod.fst =
      witnessRowRequirements tree htree r := by
  simp [witnessRowDepthEntries, witnessRowRequirements,
    List.map_ofFn, Function.comp_def]

theorem witnessSourceStateDepthEntries_map_fst
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : SourceDepthInjective tree) (i : Source) :
    (witnessSourceStateDepthEntries tree htree i).map Prod.fst =
      witnessSourceStateRequirements tree htree i := by
  simp [witnessSourceStateDepthEntries, witnessSourceStateRequirements,
    List.map_ofFn, Function.comp_def]

private theorem rowDepth_gt_of_rank_lt
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : RowDepthInjective tree) {r : Row}
    (left right : RowNode tree r)
    (hrank : rowRank tree left.1 r < rowRank tree right.1 r) :
    tree.depth right.1 < tree.depth left.1 := by
  have hleft := (mem_rowNodes tree r left.1).mp left.2
  have hright := (mem_rowNodes tree r right.1).mp right.2
  rcases lt_trichotomy (tree.depth left.1) (tree.depth right.1) with
      hdepth | hdepth | hdepth
  · have hreverse := rowRank_lt_of_depth_lt
      hleft.1 hright.1 hright.2 hdepth
    omega
  · have hnodes := htree hleft.1 hright.1
      (hleft.2.trans hright.2.symm) hdepth
    have : left = right := Subtype.ext hnodes
    subst right
    omega
  · exact hdepth

private theorem sourceDepth_gt_of_rank_lt
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : SourceDepthInjective tree) {i : Source}
    (left right : SourceNode tree i)
    (hrank : sourceRank tree left.1 i < sourceRank tree right.1 i) :
    tree.depth right.1 < tree.depth left.1 := by
  have hleft := (mem_sourceNodes tree i left.1).mp left.2
  have hright := (mem_sourceNodes tree i right.1).mp right.2
  rcases lt_trichotomy (tree.depth left.1) (tree.depth right.1) with
      hdepth | hdepth | hdepth
  · have hreverse := sourceRank_lt_of_depth_lt
      hleft.1 hright.1 hright.2 hdepth
    omega
  · have hnodes := htree left.1 right.1 i
      hleft.1 hright.1 hleft.2 hright.2 hdepth
    have : left = right := Subtype.ext hnodes
    subst right
    omega
  · exact hdepth

theorem witnessRowDepthEntries_pairwise
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : RowDepthInjective tree) (r : Row) :
    (witnessRowDepthEntries tree htree r).Pairwise
      (@LE.le (PartialAssignment Source State × Nat)
        (valueDepthLinearOrder (PartialAssignment Source State)).toLE) := by
  apply List.pairwise_ofFn.mpr
  intro left right hlt
  apply valueDepth_le_of_depth_gt
  let leftNode := (rowRankEquiv tree htree r).symm left
  let rightNode := (rowRankEquiv tree htree r).symm right
  apply rowDepth_gt_of_rank_lt htree leftNode rightNode
  have hleft := congrArg Fin.val
    ((rowRankEquiv tree htree r).apply_symm_apply left)
  have hright := congrArg Fin.val
    ((rowRankEquiv tree htree r).apply_symm_apply right)
  change rowRank tree leftNode.1 r = left.1 at hleft
  change rowRank tree rightNode.1 r = right.1 at hright
  omega

theorem witnessSourceStateDepthEntries_pairwise
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : SourceDepthInjective tree) (i : Source) :
    (witnessSourceStateDepthEntries tree htree i).Pairwise
      (@LE.le (State × Nat) (valueDepthLinearOrder State).toLE) := by
  apply List.pairwise_ofFn.mpr
  intro left right hlt
  apply valueDepth_le_of_depth_gt
  let leftNode := (sourceRankEquiv tree htree i).symm left
  let rightNode := (sourceRankEquiv tree htree i).symm right
  apply sourceDepth_gt_of_rank_lt htree leftNode rightNode
  have hleft := congrArg Fin.val
    ((sourceRankEquiv tree htree i).apply_symm_apply left)
  have hright := congrArg Fin.val
    ((sourceRankEquiv tree htree i).apply_symm_apply right)
  change sourceRank tree leftNode.1 i = left.1 at hleft
  change sourceRank tree rightNode.1 i = right.1 at hright
  omega

private theorem ofFn_id_perm_univ_toList (n : Nat) :
    List.ofFn (fun rank : Fin n ↦ rank) ~
      (Finset.univ : Finset (Fin n)).toList := by
  apply (List.perm_ext_iff_of_nodup
    (List.nodup_ofFn.mpr fun _ _ h ↦ h)
    (Finset.nodup_toList _)).2
  intro rank
  simp

private theorem nodup_filterMap_on
    {Alpha Beta : Type*} {items : List Alpha} {f : Alpha → Option Beta}
    (hitems : items.Nodup)
    (hinjective : ∀ left ∈ items, ∀ right ∈ items, ∀ value,
      value ∈ f left → value ∈ f right → left = right) :
    (items.filterMap f).Nodup := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      have hdata := List.nodup_cons.mp hitems
      cases hvalue : f head with
      | none =>
          simp only [List.filterMap_cons, hvalue]
          apply ih hdata.2
          intro left hleft right hright value hvalueLeft hvalueRight
          exact hinjective left (by simp [hleft]) right (by simp [hright])
            value hvalueLeft hvalueRight
      | some value =>
          simp only [List.filterMap_cons, hvalue, List.nodup_cons]
          constructor
          · intro hvalueTail
            rw [List.mem_filterMap] at hvalueTail
            obtain ⟨other, hother, hotherValue⟩ := hvalueTail
            have heq := hinjective head (by simp) other (by simp [hother])
              value (by simp [hvalue]) (by simpa [hotherValue])
            exact hdata.1 (heq ▸ hother)
          · apply ih hdata.2
            intro left hleft right hright item hitemLeft hitemRight
            exact hinjective left (by simp [hleft]) right (by simp [hright])
              item hitemLeft hitemRight

private theorem univ_rowNode_entries_perm_occurrence
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : RowDepthInjective tree) (r : Row) :
    ((Finset.univ : Finset (RowNode tree r)).toList.map fun node ↦
        (node.1.2.2, tree.depth node.1)) ~
      tree.nodes.toList.filterMap (fun node ↦
        if node.2.1 = r then some (node.2.2, tree.depth node) else none) := by
  have hleft :
      ((Finset.univ : Finset (RowNode tree r)).toList.map fun node ↦
        (node.1.2.2, tree.depth node.1)).Nodup := by
    apply (Finset.nodup_toList _).map
    intro left right heq
    apply Subtype.ext
    have hleftData := (mem_rowNodes tree r left.1).mp left.2
    have hrightData := (mem_rowNodes tree r right.1).mp right.2
    apply htree hleftData.1 hrightData.1
      (hleftData.2.trans hrightData.2.symm)
    exact congrArg Prod.snd heq
  have hright :
      (tree.nodes.toList.filterMap (fun node ↦
        if node.2.1 = r then some (node.2.2, tree.depth node)
        else none)).Nodup := by
    apply nodup_filterMap_on (Finset.nodup_toList tree.nodes)
    intro left hleft right hright item hleftItem hrightItem
    by_cases hleftRow : left.2.1 = r
    · by_cases hrightRow : right.2.1 = r
      · have hleftEq : (left.2.2, tree.depth left) = item := by
          simpa [hleftRow] using hleftItem
        have hrightEq : (right.2.2, tree.depth right) = item := by
          simpa [hrightRow] using hrightItem
        apply htree
          (Finset.mem_toList.mp hleft)
          (Finset.mem_toList.mp hright)
          (hleftRow.trans hrightRow.symm)
        exact congrArg Prod.snd (hleftEq.trans hrightEq.symm)
      · simp [hrightRow] at hrightItem
    · simp [hleftRow] at hleftItem
  apply (List.perm_ext_iff_of_nodup hleft hright).2
  intro item
  simp [mem_rowNodes]

private theorem univ_sourceNode_entries_perm_occurrence
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : SourceDepthInjective tree) (i : Source) :
    ((Finset.univ : Finset (SourceNode tree i)).toList.map fun node ↦
        (sourceNodeState node, tree.depth node.1)) ~
      tree.nodes.toList.filterMap (fun node ↦
        (node.2.2 i).map fun state ↦ (state, tree.depth node)) := by
  have hleft :
      ((Finset.univ : Finset (SourceNode tree i)).toList.map fun node ↦
        (sourceNodeState node, tree.depth node.1)).Nodup := by
    apply (Finset.nodup_toList _).map
    intro left right heq
    apply Subtype.ext
    have hleftData := (mem_sourceNodes tree i left.1).mp left.2
    have hrightData := (mem_sourceNodes tree i right.1).mp right.2
    apply htree left.1 right.1 i hleftData.1 hrightData.1
      hleftData.2 hrightData.2
    exact congrArg Prod.snd heq
  have hright :
      (tree.nodes.toList.filterMap (fun node ↦
        (node.2.2 i).map fun state ↦
          (state, tree.depth node))).Nodup := by
    apply nodup_filterMap_on (Finset.nodup_toList tree.nodes)
    intro left hleft right hright item hleftItem hrightItem
    cases hleftState : left.2.2 i with
    | none => simp [hleftState] at hleftItem
    | some leftState =>
      cases hrightState : right.2.2 i with
      | none => simp [hrightState] at hrightItem
      | some rightState =>
        have hleftEq : (leftState, tree.depth left) = item := by
          simpa [hleftState] using hleftItem
        have hrightEq : (rightState, tree.depth right) = item := by
          simpa [hrightState] using hrightItem
        apply htree left right i
          (Finset.mem_toList.mp hleft)
          (Finset.mem_toList.mp hright)
          (by simp [UsesSource, hleftState])
          (by simp [UsesSource, hrightState])
        exact congrArg Prod.snd (hleftEq.trans hrightEq.symm)
  apply (List.perm_ext_iff_of_nodup hleft hright).2
  intro item
  constructor
  · intro hitem
    rw [List.mem_map] at hitem
    obtain ⟨node, _hnode, rfl⟩ := hitem
    apply List.mem_filterMap.mpr
    refine ⟨node.1, Finset.mem_toList.mpr
      ((mem_sourceNodes tree i node.1).mp node.2 |>.1), ?_⟩
    rw [sourceNodeState_spec]
    rfl
  · intro hitem
    rw [List.mem_filterMap] at hitem
    obtain ⟨node, hnode, hentry⟩ := hitem
    cases hstate : node.2.2 i with
    | none => simp [hstate] at hentry
    | some state =>
      have huses : UsesSource node.2.2 i := by
        simp [UsesSource, hstate]
      let sourceNode : SourceNode tree i :=
        ⟨node, (mem_sourceNodes tree i node).mpr
          ⟨Finset.mem_toList.mp hnode, huses⟩⟩
      have hchosen : sourceNodeState sourceNode = state := by
        apply Option.some.inj
        exact (sourceNodeState_spec sourceNode).symm.trans hstate
      apply List.mem_map.mpr
      refine ⟨sourceNode, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
      simpa [sourceNode, hstate, hchosen] using hentry

theorem witnessRowDepthEntries_perm_occurrence
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : RowDepthInjective tree) (r : Row) :
    witnessRowDepthEntries tree htree r ~
      tree.nodes.toList.filterMap (fun node ↦
        if node.2.1 = r then some (node.2.2, tree.depth node) else none) := by
  let rankEntry : Fin (rowNodeCount tree r) →
      PartialAssignment Source State × Nat := fun rank ↦
    let node := (rowRankEquiv tree htree r).symm rank
    (node.1.2.2, tree.depth node.1)
  let nodeEntry : RowNode tree r →
      PartialAssignment Source State × Nat := fun node ↦
    (node.1.2.2, tree.depth node.1)
  have hindices :=
    (ofFn_id_perm_univ_toList (rowNodeCount tree r)).map rankEntry
  have hranks :=
    (univ_toList_map_equiv_perm (rowRankEquiv tree htree r).symm).map
      nodeEntry
  have hfirst : witnessRowDepthEntries tree htree r ~
      (Finset.univ : Finset (RowNode tree r)).toList.map nodeEntry := by
    calc
      _ ~ (Finset.univ : Finset (Fin (rowNodeCount tree r))).toList.map
          rankEntry := by
        simpa [witnessRowDepthEntries, rankEntry] using hindices
      _ ~ (Finset.univ : Finset (RowNode tree r)).toList.map
          nodeEntry := by
        simpa [rankEntry, nodeEntry, List.map_map, Function.comp_def] using
          hranks
  exact hfirst.trans (by
    simpa [nodeEntry] using univ_rowNode_entries_perm_occurrence htree r)

theorem witnessSourceStateDepthEntries_perm_occurrence
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : SourceDepthInjective tree) (i : Source) :
    witnessSourceStateDepthEntries tree htree i ~
      tree.nodes.toList.filterMap (fun node ↦
        (node.2.2 i).map fun state ↦ (state, tree.depth node)) := by
  let rankEntry : Fin (sourceNodeCount tree i) → State × Nat :=
    fun rank ↦
      let node := (sourceRankEquiv tree htree i).symm rank
      (sourceNodeState node, tree.depth node.1)
  let nodeEntry : SourceNode tree i → State × Nat := fun node ↦
    (sourceNodeState node, tree.depth node.1)
  have hindices :=
    (ofFn_id_perm_univ_toList (sourceNodeCount tree i)).map rankEntry
  have hranks :=
    (univ_toList_map_equiv_perm (sourceRankEquiv tree htree i).symm).map
      nodeEntry
  have hfirst : witnessSourceStateDepthEntries tree htree i ~
      (Finset.univ : Finset (SourceNode tree i)).toList.map nodeEntry := by
    calc
      _ ~ (Finset.univ : Finset (Fin (sourceNodeCount tree i))).toList.map
          rankEntry := by
        simpa [witnessSourceStateDepthEntries, rankEntry] using hindices
      _ ~ (Finset.univ : Finset (SourceNode tree i)).toList.map
          nodeEntry := by
        simpa [rankEntry, nodeEntry, List.map_map, Function.comp_def] using
          hranks
  exact hfirst.trans (by
    simpa [nodeEntry] using
      univ_sourceNode_entries_perm_occurrence htree i)

end IntrinsicSourceRequirements

section EndpointRequirementCorrespondence

/-- Transporting only the root index leaves the full flattening unchanged. -/
@[simp] theorem canonicalDepthFlattening_transport_root
    {Label' : Type*} [Fintype Label'] [DecidableEq Label']
    {AllowedChildren : Label' → Finset Label' → Prop}
    {depth : Nat} {left right : Label'} (h : left = right)
    (tree : ProperRootedTree AllowedChildren depth left) :
    canonicalDepthFlattening (h ▸ tree) =
      canonicalDepthFlattening tree := by
  cases h
  rfl

/-- The fixed-depth endpoint tree has exactly the label/depth multiset of
its occurrence witness. -/
theorem canonicalDepthFlattening_witnessAtProperRootedTree_perm {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (endpoint : Fin n) :
    canonicalDepthFlattening
        (witnessAtProperRootedTree history hnonempty endpoint) ~
      (witnessAt history endpoint).nodes.toList.map fun occurrence ↦
        (occurrence.2, (witnessAt history endpoint).depth occurrence) := by
  let tree := witnessAt history endpoint
  have hproper : IsProper tree :=
    witnessAt_isProper history hnonempty endpoint
  have hmax : maxDepth tree ≤ n :=
    (witnessAt_maxDepth_le_time history endpoint).trans
      (Nat.le_of_lt endpoint.2)
  have hperm := canonicalDepthFlattening_toProperRootedTreeWithFuel_perm
    tree hproper n hmax
  unfold witnessAtProperRootedTree
  simp only [canonicalDepthFlattening_transport_root]
  exact hperm

theorem canonicalDepthFlattening_endpointCertificate_perm {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (endpoint : Fin n) :
    canonicalDepthFlattening
        (endpointCertificate history hnonempty endpoint).2 ~
      (witnessAt history endpoint).nodes.toList.map fun occurrence ↦
        (occurrence.2, (witnessAt history endpoint).depth occurrence) := by
  simpa [endpointCertificate] using
    canonicalDepthFlattening_witnessAtProperRootedTree_perm
      history hnonempty endpoint

private theorem perm_filterMap
    {Alpha Beta : Type*} {left right : List Alpha}
    (hperm : left ~ right) (f : Alpha → Option Beta) :
    left.filterMap f ~ right.filterMap f := by
  rw [List.filterMap_eq_flatMap_toList,
    List.filterMap_eq_flatMap_toList]
  exact hperm.flatMap_right fun item ↦ (f item).toList

theorem certificateRowDepthEntries_endpointCertificate {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (endpoint : Fin n) (r : Row) :
    certificateRowDepthEntries
        (endpointCertificate history hnonempty endpoint) r =
      witnessRowDepthEntries (witnessAt history endpoint)
        (witnessAt_rowDepthInjective_property history endpoint) r := by
  let tree := witnessAt history endpoint
  let hrow : RowDepthInjective tree :=
    witnessAt_rowDepthInjective_property history endpoint
  have hflatten := canonicalDepthFlattening_endpointCertificate_perm
    history hnonempty endpoint
  have hfiltered := perm_filterMap hflatten (fun item ↦
    if item.1.1 = r then some (item.1.2, item.2) else none)
  have hintrinsic := witnessRowDepthEntries_perm_occurrence hrow r
  have hraw :
      ((canonicalDepthFlattening
          (endpointCertificate history hnonempty endpoint).2).filterMap
        fun item ↦
          if item.1.1 = r then some (item.1.2, item.2) else none) ~
        witnessRowDepthEntries tree hrow r := by
    exact hfiltered.trans (by
      simpa [tree] using hintrinsic.symm)
  unfold certificateRowDepthEntries
  calc
    sortValueDepth _ =
        sortValueDepth (witnessRowDepthEntries tree hrow r) :=
      sortValueDepth_eq_of_perm hraw
    _ = witnessRowDepthEntries tree hrow r :=
      sortValueDepth_eq_self
        (witnessRowDepthEntries_pairwise tree hrow r)

/-- The row lists read from an endpoint certificate are exactly the
intrinsic row-rank lists of its occurrence witness. -/
theorem certificateRowRequirements_endpointCertificate {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (endpoint : Fin n) :
    certificateRowRequirements
        (endpointCertificate history hnonempty endpoint) =
      witnessRowRequirements (witnessAt history endpoint)
        (witnessAt_rowDepthInjective_property history endpoint) := by
  funext r
  unfold certificateRowRequirements
  rw [certificateRowDepthEntries_endpointCertificate
    history hnonempty endpoint r]
  exact witnessRowDepthEntries_map_fst
    (witnessAt history endpoint)
    (witnessAt_rowDepthInjective_property history endpoint) r

theorem certificateSourceStateDepthEntries_endpointCertificate {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (endpoint : Fin n) (i : Source) :
    certificateSourceStateDepthEntries
        (endpointCertificate history hnonempty endpoint) i =
      witnessSourceStateDepthEntries (witnessAt history endpoint)
        (witnessAt_sourceDepthInjective history endpoint) i := by
  let tree := witnessAt history endpoint
  let hsource : SourceDepthInjective tree :=
    witnessAt_sourceDepthInjective history endpoint
  have hflatten := canonicalDepthFlattening_endpointCertificate_perm
    history hnonempty endpoint
  have hfiltered := perm_filterMap hflatten (fun item ↦
    (item.1.2 i).map fun state ↦ (state, item.2))
  have hintrinsic := witnessSourceStateDepthEntries_perm_occurrence hsource i
  have hraw :
      ((canonicalDepthFlattening
          (endpointCertificate history hnonempty endpoint).2).filterMap
        fun item ↦ (item.1.2 i).map fun state ↦ (state, item.2)) ~
        witnessSourceStateDepthEntries tree hsource i := by
    exact hfiltered.trans (by
      simpa [tree] using hintrinsic.symm)
  unfold certificateSourceStateDepthEntries
  calc
    sortValueDepth _ =
        sortValueDepth (witnessSourceStateDepthEntries tree hsource i) :=
      sortValueDepth_eq_of_perm hraw
    _ = witnessSourceStateDepthEntries tree hsource i :=
      sortValueDepth_eq_self
        (witnessSourceStateDepthEntries_pairwise tree hsource i)

/-- The source-state lists read from an endpoint certificate are exactly the
intrinsic source-rank lists of its occurrence witness. -/
theorem certificateSourceStateRequirements_endpointCertificate {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (endpoint : Fin n) :
    certificateSourceStateRequirements
        (endpointCertificate history hnonempty endpoint) =
      witnessSourceStateRequirements (witnessAt history endpoint)
        (witnessAt_sourceDepthInjective history endpoint) := by
  funext i
  unfold certificateSourceStateRequirements
  rw [certificateSourceStateDepthEntries_endpointCertificate
    history hnonempty endpoint i]
  exact witnessSourceStateDepthEntries_map_fst
    (witnessAt history endpoint)
    (witnessAt_sourceDepthInjective history endpoint) i

end EndpointRequirementCorrespondence

section SourceFitAndRealization

@[simp] theorem witnessSourceStateRequirements_length
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : SourceDepthInjective tree) (i : Source) :
    (witnessSourceStateRequirements tree htree i).length =
      sourceNodeCount tree i := by
  simp [witnessSourceStateRequirements]

theorem witnessSourceStateRequirements_fit {h : Nat}
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : SourceDepthInjective tree)
    (hcard : tree.nodes.card < h + 1) :
    SourceRequirementsFit h
      (witnessSourceStateRequirements tree htree) := by
  intro i
  rw [witnessSourceStateRequirements_length]
  exact (Finset.card_filter_le tree.nodes
    (fun node ↦ UsesSource node.2.2 i)).trans
      (Nat.le_of_lt hcard)

/-- An `n`-step occurrence witness contains at most `n` nodes. -/
theorem witnessAt_nodes_card_le_horizon {n : Nat}
    (history : Fin n → Label Source State Row) (endpoint : Fin n) :
    (witnessAt history endpoint).nodes.card ≤ n := by
  classical
  let occurrence : Fin n → Occurrence Source State Row :=
    fun time ↦ (time.1, history time)
  have hsubset : (witnessAt history endpoint).nodes ⊆
      (Finset.univ : Finset (Fin n)).image occurrence := by
    intro node hnode
    obtain ⟨time, _htime, hnodeEq⟩ :=
      witnessAt_node_provenance history endpoint hnode
    subst node
    exact Finset.mem_image.mpr ⟨time, Finset.mem_univ _, rfl⟩
  calc
    (witnessAt history endpoint).nodes.card ≤
        ((Finset.univ : Finset (Fin n)).image occurrence).card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := by simp

theorem witnessAt_nodes_card_lt_horizon_succ {n : Nat}
    (history : Fin n → Label Source State Row) (endpoint : Fin n) :
    (witnessAt history endpoint).nodes.card < n + 1 := by
  have hle := witnessAt_nodes_card_le_horizon history endpoint
  omega

/-- Every source list of an endpoint certificate fits in the `n+1` cells
of an `n`-indexed finite table. -/
theorem certificateSourceStateRequirements_endpoint_fit {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (endpoint : Fin n) :
    SourceRequirementsFit n
      (certificateSourceStateRequirements
        (endpointCertificate history hnonempty endpoint)) := by
  rw [certificateSourceStateRequirements_endpointCertificate
    history hnonempty endpoint]
  exact witnessSourceStateRequirements_fit
    (witnessAt history endpoint)
    (witnessAt_sourceDepthInjective history endpoint)
    (witnessAt_nodes_card_lt_horizon_succ history endpoint)

/-- Intrinsic witness-table realization implies realization of the same
requirements written as source-indexed lists. -/
theorem realizes_witnessSourceStateRequirements_of_realizesWitnessTable
    {h : Nat}
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (htree : SourceDepthInjective tree)
    (hfit : SourceRequirementsFit h
      (witnessSourceStateRequirements tree htree))
    (hcard : tree.nodes.card < h + 1)
    (T : FiniteResamplingTable Source State h)
    (hwitness : RealizesWitnessTable tree hcard T) :
    RealizesSourceRequirements
      (witnessSourceStateRequirements tree htree) hfit T := by
  rintro ⟨i, rank⟩
  let sourceRankValue : Fin (sourceNodeCount tree i) :=
    ⟨rank.1, by
      simpa [witnessSourceStateRequirements] using rank.2⟩
  let node : SourceNode tree i :=
    (sourceRankEquiv tree htree i).symm sourceRankValue
  let requirement : WitnessRequirement tree :=
    ⟨⟨node.1, (mem_sourceNodes tree i node.1).mp node.2 |>.1⟩,
      i, ⟨sourceNodeState node, sourceNodeState_spec node⟩⟩
  have hrank := congrArg Fin.val
    ((sourceRankEquiv tree htree i).apply_symm_apply sourceRankValue)
  change sourceRank tree node.1 i = sourceRankValue.1 at hrank
  have hcell :
      sourceRequirementCell (witnessSourceStateRequirements tree htree)
          hfit ⟨i, rank⟩ =
        witnessRequirementCell tree hcard requirement := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      exact hrank.symm
  have hstate :
      sourceRequirementState (witnessSourceStateRequirements tree htree)
          ⟨i, rank⟩ =
        witnessRequirementState tree requirement := by
    simp [sourceRequirementState, witnessRequirementState,
      witnessSourceStateRequirements, sourceRankValue, node, requirement]
  rw [hcell, hstate]
  exact hwitness requirement

/-- Endpoint specialization of the witness-to-list realization bridge. -/
theorem realizes_certificateSourceStateRequirements_endpoint {n : Nat}
    (history : Fin n → Label Source State Row)
    (hnonempty : ∀ time, NonemptyPartial (history time).2)
    (endpoint : Fin n)
    (hfit : SourceRequirementsFit n
      (certificateSourceStateRequirements
        (endpointCertificate history hnonempty endpoint)))
    (hcard : (witnessAt history endpoint).nodes.card < n + 1)
    (T : FiniteResamplingTable Source State n)
    (hwitness : RealizesWitnessTable
      (witnessAt history endpoint) hcard T) :
    RealizesSourceRequirements
      (certificateSourceStateRequirements
        (endpointCertificate history hnonempty endpoint)) hfit T := by
  have hrequirements :=
    certificateSourceStateRequirements_endpointCertificate
      history hnonempty endpoint
  have hfitWitness : SourceRequirementsFit n
      (witnessSourceStateRequirements (witnessAt history endpoint)
        (witnessAt_sourceDepthInjective history endpoint)) := by
    simpa only [← hrequirements] using hfit
  have hreal :=
    realizes_witnessSourceStateRequirements_of_realizesWitnessTable
    (witnessAt history endpoint)
    (witnessAt_sourceDepthInjective history endpoint)
    hfitWitness hcard T hwitness
  simpa only [hrequirements] using hreal

end SourceFitAndRealization

section CertificateWeight

private theorem prod_map_sortValueDepth_eq
    {Value : Type*} [Fintype Value] [DecidableEq Value]
    (f : Value × Nat → ℝ) (items : List (Value × Nat)) :
    ((sortValueDepth items).map f).prod = (items.map f).prod :=
  ((sortValueDepth_perm items).map f).prod_eq

private theorem prod_raw_rowDepthEntries_eq
    (q : Row → PartialAssignment Source State → ℝ)
    (items : List (Label Source State Row × Nat)) :
    (∏ r,
      ((items.filterMap fun item ↦
          if item.1.1 = r then some (item.1.2, item.2) else none).map
        (fun entry ↦ q r entry.1)).prod) =
      (items.map fun item ↦ q item.1.1 item.1.2).prod := by
  induction items with
  | nil => simp
  | cons item items ih =>
      let tailFactor : Row → ℝ := fun r ↦
        ((items.filterMap fun tail ↦
            if tail.1.1 = r then some (tail.1.2, tail.2) else none).map
          (fun entry ↦ q r entry.1)).prod
      calc
        (∏ r,
            (((item :: items).filterMap fun entry ↦
                if entry.1.1 = r then some (entry.1.2, entry.2)
                else none).map (fun entry ↦ q r entry.1)).prod) =
            ∏ r, (if item.1.1 = r then q r item.1.2 else 1) *
              tailFactor r := by
          apply Fintype.prod_congr
          intro r
          by_cases hrow : item.1.1 = r <;>
            simp [hrow, tailFactor]
        _ = (∏ r, if item.1.1 = r then q r item.1.2 else 1) *
              ∏ r, tailFactor r := by
          rw [Finset.prod_mul_distrib]
        _ = q item.1.1 item.1.2 * ∏ r, tailFactor r := by
          rw [Fintype.prod_ite_eq]
        _ = q item.1.1 item.1.2 *
              (items.map fun tail ↦ q tail.1.1 tail.1.2).prod := by
          rw [← ih]
        _ = ((item :: items).map fun entry ↦
              q entry.1.1 entry.1.2).prod := by simp

private theorem prod_raw_sourceStateDepthEntries_eq
    (p : Source → State → ℝ)
    (items : List (Label Source State Row × Nat)) :
    (∏ i,
      ((items.filterMap fun item ↦
          (item.1.2 i).map fun state ↦ (state, item.2)).map
        (fun entry ↦ p i entry.1)).prod) =
      (items.map fun item ↦
        partialLambdaProduct p item.1.2).prod := by
  induction items with
  | nil => simp
  | cons item items ih =>
      let tailFactor : Source → ℝ := fun i ↦
        ((items.filterMap fun tail ↦
            (tail.1.2 i).map fun state ↦ (state, tail.2)).map
          (fun entry ↦ p i entry.1)).prod
      let localFactor : Source → ℝ := fun i ↦
        match item.1.2 i with
        | none => 1
        | some state => p i state
      calc
        (∏ i,
            (((item :: items).filterMap fun entry ↦
                (entry.1.2 i).map fun state ↦
                  (state, entry.2)).map
              (fun entry ↦ p i entry.1)).prod) =
            ∏ i, localFactor i * tailFactor i := by
          apply Fintype.prod_congr
          intro i
          cases hstate : item.1.2 i <;>
            simp [hstate, localFactor, tailFactor]
        _ = (∏ i, localFactor i) * ∏ i, tailFactor i := by
          rw [Finset.prod_mul_distrib]
        _ = partialLambdaProduct p item.1.2 *
              ∏ i, tailFactor i := by
          rfl
        _ = partialLambdaProduct p item.1.2 *
              (items.map fun tail ↦
                partialLambdaProduct p tail.1.2).prod := by
          rw [← ih]
        _ = ((item :: items).map fun entry ↦
              partialLambdaProduct p entry.1.2).prod := by simp

/-- The row-prefix weight of a certificate is the product of the row factor
over every flattened node, including repeated labels. -/
theorem requirementsWeight_certificateRowRequirements
    (q : Row → PartialAssignment Source State → ℝ) {depth : Nat}
    (certificate : CanonicalCertificate Source State Row depth) :
    requirementsWeight q (certificateRowRequirements certificate) =
      ((canonicalDepthFlattening certificate.2).map fun item ↦
        q item.1.1 item.1.2).prod := by
  unfold requirementsWeight certificateRowRequirements
  calc
    (∏ r,
        (((certificateRowDepthEntries certificate r).map Prod.fst).map
          (q r)).prod) =
        ∏ r,
          (((canonicalDepthFlattening certificate.2).filterMap fun item ↦
              if item.1.1 = r then some (item.1.2, item.2)
              else none).map (fun entry ↦ q r entry.1)).prod := by
      apply Fintype.prod_congr
      intro r
      rw [List.map_map]
      unfold certificateRowDepthEntries
      exact prod_map_sortValueDepth_eq
        (fun entry ↦ q r entry.1) _
    _ = ((canonicalDepthFlattening certificate.2).map fun item ↦
          q item.1.1 item.1.2).prod :=
      prod_raw_rowDepthEntries_eq q _

/-- The source-prefix weight of a certificate is the product of the
categorical patch mass over every flattened node. -/
theorem sourceRequirementsWeight_certificateSourceStateRequirements
    (p : Source → State → ℝ) {depth : Nat}
    (certificate : CanonicalCertificate Source State Row depth) :
    sourceRequirementsWeight p
        (certificateSourceStateRequirements certificate) =
      ((canonicalDepthFlattening certificate.2).map fun item ↦
        partialLambdaProduct p item.1.2).prod := by
  unfold sourceRequirementsWeight certificateSourceStateRequirements
  calc
    (∏ i,
        (((certificateSourceStateDepthEntries certificate i).map Prod.fst).map
          (p i)).prod) =
        ∏ i,
          (((canonicalDepthFlattening certificate.2).filterMap fun item ↦
              (item.1.2 i).map fun state ↦ (state, item.2)).map
            (fun entry ↦ p i entry.1)).prod := by
      apply Fintype.prod_congr
      intro i
      rw [List.map_map]
      unfold certificateSourceStateDepthEntries
      exact prod_map_sortValueDepth_eq
        (fun entry ↦ p i entry.1) _
    _ = ((canonicalDepthFlattening certificate.2).map fun item ↦
          partialLambdaProduct p item.1.2).prod :=
      prod_raw_sourceStateDepthEntries_eq p _

private theorem prod_flatMap_eq_prod_map_prod
    {Alpha : Type*} (items : List Alpha) (f : Alpha → List ℝ) :
    (items.flatMap f).prod = (items.map fun item ↦ (f item).prod).prod := by
  induction items with
  | nil => simp
  | cons item items ih => simp [ih, List.prod_append]

private theorem prod_map_canonicalDepthFlatteningAux_eq_treeWeight
    {Label' : Type*} [Fintype Label'] [DecidableEq Label']
    {AllowedChildren : Label' → Finset Label' → Prop}
    (base : Label' → ℝ) (level : Nat) :
    {depth : Nat} → {root : Label'} →
      (tree : ProperRootedTree AllowedChildren depth root) →
      ((canonicalDepthFlatteningAux level tree).map fun item ↦
        base item.1).prod = treeWeight base tree
  | 0, _root, tree => nomatch tree
  | _depth + 1, root, ⟨childset, branches⟩ => by
      simp only [canonicalDepthFlatteningAux, List.map_cons, List.prod_cons,
        treeWeight, nodeWeight]
      apply congrArg (base root * ·)
      rw [List.map_flatMap,
        prod_flatMap_eq_prod_map_prod]
      rw [Finset.prod_map_toList]
      apply Fintype.prod_congr
      intro child
      exact prod_map_canonicalDepthFlatteningAux_eq_treeWeight
        base (level + 1) (branches child)

theorem prod_map_canonicalDepthFlattening_eq_treeWeight
    {Label' : Type*} [Fintype Label'] [DecidableEq Label']
    {AllowedChildren : Label' → Finset Label' → Prop}
    (base : Label' → ℝ) {depth : Nat} {root : Label'}
    (tree : ProperRootedTree AllowedChildren depth root) :
    ((canonicalDepthFlattening tree).map fun item ↦ base item.1).prod =
      treeWeight base tree := by
  exact prod_map_canonicalDepthFlatteningAux_eq_treeWeight base 0 tree

private theorem prod_map_mul
    {Alpha : Type*} (items : List Alpha) (left right : Alpha → ℝ) :
    (items.map left).prod * (items.map right).prod =
      (items.map fun item ↦ left item * right item).prod := by
  induction items with
  | nil => simp
  | cons item items ih =>
      simp only [List.map_cons, List.prod_cons]
      calc
        left item * (items.map left).prod *
            (right item * (items.map right).prod) =
          left item * right item *
            ((items.map left).prod * (items.map right).prod) := by ring
        _ = left item * right item *
            (items.map fun entry ↦ left entry * right entry).prod := by
          rw [ih]

/-- The product of the deterministic source and row prefix weights is
exactly the canonical product weight, for every certificate. -/
theorem certificateRequirementsWeight_eq_coarseCertificateWeight
    (q : Row → PartialAssignment Source State → ℝ)
    (p : Source → State → ℝ) {depth : Nat}
    (certificate : CanonicalCertificate Source State Row depth) :
    sourceRequirementsWeight p
        (certificateSourceStateRequirements certificate) *
      requirementsWeight q (certificateRowRequirements certificate) =
        coarseCertificateWeight q p certificate := by
  rw [sourceRequirementsWeight_certificateSourceStateRequirements,
    requirementsWeight_certificateRowRequirements]
  let items := canonicalDepthFlattening certificate.2
  calc
    (items.map fun item ↦ partialLambdaProduct p item.1.2).prod *
        (items.map fun item ↦ q item.1.1 item.1.2).prod =
      (items.map fun item ↦
        partialLambdaProduct p item.1.2 * q item.1.1 item.1.2).prod :=
      prod_map_mul items _ _
    _ = (items.map fun item ↦
        q item.1.1 item.1.2 * partialLambdaProduct p item.1.2).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro item _hitem
      rw [mul_comm]
    _ = treeWeight
        (fun label : Label Source State Row ↦
          q label.1 label.2 * partialLambdaProduct p label.2)
        certificate.2 := by
      simpa [items] using
        (prod_map_canonicalDepthFlattening_eq_treeWeight
          (fun label : Label Source State Row ↦
            q label.1 label.2 * partialLambdaProduct p label.2)
          certificate.2)
    _ = coarseCertificateWeight q p certificate := rfl

end CertificateWeight

end

end WeightedEdgeColoring.FinitePartialResamplingCertificateRequirements
