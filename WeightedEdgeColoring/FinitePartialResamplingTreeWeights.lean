import WeightedEdgeColoring.FinitePartialResamplingChargeBounds

/-!
# Finite-depth rooted-tree weight bound

This file isolates the elementary tree calculation used in witness-tree
arguments.  Labels form a finite type.  A node chooses a finite set of child
labels and has exactly one branch for every chosen label, so two children of
one node can never have the same label.  The predicate `AllowedChildren`
decides which child-label sets are proper for each root label.

Depth zero contains no rooted tree.  At depth `d + 1`, a tree consists of its
root, an allowed child-label set, and one depth-`d` tree rooted at every child
label.  In particular, a leaf first appears at depth one, when the empty
child set is allowed.  This convention makes the recursive total exact even
when the abstract predicate does not allow the empty set.

The total weight is written as the corresponding finite product-sum.  The
main theorem proves by induction on the depth that this total is at most
`mu root`, provided the same one-node product-sum with `mu` on the children
is at most `mu root`.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingTreeWeights

open scoped BigOperators

universe u

variable {Label : Type u}
variable [Fintype Label] [DecidableEq Label]

/-- Universe-polymorphic empty type used at depth zero. -/
inductive NoProperRootedTree : Type u

/-- The depth-zero tree type is finite (and empty). -/
instance noProperRootedTreeFintype : Fintype NoProperRootedTree where
  elems := ∅
  complete tree := nomatch tree

/-- Equality on the depth-zero tree type is decidable. -/
instance noProperRootedTreeDecidableEq : DecidableEq NoProperRootedTree :=
  fun tree ↦ nomatch tree

/-- Decidability of the abstract proper-child-set predicate. -/
abbrev DecidableAllowedChildren
    (AllowedChildren : Label → Finset Label → Prop) :=
  ∀ root childset, Decidable (AllowedChildren root childset)

/-- A canonical proper rooted tree with a strict depth budget.

At a positive depth, the finite child-label set records which labels occur,
and the dependent function gives exactly one subtree for each recorded
label.  Thus a node has at most one child of any label.  Properness is built
into the subtype containing the child-label set. -/
def ProperRootedTree
    (AllowedChildren : Label → Finset Label → Prop) :
    Nat → Label → Type u
  | 0, _root => NoProperRootedTree
  | depth + 1, root =>
      Σ childset : {s : Finset Label // AllowedChildren root s},
        (child : ↥childset.1) →
          ProperRootedTree AllowedChildren depth child.1

/-- At every finite depth there are only finitely many canonical proper
rooted trees. -/
instance properRootedTreeFintype
    (AllowedChildren : Label → Finset Label → Prop)
    [DecidableAllowedChildren AllowedChildren] :
    (depth : Nat) → (root : Label) →
      Fintype (ProperRootedTree AllowedChildren depth root)
  | 0, _root => noProperRootedTreeFintype
  | depth + 1, root => by
      letI : ∀ child : Label,
          Fintype (ProperRootedTree AllowedChildren depth child) :=
        fun child ↦ properRootedTreeFintype AllowedChildren depth child
      change Fintype
        (Σ childset : {s : Finset Label // AllowedChildren root s},
          (child : ↥childset.1) →
            ProperRootedTree AllowedChildren depth child.1)
      exact inferInstance

/-- Equality of canonical proper rooted trees is decidable at every finite
depth. -/
instance properRootedTreeDecidableEq
    (AllowedChildren : Label → Finset Label → Prop)
    [DecidableAllowedChildren AllowedChildren] :
    (depth : Nat) → (root : Label) →
      DecidableEq (ProperRootedTree AllowedChildren depth root)
  | 0, _root => noProperRootedTreeDecidableEq
  | depth + 1, root => by
      letI : ∀ child : Label,
          DecidableEq (ProperRootedTree AllowedChildren depth child) :=
        fun child ↦ properRootedTreeDecidableEq AllowedChildren depth child
      change DecidableEq
        (Σ childset : {s : Finset Label // AllowedChildren root s},
          (child : ↥childset.1) →
            ProperRootedTree AllowedChildren depth child.1)
      exact inferInstance

/-- The child-label set at the root of a positive-depth proper tree. -/
def rootChildSet
    {AllowedChildren : Label → Finset Label → Prop}
    {depth : Nat} {root : Label}
    (tree : ProperRootedTree AllowedChildren (depth + 1) root) :
    Finset Label :=
  tree.1.1

/-- Weight of one node after weights have been assigned to all its child
branches. -/
def nodeWeight (base : Label → ℝ) (root : Label)
    {childset : Finset Label} (branchWeight : ↥childset → ℝ) : ℝ :=
  base root * ∏ child, branchWeight child

/-- Product weight of a finite proper rooted tree.  Every node contributes
one factor `base` at its own label. -/
def treeWeight
    {AllowedChildren : Label → Finset Label → Prop}
    (base : Label → ℝ) :
    {depth : Nat} → {root : Label} →
      ProperRootedTree AllowedChildren depth root → ℝ
  | 0, _root, tree => nomatch tree
  | _depth + 1, root, ⟨childset, branches⟩ =>
      nodeWeight base root fun child ↦ treeWeight base (branches child)

/-- The finite total weight of all proper rooted trees within one depth
budget.  For a fixed allowed child-label set, choices of child subtrees are
independent, so their total is the product of the child totals. -/
def totalProperTreeWeight
    (AllowedChildren : Label → Finset Label → Prop)
    [DecidableAllowedChildren AllowedChildren]
    (base : Label → ℝ) : Nat → Label → ℝ
  | 0, _root => 0
  | depth + 1, root =>
      base root *
        ∑ childset : Finset Label,
          if AllowedChildren root childset then
            ∏ child : ↥childset,
              totalProperTreeWeight AllowedChildren base depth child.1
          else 0

/-- The recursive product-sum is exactly the sum of the weights of all
canonical proper rooted trees with the given depth budget and root. -/
theorem sum_treeWeight_eq_totalProperTreeWeight
    (AllowedChildren : Label → Finset Label → Prop)
    [DecidableAllowedChildren AllowedChildren]
    (base : Label → ℝ) (depth : Nat) (root : Label) :
    (∑ tree : ProperRootedTree AllowedChildren depth root,
        treeWeight base tree) =
      totalProperTreeWeight AllowedChildren base depth root := by
  induction depth generalizing root with
  | zero =>
      change (∑ tree : NoProperRootedTree,
        @treeWeight Label AllowedChildren base 0 root tree) = 0
      rfl
  | succ depth ih =>
      rw [totalProperTreeWeight]
      change
        (∑ tree :
            (Σ childset : {s : Finset Label // AllowedChildren root s},
              (child : ↥childset.1) →
                ProperRootedTree AllowedChildren depth child.1),
          @treeWeight Label AllowedChildren base (depth + 1) root tree) = _
      rw [Fintype.sum_sigma]
      simp only [treeWeight, nodeWeight]
      simp_rw [← Finset.mul_sum]
      apply congrArg (fun total ↦ base root * total)
      simp_rw [← Fintype.prod_sum]
      simp_rw [ih]
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype
        (Finset.univ.filter (AllowedChildren root)) (by simp)
        (fun childset ↦
          ∏ child : ↥childset,
            totalProperTreeWeight AllowedChildren base depth child.1)).symm

/-- A single tree has nonnegative weight when all node weights are
nonnegative. -/
theorem treeWeight_nonneg
    {AllowedChildren : Label → Finset Label → Prop}
    {base : Label → ℝ} (hbase : ∀ root, 0 ≤ base root) :
    {depth : Nat} → {root : Label} →
      (tree : ProperRootedTree AllowedChildren depth root) →
        0 ≤ treeWeight base tree
  | 0, _root, tree => nomatch tree
  | _depth + 1, root, ⟨childset, branches⟩ => by
      rw [treeWeight, nodeWeight]
      exact mul_nonneg (hbase root)
        (Finset.prod_nonneg fun child _hchild ↦
          treeWeight_nonneg hbase (branches child))

/-- Every nonnegative tree weight is at most the total weight of all trees
with the same depth budget and root. -/
theorem treeWeight_le_totalProperTreeWeight
    (AllowedChildren : Label → Finset Label → Prop)
    [DecidableAllowedChildren AllowedChildren]
    {base : Label → ℝ} (hbase : ∀ root, 0 ≤ base root)
    {depth : Nat} {root : Label}
    (tree : ProperRootedTree AllowedChildren depth root) :
    treeWeight base tree ≤
      totalProperTreeWeight AllowedChildren base depth root := by
  rw [← sum_treeWeight_eq_totalProperTreeWeight
    AllowedChildren base depth root]
  exact Finset.single_le_sum
    (fun other _hother ↦ treeWeight_nonneg hbase other)
    (Finset.mem_univ tree)

/-- The recursively defined total is nonnegative when every node weight is
nonnegative. -/
theorem totalProperTreeWeight_nonneg
    (AllowedChildren : Label → Finset Label → Prop)
    [DecidableAllowedChildren AllowedChildren]
    {base : Label → ℝ} (hbase : ∀ root, 0 ≤ base root)
    (depth : Nat) (root : Label) :
    0 ≤ totalProperTreeWeight AllowedChildren base depth root := by
  induction depth generalizing root with
  | zero =>
      simp [totalProperTreeWeight]
  | succ depth ih =>
      rw [totalProperTreeWeight]
      apply mul_nonneg (hbase root)
      apply Finset.sum_nonneg
      intro childset _hchildset
      by_cases hallowed : AllowedChildren root childset
      · simp only [hallowed, if_true]
        exact Finset.prod_nonneg fun child _hchild ↦ ih child.1
      · simp [hallowed]

/-- Product-sum criterion for all finite depths.

If replacing every possible child subtree by its proposed upper bound `mu`
makes the one-node product-sum at most `mu root`, then the total weight of all
proper rooted trees at every finite depth is at most `mu root`. -/
theorem totalProperTreeWeight_le_mu
    (AllowedChildren : Label → Finset Label → Prop)
    [DecidableAllowedChildren AllowedChildren]
    {base mu : Label → ℝ}
    (hbase : ∀ root, 0 ≤ base root)
    (hmu : ∀ root, 0 ≤ mu root)
    (hlocal : ∀ root,
      base root *
          (∑ childset : Finset Label,
            if AllowedChildren root childset then
              ∏ child : ↥childset, mu child.1
            else 0) ≤
        mu root)
    (depth : Nat) (root : Label) :
    totalProperTreeWeight AllowedChildren base depth root ≤ mu root := by
  induction depth generalizing root with
  | zero =>
      simpa [totalProperTreeWeight] using hmu root
  | succ depth ih =>
      rw [totalProperTreeWeight]
      calc
        base root *
              (∑ childset : Finset Label,
                if AllowedChildren root childset then
                  ∏ child : ↥childset,
                    totalProperTreeWeight AllowedChildren base depth child.1
                else 0) ≤
            base root *
              (∑ childset : Finset Label,
                if AllowedChildren root childset then
                  ∏ child : ↥childset, mu child.1
                else 0) := by
          apply mul_le_mul_of_nonneg_left _ (hbase root)
          apply Finset.sum_le_sum
          intro childset _hchildset
          by_cases hallowed : AllowedChildren root childset
          · simp only [hallowed, if_true]
            apply Finset.prod_le_prod
            · intro child _hchild
              exact totalProperTreeWeight_nonneg AllowedChildren hbase
                depth child.1
            · intro child _hchild
              exact ih child.1
          · simp [hallowed]
        _ ≤ mu root := hlocal root

end WeightedEdgeColoring.FinitePartialResamplingTreeWeights
