import WeightedEdgeColoring.FinitePartialResamplingFiniteRun
import WeightedEdgeColoring.FinitePartialResamplingWitnessStructure
import Mathlib.Data.Finset.Card

/-!
# Table cylinders attached to partial-resampling witnesses

This file isolates the finite product calculation behind the table part of a
witness argument.  A requirement fixes one state at one table cell.  If the
required cells are distinct, the total mass of all finite tables satisfying
the requirements is exactly the product of their one-cell probabilities.

For an occurrence witness, the cell belonging to a node and a source is
described intrinsically.  Its index is the number of deeper witness nodes
which use the same source.  Thus the cell assignment does not remember the
absolute occurrence times.  The only structural hypothesis needed for its
injectivity is that two witness nodes using the same source cannot have the
same depth.  The backward-scan lemmas later in this file are intended to
supply that hypothesis for `witnessAt`.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingWitnessCylinder

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential
open WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
open WeightedEdgeColoring.FinitePartialResamplingProcess
open WeightedEdgeColoring.FinitePartialResamplingWitnessStructure

noncomputable section

section FiniteCylinder

variable {Coord Value Requirement : Type*}
variable [Fintype Coord] [DecidableEq Coord]
variable [Fintype Value] [DecidableEq Value]
variable [Fintype Requirement] [DecidableEq Requirement]

/-- A complete assignment realizes a finite family of one-coordinate
requirements. -/
def RealizesCylinder (cell : Requirement → Coord)
    (value : Requirement → Value) (x : Coord → Value) : Prop :=
  ∀ r, x (cell r) = value r

noncomputable instance realizesCylinderDecidable
    (cell : Requirement → Coord) (value : Requirement → Value)
    (x : Coord → Value) : Decidable (RealizesCylinder cell value x) :=
  Classical.propDecidable _

/-- The one-coordinate factor obtained by imposing every requirement which
lands at `c`. -/
def cylinderLocalMass (prob : Coord → Value → ℝ)
    (cell : Requirement → Coord) (value : Requirement → Value)
    (c : Coord) (a : Value) : ℝ :=
  if ∀ r, cell r = c → a = value r then prob c a else 0

/-- A global cylinder indicator is the product of its local indicators. -/
theorem cylinderIndicator_eq_prod_local
    (prob : Coord → Value → ℝ)
    (cell : Requirement → Coord) (value : Requirement → Value)
    (x : Coord → Value) :
    (if RealizesCylinder cell value x then ∏ c, prob c (x c) else 0) =
      ∏ c, cylinderLocalMass prob cell value c (x c) := by
  classical
  by_cases hreal : RealizesCylinder cell value x
  · rw [if_pos hreal]
    apply Finset.prod_congr rfl
    intro c _hc
    rw [cylinderLocalMass, if_pos]
    intro r hr
    have h := hreal r
    simpa [hr] using h
  · rw [if_neg hreal]
    have hfailure : ∃ r, x (cell r) ≠ value r := by
      simpa [RealizesCylinder] using hreal
    obtain ⟨r, hr⟩ := hfailure
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ (cell r))
    rw [cylinderLocalMass, if_neg]
    intro hall
    exact hr (hall r rfl)

/-- At a required coordinate, the local mass is the probability of its
unique required value. -/
theorem sum_cylinderLocalMass_at_cell
    (prob : Coord → Value → ℝ)
    (cell : Requirement → Coord) (value : Requirement → Value)
    (hcell : Function.Injective cell) (r : Requirement) :
    (∑ a, cylinderLocalMass prob cell value (cell r) a) =
      prob (cell r) (value r) := by
  classical
  have hiff (a : Value) :
      (∀ s, cell s = cell r → a = value s) ↔ a = value r := by
    constructor
    · intro h
      exact h r rfl
    · intro ha s hs
      have hsr : s = r := hcell hs
      simpa [hsr] using ha
  simp only [cylinderLocalMass]
  simp_rw [hiff]
  simp

/-- Away from the image of the requirement map, a local coordinate is
unconstrained and has total mass one. -/
theorem sum_cylinderLocalMass_of_not_mem_image
    (prob : Coord → Value → ℝ)
    (hprobSum : ∀ c, ∑ a, prob c a = 1)
    (cell : Requirement → Coord) (value : Requirement → Value)
    {c : Coord} (hc : c ∉ (Finset.univ : Finset Requirement).image cell) :
    (∑ a, cylinderLocalMass prob cell value c a) = 1 := by
  classical
  have hnone : ∀ r, cell r ≠ c := by
    intro r hr
    apply hc
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hr⟩
  have hall (a : Value) : ∀ r, cell r = c → a = value r := by
    intro r hr
    exact (hnone r hr).elim
  calc
    (∑ a, cylinderLocalMass prob cell value c a) = ∑ a, prob c a := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [cylinderLocalMass, if_pos (hall a)]
    _ = 1 := hprobSum c

/-- Exact finite cylinder mass.  This is the division-free independence
statement used for a fixed witness: distinct required cells contribute the
product of their one-cell probabilities, while every other cell sums out. -/
theorem sum_cylinderMass_eq_prod
    (prob : Coord → Value → ℝ)
    (hprobSum : ∀ c, ∑ a, prob c a = 1)
    (cell : Requirement → Coord) (value : Requirement → Value)
    (hcell : Function.Injective cell) :
    (∑ x : Coord → Value,
      if RealizesCylinder cell value x then ∏ c, prob c (x c) else 0) =
      ∏ r, prob (cell r) (value r) := by
  classical
  let localSum : Coord → ℝ := fun c ↦
    ∑ a, cylinderLocalMass prob cell value c a
  let selected : Finset Coord := (Finset.univ : Finset Requirement).image cell
  have hselected :
      (∏ c ∈ selected, localSum c) =
        ∏ r, prob (cell r) (value r) := by
    dsimp only [selected]
    rw [Finset.prod_image hcell.injOn]
    apply Finset.prod_congr rfl
    intro r _hr
    exact sum_cylinderLocalMass_at_cell prob cell value hcell r
  have houtside :
      (∏ c ∈ (Finset.univ : Finset Coord) \ selected, localSum c) = 1 := by
    apply Finset.prod_eq_one
    intro c hc
    apply sum_cylinderLocalMass_of_not_mem_image prob hprobSum cell value
    exact (Finset.mem_sdiff.mp hc).2
  calc
    (∑ x : Coord → Value,
        if RealizesCylinder cell value x then ∏ c, prob c (x c) else 0) =
        ∑ x : Coord → Value,
          ∏ c, cylinderLocalMass prob cell value c (x c) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact cylinderIndicator_eq_prod_local prob cell value x
    _ = ∏ c, localSum c := by
      exact (Fintype.prod_sum
        (fun c a ↦ cylinderLocalMass prob cell value c a)).symm
    _ = (∏ c ∈ selected, localSum c) *
          ∏ c ∈ (Finset.univ : Finset Coord) \ selected, localSum c := by
      rw [← Finset.prod_union Finset.disjoint_sdiff]
      rw [Finset.union_sdiff_of_subset (Finset.subset_univ selected)]
    _ = ∏ r, prob (cell r) (value r) := by
      rw [hselected, houtside, mul_one]

end FiniteCylinder

section WitnessCells

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- Number of deeper nodes of `tree` which use source `i`.  For a canonical
backward witness, deeper means earlier, so this is the table pointer at the
occurrence `node`. -/
def sourceRank
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (node : Occurrence Source State Row) (i : Source) : Nat :=
  (tree.nodes.filter fun other ↦
    UsesSource other.2.2 i ∧ tree.depth node < tree.depth other).card

/-- Moving to a deeper node which uses the same source strictly decreases
the number of still deeper same-source nodes. -/
theorem sourceRank_lt_of_depth_lt
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {shallow deep : Occurrence Source State Row} {i : Source}
    (hshallow : shallow ∈ tree.nodes) (hdeep : deep ∈ tree.nodes)
    (hdeepUses : UsesSource deep.2.2 i)
    (hdepth : tree.depth shallow < tree.depth deep) :
    sourceRank tree deep i < sourceRank tree shallow i := by
  classical
  unfold sourceRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro other hother
    have data := Finset.mem_filter.mp hother
    exact Finset.mem_filter.mpr ⟨data.1, data.2.1,
      lt_trans hdepth data.2.2⟩
  · intro heq
    have hlarge : deep ∈ tree.nodes.filter fun other ↦
        UsesSource other.2.2 i ∧ tree.depth shallow < tree.depth other :=
      Finset.mem_filter.mpr ⟨hdeep, hdeepUses, hdepth⟩
    have hsmall : deep ∈ tree.nodes.filter fun other ↦
        UsesSource other.2.2 i ∧ tree.depth deep < tree.depth other := by
      rw [heq]
      exact hlarge
    exact (Nat.lt_irrefl _ (Finset.mem_filter.mp hsmall).2.2)

/-- The minimal structural condition needed to distinguish the table cells
read by a fixed occurrence witness. -/
def SourceDepthInjective
    (tree : Witness (Source := Source) (State := State) (Row := Row)) : Prop :=
  ∀ left right : Occurrence Source State Row, ∀ i : Source,
    left ∈ tree.nodes → right ∈ tree.nodes →
    UsesSource left.2.2 i → UsesSource right.2.2 i →
    tree.depth left = tree.depth right → left = right

/-- Under `SourceDepthInjective`, same-source ranks identify witness nodes. -/
theorem sourceRank_injective_on_source
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    (htree : SourceDepthInjective tree)
    {left right : Occurrence Source State Row} {i : Source}
    (hleft : left ∈ tree.nodes) (hright : right ∈ tree.nodes)
    (hleftUses : UsesSource left.2.2 i)
    (hrightUses : UsesSource right.2.2 i)
    (hrank : sourceRank tree left i = sourceRank tree right i) :
    left = right := by
  by_cases hdepth : tree.depth left = tree.depth right
  · exact htree left right i hleft hright hleftUses hrightUses hdepth
  · rcases lt_or_gt_of_ne hdepth with hlt | hgt
    · have hstrict := sourceRank_lt_of_depth_lt hleft hright
        hrightUses hlt
      omega
    · have hstrict := sourceRank_lt_of_depth_lt hright hleft
        hleftUses hgt
      omega

/-- One state requirement for every source mentioned by every witness node.
The state is carried explicitly, together with the equation saying that it
is the state named by the node's partial assignment. -/
abbrev WitnessRequirement
    (tree : Witness (Source := Source) (State := State) (Row := Row)) :=
  Σ node : {node : Occurrence Source State Row // node ∈ tree.nodes},
    Σ i : Source, {a : State // node.1.2.2 i = some a}

/-- The table cell read by one witness requirement.  The cardinality
hypothesis merely puts the intrinsic rank inside the chosen finite prefix. -/
def witnessRequirementCell {h : Nat}
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (hcard : tree.nodes.card < h + 1) :
    WitnessRequirement tree → Source × Fin (h + 1) :=
  fun requirement ↦
    (requirement.2.1,
      ⟨sourceRank tree requirement.1.1 requirement.2.1, by
        have hfilter :
            (tree.nodes.filter fun other ↦
              UsesSource other.2.2 requirement.2.1 ∧
                tree.depth requirement.1.1 < tree.depth other).card ≤
              tree.nodes.card := Finset.card_filter_le _ _
        exact lt_of_le_of_lt hfilter hcard⟩)

/-- The state fixed by one witness requirement. -/
def witnessRequirementState
    (tree : Witness (Source := Source) (State := State) (Row := Row)) :
    WitnessRequirement tree → State :=
  fun requirement ↦ requirement.2.2.1

/-- Distinct node/source requirements of a structurally ordered witness read
distinct cells of the resampling table. -/
theorem witnessRequirementCell_injective {h : Nat}
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (hcard : tree.nodes.card < h + 1)
    (htree : SourceDepthInjective tree) :
    Function.Injective (witnessRequirementCell tree hcard) := by
  classical
  rintro ⟨⟨left, hleft⟩, i, ⟨a, ha⟩⟩
    ⟨⟨right, hright⟩, j, ⟨b, hb⟩⟩ hcell
  have hij : i = j := congrArg Prod.fst hcell
  subst j
  have hfin :
      (witnessRequirementCell tree hcard
        ⟨⟨left, hleft⟩, i, ⟨a, ha⟩⟩).2 =
      (witnessRequirementCell tree hcard
        ⟨⟨right, hright⟩, i, ⟨b, hb⟩⟩).2 :=
    congrArg Prod.snd hcell
  have hrank : sourceRank tree left i = sourceRank tree right i := by
    exact congrArg Fin.val hfin
  have hleftUses : UsesSource left.2.2 i := by
    unfold UsesSource
    rw [ha]
    simp
  have hrightUses : UsesSource right.2.2 i := by
    unfold UsesSource
    rw [hb]
    simp
  have hnode : left = right :=
    sourceRank_injective_on_source htree hleft hright hleftUses hrightUses hrank
  subst right
  have hab : a = b := Option.some.inj (ha.symm.trans hb)
  subst b
  rfl

/-- A finite resampling table satisfies every state requirement of a fixed
witness. -/
def RealizesWitnessTable {h : Nat}
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (hcard : tree.nodes.card < h + 1)
    (T : FiniteResamplingTable Source State h) : Prop :=
  ∀ requirement : WitnessRequirement tree,
    T (witnessRequirementCell tree hcard requirement).1
        (witnessRequirementCell tree hcard requirement).2 =
      witnessRequirementState tree requirement

noncomputable instance realizesWitnessTableDecidable {h : Nat}
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (hcard : tree.nodes.card < h + 1)
    (T : FiniteResamplingTable Source State h) :
    Decidable (RealizesWitnessTable tree hcard T) :=
  Classical.propDecidable _

/-- Exact table-cylinder mass for a fixed occurrence witness. -/
theorem sum_finiteTableMass_realizing_witness {h : Nat}
    (prob : Source → State → ℝ)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (hcard : tree.nodes.card < h + 1)
    (htree : SourceDepthInjective tree) :
    (∑ T : FiniteResamplingTable Source State h,
      if RealizesWitnessTable tree hcard T then finiteTableMass prob T else 0) =
      ∏ requirement : WitnessRequirement tree,
        prob (witnessRequirementCell tree hcard requirement).1
          (witnessRequirementState tree requirement) := by
  classical
  let curryEquiv := Equiv.curry Source (Fin (h + 1)) State
  let cellProb : (Source × Fin (h + 1)) → State → ℝ :=
    fun c a ↦ prob c.1 a
  let cell := witnessRequirementCell tree hcard
  let value := witnessRequirementState tree
  have hcell : Function.Injective cell :=
    witnessRequirementCell_injective tree hcard htree
  have hcellProbSum : ∀ c, ∑ a, cellProb c a = 1 := by
    intro c
    exact hprobSum c.1
  calc
    (∑ T : FiniteResamplingTable Source State h,
        if RealizesWitnessTable tree hcard T then finiteTableMass prob T else 0) =
        ∑ x : (Source × Fin (h + 1)) → State,
          if RealizesCylinder cell value x then
            ∏ c, cellProb c (x c) else 0 := by
      apply Fintype.sum_equiv curryEquiv.symm
      intro T
      simp only [curryEquiv, Equiv.curry_symm_apply]
      unfold RealizesWitnessTable finiteTableMass
      rw [Fintype.prod_prod_type]
      rfl
    _ = ∏ requirement : WitnessRequirement tree,
          cellProb (cell requirement) (value requirement) :=
      sum_cylinderMass_eq_prod cellProb hcellProbSum cell value hcell
    _ = ∏ requirement : WitnessRequirement tree,
          prob (witnessRequirementCell tree hcard requirement).1
            (witnessRequirementState tree requirement) := by
      rfl

end WitnessCells

section CanonicalWitness

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- Backward insertion adds at most the occurrence currently being read. -/
theorem insertEarlier_nodes_subset_insert
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (node : Occurrence Source State Row) :
    (insertEarlier tree node).nodes ⊆ insert node tree.nodes := by
  classical
  intro current hcurrent
  by_cases hnode : node ∈ tree.nodes
  · have hold : current ∈ tree.nodes := by
      simpa [insertEarlier, hnode] using hcurrent
    exact Finset.mem_insert_of_mem hold
  · cases hparent : deepestParent tree node.2 with
    | none =>
        exact Finset.mem_insert_of_mem (by
          simpa [insertEarlier, hnode, hparent] using hcurrent)
    | some parent =>
        simpa [insertEarlier, hnode, hparent, insertNode] using hcurrent

/-- Every final scan node was either already present or occurred in the scan
list. -/
theorem scanBackward_nodes_subset_union
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (history : List (Occurrence Source State Row)) :
    (scanBackward tree history).nodes ⊆ tree.nodes ∪ history.toFinset := by
  classical
  induction history generalizing tree with
  | nil => simp
  | cons node history ih =>
      intro current hcurrent
      have hwhere := ih (tree := insertEarlier tree node) hcurrent
      rcases Finset.mem_union.mp hwhere with hinsert | htail
      · have hupper := insertEarlier_nodes_subset_insert tree node hinsert
        rcases Finset.mem_insert.mp hupper with hnode | hold
        · subst current
          exact Finset.mem_union_right _ (by simp)
        · exact Finset.mem_union_left _ hold
      · exact Finset.mem_union_right _ (by simp [htail])

/-- In a chronologically built witness, an earlier conflicting occurrence is
strictly deeper than a later one. -/
def ChronologicalDepth
    (tree : Witness (Source := Source) (State := State) (Row := Row)) : Prop :=
  ∀ earlier later : Occurrence Source State Row,
    earlier ∈ tree.nodes → later ∈ tree.nodes →
    earlier.1 < later.1 → Conflict earlier.2 later.2 →
    tree.depth later < tree.depth earlier

/-- A singleton occurrence witness has chronological depths. -/
theorem singletonWitness_chronologicalDepth
    (root : Occurrence Source State Row) :
    ChronologicalDepth (singletonWitness root) := by
  intro earlier later hearlier hlater hlt _hconflict
  have he : earlier = root := by
    simpa [singletonWitness] using hearlier
  have hl : later = root := by
    simpa [singletonWitness] using hlater
  subst earlier
  subst later
  exact (Nat.lt_irrefl _ hlt).elim

/-- Inserting an occurrence which is earlier than every current node
preserves chronological depths. -/
theorem insertEarlier_chronologicalDepth
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {node : Occurrence Source State Row}
    (htree : ChronologicalDepth tree)
    (hbefore : ∀ old ∈ tree.nodes, node.1 < old.1) :
    ChronologicalDepth (insertEarlier tree node) := by
  classical
  intro earlier later hearlier hlater hlt hconflict
  by_cases hnode : node ∈ tree.nodes
  · have hearlierOld : earlier ∈ tree.nodes := by
      simpa [insertEarlier, hnode] using hearlier
    have hlaterOld : later ∈ tree.nodes := by
      simpa [insertEarlier, hnode] using hlater
    simpa [insertEarlier, hnode] using
      htree earlier later hearlierOld hlaterOld hlt hconflict
  · cases hparent : deepestParent tree node.2 with
    | none =>
        have hearlierOld : earlier ∈ tree.nodes := by
          simpa [insertEarlier, hnode, hparent] using hearlier
        have hlaterOld : later ∈ tree.nodes := by
          simpa [insertEarlier, hnode, hparent] using hlater
        simpa [insertEarlier, hnode, hparent] using
          htree earlier later hearlierOld hlaterOld hlt hconflict
    | some parent =>
        have hparentSpec := deepestParent_spec hparent
        have hearlierData : earlier = node ∨ earlier ∈ tree.nodes := by
          simpa [insertEarlier, hnode, hparent, insertNode] using hearlier
        have hlaterData : later = node ∨ later ∈ tree.nodes := by
          simpa [insertEarlier, hnode, hparent, insertNode] using hlater
        rcases hearlierData with rfl | hearlierOld
        · rcases hlaterData with rfl | hlaterOld
          · exact (Nat.lt_irrefl _ hlt).elim
          · have hmax : tree.depth later ≤ tree.depth parent :=
              hparentSpec.2.2 later hlaterOld (conflict_symm.mp hconflict)
            have hlaterNe : later ≠ earlier := by
              intro heq
              apply hnode
              simpa [heq] using hlaterOld
            have hdepthLater :
                (insertEarlier tree earlier).depth later = tree.depth later := by
              simp [insertEarlier, hnode, hparent, insertNode, hlaterNe]
            have hdepthEarlier :
                (insertEarlier tree earlier).depth earlier =
                  tree.depth parent + 1 := by
              simp [insertEarlier, hnode, hparent, insertNode]
            rw [hdepthLater, hdepthEarlier]
            omega
        · rcases hlaterData with rfl | hlaterOld
          · have hreverse := hbefore earlier hearlierOld
            exact (Nat.not_lt_of_ge hreverse.le hlt).elim
          · have hold := htree earlier later hearlierOld hlaterOld hlt hconflict
            have hearlierNe : earlier ≠ node := by
              intro heq
              apply hnode
              simpa [heq] using hearlierOld
            have hlaterNe : later ≠ node := by
              intro heq
              apply hnode
              simpa [heq] using hlaterOld
            simpa [insertEarlier, hnode, hparent, insertNode,
              hearlierNe, hlaterNe] using hold

/-- Scanning a strictly decreasing list of earlier occurrence times preserves
chronological depths. -/
theorem scanBackward_chronologicalDepth
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {history : List (Occurrence Source State Row)}
    (htree : ChronologicalDepth tree)
    (hbefore : ∀ node ∈ history, ∀ old ∈ tree.nodes,
      node.1 < old.1)
    (horder : history.Pairwise
      (fun later earlier ↦ earlier.1 < later.1)) :
    ChronologicalDepth (scanBackward tree history) := by
  induction history generalizing tree with
  | nil => simpa using htree
  | cons node history ih =>
      rw [scanBackward_cons]
      apply ih
      · apply insertEarlier_chronologicalDepth htree
        intro old hold
        exact hbefore node (by simp) old hold
      · intro current hcurrent old hold
        have hupper := insertEarlier_nodes_subset_insert tree node hold
        rcases Finset.mem_insert.mp hupper with rfl | holdOld
        · exact (List.pairwise_cons.mp horder).1 current hcurrent
        · exact hbefore current (by simp [hcurrent]) old holdOld
      · exact (List.pairwise_cons.mp horder).2

/-- The list inspected by `witnessAt` is strictly decreasing in occurrence
time. -/
theorem earlierOccurrences_pairwise {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n) :
    (earlierOccurrences history time).Pairwise
      (fun later earlier ↦ earlier.1 < later.1) := by
  rw [earlierOccurrences, List.pairwise_reverse, List.pairwise_ofFn]
  intro i j hij
  simpa using hij

/-- Every occurrence inspected by `witnessAt` is earlier than its singleton
root. -/
theorem earlierOccurrences_before_root {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n) :
    ∀ node ∈ earlierOccurrences history time,
      ∀ old ∈ (singletonWitness (time.1, history time)).nodes,
        node.1 < old.1 := by
  intro node hnode old hold
  have holdEq : old = (time.1, history time) := by
    simpa [singletonWitness] using hold
  subst old
  rw [earlierOccurrences, List.mem_reverse, List.mem_ofFn] at hnode
  obtain ⟨earlier, rfl⟩ := hnode
  exact earlier.2

/-- Canonical history witnesses have depth strictly reversed from time along
every conflicting pair. -/
theorem witnessAt_chronologicalDepth {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n) :
    ChronologicalDepth (witnessAt history time) := by
  apply scanBackward_chronologicalDepth
  · exact singletonWitness_chronologicalDepth _
  · exact earlierOccurrences_before_root history time
  · exact earlierOccurrences_pairwise history time

/-- If an occurrence in a decreasing scan is earlier than, and conflicts
with, a node selected by the final scan, then the earlier occurrence is also
selected.  This is the prefix-closure property of backward witnesses. -/
theorem mem_scanBackward_of_earlier_conflict
    {tree : Witness (Source := Source) (State := State) (Row := Row)}
    {history : List (Occurrence Source State Row)}
    {earlier later : Occurrence Source State Row}
    (hbefore : ∀ node ∈ history, ∀ old ∈ tree.nodes,
      node.1 < old.1)
    (horder : history.Pairwise
      (fun later earlier ↦ earlier.1 < later.1))
    (hearlier : earlier ∈ history)
    (hlater : later ∈ (scanBackward tree history).nodes)
    (htime : earlier.1 < later.1)
    (hconflict : Conflict earlier.2 later.2) :
    earlier ∈ (scanBackward tree history).nodes := by
  induction history generalizing tree with
  | nil => simp at hearlier
  | cons current history ih =>
      rcases List.mem_cons.mp hearlier with hcurrent | hearlierTail
      · subst current
        have hwhere := scanBackward_nodes_subset_union
          (insertEarlier tree earlier) history hlater
        rcases Finset.mem_union.mp hwhere with hinsert | hlaterTail
        · have hupper := insertEarlier_nodes_subset_insert tree earlier hinsert
          rcases Finset.mem_insert.mp hupper with hlaterEq | hlaterOld
          · subst later
            exact (Nat.lt_irrefl _ htime).elim
          · have hinserted : earlier ∈ (insertEarlier tree earlier).nodes :=
              mem_insertEarlier_of_conflict hlaterOld
                (conflict_symm.mp hconflict)
            exact nodes_subset_scanBackward
              (insertEarlier tree earlier) history hinserted
        · have hlaterMem : later ∈ history := by simpa using hlaterTail
          have hreverse := (List.pairwise_cons.mp horder).1 later hlaterMem
          omega
      · rw [scanBackward_cons] at hlater ⊢
        apply ih
        · intro node hnode old hold
          have hupper := insertEarlier_nodes_subset_insert tree current hold
          rcases Finset.mem_insert.mp hupper with rfl | holdOld
          · exact (List.pairwise_cons.mp horder).1 node hnode
          · exact hbefore node (by simp [hnode]) old holdOld
        · exact (List.pairwise_cons.mp horder).2
        · exact hearlierTail
        · exact hlater

/-- Every node of `witnessAt` is an actual history occurrence no later than
the endpoint. -/
theorem witnessAt_node_provenance {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n)
    {node : Occurrence Source State Row}
    (hnode : node ∈ (witnessAt history time).nodes) :
    ∃ occurrence : Fin n,
      occurrence.1 ≤ time.1 ∧ node = (occurrence.1, history occurrence) := by
  have hwhere := scanBackward_nodes_subset_union
    (singletonWitness (time.1, history time))
    (earlierOccurrences history time) hnode
  rcases Finset.mem_union.mp hwhere with hroot | hearlier
  · have hrootEq : node = (time.1, history time) := by
      simpa [singletonWitness] using hroot
    exact ⟨time, le_rfl, hrootEq⟩
  · have hearlierList : node ∈ earlierOccurrences history time := by
      simpa using hearlier
    rw [earlierOccurrences, List.mem_reverse, List.mem_ofFn] at hearlierList
    obtain ⟨earlier, rfl⟩ := hearlierList
    let occurrence : Fin n :=
      ⟨earlier.1, Nat.lt_trans earlier.2 time.2⟩
    exact ⟨occurrence, Nat.le_of_lt earlier.2, rfl⟩

/-- Every earlier history occurrence which conflicts with a selected node is
also a node of the canonical witness.  In particular, occurrences using a
fixed source, or occurrences in a fixed row, form chronological prefixes. -/
theorem witnessAt_mem_of_earlier_conflict {n : Nat}
    (history : Fin n → Label Source State Row) (endpoint : Fin n)
    {earlier later : Fin n}
    (htime : earlier.1 < later.1)
    (hlater : (later.1, history later) ∈
      (witnessAt history endpoint).nodes)
    (hconflict : Conflict (history earlier) (history later)) :
    (earlier.1, history earlier) ∈ (witnessAt history endpoint).nodes := by
  obtain ⟨laterTime, hlaterEndpoint, hlaterEq⟩ :=
    witnessAt_node_provenance history endpoint hlater
  have hlaterTimeEq : laterTime = later := by
    apply Fin.ext
    have := congrArg Prod.fst hlaterEq
    simpa using this.symm
  subst laterTime
  have hearlierEndpoint : earlier.1 < endpoint.1 :=
    lt_of_lt_of_le htime hlaterEndpoint
  apply mem_scanBackward_of_earlier_conflict
      (tree := singletonWitness (endpoint.1, history endpoint))
      (history := earlierOccurrences history endpoint)
      (earlier := (earlier.1, history earlier))
      (later := (later.1, history later))
  · exact earlierOccurrences_before_root history endpoint
  · exact earlierOccurrences_pairwise history endpoint
  · exact mem_earlierOccurrences history hearlierEndpoint
  · exact hlater
  · exact htime
  · exact hconflict

/-- A canonical witness contains at most one node at each occurrence time. -/
theorem witnessAt_time_injective {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n)
    {left right : Occurrence Source State Row}
    (hleft : left ∈ (witnessAt history time).nodes)
    (hright : right ∈ (witnessAt history time).nodes)
    (htime : left.1 = right.1) : left = right := by
  obtain ⟨leftTime, _hleftLe, hleftEq⟩ :=
    witnessAt_node_provenance history time hleft
  obtain ⟨rightTime, _hrightLe, hrightEq⟩ :=
    witnessAt_node_provenance history time hright
  have hfin : leftTime = rightTime := by
    apply Fin.ext
    simpa [hleftEq, hrightEq] using htime
  subst rightTime
  simpa [hleftEq, hrightEq]

/-- Equal depths on conflicting nodes force equality in a canonical witness. -/
theorem witnessAt_eq_of_conflict_of_depth_eq {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n)
    {left right : Occurrence Source State Row}
    (hleft : left ∈ (witnessAt history time).nodes)
    (hright : right ∈ (witnessAt history time).nodes)
    (hconflict : Conflict left.2 right.2)
    (hdepth : (witnessAt history time).depth left =
      (witnessAt history time).depth right) : left = right := by
  by_cases htime : left.1 = right.1
  · exact witnessAt_time_injective history time hleft hright htime
  · rcases lt_or_gt_of_ne htime with hlt | hgt
    · have hstrict := witnessAt_chronologicalDepth history time
        left right hleft hright hlt hconflict
      omega
    · have hstrict := witnessAt_chronologicalDepth history time
        right left hright hleft hgt (conflict_symm.mp hconflict)
      omega

/-- On conflicting nodes of a canonical witness, greater depth is exactly
earlier occurrence time. -/
theorem witnessAt_depth_lt_iff_time_gt {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n)
    {left right : Occurrence Source State Row}
    (hleft : left ∈ (witnessAt history time).nodes)
    (hright : right ∈ (witnessAt history time).nodes)
    (hconflict : Conflict left.2 right.2) :
    (witnessAt history time).depth left <
        (witnessAt history time).depth right ↔
      right.1 < left.1 := by
  constructor
  · intro hdepth
    rcases lt_trichotomy right.1 left.1 with hrightLeft | heq | hleftRight
    · exact hrightLeft
    · have hnodes : left = right :=
        witnessAt_time_injective history time hleft hright heq.symm
      subst right
      exact (Nat.lt_irrefl _ hdepth).elim
    · have hreverse := witnessAt_chronologicalDepth history time
        left right hleft hright hleftRight hconflict
      omega
  · intro hrightLeft
    exact witnessAt_chronologicalDepth history time
      right left hright hleft hrightLeft (conflict_symm.mp hconflict)

/-- The intrinsic same-source cell map is injective for every canonical
history witness. -/
theorem witnessAt_sourceDepthInjective {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n) :
    SourceDepthInjective (witnessAt history time) := by
  intro left right i hleft hright hleftUses hrightUses hdepth
  apply witnessAt_eq_of_conflict_of_depth_eq history time hleft hright
  · exact Or.inr ⟨i, hleftUses, hrightUses⟩
  · exact hdepth

/-- More generally, row equality also makes depth injective, since equal rows
are conflicting labels. -/
theorem witnessAt_rowDepthInjective {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n)
    {left right : Occurrence Source State Row}
    (hleft : left ∈ (witnessAt history time).nodes)
    (hright : right ∈ (witnessAt history time).nodes)
    (hrow : left.2.1 = right.2.1)
    (hdepth : (witnessAt history time).depth left =
      (witnessAt history time).depth right) : left = right := by
  exact witnessAt_eq_of_conflict_of_depth_eq history time hleft hright
    (Or.inl hrow) hdepth

/-- History times strictly before `time` at which source `i` is used. -/
def priorSourceTimes {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n)
    (i : Source) : Finset (Fin n) :=
  Finset.univ.filter fun earlier ↦
    earlier.1 < time.1 ∧ UsesSource (history earlier).2 i

/-- History times strictly before `time` at which row `r` is visited. -/
def priorRowTimes {n : Nat}
    (history : Fin n → Label Source State Row) (time : Fin n)
    (r : Row) : Finset (Fin n) :=
  Finset.univ.filter fun earlier ↦
    earlier.1 < time.1 ∧ (history earlier).1 = r

/-- The intrinsic source rank of a canonical witness node is exactly the
number of earlier uses of that source in the full history.  Prefix closure is
what rules out hidden earlier table reads outside the witness. -/
theorem witnessAt_sourceRank_eq_priorSourceTimes_card {n : Nat}
    (history : Fin n → Label Source State Row) (endpoint time : Fin n)
    (hnode : (time.1, history time) ∈
      (witnessAt history endpoint).nodes)
    {i : Source} (huses : UsesSource (history time).2 i) :
    sourceRank (witnessAt history endpoint) (time.1, history time) i =
      (priorSourceTimes history time i).card := by
  classical
  let occurrence : Fin n → Occurrence Source State Row :=
    fun t ↦ (t.1, history t)
  have hoccurrence : Function.Injective occurrence := by
    intro left right heq
    apply Fin.ext
    exact congrArg Prod.fst heq
  have hsets :
      (priorSourceTimes history time i).image occurrence =
        (witnessAt history endpoint).nodes.filter fun other ↦
          UsesSource other.2.2 i ∧
            (witnessAt history endpoint).depth (time.1, history time) <
              (witnessAt history endpoint).depth other := by
    ext other
    constructor
    · intro hother
      obtain ⟨earlier, hearlier, rfl⟩ := Finset.mem_image.mp hother
      have hearlierData := Finset.mem_filter.mp hearlier
      have hearlierNode : (earlier.1, history earlier) ∈
          (witnessAt history endpoint).nodes := by
        apply witnessAt_mem_of_earlier_conflict history endpoint
          hearlierData.2.1 hnode
        exact Or.inr ⟨i, hearlierData.2.2, huses⟩
      apply Finset.mem_filter.mpr
      refine ⟨hearlierNode, hearlierData.2.2, ?_⟩
      exact witnessAt_chronologicalDepth history endpoint
        (earlier.1, history earlier) (time.1, history time)
        hearlierNode hnode hearlierData.2.1
        (Or.inr ⟨i, hearlierData.2.2, huses⟩)
    · intro hother
      have hotherData := Finset.mem_filter.mp hother
      obtain ⟨otherTime, _hotherLe, hotherEq⟩ :=
        witnessAt_node_provenance history endpoint hotherData.1
      subst other
      have htime : otherTime.1 < time.1 :=
        (witnessAt_depth_lt_iff_time_gt history endpoint
          hnode hotherData.1
          (Or.inr ⟨i, huses, hotherData.2.1⟩)).mp hotherData.2.2
      apply Finset.mem_image.mpr
      refine ⟨otherTime, ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, htime, hotherData.2.1⟩
  unfold sourceRank
  rw [← hsets, Finset.card_image_of_injective _ hoccurrence]

/-- Every intrinsic requirement cell of a canonical witness is the genuine
source pointer index at the corresponding history occurrence. -/
theorem witnessRequirementCell_val_eq_priorSourceTimes_card
    {n h : Nat}
    (history : Fin n → Label Source State Row) (endpoint : Fin n)
    (hcard : (witnessAt history endpoint).nodes.card < h + 1)
    (requirement : WitnessRequirement (witnessAt history endpoint)) :
    ∃ time : Fin n,
      requirement.1.1 = (time.1, history time) ∧
      (witnessRequirementCell (witnessAt history endpoint) hcard
          requirement).2.1 =
        (priorSourceTimes history time requirement.2.1).card := by
  obtain ⟨time, _htime, hnode⟩ :=
    witnessAt_node_provenance history endpoint requirement.1.2
  refine ⟨time, hnode, ?_⟩
  have huses : UsesSource (history time).2 requirement.2.1 := by
    unfold UsesSource
    have hrequired :
        (history time).2 requirement.2.1 = some requirement.2.2.1 := by
      simpa only [hnode] using requirement.2.2.2
    rw [hrequired]
    simp
  have hrank := witnessAt_sourceRank_eq_priorSourceTimes_card
    history endpoint time (by simpa [hnode] using requirement.1.2) huses
  simpa [witnessRequirementCell, hnode] using hrank

/-- Intrinsic row rank, parallel to `sourceRank`. -/
def rowRank
    (tree : Witness (Source := Source) (State := State) (Row := Row))
    (node : Occurrence Source State Row) (r : Row) : Nat :=
  (tree.nodes.filter fun other ↦
    other.2.1 = r ∧ tree.depth node < tree.depth other).card

/-- The intrinsic row rank of a canonical witness node is exactly the number
of earlier visits to that row in the full history. -/
theorem witnessAt_rowRank_eq_priorRowTimes_card {n : Nat}
    (history : Fin n → Label Source State Row) (endpoint time : Fin n)
    (hnode : (time.1, history time) ∈
      (witnessAt history endpoint).nodes) :
    rowRank (witnessAt history endpoint) (time.1, history time)
        (history time).1 =
      (priorRowTimes history time (history time).1).card := by
  classical
  let occurrence : Fin n → Occurrence Source State Row :=
    fun t ↦ (t.1, history t)
  have hoccurrence : Function.Injective occurrence := by
    intro left right heq
    apply Fin.ext
    exact congrArg Prod.fst heq
  have hsets :
      (priorRowTimes history time (history time).1).image occurrence =
        (witnessAt history endpoint).nodes.filter fun other ↦
          other.2.1 = (history time).1 ∧
            (witnessAt history endpoint).depth (time.1, history time) <
              (witnessAt history endpoint).depth other := by
    ext other
    constructor
    · intro hother
      obtain ⟨earlier, hearlier, rfl⟩ := Finset.mem_image.mp hother
      have hearlierData := Finset.mem_filter.mp hearlier
      have hearlierNode : (earlier.1, history earlier) ∈
          (witnessAt history endpoint).nodes := by
        apply witnessAt_mem_of_earlier_conflict history endpoint
          hearlierData.2.1 hnode
        exact Or.inl hearlierData.2.2
      apply Finset.mem_filter.mpr
      refine ⟨hearlierNode, hearlierData.2.2, ?_⟩
      exact witnessAt_chronologicalDepth history endpoint
        (earlier.1, history earlier) (time.1, history time)
        hearlierNode hnode hearlierData.2.1 (Or.inl hearlierData.2.2)
    · intro hother
      have hotherData := Finset.mem_filter.mp hother
      obtain ⟨otherTime, _hotherLe, hotherEq⟩ :=
        witnessAt_node_provenance history endpoint hotherData.1
      subst other
      have htime : otherTime.1 < time.1 :=
        (witnessAt_depth_lt_iff_time_gt history endpoint
          hnode hotherData.1
          (Or.inl hotherData.2.1.symm)).mp hotherData.2.2
      apply Finset.mem_image.mpr
      refine ⟨otherTime, ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, htime, hotherData.2.1⟩
  unfold rowRank
  rw [← hsets, Finset.card_image_of_injective _ hoccurrence]

end CanonicalWitness

end

end WeightedEdgeColoring.FinitePartialResamplingWitnessCylinder
