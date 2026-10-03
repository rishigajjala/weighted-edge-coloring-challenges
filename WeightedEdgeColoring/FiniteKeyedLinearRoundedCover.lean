import WeightedEdgeColoring.PreCoverLinearGrouping
import WeightedEdgeColoring.FiniteDemandHarmonicSaturation

/-!
# Keyed linear grouping as a finite demand cover

Each active key cell is sorted by decreasing weight and divided into `M`
consecutive groups.  Group zero is exceptional.  Every nonempty later group
is one item type of a rounded bin-packing instance; its demand is the size of
the group and its weight is the weight of the first item in the group.

A later rank is sent one group to the left.  These predecessor maps combine
to one global injection.  Therefore replacing every original pattern by the
counts of predecessor images gives a feasible rounded pattern.  An exact
unit-demand cover of the original instance consequently induces a demand
cover of the rounded instance with exactly the same cost.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance
namespace KeyedLinearRoundedCover

noncomputable section

universe u v

variable {B : BinPackingInstance.{u}}
variable {κ : Type v} [Fintype κ] [DecidableEq κ]

/-- One key cell of the original finite item type. -/
def cell (key : B.Item → κ) (a : κ) : Finset B.Item :=
  Finset.univ.filter fun i ↦ key i = a

/-- Width of the linear groups in one key cell. -/
def width (key : B.Item → κ) (M : ℕ) (a : κ) : ℕ :=
  linearGroupSize (cell key a).card M

/-- The group with number `r+1`.  Thus `r : Fin (M-1)` parametrizes exactly
the possible later groups `1,...,M-1`. -/
def laterIndices (key : B.Item → κ) (M : ℕ) (a : κ)
    (r : Fin (M - 1)) : Finset (Fin (cell key a).card) :=
  linearGroupIndices (cell key a).card (width key M a)
    (r.1 * width key M a + width key M a)

/-- A rounded coordinate is a nonempty later group in an active cell. -/
def IsRoundedItem (key : B.Item → κ) (M : ℕ)
    (z : κ × Fin (M - 1)) : Prop :=
  M ≤ (cell key z.1).card ∧ (laterIndices key M z.1 z.2).Nonempty

/-- Item type of the rounded bin-packing instance. -/
abbrev RoundedItem (key : B.Item → κ) (M : ℕ) :=
  {z : κ × Fin (M - 1) // IsRoundedItem key M z}

noncomputable instance instFintypeRoundedItem
    (key : B.Item → κ) (M : ℕ) : Fintype (RoundedItem key M) :=
  Fintype.ofFinite _

noncomputable instance instDecidableEqRoundedItem
    (key : B.Item → κ) (M : ℕ) : DecidableEq (RoundedItem key M) :=
  Classical.decEq _

variable (key : B.Item → κ) (M : ℕ)

namespace RoundedItem

abbrev keyValue (z : RoundedItem key M) : κ := z.1.1

abbrev number (z : RoundedItem key M) : Fin (M - 1) := z.1.2

theorem active (z : RoundedItem key M) :
    M ≤ (cell key z.keyValue).card := z.2.1

theorem nonempty (z : RoundedItem key M) :
    (laterIndices key M z.keyValue z.number).Nonempty := z.2.2

/-- A chosen rank in the nonempty later group.  It is used only to supply
the bound needed to construct the group's first rank. -/
def witness (z : RoundedItem key M) :
    {i : Fin (cell key z.keyValue).card //
      i ∈ laterIndices key M z.keyValue z.number} :=
  ⟨z.nonempty.choose, z.nonempty.choose_spec⟩

/-- The first rank of a rounded group. -/
def firstRank (z : RoundedItem key M) : Fin (cell key z.keyValue).card :=
  linearGroupRepresentative (cell key z.keyValue).card
    (width key M z.keyValue) (z.number.1 * width key M z.keyValue) z.witness

@[simp] theorem firstRank_val (z : RoundedItem key M) :
    z.firstRank.1 = z.number.1 * width key M z.keyValue +
      width key M z.keyValue := by
  rfl

/-- The original item at the first rank of a rounded group. -/
def representative (z : RoundedItem key M) : B.Item :=
  finiteCellItem (cell key z.keyValue) B.weight z.firstRank

theorem representative_mem_cell (z : RoundedItem key M) :
    z.representative ∈ cell key z.keyValue :=
  finiteCellItem_mem (cell key z.keyValue) B.weight z.firstRank

@[simp] theorem key_representative (z : RoundedItem key M) :
    key z.representative = z.keyValue := by
  exact (Finset.mem_filter.mp z.representative_mem_cell).2

theorem width_pos (hM : 0 < M) (z : RoundedItem key M) :
    0 < width key M z.keyValue := by
  apply linearGroupSize_pos
  · exact lt_of_lt_of_le hM z.active
  · exact hM

end RoundedItem

/-- Rounded weight: the first, and hence heaviest, item in the group. -/
def roundedWeight (z : RoundedItem key M) : ℝ :=
  B.weight z.representative

/-- The finite rounded bin-packing instance. -/
def roundedInstance : BinPackingInstance where
  Item := RoundedItem (B := B) key M
  instFintypeItem := inferInstance
  instDecidableEqItem := Classical.decEq _
  weight := fun z ↦ roundedWeight (B := B) key M z
  weight_pos := by
    intro z
    simpa [roundedWeight] using
      B.weight_pos (RoundedItem.representative (B := B) key M z)
  weight_le_one := by
    intro z
    simpa [roundedWeight] using
      B.weight_le_one (RoundedItem.representative (B := B) key M z)

/-- Demand of a rounded coordinate. -/
def roundedDemand (z : (roundedInstance key M).Item) : ℕ :=
  (laterIndices key M z.keyValue z.number).card

/-- One actual rank belonging to one rounded coordinate. -/
abbrev TargetOccurrence :=
  Σ z : RoundedItem key M,
    {i : Fin (cell key z.keyValue).card //
      i ∈ laterIndices key M z.keyValue z.number}

/-- The original item at a target occurrence. -/
def targetItem (o : TargetOccurrence key M) : B.Item :=
  finiteCellItem (cell key o.1.keyValue) B.weight o.2.1

/-- Move a target rank one group to the left. -/
def predecessorRank (o : TargetOccurrence key M) :
    {i : Fin (cell key o.1.keyValue).card //
      i ∈ linearGroupIndices (cell key o.1.keyValue).card
        (width key M o.1.keyValue)
        (o.1.number.1 * width key M o.1.keyValue)} :=
  previousLinearGroupEmbedding (cell key o.1.keyValue).card
    (width key M o.1.keyValue)
    (o.1.number.1 * width key M o.1.keyValue) o.2

/-- Original predecessor item used to pay for a target occurrence. -/
def predecessorItem (o : TargetOccurrence key M) : B.Item :=
  finiteCellItem (cell key o.1.keyValue) B.weight (predecessorRank key M o).1

theorem predecessorItem_mem_cell (o : TargetOccurrence key M) :
    predecessorItem key M o ∈ cell key o.1.keyValue :=
  finiteCellItem_mem (cell key o.1.keyValue) B.weight
    (predecessorRank key M o).1

@[simp] theorem key_predecessorItem (o : TargetOccurrence key M) :
    key (predecessorItem key M o) = o.1.keyValue := by
  exact (Finset.mem_filter.mp (predecessorItem_mem_cell key M o)).2

@[simp] theorem key_targetItem (o : TargetOccurrence key M) :
    key (targetItem key M o) = o.1.keyValue := by
  exact (Finset.mem_filter.mp
    (finiteCellItem_mem (cell key o.1.keyValue) B.weight o.2.1)).2

/-- Later-group intervals belonging to distinct rounded coordinates are
disjoint.  Hence target occurrences name distinct original items. -/
theorem targetItem_injective :
    Function.Injective (targetItem key M) := by
  rintro ⟨⟨⟨a, r⟩, ha⟩, ⟨i, hi⟩⟩ ⟨⟨⟨b, s⟩, hb⟩, ⟨j, hj⟩⟩ hxy
  have hab : a = b := by
    have hka : key (targetItem key M
        ⟨⟨⟨a, r⟩, ha⟩, ⟨i, hi⟩⟩) = a :=
      key_targetItem key M _
    have hkb : key (targetItem key M
        ⟨⟨⟨b, s⟩, hb⟩, ⟨j, hj⟩⟩) = b :=
      key_targetItem key M _
    rw [hxy] at hka
    exact hka.symm.trans hkb
  subst b
  let k : ℕ := width key M a
  have hijFin : i = j := by
    apply finiteCellItem_injective (cell key a) B.weight
    simpa [targetItem] using hxy
  have hrbounds :
      r.1 * k + k ≤ i.1 ∧ i.1 < r.1 * k + k + k := by
    simpa [laterIndices, k] using (mem_linearGroupIndices.mp hi)
  have hsbounds :
      s.1 * k + k ≤ j.1 ∧ j.1 < s.1 * k + k + k := by
    simpa [laterIndices, k] using (mem_linearGroupIndices.mp hj)
  have hval : i.1 = j.1 := congrArg Fin.val hijFin
  have hrs : r.1 = s.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hrs | hsr
    · have hbase : r.1 * k + k ≤ s.1 * k := by
        simpa [Nat.add_mul] using
          (Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr hrs))
      have hmul : r.1 * k + k + k ≤ s.1 * k + k :=
        Nat.add_le_add_right hbase k
      omega
    · have hbase : s.1 * k + k ≤ r.1 * k := by
        simpa [Nat.add_mul] using
          (Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr hsr))
      have hmul : s.1 * k + k + k ≤ r.1 * k + k :=
        Nat.add_le_add_right hbase k
      omega
  have hrsFin : r = s := Fin.ext hrs
  subst s
  cases hijFin
  rfl

/-- Every actual target item is no heavier than its rounded representative. -/
theorem targetItem_weight_le_roundedWeight (o : TargetOccurrence key M) :
    B.weight (targetItem key M o) ≤ roundedWeight key M o.1 := by
  apply finiteCellItem_weight_antitone
  exact (mem_linearGroupIndices.mp o.2.2).1

/-- The rounded representative is no heavier than the predecessor item. -/
theorem roundedWeight_le_predecessorItem
    (hM : 0 < M) (o : TargetOccurrence key M) :
    roundedWeight key M o.1 ≤ B.weight (predecessorItem key M o) := by
  have h := roundedFiniteCellWeight_le_previous
    (cell key o.1.keyValue) B.weight (o.1.width_pos key M hM) o.2
  simpa [roundedWeight, RoundedItem.representative, RoundedItem.firstRank,
    predecessorItem, predecessorRank] using h

/-- If the key fixes harmonic charge, rounding preserves the harmonic charge
of every target item exactly. -/
theorem harmonicCharge_targetItem_eq_roundedWeight
    (hkeyCharge : ∀ i j : B.Item, key i = key j →
      harmonicCharge (B.weight i) = harmonicCharge (B.weight j))
    (o : TargetOccurrence key M) :
    harmonicCharge (B.weight (targetItem key M o)) =
      harmonicCharge (roundedWeight key M o.1) := by
  exact hkeyCharge _ _ ((key_targetItem key M o).trans
    (RoundedItem.key_representative key M o.1).symm)

/-- The predecessor intervals of distinct later groups and distinct key
cells are disjoint.  Hence all predecessor items are globally distinct. -/
theorem predecessorItem_injective (hM : 0 < M) :
    Function.Injective (predecessorItem key M) := by
  rintro ⟨⟨⟨a, r⟩, ha⟩, ⟨i, hi⟩⟩ ⟨⟨⟨b, s⟩, hb⟩, ⟨j, hj⟩⟩ hxy
  have hab : a = b := by
    have hka : key (predecessorItem key M
        ⟨⟨⟨a, r⟩, ha⟩, ⟨i, hi⟩⟩) = a :=
      key_predecessorItem key M _
    have hkb : key (predecessorItem key M
        ⟨⟨⟨b, s⟩, hb⟩, ⟨j, hj⟩⟩) = b :=
      key_predecessorItem key M _
    rw [hxy] at hka
    exact hka.symm.trans hkb
  subst b
  let k : ℕ := width key M a
  have hpredFin :
      (previousLinearGroupEmbedding (cell key a).card k (r.1 * k)
        ⟨i, hi⟩).1 =
      (previousLinearGroupEmbedding (cell key a).card k (s.1 * k)
        ⟨j, hj⟩).1 := by
    apply finiteCellItem_injective (cell key a) B.weight
    simpa [predecessorItem, predecessorRank, k] using hxy
  have hrmem :=
    (previousLinearGroupEmbedding (cell key a).card k (r.1 * k)
      ⟨i, hi⟩).2
  have hsmem :=
    (previousLinearGroupEmbedding (cell key a).card k (s.1 * k)
      ⟨j, hj⟩).2
  have hrbounds := mem_linearGroupIndices.mp hrmem
  have hsbounds := mem_linearGroupIndices.mp hsmem
  have hval := congrArg Fin.val hpredFin
  have hk : 0 < k := by
    dsimp [k]
    exact RoundedItem.width_pos key M hM ⟨⟨a, r⟩, ha⟩
  have hrs : r.1 = s.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hrs | hsr
    · have hmul : (r.1 + 1) * k ≤ s.1 * k := by
        exact Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr hrs)
      have hrupper :
          (previousLinearGroupEmbedding (cell key a).card k (r.1 * k)
            ⟨i, hi⟩).1.1 < (r.1 + 1) * k := by
        simpa [Nat.succ_mul] using hrbounds.2
      omega
    · have hmul : (s.1 + 1) * k ≤ r.1 * k := by
        exact Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr hsr)
      have hsupper :
          (previousLinearGroupEmbedding (cell key a).card k (s.1 * k)
            ⟨j, hj⟩).1.1 < (s.1 + 1) * k := by
        simpa [Nat.succ_mul] using hsbounds.2
      omega
  have hrsFin : r = s := Fin.ext hrs
  subst s
  have hij : (⟨i, hi⟩ :
      {t : Fin (cell key a).card //
        t ∈ linearGroupIndices (cell key a).card k
          (r.1 * k + k)}) = ⟨j, hj⟩ := by
    apply (previousLinearGroupEmbedding (cell key a).card k
      (r.1 * k)).injective
    exact Subtype.ext hpredFin
  cases hij
  rfl

/-- Multiplicity of one rounded coordinate in the image of an original
pattern: sum the multiplicities of all predecessor items. -/
def roundedMultiplicity (p : B.Pattern)
    (z : (roundedInstance key M).Item) : ℕ :=
  ∑ i : {i : Fin (cell key z.keyValue).card //
      i ∈ laterIndices key M z.keyValue z.number},
    p.multiplicity (predecessorItem key M ⟨z, i⟩)

/-- The rounded image of one original pattern. -/
def roundedPattern (hM : 0 < M) (p : B.Pattern) :
    (roundedInstance key M).Pattern where
  multiplicity := roundedMultiplicity key M p
  capacity := by
    calc
      (∑ z : (roundedInstance key M).Item,
          (roundedMultiplicity key M p z : ℝ) * roundedWeight key M z) =
          ∑ z : RoundedItem key M,
            ∑ i : {i : Fin (cell key z.keyValue).card //
              i ∈ laterIndices key M z.keyValue z.number},
              (p.multiplicity (predecessorItem key M ⟨z, i⟩) : ℝ) *
                roundedWeight key M z := by
        apply Finset.sum_congr rfl
        intro z _hz
        rw [roundedMultiplicity, Nat.cast_sum]
        rw [Finset.sum_mul]
      _ = ∑ o : TargetOccurrence key M,
          (p.multiplicity (predecessorItem key M o) : ℝ) *
            roundedWeight key M o.1 := by
        exact (Fintype.sum_sigma (fun o : TargetOccurrence key M ↦
          (p.multiplicity (predecessorItem key M o) : ℝ) *
            roundedWeight key M o.1)).symm
      _ ≤ ∑ o : TargetOccurrence key M,
          (p.multiplicity (predecessorItem key M o) : ℝ) *
            B.weight (predecessorItem key M o) := by
        apply Finset.sum_le_sum
        intro o _ho
        exact mul_le_mul_of_nonneg_left
          (roundedWeight_le_predecessorItem key M hM o) (Nat.cast_nonneg _)
      _ ≤ ∑ i : B.Item,
          (p.multiplicity i : ℝ) * B.weight i := by
        let image : Finset B.Item :=
          (Finset.univ : Finset (TargetOccurrence key M)).image
            (predecessorItem key M)
        calc
          _ = ∑ i ∈ image, (p.multiplicity i : ℝ) * B.weight i := by
            unfold image
            rw [Finset.sum_image (predecessorItem_injective key M hM).injOn]
          _ ≤ ∑ i : B.Item,
              (p.multiplicity i : ℝ) * B.weight i := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_univ image) (by
                intro i _hi _hnot
                exact mul_nonneg (Nat.cast_nonneg _) (B.weight_nonneg i))
      _ ≤ 1 := p.capacity

/-- The rounded coordinate is covered exactly by the pushed-forward exact
unit-demand cover. -/
theorem rounded_coverage_eq
    (C : B.ExactDemandPatternCover (fun _ ↦ 1))
    (hM : 0 < M) (z : (roundedInstance key M).Item) :
    (∑ p : B.Pattern,
      C.coeff p * (((roundedPattern key M hM p).multiplicity z : ℕ) : ℝ)) =
      roundedDemand key M z := by
  change (∑ p : B.Pattern,
    C.coeff p * (roundedMultiplicity key M p z : ℝ)) =
      roundedDemand key M z
  simp only [roundedMultiplicity]
  push_cast
  calc
    (∑ p : B.Pattern,
        C.coeff p *
          ∑ x : {i : Fin (cell key z.keyValue).card //
            i ∈ laterIndices key M z.keyValue z.number},
            (p.multiplicity (predecessorItem key M ⟨z, x⟩) : ℝ)) =
        ∑ p : B.Pattern,
          ∑ x : {i : Fin (cell key z.keyValue).card //
            i ∈ laterIndices key M z.keyValue z.number},
            C.coeff p *
              (p.multiplicity (predecessorItem key M ⟨z, x⟩) : ℝ) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.mul_sum]
    _ = ∑ x : {i : Fin (cell key z.keyValue).card //
        i ∈ laterIndices key M z.keyValue z.number},
      ∑ p : B.Pattern,
        C.coeff p *
          (p.multiplicity (predecessorItem key M ⟨z, x⟩) : ℝ) := by
      rw [Finset.sum_comm]
    _ = ∑ _x : {i : Fin (cell key z.keyValue).card //
        i ∈ laterIndices key M z.keyValue z.number},
        (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro x _hx
      simpa using C.sum_coeff_mul_multiplicity_eq
        (predecessorItem key M ⟨z, x⟩)
    _ = roundedDemand key M z := by
      simp [roundedDemand]

/-- Push an exact unit-demand cover through keyed linear grouping. -/
def toDemandPatternCover
    (C : B.ExactDemandPatternCover (fun _ ↦ 1)) (hM : 0 < M) :
    (roundedInstance key M).DemandPatternCover (roundedDemand key M) :=
  DemandPatternCover.ofFinitePatterns (roundedPattern key M hM) C.coeff
    C.coeff_nonneg (by
      intro z
      exact (rounded_coverage_eq key M C hM z).ge)

/-- The aggregated coefficients of the pushed-forward cover attain the
rounded demand exactly. -/
theorem toDemandPatternCover_coverage_eq
    (C : B.ExactDemandPatternCover (fun _ ↦ 1))
    (hM : 0 < M) (z : (roundedInstance key M).Item) :
    (∑ q : (roundedInstance key M).Pattern,
      (toDemandPatternCover key M C hM).coeff q *
        (q.multiplicity z : ℝ)) =
      roundedDemand key M z := by
  classical
  rw [← rounded_coverage_eq key M C hM z]
  rw [← Finsupp.sum_fintype (toDemandPatternCover key M C hM).coeff
    (fun q c ↦ c * (q.multiplicity z : ℝ)) (by simp)]
  change
    ((∑ p : B.Pattern,
      Finsupp.single (roundedPattern key M hM p) (C.coeff p)).sum
        (fun q c ↦ c * (q.multiplicity z : ℝ))) =
      ∑ p : B.Pattern,
        C.coeff p *
          ((roundedPattern key M hM p).multiplicity z : ℝ)
  rw [← Finsupp.sum_finset_sum_index]
  · simp
  · intro q
    simp
  · intro q c e
    simp [add_mul]

/-- Saturating the pushed-forward cover still attains every rounded demand
exactly. -/
theorem harmonicSaturate_toDemandPatternCover_coverage_eq
    (C : B.ExactDemandPatternCover (fun _ ↦ 1))
    (hM : 0 < M) (z : (roundedInstance key M).Item) :
    (∑ q : (roundedInstance key M).Pattern,
      ((toDemandPatternCover key M C hM).harmonicSaturate.coeff q) *
        (q.multiplicity z : ℝ)) =
      roundedDemand key M z := by
  rw [(toDemandPatternCover key M C hM).harmonicSaturate_coverage_eq z]
  exact toDemandPatternCover_coverage_eq key M C hM z

/-- Consequently, all full packets obtained by flooring the saturated
cover can be assigned to distinct target occurrences of their coordinates. -/
theorem harmonicSaturate_toDemandPatternCover_floorCoveredDemand_le
    (C : B.ExactDemandPatternCover (fun _ ↦ 1))
    (hM : 0 < M) (z : (roundedInstance key M).Item) :
    (toDemandPatternCover key M C hM).harmonicSaturate.floorCoveredDemand z ≤
      roundedDemand key M z := by
  have hreal :
      ((toDemandPatternCover key M C hM).harmonicSaturate.floorCoveredDemand z : ℝ) ≤
        (roundedDemand key M z : ℝ) := by
    rw [DemandPatternCover.floorCoveredDemand, Nat.cast_sum]
    push_cast
    calc
      (∑ q : (roundedInstance key M).Pattern,
          (Nat.floor
            ((toDemandPatternCover key M C hM).harmonicSaturate.coeff q) : ℝ) *
            (q.multiplicity z : ℝ)) ≤
          ∑ q : (roundedInstance key M).Pattern,
            (toDemandPatternCover key M C hM).harmonicSaturate.coeff q *
              (q.multiplicity z : ℝ) := by
        apply Finset.sum_le_sum
        intro q _hq
        exact mul_le_mul_of_nonneg_right
          (Nat.floor_le
            ((toDemandPatternCover key M C hM).harmonicSaturate.coeff_nonneg q))
          (Nat.cast_nonneg _)
      _ = roundedDemand key M z :=
        harmonicSaturate_toDemandPatternCover_coverage_eq key M C hM z
  exact_mod_cast hreal

/-- Pushing the cover forward neither loses nor creates fractional cost. -/
@[simp] theorem toDemandPatternCover_cost
    (C : B.ExactDemandPatternCover (fun _ ↦ 1)) (hM : 0 < M) :
    (toDemandPatternCover key M C hM).cost = C.cost := by
  rw [toDemandPatternCover, DemandPatternCover.ofFinitePatterns_cost]
  exact C.sum_coeff_eq_cost

end

end KeyedLinearRoundedCover
end BinPackingInstance
end WeightedEdgeColoring

#print axioms WeightedEdgeColoring.BinPackingInstance.KeyedLinearRoundedCover.predecessorItem_injective
#print axioms WeightedEdgeColoring.BinPackingInstance.KeyedLinearRoundedCover.targetItem_injective
#print axioms WeightedEdgeColoring.BinPackingInstance.KeyedLinearRoundedCover.roundedPattern
#print axioms WeightedEdgeColoring.BinPackingInstance.KeyedLinearRoundedCover.toDemandPatternCover_coverage_eq
#print axioms WeightedEdgeColoring.BinPackingInstance.KeyedLinearRoundedCover.harmonicSaturate_toDemandPatternCover_coverage_eq
#print axioms WeightedEdgeColoring.BinPackingInstance.KeyedLinearRoundedCover.harmonicSaturate_toDemandPatternCover_floorCoveredDemand_le
#print axioms WeightedEdgeColoring.BinPackingInstance.KeyedLinearRoundedCover.toDemandPatternCover_cost
