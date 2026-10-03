import WeightedEdgeColoring.BPGeneralFiniteTwoBagExtraction
import WeightedEdgeColoring.FiniteFractionalPatternCover
import WeightedEdgeColoring.FiniteExactDemandPatternCover

/-!
# Operational separated pattern covers

The numerical separated costs in `FiniteTwoBagJointPacking` are realized here
by genuine finite-support fractional pattern covers.  The presentation keeps
the item multiplicities carried by each joint bin and assumes that the joint
mass covers both collections.  Pair-piece and nonheavy-bin patterns are then
written explicitly.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u v w x

variable (A : BinPackingInstance.{u}) (B : BinPackingInstance.{v})
variable {ι : Type w} {κ : Type x}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A joint finite packing whose bins retain the item multiplicities from
the two collections. -/
structure FiniteTwoBagPatternPresentation where
  packing : FiniteTwoBagJointPacking (ι := ι) (κ := κ)
  firstMultiplicity : ι → A.Item → ℕ
  secondMultiplicity : ι → B.Item → ℕ
  firstWeight_eq : ∀ i,
    (∑ a : A.Item, (firstMultiplicity i a : ℝ) * A.weight a) =
      packing.firstWeight i
  secondWeight_eq : ∀ i,
    (∑ b : B.Item, (secondMultiplicity i b : ℝ) * B.weight b) =
      packing.secondWeight i
  covers_first : ∀ a : A.Item,
    1 ≤ ∑ i : ι, packing.mass i * firstMultiplicity i a
  covers_second : ∀ b : B.Item,
    1 ≤ ∑ i : ι, packing.mass i * secondMultiplicity i b

namespace FiniteTwoBagPatternPresentation

variable {A B} (D : FiniteTwoBagPatternPresentation A B (ι := ι) (κ := κ))

abbrev P := D.packing

private def mkPattern (mult : A.Item → ℕ)
    (h : ∑ a : A.Item, (mult a : ℝ) * A.weight a ≤ 1) : A.Pattern :=
  ⟨mult, h⟩

private def firstRestriction (i : ι) : A.Pattern :=
  mkPattern (fun a ↦ D.firstMultiplicity i a) (by
    rw [D.firstWeight_eq]
    have hcap := D.P.capacity i
    have hnonneg := D.P.secondWeight_nonneg i
    linarith)

private def secondRestriction (i : ι) : B.Pattern :=
  mkPattern (A := B) (fun b ↦ D.secondMultiplicity i b) (by
    rw [D.secondWeight_eq]
    have hcap := D.P.capacity i
    have hnonneg := D.P.firstWeight_nonneg i
    linarith)

private def firstDouble (i : ι) (h : 2 * D.P.firstWeight i ≤ 1) : A.Pattern :=
  mkPattern (fun a ↦ 2 * D.firstMultiplicity i a) (by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      (∑ a : A.Item, 2 * (D.firstMultiplicity i a : ℝ) * A.weight a) =
          2 * ∑ a : A.Item,
            (D.firstMultiplicity i a : ℝ) * A.weight a := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
      _ = 2 * D.P.firstWeight i := by rw [D.firstWeight_eq]
      _ ≤ 1 := h)

private def secondDouble (i : ι) (h : 2 * D.P.secondWeight i ≤ 1) : B.Pattern :=
  mkPattern (A := B) (fun b ↦ 2 * D.secondMultiplicity i b) (by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      (∑ b : B.Item, 2 * (D.secondMultiplicity i b : ℝ) * B.weight b) =
          2 * ∑ b : B.Item,
            (D.secondMultiplicity i b : ℝ) * B.weight b := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _hb
        ring
      _ = 2 * D.P.secondWeight i := by rw [D.secondWeight_eq]
      _ ≤ 1 := h)

private def firstCombined (i j : ι)
    (h : D.P.firstWeight i + D.P.firstWeight j ≤ 1) : A.Pattern :=
  mkPattern (fun a ↦ D.firstMultiplicity i a + D.firstMultiplicity j a) (by
    simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib]
    rw [D.firstWeight_eq, D.firstWeight_eq]
    exact h)

private def secondCombined (i j : ι)
    (h : D.P.secondWeight i + D.P.secondWeight j ≤ 1) : B.Pattern :=
  mkPattern (A := B)
    (fun b ↦ D.secondMultiplicity i b + D.secondMultiplicity j b) (by
      simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib]
      rw [D.secondWeight_eq, D.secondWeight_eq]
      exact h)

private def zeroPattern : A.Pattern :=
  mkPattern (fun _ ↦ 0) (by simp)

/-- Atoms used by the first separated cover: unpaired first-heavy pieces,
two slots for every pair piece, and doubled nonheavy bins. -/
abbrev FirstAtom :=
  {i : ι // i ∈ D.P.firstHeavyBins} ⊕
    ((κ × Fin 2) ⊕ {i : ι // i ∈ D.P.nonheavyBins})

/-- Atoms used by the second separated cover. -/
abbrev SecondAtom := D.FirstAtom

private def firstAtomMass : D.FirstAtom → ℝ
  | Sum.inl i => D.P.mass i.1 - D.P.leftUse i.1
  | Sum.inr (Sum.inl (k, slot)) =>
      if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k) then
        if slot.1 = 0 then D.P.pairMass k else 0
      else if slot.1 = 0 then D.P.pairMass k else D.P.pairMass k / 2
  | Sum.inr (Sum.inr i) => D.P.mass i.1 / 2

private def secondAtomMass : D.SecondAtom → ℝ
  | Sum.inl i => (D.P.mass i.1 - D.P.leftUse i.1) / 2
  | Sum.inr (Sum.inl (k, slot)) =>
      if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k) then
        if slot.1 = 0 then D.P.pairMass k else D.P.pairMass k / 2
      else if slot.1 = 0 then D.P.pairMass k else 0
  | Sum.inr (Sum.inr i) => D.P.mass i.1 / 2

private def firstAtomPattern : D.FirstAtom → A.Pattern
  | Sum.inl i => D.firstRestriction i.1
  | Sum.inr (Sum.inl (k, slot)) => by
      by_cases h : D.P.firstWeight (D.P.left k) ≤
          D.P.secondWeight (D.P.right k)
      · by_cases hs : slot.1 = 0
        · exact D.firstCombined (D.P.left k) (D.P.right k)
            (D.P.first_packets_fit_of_combined k h)
        · exact zeroPattern (A := A)
      · by_cases hs : slot.1 = 0
        · exact D.firstRestriction (D.P.left k)
        · exact D.firstDouble (D.P.right k) (by
            have hcap := D.P.capacity (D.P.right k)
            have hheavy := D.P.right_heavy k
            linarith)
  | Sum.inr (Sum.inr i) =>
      D.firstDouble i.1 (D.P.doubled_weights_fit_of_mem_nonheavy i.2).1

private def secondAtomPattern : D.SecondAtom → B.Pattern
  | Sum.inl i => D.secondDouble i.1 (by
      have hcap := D.P.capacity i.1
      have hheavy := (Finset.mem_filter.mp i.2).2
      linarith)
  | Sum.inr (Sum.inl (k, slot)) => by
      by_cases h : D.P.firstWeight (D.P.left k) ≤
          D.P.secondWeight (D.P.right k)
      · by_cases hs : slot.1 = 0
        · exact D.secondRestriction (D.P.right k)
        · exact D.secondDouble (D.P.left k) (by
            have hcap := D.P.capacity (D.P.left k)
            have hheavy := D.P.left_heavy k
            linarith)
      · by_cases hs : slot.1 = 0
        · exact D.secondCombined (D.P.left k) (D.P.right k)
            (D.P.second_packets_fit_of_not_combined k h)
        · exact zeroPattern (A := B)
  | Sum.inr (Sum.inr i) =>
      D.secondDouble i.1 (D.P.doubled_weights_fit_of_mem_nonheavy i.2).2

@[simp] private theorem firstAtomPattern_unpaired_mult
    (i : {i : ι // i ∈ D.P.firstHeavyBins}) (a : A.Item) :
    (D.firstAtomPattern (Sum.inl i)).multiplicity a =
      D.firstMultiplicity i.1 a := rfl

@[simp] private theorem firstAtomPattern_nonheavy_mult
    (i : {i : ι // i ∈ D.P.nonheavyBins}) (a : A.Item) :
    (D.firstAtomPattern (Sum.inr (Sum.inr i))).multiplicity a =
      2 * D.firstMultiplicity i.1 a := rfl

@[simp] private theorem firstAtomPattern_pair_zero_mult (k : κ) (a : A.Item) :
    (D.firstAtomPattern (Sum.inr (Sum.inl (k, (0 : Fin 2))))).multiplicity a =
      if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
      then D.firstMultiplicity (D.P.left k) a +
        D.firstMultiplicity (D.P.right k) a
      else D.firstMultiplicity (D.P.left k) a := by
  by_cases h : D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
  · simp [firstAtomPattern, firstCombined, mkPattern, h]
  · simp [firstAtomPattern, firstRestriction, mkPattern, h]

@[simp] private theorem firstAtomPattern_pair_one_mult (k : κ) (a : A.Item) :
    (D.firstAtomPattern (Sum.inr (Sum.inl (k, (1 : Fin 2))))).multiplicity a =
      if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
      then 0 else 2 * D.firstMultiplicity (D.P.right k) a := by
  by_cases h : D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
  · simp [firstAtomPattern, zeroPattern, mkPattern, h]
  · simp [firstAtomPattern, firstDouble, mkPattern, h]

@[simp] private theorem secondAtomPattern_unpaired_mult
    (i : {i : ι // i ∈ D.P.firstHeavyBins}) (b : B.Item) :
    (D.secondAtomPattern (Sum.inl i)).multiplicity b =
      2 * D.secondMultiplicity i.1 b := rfl

@[simp] private theorem secondAtomPattern_nonheavy_mult
    (i : {i : ι // i ∈ D.P.nonheavyBins}) (b : B.Item) :
    (D.secondAtomPattern (Sum.inr (Sum.inr i))).multiplicity b =
      2 * D.secondMultiplicity i.1 b := rfl

@[simp] private theorem secondAtomPattern_pair_zero_mult (k : κ) (b : B.Item) :
    (D.secondAtomPattern (Sum.inr (Sum.inl (k, (0 : Fin 2))))).multiplicity b =
      if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
      then D.secondMultiplicity (D.P.right k) b
      else D.secondMultiplicity (D.P.left k) b +
        D.secondMultiplicity (D.P.right k) b := by
  by_cases h : D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
  · simp [secondAtomPattern, secondRestriction, mkPattern, h]
  · simp [secondAtomPattern, secondCombined, mkPattern, h]

@[simp] private theorem secondAtomPattern_pair_one_mult (k : κ) (b : B.Item) :
    (D.secondAtomPattern (Sum.inr (Sum.inl (k, (1 : Fin 2))))).multiplicity b =
      if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
      then 2 * D.secondMultiplicity (D.P.left k) b else 0 := by
  by_cases h : D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
  · simp [secondAtomPattern, secondDouble, mkPattern, h]
  · simp [secondAtomPattern, zeroPattern, mkPattern, h]

private theorem firstAtomMass_nonneg (j : D.FirstAtom) :
    0 ≤ D.firstAtomMass j := by
  rcases j with i | j
  · exact D.P.unpaired_firstHeavy_nonneg i.1
  · rcases j with ks | i
    · rcases ks with ⟨k, slot⟩
      fin_cases slot
      · simp [firstAtomMass, D.P.pairMass_nonneg]
      · simp [firstAtomMass]
        split_ifs
        · exact le_rfl
        · exact div_nonneg (D.P.pairMass_nonneg k) (by norm_num)
    · exact div_nonneg (D.P.mass_nonneg i.1) (by norm_num)

private theorem secondAtomMass_nonneg (j : D.SecondAtom) :
    0 ≤ D.secondAtomMass j := by
  rcases j with i | j
  · exact div_nonneg (D.P.unpaired_firstHeavy_nonneg i.1) (by norm_num)
  · rcases j with ks | i
    · rcases ks with ⟨k, slot⟩
      fin_cases slot
      · simp [secondAtomMass, D.P.pairMass_nonneg]
      · simp [secondAtomMass]
        split_ifs
        · exact div_nonneg (D.P.pairMass_nonneg k) (by norm_num)
        · exact le_rfl
    · exact div_nonneg (D.P.mass_nonneg i.1) (by norm_num)

private theorem first_atom_sum (a : A.Item) :
    (∑ j : D.FirstAtom,
      D.firstAtomMass j * (D.firstAtomPattern j).multiplicity a) =
      ∑ i : ι, D.P.mass i * D.firstMultiplicity i a := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, firstAtomMass,
    firstAtomPattern_unpaired_mult, firstAtomPattern_nonheavy_mult,
    firstAtomPattern_pair_zero_mult, firstAtomPattern_pair_one_mult]
  simp only [show ((0 : Fin 2).1 = 0) by rfl, if_true,
    show ¬((1 : Fin 2).1 = 0) by decide, if_false]
  push_cast
  have hpair :
      (∑ k : κ,
        ((if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
          then D.P.pairMass k else D.P.pairMass k) *
            (if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
              then (D.firstMultiplicity (D.P.left k) a : ℝ) +
                (D.firstMultiplicity (D.P.right k) a : ℝ)
              else (D.firstMultiplicity (D.P.left k) a : ℝ)) +
        (if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
          then 0 else D.P.pairMass k / 2) *
            (if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
              then (0 : ℝ) else
                2 * (D.firstMultiplicity (D.P.right k) a : ℝ)))) =
      (∑ k : κ,
        D.P.pairMass k * (D.firstMultiplicity (D.P.left k) a : ℝ)) +
      ∑ k : κ,
        D.P.pairMass k * (D.firstMultiplicity (D.P.right k) a : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    split_ifs <;> ring
  rw [hpair,
    FiniteTwoBagJointPacking.sum_pairMass_mul_left D.P
      (fun i ↦ (D.firstMultiplicity i a : ℝ)),
    FiniteTwoBagJointPacking.sum_pairMass_mul_right D.P
      (fun i ↦ (D.firstMultiplicity i a : ℝ))]
  rw [← Finset.sum_subtype D.P.firstHeavyBins (by simp)
      (fun i ↦ (D.P.mass i - D.P.leftUse i) *
        (D.firstMultiplicity i a : ℝ)),
    ← Finset.sum_subtype D.P.nonheavyBins (by simp)
      (fun i ↦ D.P.mass i / 2 *
        (2 * (D.firstMultiplicity i a : ℝ)))]
  have hfirst :
      (∑ i ∈ D.P.firstHeavyBins,
        (D.P.mass i - D.P.leftUse i) *
          (D.firstMultiplicity i a : ℝ)) +
      (∑ i ∈ D.P.firstHeavyBins,
        D.P.leftUse i * (D.firstMultiplicity i a : ℝ)) =
      ∑ i ∈ D.P.firstHeavyBins,
        D.P.mass i * (D.firstMultiplicity i a : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hnon :
      (∑ i ∈ D.P.nonheavyBins,
        D.P.mass i / 2 * (2 * (D.firstMultiplicity i a : ℝ))) =
      ∑ i ∈ D.P.nonheavyBins,
        D.P.mass i * (D.firstMultiplicity i a : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  calc
    (∑ i ∈ D.P.firstHeavyBins,
        (D.P.mass i - D.P.leftUse i) *
          (D.firstMultiplicity i a : ℝ)) +
        (((∑ i ∈ D.P.firstHeavyBins,
            D.P.leftUse i * (D.firstMultiplicity i a : ℝ)) +
          ∑ i ∈ D.P.secondHeavyBins,
            D.P.mass i * (D.firstMultiplicity i a : ℝ)) +
        ∑ i ∈ D.P.nonheavyBins,
          D.P.mass i / 2 * (2 * (D.firstMultiplicity i a : ℝ))) =
      (∑ i ∈ D.P.firstHeavyBins,
          D.P.mass i * (D.firstMultiplicity i a : ℝ)) +
        (∑ i ∈ D.P.secondHeavyBins,
          D.P.mass i * (D.firstMultiplicity i a : ℝ)) +
        ∑ i ∈ D.P.nonheavyBins,
          D.P.mass i * (D.firstMultiplicity i a : ℝ) := by
      rw [hnon]
      linarith [hfirst]
    _ = ∑ i : ι, D.P.mass i * (D.firstMultiplicity i a : ℝ) :=
      (D.P.sum_mass_mul_partition
        (fun i ↦ (D.firstMultiplicity i a : ℝ))).symm

private theorem second_atom_sum (b : B.Item) :
    (∑ j : D.SecondAtom,
      D.secondAtomMass j * (D.secondAtomPattern j).multiplicity b) =
      ∑ i : ι, D.P.mass i * D.secondMultiplicity i b := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, secondAtomMass,
    secondAtomPattern_unpaired_mult, secondAtomPattern_nonheavy_mult,
    secondAtomPattern_pair_zero_mult, secondAtomPattern_pair_one_mult]
  simp only [show ((0 : Fin 2).1 = 0) by rfl, if_true,
    show ¬((1 : Fin 2).1 = 0) by decide, if_false]
  push_cast
  have hpair :
      (∑ k : κ,
        ((if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
          then D.P.pairMass k else D.P.pairMass k) *
            (if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
              then (D.secondMultiplicity (D.P.right k) b : ℝ)
              else (D.secondMultiplicity (D.P.left k) b : ℝ) +
                (D.secondMultiplicity (D.P.right k) b : ℝ)) +
        (if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
          then D.P.pairMass k / 2 else 0) *
            (if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
              then 2 * (D.secondMultiplicity (D.P.left k) b : ℝ)
              else (0 : ℝ)))) =
      (∑ k : κ,
        D.P.pairMass k * (D.secondMultiplicity (D.P.left k) b : ℝ)) +
      ∑ k : κ,
        D.P.pairMass k * (D.secondMultiplicity (D.P.right k) b : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    split_ifs <;> ring
  rw [hpair,
    FiniteTwoBagJointPacking.sum_pairMass_mul_left D.P
      (fun i ↦ (D.secondMultiplicity i b : ℝ)),
    FiniteTwoBagJointPacking.sum_pairMass_mul_right D.P
      (fun i ↦ (D.secondMultiplicity i b : ℝ))]
  rw [← Finset.sum_subtype D.P.firstHeavyBins (by simp)
      (fun i ↦ (D.P.mass i - D.P.leftUse i) / 2 *
        (2 * (D.secondMultiplicity i b : ℝ))),
    ← Finset.sum_subtype D.P.nonheavyBins (by simp)
      (fun i ↦ D.P.mass i / 2 *
        (2 * (D.secondMultiplicity i b : ℝ)))]
  have hfirst :
      (∑ i ∈ D.P.firstHeavyBins,
        (D.P.mass i - D.P.leftUse i) / 2 *
          (2 * (D.secondMultiplicity i b : ℝ))) +
      (∑ i ∈ D.P.firstHeavyBins,
        D.P.leftUse i * (D.secondMultiplicity i b : ℝ)) =
      ∑ i ∈ D.P.firstHeavyBins,
        D.P.mass i * (D.secondMultiplicity i b : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hnon :
      (∑ i ∈ D.P.nonheavyBins,
        D.P.mass i / 2 * (2 * (D.secondMultiplicity i b : ℝ))) =
      ∑ i ∈ D.P.nonheavyBins,
        D.P.mass i * (D.secondMultiplicity i b : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  calc
    (∑ i ∈ D.P.firstHeavyBins,
        (D.P.mass i - D.P.leftUse i) / 2 *
          (2 * (D.secondMultiplicity i b : ℝ))) +
        (((∑ i ∈ D.P.firstHeavyBins,
            D.P.leftUse i * (D.secondMultiplicity i b : ℝ)) +
          ∑ i ∈ D.P.secondHeavyBins,
            D.P.mass i * (D.secondMultiplicity i b : ℝ)) +
        ∑ i ∈ D.P.nonheavyBins,
          D.P.mass i / 2 * (2 * (D.secondMultiplicity i b : ℝ))) =
      (∑ i ∈ D.P.firstHeavyBins,
          D.P.mass i * (D.secondMultiplicity i b : ℝ)) +
        (∑ i ∈ D.P.secondHeavyBins,
          D.P.mass i * (D.secondMultiplicity i b : ℝ)) +
        ∑ i ∈ D.P.nonheavyBins,
          D.P.mass i * (D.secondMultiplicity i b : ℝ) := by
      rw [hnon]
      linarith [hfirst]
    _ = ∑ i : ι, D.P.mass i * (D.secondMultiplicity i b : ℝ) :=
      (D.P.sum_mass_mul_partition
        (fun i ↦ (D.secondMultiplicity i b : ℝ))).symm

/-- The first operational cost is realized by a genuine fractional pattern
cover of the first collection. -/
def firstSeparatedCover : A.FractionalPatternCover :=
  BinPackingInstance.FractionalPatternCover.ofFinitePatterns
    D.firstAtomPattern D.firstAtomMass D.firstAtomMass_nonneg
    (fun a ↦ D.first_atom_sum a ▸ D.covers_first a)

/-- The second operational cost is realized by a genuine fractional pattern
cover of the second collection. -/
def secondSeparatedCover : B.FractionalPatternCover :=
  BinPackingInstance.FractionalPatternCover.ofFinitePatterns
    D.secondAtomPattern D.secondAtomMass D.secondAtomMass_nonneg
    (fun b ↦ D.second_atom_sum b ▸ D.covers_second b)

/-- When the joint presentation covers a prescribed first demand exactly,
the operational first-side construction preserves that exact demand. -/
def firstSeparatedExactDemandCover (demand : A.Item → ℕ)
    (hexact : ∀ a : A.Item,
      (∑ i : ι, D.P.mass i * D.firstMultiplicity i a) = demand a) :
    A.ExactDemandPatternCover demand :=
  BinPackingInstance.ExactDemandPatternCover.ofFinitePatterns
    D.firstAtomPattern D.firstAtomMass D.firstAtomMass_nonneg
    (fun a ↦ (D.first_atom_sum a).trans (hexact a))

/-- Symmetric exact-demand preservation for the second side. -/
def secondSeparatedExactDemandCover (demand : B.Item → ℕ)
    (hexact : ∀ b : B.Item,
      (∑ i : ι, D.P.mass i * D.secondMultiplicity i b) = demand b) :
    B.ExactDemandPatternCover demand :=
  BinPackingInstance.ExactDemandPatternCover.ofFinitePatterns
    D.secondAtomPattern D.secondAtomMass D.secondAtomMass_nonneg
    (fun b ↦ (D.second_atom_sum b).trans (hexact b))

theorem firstSeparatedCover_cost :
    D.firstSeparatedCover.cost = D.P.firstSeparatedCost := by
  rw [firstSeparatedCover,
    BinPackingInstance.FractionalPatternCover.ofFinitePatterns_cost]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, firstAtomMass,
    Fin.sum_univ_two]
  simp only [show ((0 : Fin 2).1 = 0) by rfl, if_true,
    show ¬((1 : Fin 2).1 = 0) by decide, if_false]
  have hunpaired :
      (∑ i : {i : ι // i ∈ D.P.firstHeavyBins},
        (D.P.mass i.1 - D.P.leftUse i.1)) =
      ∑ i ∈ D.P.firstHeavyBins, (D.P.mass i - D.P.leftUse i) :=
    (Finset.sum_subtype D.P.firstHeavyBins (by simp)
      (fun i ↦ D.P.mass i - D.P.leftUse i)).symm
  have hpair :
      (∑ k : κ,
        ((if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
          then D.P.pairMass k else D.P.pairMass k) +
        (if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
          then 0 else D.P.pairMass k / 2))) =
      ∑ k : κ,
        if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
        then D.P.pairMass k else (3 / 2) * D.P.pairMass k := by
    apply Finset.sum_congr rfl
    intro k _hk
    split_ifs <;> ring
  have hnonheavy :
      (∑ i : {i : ι // i ∈ D.P.nonheavyBins}, D.P.mass i.1 / 2) =
      D.P.nonheavyMass / 2 := by
    unfold FiniteTwoBagJointPacking.nonheavyMass
    calc
      (∑ i : {i : ι // i ∈ D.P.nonheavyBins}, D.P.mass i.1 / 2) =
          ∑ i ∈ D.P.nonheavyBins, D.P.mass i / 2 :=
        (Finset.sum_subtype D.P.nonheavyBins (by intro i; rfl)
          (fun i ↦ D.P.mass i / 2)).symm
      _ = (∑ i ∈ D.P.nonheavyBins, D.P.mass i) / 2 :=
        (Finset.sum_div D.P.nonheavyBins D.P.mass 2).symm
  unfold FiniteTwoBagJointPacking.firstSeparatedCost
  rw [hunpaired, hpair, hnonheavy]
  ring

theorem firstSeparatedExactDemandCover_cost (demand : A.Item → ℕ)
    (hexact : ∀ a : A.Item,
      (∑ i : ι, D.P.mass i * D.firstMultiplicity i a) = demand a) :
    (D.firstSeparatedExactDemandCover demand hexact).cost =
      D.P.firstSeparatedCost := by
  rw [firstSeparatedExactDemandCover,
    BinPackingInstance.ExactDemandPatternCover.ofFinitePatterns_cost]
  have h := D.firstSeparatedCover_cost
  rw [firstSeparatedCover,
    BinPackingInstance.FractionalPatternCover.ofFinitePatterns_cost] at h
  exact h

theorem secondSeparatedCover_cost :
    D.secondSeparatedCover.cost = D.P.secondSeparatedCost := by
  rw [secondSeparatedCover,
    BinPackingInstance.FractionalPatternCover.ofFinitePatterns_cost]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, secondAtomMass,
    Fin.sum_univ_two]
  simp only [show ((0 : Fin 2).1 = 0) by rfl, if_true,
    show ¬((1 : Fin 2).1 = 0) by decide, if_false]
  have hunpaired :
      (∑ i : {i : ι // i ∈ D.P.firstHeavyBins},
        (D.P.mass i.1 - D.P.leftUse i.1) / 2) =
      ∑ i ∈ D.P.firstHeavyBins,
        (D.P.mass i - D.P.leftUse i) / 2 :=
    (Finset.sum_subtype D.P.firstHeavyBins (by simp)
      (fun i ↦ (D.P.mass i - D.P.leftUse i) / 2)).symm
  have hpair :
      (∑ k : κ,
        ((if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
          then D.P.pairMass k else D.P.pairMass k) +
        (if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
          then D.P.pairMass k / 2 else 0))) =
      ∑ k : κ,
        if D.P.firstWeight (D.P.left k) ≤ D.P.secondWeight (D.P.right k)
        then (3 / 2) * D.P.pairMass k else D.P.pairMass k := by
    apply Finset.sum_congr rfl
    intro k _hk
    split_ifs <;> ring
  have hnonheavy :
      (∑ i : {i : ι // i ∈ D.P.nonheavyBins}, D.P.mass i.1 / 2) =
      D.P.nonheavyMass / 2 := by
    unfold FiniteTwoBagJointPacking.nonheavyMass
    calc
      (∑ i : {i : ι // i ∈ D.P.nonheavyBins}, D.P.mass i.1 / 2) =
          ∑ i ∈ D.P.nonheavyBins, D.P.mass i / 2 :=
        (Finset.sum_subtype D.P.nonheavyBins (by intro i; rfl)
          (fun i ↦ D.P.mass i / 2)).symm
      _ = (∑ i ∈ D.P.nonheavyBins, D.P.mass i) / 2 :=
        (Finset.sum_div D.P.nonheavyBins D.P.mass 2).symm
  unfold FiniteTwoBagJointPacking.secondSeparatedCost
  rw [hunpaired, hpair, hnonheavy]
  ring

theorem secondSeparatedExactDemandCover_cost (demand : B.Item → ℕ)
    (hexact : ∀ b : B.Item,
      (∑ i : ι, D.P.mass i * D.secondMultiplicity i b) = demand b) :
    (D.secondSeparatedExactDemandCover demand hexact).cost =
      D.P.secondSeparatedCost := by
  rw [secondSeparatedExactDemandCover,
    BinPackingInstance.ExactDemandPatternCover.ofFinitePatterns_cost]
  have h := D.secondSeparatedCover_cost
  rw [secondSeparatedCover,
    BinPackingInstance.FractionalPatternCover.ofFinitePatterns_cost] at h
  exact h

end FiniteTwoBagPatternPresentation

end

end WeightedEdgeColoring
