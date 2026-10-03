import WeightedEdgeColoring.BPGeneralExactDemandTwoBagExtraction
import WeightedEdgeColoring.BPGraphEdgeBinPacking

/-!
# Exact-demand covers of parallel graph bundles

For one physical edge bundle, the item types are the distinct weights that
occur in the bundle and the demand of a type is its physical multiplicity.
Thus a packing of an original vertex star gives an exact-demand packing of
any two disjoint incident bundles, without first packing the grouped packet
graph.

The full packets in the manuscript's floor construction are the integer
parts of the coefficients of a minimum exact-demand pattern cover.  Their
number is at most the exact cover cost.  Combining this observation with the
finite two-bag extraction gives the exact `2n` bound for three floor packet
counts from the three original star packings.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

namespace BinPackingInstance.ExactDemandPatternCover

noncomputable section

universe u

variable {B : BinPackingInstance.{u}} {demand : B.Item → ℕ}

/-- A pattern names at least one physical item copy. -/
def PatternNonempty (p : B.Pattern) : Prop :=
  ∃ i : B.Item, 0 < p.multiplicity i

instance (p : B.Pattern) : Decidable (PatternNonempty p) := by
  unfold PatternNonempty
  infer_instance

/-- Remove all mass on the zero pattern(s).  Such patterns contribute no
coverage and therefore never belong in a minimum-cost representative. -/
def eraseEmptyPatterns (C : B.ExactDemandPatternCover demand) :
    B.ExactDemandPatternCover demand := by
  let x : B.Pattern → ℝ := fun p ↦
    if PatternNonempty p then C.coeff p else 0
  apply ofCoefficientFunction B demand x
  constructor
  · intro p
    by_cases hp : PatternNonempty p
    · simp [x, hp, C.coeff_nonneg p]
    · simp [x, hp]
  · intro i
    unfold FractionalPatternCover.coefficientCoverage
    calc
      (∑ p : B.Pattern, x p * (p.multiplicity i : ℝ)) =
          ∑ p : B.Pattern, C.coeff p * (p.multiplicity i : ℝ) := by
        apply Finset.sum_congr rfl
        intro p _hp
        by_cases hp : PatternNonempty p
        · simp [x, hp]
        · have hm : p.multiplicity i = 0 := by
            exact Nat.eq_zero_of_not_pos (fun h ↦ hp ⟨i, h⟩)
          simp [x, hp, hm]
      _ = ∑ p ∈ C.coeff.support,
          C.coeff p * (p.multiplicity i : ℝ) := by
        symm
        exact Finsupp.sum_fintype C.coeff
          (fun p c ↦ c * (p.multiplicity i : ℝ)) (by simp)
      _ = demand i := C.covers_exact i

theorem eraseEmptyPatterns_coeff_of_not_nonempty
    (C : B.ExactDemandPatternCover demand) (p : B.Pattern)
    (hp : ¬ PatternNonempty p) :
    (C.eraseEmptyPatterns).coeff p = 0 := by
  simp [eraseEmptyPatterns, ofCoefficientFunction, hp]

theorem eraseEmptyPatterns_cost_le
    (C : B.ExactDemandPatternCover demand) :
    C.eraseEmptyPatterns.cost ≤ C.cost := by
  rw [← C.eraseEmptyPatterns.sum_coeff_eq_cost, ← C.sum_coeff_eq_cost]
  apply Finset.sum_le_sum
  intro p _hp
  by_cases hp : PatternNonempty p
  · simp [eraseEmptyPatterns, ofCoefficientFunction, hp]
  · simp [eraseEmptyPatterns, ofCoefficientFunction, hp, C.coeff_nonneg p]

/-- Minimum exact covers may be chosen with zero coefficient on every empty
pattern. -/
theorem exists_reducedMinimumCost
    (B : BinPackingInstance.{u}) (demand : B.Item → ℕ) :
    ∃ C : B.ExactDemandPatternCover demand,
      C.IsMinimumCost ∧
        ∀ p, ¬ PatternNonempty p → C.coeff p = 0 := by
  obtain ⟨C, hC⟩ := exists_minimumCost B demand
  let D := C.eraseEmptyPatterns
  refine ⟨D, ?_, ?_⟩
  · intro E
    exact C.eraseEmptyPatterns_cost_le.trans (hC E)
  · intro p hp
    exact C.eraseEmptyPatterns_coeff_of_not_nonempty p hp

/-- Number of integral pattern copies retained by taking the floor of every
coefficient of an exact-demand cover. -/
def floorPacketCount (C : B.ExactDemandPatternCover demand) : ℕ :=
  ∑ p : B.Pattern, Nat.floor (C.coeff p)

/-- The labelled full packets produced by the coefficient-floor
construction. -/
abbrev FloorPacket (C : B.ExactDemandPatternCover demand) :=
  Σ p : B.Pattern, Fin (Nat.floor (C.coeff p))

/-- One requested physical copy in a labelled floor packet. -/
abbrev FloorOccurrence (C : B.ExactDemandPatternCover demand)
    (i : B.Item) :=
  Σ q : C.FloorPacket, Fin (q.1.multiplicity i)

@[simp] theorem card_floorPacket
    (C : B.ExactDemandPatternCover demand) :
    Fintype.card C.FloorPacket = C.floorPacketCount := by
  simp [FloorPacket, floorPacketCount]

/-- Total demand retained by the integer coefficient floors. -/
def floorCoveredDemand (C : B.ExactDemandPatternCover demand)
    (i : B.Item) : ℕ :=
  ∑ p : B.Pattern, Nat.floor (C.coeff p) * p.multiplicity i

/-- The integer floors never request more copies of an item type than the
original exact demand.  This is the feasibility fact used when concrete
physical copies are assigned to the full packet occurrences. -/
theorem floorCoveredDemand_le
    (C : B.ExactDemandPatternCover demand) (i : B.Item) :
    C.floorCoveredDemand i ≤ demand i := by
  have hreal : (C.floorCoveredDemand i : ℝ) ≤ (demand i : ℝ) := by
    rw [floorCoveredDemand, Nat.cast_sum]
    push_cast
    calc
      (∑ p : B.Pattern,
          (Nat.floor (C.coeff p) : ℝ) * (p.multiplicity i : ℝ)) ≤
          ∑ p : B.Pattern,
            C.coeff p * (p.multiplicity i : ℝ) := by
        exact Finset.sum_le_sum fun p _hp ↦
          mul_le_mul_of_nonneg_right
            (Nat.floor_le (C.coeff_nonneg p)) (Nat.cast_nonneg _)
      _ = ∑ p ∈ C.coeff.support,
            C.coeff p * (p.multiplicity i : ℝ) := by
        symm
        exact Finsupp.sum_fintype C.coeff
          (fun p c ↦ c * (p.multiplicity i : ℝ)) (by simp)
      _ = demand i := C.covers_exact i
  exact_mod_cast hreal

/-- Summing the multiplicities of the labelled full packets gives exactly
the floor-retained demand. -/
theorem sum_floorPacket_multiplicity
    (C : B.ExactDemandPatternCover demand) (i : B.Item) :
  (∑ q : C.FloorPacket, q.1.multiplicity i) =
      C.floorCoveredDemand i := by
  rw [Fintype.sum_sigma]
  simp [floorCoveredDemand]

@[simp] theorem card_floorOccurrence
    (C : B.ExactDemandPatternCover demand) (i : B.Item) :
    Fintype.card (C.FloorOccurrence i) = C.floorCoveredDemand i := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact C.sum_floorPacket_multiplicity i

/-- Flooring coefficients never creates more packets than the total cover
mass. -/
theorem floorPacketCount_cast_le_cost
    (C : B.ExactDemandPatternCover demand) :
    (C.floorPacketCount : ℝ) ≤ C.cost := by
  rw [floorPacketCount]
  push_cast
  calc
    (∑ p : B.Pattern, (Nat.floor (C.coeff p) : ℝ)) ≤
        ∑ p : B.Pattern, C.coeff p := by
      exact Finset.sum_le_sum fun p _hp ↦
        Nat.floor_le (C.coeff_nonneg p)
    _ = C.cost := C.sum_coeff_eq_cost

end

end BinPackingInstance.ExactDemandPatternCover

namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- Physical edges of `F` joining the unordered pair `{u,v}`.  This local
name keeps the exact-demand bridge independent of the later odd-set module. -/
def exactDemandEdgesBetween (F : Finset G.E) (u v : G.V) : Finset G.E :=
  F.filter fun e ↦
    (G.fst e = u ∧ G.snd e = v) ∨
      (G.fst e = v ∧ G.snd e = u)

theorem inc_left_of_mem_exactDemandEdgesBetween
    {F : Finset G.E} {u v : G.V} {e : G.E}
    (he : e ∈ G.exactDemandEdgesBetween F u v) :
    G.Inc u e := by
  rcases (Finset.mem_filter.mp he).2 with h | h
  · exact Or.inl h.1
  · exact Or.inr h.2

theorem inc_right_of_mem_exactDemandEdgesBetween
    {F : Finset G.E} {u v : G.V} {e : G.E}
    (he : e ∈ G.exactDemandEdgesBetween F u v) :
    G.Inc v e := by
  rcases (Finset.mem_filter.mp he).2 with h | h
  · exact Or.inr h.2
  · exact Or.inl h.1

theorem exactDemandEdgesBetween_pairwise_disjoint
    (F : Finset G.E) {a b c : G.V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Disjoint (G.exactDemandEdgesBetween F a b)
        (G.exactDemandEdgesBetween F a c) ∧
      Disjoint (G.exactDemandEdgesBetween F a b)
        (G.exactDemandEdgesBetween F b c) ∧
      Disjoint (G.exactDemandEdgesBetween F a c)
        (G.exactDemandEdgesBetween F b c) := by
  constructor
  · rw [Finset.disjoint_left]
    intro e heAB heAC
    simp only [exactDemandEdgesBetween, Finset.mem_filter] at heAB heAC
    rcases heAB.2 with ⟨hfa, hsb⟩ | ⟨hfb, hsa⟩ <;>
      rcases heAC.2 with ⟨hfa', hsc⟩ | ⟨hfc, hsa'⟩
    · exact hbc (hsb.symm.trans hsc)
    · exact hac (hfa.symm.trans hfc)
    · exact hab (hfa'.symm.trans hfb)
    · exact hbc (hfb.symm.trans hfc)
  constructor
  · rw [Finset.disjoint_left]
    intro e heAB heBC
    simp only [exactDemandEdgesBetween, Finset.mem_filter] at heAB heBC
    rcases heAB.2 with ⟨hfa, hsb⟩ | ⟨hfb, hsa⟩ <;>
      rcases heBC.2 with ⟨hfb', hsc⟩ | ⟨hfc, hsb'⟩
    · exact hab (hfa.symm.trans hfb')
    · exact hac (hfa.symm.trans hfc)
    · exact hac (hsa.symm.trans hsc)
    · exact hab (hsa.symm.trans hsb')
  · rw [Finset.disjoint_left]
    intro e heAC heBC
    simp only [exactDemandEdgesBetween, Finset.mem_filter] at heAC heBC
    rcases heAC.2 with ⟨hfa, hsc⟩ | ⟨hfc, hsa⟩ <;>
      rcases heBC.2 with ⟨hfb, hsc'⟩ | ⟨hfc', hsb⟩
    · exact hab (hfa.symm.trans hfb)
    · exact hbc (hsb.symm.trans hsc)
    · exact hbc (hfb.symm.trans hfc)
    · exact hab (hsa.symm.trans hsb)

/-- The finite type of physical weights occurring in an edge set. -/
abbrev EdgeSetWeightType (F : Finset G.E) :=
  {x : ℝ // x ∈ F.image G.weight}

/-- Physical edge copies of one weight type inside `F`. -/
abbrev EdgeSetPhysicalCopy (F : Finset G.E)
    (x : G.EdgeSetWeightType F) :=
  {e : G.E // e ∈ F ∧ G.weight e = x.1}

/-- The bin-packing instance of weight types occurring in `F`. -/
def edgeSetWeightBinPackingInstance (F : Finset G.E) :
    BinPackingInstance where
  Item := G.EdgeSetWeightType F
  instFintypeItem := inferInstance
  instDecidableEqItem := inferInstance
  weight := fun x ↦ x.1
  weight_pos := by
    intro x
    rcases Finset.mem_image.mp x.2 with ⟨e, _heF, he⟩
    simpa [← he] using G.weight_pos e
  weight_le_one := by
    intro x
    rcases Finset.mem_image.mp x.2 with ⟨e, _heF, he⟩
    simpa [← he] using G.weight_le_one e

@[simp] theorem edgeSetWeightBinPackingInstance_weight
    (F : Finset G.E) (x : G.EdgeSetWeightType F) :
    (G.edgeSetWeightBinPackingInstance F).weight x = x.1 := rfl

/-- Exact physical multiplicity of one weight type in an edge set. -/
def edgeSetWeightDemand (F : Finset G.E) (x : G.EdgeSetWeightType F) : ℕ :=
  (F.filter fun e ↦ G.weight e = x.1).card

/-- An exact-demand pattern cover of the physical weight multiplicities in
an edge set. -/
abbrev EdgeSetExactDemandCover (F : Finset G.E) :=
  (G.edgeSetWeightBinPackingInstance F).ExactDemandPatternCover
    (G.edgeSetWeightDemand F)

theorem edgeSetWeightDemand_pos (F : Finset G.E)
    (x : G.EdgeSetWeightType F) :
    1 ≤ G.edgeSetWeightDemand F x := by
  rcases Finset.mem_image.mp x.2 with ⟨e, heF, he⟩
  apply Finset.one_le_card.mpr
  exact ⟨e, Finset.mem_filter.mpr ⟨heF, he⟩⟩

theorem card_edgeSetPhysicalCopy (F : Finset G.E)
    (x : G.EdgeSetWeightType F) :
    Fintype.card (G.EdgeSetPhysicalCopy F x) =
      G.edgeSetWeightDemand F x := by
  let equiv : G.EdgeSetPhysicalCopy F x ≃
      {e : G.E // e ∈ F.filter fun e ↦ G.weight e = x.1} :=
    { toFun := fun e ↦ ⟨e.1, Finset.mem_filter.mpr e.2⟩
      invFun := fun e ↦ ⟨e.1, (Finset.mem_filter.mp e.2)⟩
      left_inv := fun e ↦ by rfl
      right_inv := fun e ↦ by rfl }
  calc
    Fintype.card (G.EdgeSetPhysicalCopy F x) =
        Fintype.card {e : G.E // e ∈ F.filter fun e ↦ G.weight e = x.1} :=
      Fintype.card_congr equiv
    _ = (F.filter fun e ↦ G.weight e = x.1).card :=
      Fintype.card_coe _
    _ = G.edgeSetWeightDemand F x := rfl

/-- The retained occurrences of each weight type can be assigned injectively
to concrete physical edges of that type. -/
noncomputable def floorOccurrenceEmbedding
    (F : Finset G.E) (C : G.EdgeSetExactDemandCover F)
    (x : G.EdgeSetWeightType F) :
    C.FloorOccurrence x ↪ G.EdgeSetPhysicalCopy F x := by
  let sourceEquiv := Fintype.equivFin (C.FloorOccurrence x)
  let targetEquiv := Fintype.equivFin (G.EdgeSetPhysicalCopy F x)
  have hcard : Fintype.card (C.FloorOccurrence x) ≤
      Fintype.card (G.EdgeSetPhysicalCopy F x) := by
    rw [C.card_floorOccurrence x, G.card_edgeSetPhysicalCopy F x]
    exact C.floorCoveredDemand_le x
  exact
    { toFun := fun o ↦ targetEquiv.symm
        ⟨(sourceEquiv o).1, (sourceEquiv o).2.trans_le hcard⟩
      inj' := by
        intro o₁ o₂ h
        have hfin := targetEquiv.symm.injective h
        apply sourceEquiv.injective
        have hval : (sourceEquiv o₁).val = (sourceEquiv o₂).val :=
          congrArg (fun z ↦ z.val) hfin
        exact Fin.ext hval }

/-- Aggregate a bin assignment of the physical edges of `F` into one
weight-multiplicity pattern. -/
def edgeSetWeightPatternOfBin
    (F : Finset G.E) {n : ℕ}
    (bin : {e : G.E // e ∈ F} → Fin n)
    (hload : ∀ j, (∑ e : {e : G.E // e ∈ F},
      if bin e = j then G.weight e.1 else 0) ≤ 1)
    (j : Fin n) :
    (G.edgeSetWeightBinPackingInstance F).Pattern where
  multiplicity := fun x ↦
    ∑ e : {e : G.E // e ∈ F},
      if bin e = j ∧ G.weight e.1 = x.1 then 1 else 0
  capacity := by
    calc
      (∑ x : G.EdgeSetWeightType F,
          ((∑ e : {e : G.E // e ∈ F},
              if bin e = j ∧ G.weight e.1 = x.1 then 1 else 0 : ℕ) : ℝ) *
            (G.edgeSetWeightBinPackingInstance F).weight x) =
          ∑ x : G.EdgeSetWeightType F,
            ∑ e : {e : G.E // e ∈ F},
              if bin e = j ∧ G.weight e.1 = x.1
                then G.weight e.1 else 0 := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [Nat.cast_sum]
        push_cast
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _he
        by_cases h : bin e = j ∧ G.weight e.1 = x.1
        · simp [h]
        · simp [h]
      _ = ∑ e : {e : G.E // e ∈ F},
            ∑ x : G.EdgeSetWeightType F,
              if bin e = j ∧ G.weight e.1 = x.1
                then G.weight e.1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ e : {e : G.E // e ∈ F},
            if bin e = j then G.weight e.1 else 0 := by
        apply Finset.sum_congr rfl
        intro e _he
        by_cases hbin : bin e = j
        · let x : G.EdgeSetWeightType F :=
            ⟨G.weight e.1, Finset.mem_image.mpr ⟨e.1, e.2, rfl⟩⟩
          rw [Finset.sum_eq_single x]
          · simp [hbin, x]
          · intro y _hy hyx
            have hne : G.weight e.1 ≠ y.1 := by
              intro h
              apply hyx
              exact Subtype.ext h.symm
            simp [hbin, hne]
          · intro hx
            exact (hx (Finset.mem_univ x)).elim
        · simp [hbin]
      _ ≤ 1 := hload j

theorem edgeSetWeightPatternOfBin_load_eq
    (F : Finset G.E) {n : ℕ}
    (bin : {e : G.E // e ∈ F} → Fin n)
    (hload : ∀ j, (∑ e : {e : G.E // e ∈ F},
      if bin e = j then G.weight e.1 else 0) ≤ 1)
    (j : Fin n) :
    (∑ x : G.EdgeSetWeightType F,
        ((G.edgeSetWeightPatternOfBin F bin hload j).multiplicity x : ℝ) *
          (G.edgeSetWeightBinPackingInstance F).weight x) =
      ∑ e : {e : G.E // e ∈ F},
        if bin e = j then G.weight e.1 else 0 := by
  classical
  unfold edgeSetWeightPatternOfBin
  calc
    (∑ x : G.EdgeSetWeightType F,
        ((∑ e : {e : G.E // e ∈ F},
            if bin e = j ∧ G.weight e.1 = x.1 then 1 else 0 : ℕ) : ℝ) *
          (G.edgeSetWeightBinPackingInstance F).weight x) =
        ∑ x : G.EdgeSetWeightType F,
          ∑ e : {e : G.E // e ∈ F},
            if bin e = j ∧ G.weight e.1 = x.1
              then G.weight e.1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Nat.cast_sum]
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases h : bin e = j ∧ G.weight e.1 = x.1
      · simp [h]
      · simp [h]
    _ = ∑ e : {e : G.E // e ∈ F},
          ∑ x : G.EdgeSetWeightType F,
            if bin e = j ∧ G.weight e.1 = x.1
              then G.weight e.1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e : {e : G.E // e ∈ F},
          if bin e = j then G.weight e.1 else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hbin : bin e = j
      · let x : G.EdgeSetWeightType F :=
          ⟨G.weight e.1, Finset.mem_image.mpr ⟨e.1, e.2, rfl⟩⟩
        rw [Finset.sum_eq_single x]
        · simp [hbin, x]
        · intro y _hy hyx
          have hne : G.weight e.1 ≠ y.1 := by
            intro h
            apply hyx
            exact Subtype.ext h.symm
          simp [hbin, hne]
        · intro hx
          exact (hx (Finset.mem_univ x)).elim
      · simp [hbin]

/-- The pattern above counts all physical copies of each weight type exactly
once when summed over all bins. -/
theorem sum_edgeSetWeightPatternOfBin_multiplicity
    (F : Finset G.E) {n : ℕ}
    (bin : {e : G.E // e ∈ F} → Fin n)
    (hload : ∀ j, (∑ e : {e : G.E // e ∈ F},
      if bin e = j then G.weight e.1 else 0) ≤ 1)
    (x : G.EdgeSetWeightType F) :
    (∑ j : Fin n,
      (G.edgeSetWeightPatternOfBin F bin hload j).multiplicity x) =
      G.edgeSetWeightDemand F x := by
  classical
  unfold edgeSetWeightPatternOfBin edgeSetWeightDemand
  rw [Finset.sum_comm]
  calc
    (∑ e : {e : G.E // e ∈ F},
        ∑ j : Fin n,
          if bin e = j ∧ G.weight e.1 = x.1 then 1 else 0) =
        ∑ e : {e : G.E // e ∈ F},
          if G.weight e.1 = x.1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hw : G.weight e.1 = x.1
      · rw [Finset.sum_eq_single (bin e)]
        · simp [hw]
        · intro j _hj hne
          simp [hne.symm, hw]
        · intro h
          exact (h (Finset.mem_univ (bin e))).elim
      · simp [hw]
    _ = (F.filter fun e ↦ G.weight e = x.1).card := by
      calc
        (∑ e : {e : G.E // e ∈ F},
            if G.weight e.1 = x.1 then 1 else 0) =
            ∑ e ∈ F, if G.weight e = x.1 then 1 else 0 := by
          exact (Finset.sum_subtype (p := fun e : G.E ↦ e ∈ F) F
            (by intro e; simp)
            (fun e ↦ if G.weight e = x.1 then 1 else 0)).symm
        _ = _ := by simp

/-- Two disjoint incident physical edge bundles inherit an exact-demand
packing from the original packing of their common star. -/
theorem sum_edgeSetWeightDemand_packsInto_of_packsStarInto
    (F H : Finset G.E) (v : G.V) {n : ℕ}
    (hdisj : Disjoint F H)
    (hincF : ∀ e ∈ F, G.Inc v e)
    (hincH : ∀ e ∈ H, G.Inc v e)
    (hpack : G.PacksStarInto v n) :
    BinPackingInstance.ExactDemandPatternCover.PacksInto
      (B := (G.edgeSetWeightBinPackingInstance F).sum
        (G.edgeSetWeightBinPackingInstance H))
      (BinPackingInstance.ExactDemandPatternCover.sumDemand
        (G.edgeSetWeightDemand F) (G.edgeSetWeightDemand H)) n := by
  classical
  rcases hpack with ⟨starBin, hstarBin⟩
  let AF := G.edgeSetWeightBinPackingInstance F
  let AH := G.edgeSetWeightBinPackingInstance H
  let binF : {e : G.E // e ∈ F} → Fin n :=
    fun e ↦ starBin ⟨e.1, hincF e.1 e.2⟩
  let binH : {e : G.E // e ∈ H} → Fin n :=
    fun e ↦ starBin ⟨e.1, hincH e.1 e.2⟩
  have hloadPair : ∀ j,
      (∑ e : {e : G.E // e ∈ F},
          if binF e = j then G.weight e.1 else 0) +
        (∑ e : {e : G.E // e ∈ H},
          if binH e = j then G.weight e.1 else 0) ≤ 1 := by
    intro j
    let f : G.E → ℝ := fun e ↦
      if he : G.Inc v e then
        if starBin ⟨e, he⟩ = j then G.weight e else 0
      else 0
    have hUnionSub : F ∪ H ⊆
        (Finset.univ : Finset G.E).filter (G.Inc v) := by
      intro e he
      rcases Finset.mem_union.mp he with heF | heH
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hincF e heF⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hincH e heH⟩
    calc
      (∑ e : {e : G.E // e ∈ F},
          if binF e = j then G.weight e.1 else 0) +
          (∑ e : {e : G.E // e ∈ H},
            if binH e = j then G.weight e.1 else 0) =
          (∑ e ∈ F, f e) + ∑ e ∈ H, f e := by
        congr 1
        · rw [show (∑ e : {e : G.E // e ∈ F},
              if binF e = j then G.weight e.1 else 0) =
              ∑ e : {e : G.E // e ∈ F}, f e.1 by
            apply Finset.sum_congr rfl
            intro e _he
            simp [binF, f, hincF e.1 e.2]]
          exact (Finset.sum_subtype F (by intro e; simp) f).symm
        · rw [show (∑ e : {e : G.E // e ∈ H},
              if binH e = j then G.weight e.1 else 0) =
              ∑ e : {e : G.E // e ∈ H}, f e.1 by
            apply Finset.sum_congr rfl
            intro e _he
            simp [binH, f, hincH e.1 e.2]]
          exact (Finset.sum_subtype H (by intro e; simp) f).symm
      _ = ∑ e ∈ F ∪ H, f e := (Finset.sum_union hdisj).symm
      _ ≤ ∑ e ∈ (Finset.univ : Finset G.E).filter (G.Inc v), f e := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hUnionSub
          (fun e _heStar _heUnion ↦ by
            by_cases hve : G.Inc v e
            · by_cases hbin : starBin ⟨e, hve⟩ = j
              · simp [f, hve, hbin, G.weight_nonneg]
              · simp [f, hve, hbin]
            · simp [f, hve])
      _ = G.starBinLoad starBin j := by
        calc
          (∑ e ∈ (Finset.univ : Finset G.E).filter (G.Inc v), f e) =
              ∑ e : G.StarEdge v, f e.1 :=
            Finset.sum_subtype
              ((Finset.univ : Finset G.E).filter (G.Inc v))
              (by intro e; simp) f
          _ = G.starBinLoad starBin j := by
            unfold starBinLoad
            apply Finset.sum_congr rfl
            intro e _he
            simp [f, e.2]
      _ ≤ 1 := hstarBin j
  have hloadF : ∀ j, (∑ e : {e : G.E // e ∈ F},
      if binF e = j then G.weight e.1 else 0) ≤ 1 := by
    intro j
    exact (le_add_of_nonneg_right
      (Finset.sum_nonneg fun e _he ↦ by
        by_cases h : binH e = j
        · simp [h, G.weight_nonneg]
        · simp [h])).trans
        (hloadPair j)
  have hloadH : ∀ j, (∑ e : {e : G.E // e ∈ H},
      if binH e = j then G.weight e.1 else 0) ≤ 1 := by
    intro j
    exact (le_add_of_nonneg_left
      (Finset.sum_nonneg fun e _he ↦ by
        by_cases h : binF e = j
        · simp [h, G.weight_nonneg]
        · simp [h])).trans
        (hloadPair j)
  let pattern : Fin n → (AF.sum AH).Pattern := fun j ↦
    { multiplicity := Sum.elim
        (G.edgeSetWeightPatternOfBin F binF hloadF j).multiplicity
        (G.edgeSetWeightPatternOfBin H binH hloadH j).multiplicity
      capacity := by
        change
          (∑ i : Sum AF.Item AH.Item,
              ((Sum.elim
                (G.edgeSetWeightPatternOfBin F binF hloadF j).multiplicity
                (G.edgeSetWeightPatternOfBin H binH hloadH j).multiplicity i : ℕ) : ℝ) *
                Sum.elim AF.weight AH.weight i) ≤ 1
        rw [Fintype.sum_sum_type]
        change
          (∑ x : AF.Item,
              ((G.edgeSetWeightPatternOfBin F binF hloadF j).multiplicity x : ℝ) *
                AF.weight x) +
            (∑ x : AH.Item,
              ((G.edgeSetWeightPatternOfBin H binH hloadH j).multiplicity x : ℝ) *
                AH.weight x) ≤ 1
        dsimp only [AF, AH]
        calc
          (∑ x : G.EdgeSetWeightType F,
              ((G.edgeSetWeightPatternOfBin F binF hloadF j).multiplicity x : ℝ) *
                (G.edgeSetWeightBinPackingInstance F).weight x) +
              (∑ x : G.EdgeSetWeightType H,
                ((G.edgeSetWeightPatternOfBin H binH hloadH j).multiplicity x : ℝ) *
                  (G.edgeSetWeightBinPackingInstance H).weight x) =
              (∑ e : {e : G.E // e ∈ F},
                if binF e = j then G.weight e.1 else 0) +
              (∑ e : {e : G.E // e ∈ H},
                if binH e = j then G.weight e.1 else 0) := by
            congr 1
            · exact G.edgeSetWeightPatternOfBin_load_eq F binF hloadF j
            · exact G.edgeSetWeightPatternOfBin_load_eq H binH hloadH j
          _ ≤ 1 := hloadPair j }
  refine ⟨⟨pattern, ?_⟩⟩
  intro i
  cases i with
  | inl x =>
      simpa [pattern,
        BinPackingInstance.ExactDemandPatternCover.sumDemand] using
        G.sum_edgeSetWeightPatternOfBin_multiplicity F binF hloadF x
  | inr x =>
      simpa [pattern,
        BinPackingInstance.ExactDemandPatternCover.sumDemand] using
        G.sum_edgeSetWeightPatternOfBin_multiplicity H binH hloadH x

/-- For three parallel bundles, the coefficient-floor packet counts are at
most `2n` as soon as the three original vertex stars pack into `n` bins.
No packing hypothesis is made about the grouped packet graph. -/
theorem three_floorPacketCounts_le_two_mul_of_packsStarsInto
    (F : Finset G.E) (a b c : G.V) (n : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (CA : G.EdgeSetExactDemandCover (G.exactDemandEdgesBetween F a b))
    (CB : G.EdgeSetExactDemandCover (G.exactDemandEdgesBetween F a c))
    (CC : G.EdgeSetExactDemandCover (G.exactDemandEdgesBetween F b c))
    (hCA : CA.IsMinimumCost) (hCB : CB.IsMinimumCost)
    (hCC : CC.IsMinimumCost)
    (hpackA : G.PacksStarInto a n)
    (hpackB : G.PacksStarInto b n)
    (hpackC : G.PacksStarInto c n) :
    CA.floorPacketCount + CB.floorPacketCount + CC.floorPacketCount ≤
      2 * n := by
  let FAB := G.exactDemandEdgesBetween F a b
  let FAC := G.exactDemandEdgesBetween F a c
  let FBC := G.exactDemandEdgesBetween F b c
  obtain ⟨hABAC, hABBC, hACBC⟩ :=
    G.exactDemandEdgesBetween_pairwise_disjoint F hab hac hbc
  have hincABa : ∀ e ∈ FAB, G.Inc a e := by
    intro e he
    exact G.inc_left_of_mem_exactDemandEdgesBetween he
  have hincABb : ∀ e ∈ FAB, G.Inc b e := by
    intro e he
    exact G.inc_right_of_mem_exactDemandEdgesBetween he
  have hincACa : ∀ e ∈ FAC, G.Inc a e := by
    intro e he
    exact G.inc_left_of_mem_exactDemandEdgesBetween he
  have hincACc : ∀ e ∈ FAC, G.Inc c e := by
    intro e he
    exact G.inc_right_of_mem_exactDemandEdgesBetween he
  have hincBCb : ∀ e ∈ FBC, G.Inc b e := by
    intro e he
    exact G.inc_left_of_mem_exactDemandEdgesBetween he
  have hincBCc : ∀ e ∈ FBC, G.Inc c e := by
    intro e he
    exact G.inc_right_of_mem_exactDemandEdgesBetween he
  have hpairA :=
    G.sum_edgeSetWeightDemand_packsInto_of_packsStarInto
      FAB FAC a hABAC hincABa hincACa hpackA
  have hpairB :=
    G.sum_edgeSetWeightDemand_packsInto_of_packsStarInto
      FAB FBC b hABBC hincABb hincBCb hpackB
  have hpairC :=
    G.sum_edgeSetWeightDemand_packsInto_of_packsStarInto
      FAC FBC c hACBC hincACc hincBCc hpackC
  apply BinPackingInstance.ExactDemandPatternCover.three_packetCounts_le_two_mul_of_pairwisePacksInto
      (A := G.edgeSetWeightBinPackingInstance FAB)
      (B := G.edgeSetWeightBinPackingInstance FAC)
      (Cinst := G.edgeSetWeightBinPackingInstance FBC)
      (firstDemand := G.edgeSetWeightDemand FAB)
      (secondDemand := G.edgeSetWeightDemand FAC)
      (thirdDemand := G.edgeSetWeightDemand FBC)
      CA.floorPacketCount CB.floorPacketCount CC.floorPacketCount n
  · exact G.edgeSetWeightDemand_pos FAB
  · exact G.edgeSetWeightDemand_pos FAC
  · exact G.edgeSetWeightDemand_pos FBC
  · intro DA _hDA
    exact CA.floorPacketCount_cast_le_cost.trans (hCA DA)
  · intro DB _hDB
    exact CB.floorPacketCount_cast_le_cost.trans (hCB DB)
  · intro DC _hDC
    exact CC.floorPacketCount_cast_le_cost.trans (hCC DC)
  · exact hpairA
  · exact hpairB
  · exact hpairC

/-- The three minimum exact-demand covers, and hence their coefficient-floor
packet families, can be chosen simultaneously with the `2n` bound. -/
theorem exists_minimumEdgeSetExactDemandCovers_three_floorPacketCounts_le
    (F : Finset G.E) (a b c : G.V) (n : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpackA : G.PacksStarInto a n)
    (hpackB : G.PacksStarInto b n)
    (hpackC : G.PacksStarInto c n) :
    ∃ CA : G.EdgeSetExactDemandCover (G.exactDemandEdgesBetween F a b),
      ∃ CB : G.EdgeSetExactDemandCover (G.exactDemandEdgesBetween F a c),
        ∃ CC : G.EdgeSetExactDemandCover (G.exactDemandEdgesBetween F b c),
          CA.IsMinimumCost ∧ CB.IsMinimumCost ∧ CC.IsMinimumCost ∧
          CA.floorPacketCount + CB.floorPacketCount + CC.floorPacketCount ≤
            2 * n := by
  obtain ⟨CA, hCA⟩ := BinPackingInstance.ExactDemandPatternCover.exists_minimumCost
    (G.edgeSetWeightBinPackingInstance (G.exactDemandEdgesBetween F a b))
    (G.edgeSetWeightDemand (G.exactDemandEdgesBetween F a b))
  obtain ⟨CB, hCB⟩ := BinPackingInstance.ExactDemandPatternCover.exists_minimumCost
    (G.edgeSetWeightBinPackingInstance (G.exactDemandEdgesBetween F a c))
    (G.edgeSetWeightDemand (G.exactDemandEdgesBetween F a c))
  obtain ⟨CC, hCC⟩ := BinPackingInstance.ExactDemandPatternCover.exists_minimumCost
    (G.edgeSetWeightBinPackingInstance (G.exactDemandEdgesBetween F b c))
    (G.edgeSetWeightDemand (G.exactDemandEdgesBetween F b c))
  refine ⟨CA, CB, CC, hCA, hCB, hCC, ?_⟩
  exact G.three_floorPacketCounts_le_two_mul_of_packsStarsInto
    F a b c n hab hac hbc CA CB CC hCA hCB hCC hpackA hpackB hpackC

end


end WeightedMultigraph
end WeightedEdgeColoring
