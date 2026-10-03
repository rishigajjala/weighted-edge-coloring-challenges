import WeightedEdgeColoring.BinPacking
import WeightedEdgeColoring.BPGeneralFiniteTwoBagProportionalPairing
import WeightedEdgeColoring.BPGeneralFiniteTwoBagOperationalCovers

/-!
# Two-bag bins from a finite configuration-LP cover

A pattern for the disjoint union of two bin-packing instances is a joint bin.
Its coefficient is the bin mass and the two restricted loads are its packet
weights.  This file makes that translation literal and then applies the
canonical proportional heavy-bin pairing.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u v

/-- The disjoint union of two indexed bin-packing instances. -/
def BinPackingInstance.sum (A : BinPackingInstance.{u})
    (B : BinPackingInstance.{v}) : BinPackingInstance where
  Item := Sum A.Item B.Item
  instFintypeItem := inferInstance
  instDecidableEqItem := inferInstance
  weight := Sum.elim A.weight B.weight
  weight_pos := by
    intro i
    cases i with
    | inl i => exact A.weight_pos i
    | inr i => exact B.weight_pos i
  weight_le_one := by
    intro i
    cases i with
    | inl i => exact A.weight_le_one i
    | inr i => exact B.weight_le_one i

namespace BinPackingInstance.FractionalPatternCover

variable {A : BinPackingInstance.{u}} {B : BinPackingInstance.{v}}

/-- The finite type of positive-or-zero support entries actually named by a
fractional cover. -/
abbrev SupportBin (C : (A.sum B).FractionalPatternCover) :=
  {p : (A.sum B).Pattern // p ∈ C.coeff.support}

noncomputable instance (C : (A.sum B).FractionalPatternCover) :
    Fintype C.SupportBin :=
  Fintype.ofFinset C.coeff.support (fun _ ↦ Iff.rfl)

noncomputable instance (C : (A.sum B).FractionalPatternCover) :
    DecidableEq C.SupportBin := Classical.decEq _

/-- Mass of a support bin. -/
def supportMass (C : (A.sum B).FractionalPatternCover)
    (p : C.SupportBin) : ℝ := C.coeff p.1

/-- Load in a joint pattern contributed by the first collection. -/
def firstLoad (C : (A.sum B).FractionalPatternCover)
    (p : C.SupportBin) : ℝ :=
  ∑ i : A.Item, (p.1.multiplicity (Sum.inl i) : ℝ) * A.weight i

/-- Load in a joint pattern contributed by the second collection. -/
def secondLoad (C : (A.sum B).FractionalPatternCover)
    (p : C.SupportBin) : ℝ :=
  ∑ i : B.Item, (p.1.multiplicity (Sum.inr i) : ℝ) * B.weight i

theorem supportMass_nonneg (C : (A.sum B).FractionalPatternCover)
    (p : C.SupportBin) : 0 ≤ C.supportMass p :=
  C.coeff_nonneg p.1

theorem firstLoad_nonneg (C : (A.sum B).FractionalPatternCover)
    (p : C.SupportBin) : 0 ≤ C.firstLoad p := by
  exact Finset.sum_nonneg fun i _hi ↦
    mul_nonneg (Nat.cast_nonneg _) (A.weight_nonneg i)

theorem secondLoad_nonneg (C : (A.sum B).FractionalPatternCover)
    (p : C.SupportBin) : 0 ≤ C.secondLoad p := by
  exact Finset.sum_nonneg fun i _hi ↦
    mul_nonneg (Nat.cast_nonneg _) (B.weight_nonneg i)

theorem load_capacity (C : (A.sum B).FractionalPatternCover)
    (p : C.SupportBin) : C.firstLoad p + C.secondLoad p ≤ 1 := by
  simpa [firstLoad, secondLoad, BinPackingInstance.sum] using p.1.capacity

theorem sum_supportMass_eq_cost (C : (A.sum B).FractionalPatternCover) :
    (∑ p : C.SupportBin, C.supportMass p) = C.cost := by
  rw [BinPackingInstance.FractionalPatternCover.cost]
  exact (Finset.sum_subtype C.coeff.support (by intro p; rfl)
    (fun p ↦ C.coeff p)).symm

/-- The first-heavy mass of the bins named by a joint pattern cover. -/
def firstHeavyMass (C : (A.sum B).FractionalPatternCover) : ℝ :=
  FiniteTwoBagJointPacking.heavyMass C.supportMass C.firstLoad

/-- The second-heavy mass of the bins named by a joint pattern cover. -/
def secondHeavyMass (C : (A.sum B).FractionalPatternCover) : ℝ :=
  FiniteTwoBagJointPacking.heavyMass C.supportMass C.secondLoad

/-- In the orientation where the first heavy part is larger, a joint
configuration-LP cover produces the full explicit finite packing witness. -/
def toFiniteTwoBagJointPacking
    (C : (A.sum B).FractionalPatternCover)
    (h : C.secondHeavyMass ≤ C.firstHeavyMass) :
    FiniteTwoBagJointPacking
      (ι := C.SupportBin)
      (κ := FiniteTwoBagHeavyPair C.firstLoad C.secondLoad) :=
  FiniteTwoBagJointPacking.ofProportionalPairing
    C.supportMass C.firstLoad C.secondLoad
    C.supportMass_nonneg C.firstLoad_nonneg C.secondLoad_nonneg
    C.load_capacity h

/-- The opposite orientation uses exactly the same joint bins, with the two
restricted loads exchanged. -/
def toFiniteTwoBagJointPackingSwapped
    (C : (A.sum B).FractionalPatternCover)
    (h : C.firstHeavyMass ≤ C.secondHeavyMass) :
    FiniteTwoBagJointPacking
      (ι := C.SupportBin)
      (κ := FiniteTwoBagHeavyPair C.secondLoad C.firstLoad) :=
  FiniteTwoBagJointPacking.ofProportionalPairing
    C.supportMass C.secondLoad C.firstLoad
    C.supportMass_nonneg C.secondLoad_nonneg C.firstLoad_nonneg
    (fun p ↦ by simpa [add_comm] using C.load_capacity p) h

/-- Retain the two collections' pattern multiplicities on the canonical
oriented packing. -/
def toPatternPresentation
    (C : (A.sum B).FractionalPatternCover)
    (h : C.secondHeavyMass ≤ C.firstHeavyMass) :
    FiniteTwoBagPatternPresentation A B
      (ι := C.SupportBin)
      (κ := FiniteTwoBagHeavyPair C.firstLoad C.secondLoad) := by
  refine
    { packing := C.toFiniteTwoBagJointPacking h
      firstMultiplicity := fun p a ↦ p.1.multiplicity (Sum.inl a)
      secondMultiplicity := fun p b ↦ p.1.multiplicity (Sum.inr b)
      firstWeight_eq := fun p ↦ rfl
      secondWeight_eq := fun p ↦ rfl
      covers_first := ?_
      covers_second := ?_ }
  · intro a
    calc
      1 ≤ ∑ p ∈ C.coeff.support,
          C.coeff p * (p.multiplicity (Sum.inl a) : ℝ) := C.covers (Sum.inl a)
      _ = ∑ p : C.SupportBin,
          (C.toFiniteTwoBagJointPacking h).mass p *
            (p.1.multiplicity (Sum.inl a) : ℝ) := by
        rw [show (∑ p ∈ C.coeff.support,
            C.coeff p * (p.multiplicity (Sum.inl a) : ℝ)) =
            ∑ p : C.SupportBin,
              C.coeff p.1 * (p.1.multiplicity (Sum.inl a) : ℝ) by
          exact Finset.sum_subtype C.coeff.support (by intro p; rfl)
            (fun p ↦ C.coeff p * (p.multiplicity (Sum.inl a) : ℝ))]
        rfl
  · intro b
    calc
      1 ≤ ∑ p ∈ C.coeff.support,
          C.coeff p * (p.multiplicity (Sum.inr b) : ℝ) := C.covers (Sum.inr b)
      _ = ∑ p : C.SupportBin,
          (C.toFiniteTwoBagJointPacking h).mass p *
            (p.1.multiplicity (Sum.inr b) : ℝ) := by
        rw [show (∑ p ∈ C.coeff.support,
            C.coeff p * (p.multiplicity (Sum.inr b) : ℝ)) =
            ∑ p : C.SupportBin,
              C.coeff p.1 * (p.1.multiplicity (Sum.inr b) : ℝ) by
          exact Finset.sum_subtype C.coeff.support (by intro p; rfl)
            (fun p ↦ C.coeff p * (p.multiplicity (Sum.inr b) : ℝ))]
        rfl

/-- The multiplicity presentation in the opposite orientation. -/
def toPatternPresentationSwapped
    (C : (A.sum B).FractionalPatternCover)
    (h : C.firstHeavyMass ≤ C.secondHeavyMass) :
    FiniteTwoBagPatternPresentation B A
      (ι := C.SupportBin)
      (κ := FiniteTwoBagHeavyPair C.secondLoad C.firstLoad) := by
  refine
    { packing := C.toFiniteTwoBagJointPackingSwapped h
      firstMultiplicity := fun p b ↦ p.1.multiplicity (Sum.inr b)
      secondMultiplicity := fun p a ↦ p.1.multiplicity (Sum.inl a)
      firstWeight_eq := fun p ↦ rfl
      secondWeight_eq := fun p ↦ rfl
      covers_first := ?_
      covers_second := ?_ }
  · intro b
    calc
      1 ≤ ∑ p ∈ C.coeff.support,
          C.coeff p * (p.multiplicity (Sum.inr b) : ℝ) := C.covers (Sum.inr b)
      _ = ∑ p : C.SupportBin,
          (C.toFiniteTwoBagJointPackingSwapped h).mass p *
            (p.1.multiplicity (Sum.inr b) : ℝ) := by
        rw [show (∑ p ∈ C.coeff.support,
            C.coeff p * (p.multiplicity (Sum.inr b) : ℝ)) =
            ∑ p : C.SupportBin,
              C.coeff p.1 * (p.1.multiplicity (Sum.inr b) : ℝ) by
          exact Finset.sum_subtype C.coeff.support (by intro p; rfl)
            (fun p ↦ C.coeff p * (p.multiplicity (Sum.inr b) : ℝ))]
        rfl
  · intro a
    calc
      1 ≤ ∑ p ∈ C.coeff.support,
          C.coeff p * (p.multiplicity (Sum.inl a) : ℝ) := C.covers (Sum.inl a)
      _ = ∑ p : C.SupportBin,
          (C.toFiniteTwoBagJointPackingSwapped h).mass p *
            (p.1.multiplicity (Sum.inl a) : ℝ) := by
        rw [show (∑ p ∈ C.coeff.support,
            C.coeff p * (p.multiplicity (Sum.inl a) : ℝ)) =
            ∑ p : C.SupportBin,
              C.coeff p.1 * (p.1.multiplicity (Sum.inl a) : ℝ) by
          exact Finset.sum_subtype C.coeff.support (by intro p; rfl)
            (fun p ↦ C.coeff p * (p.multiplicity (Sum.inl a) : ℝ))]
        rfl

theorem toFiniteTwoBagJointPacking_total
    (C : (A.sum B).FractionalPatternCover)
    (h : C.secondHeavyMass ≤ C.firstHeavyMass) :
    C.cost = ∑ p : C.SupportBin, (C.toFiniteTwoBagJointPacking h).mass p := by
  simpa [toFiniteTwoBagJointPacking] using C.sum_supportMass_eq_cost.symm

theorem toFiniteTwoBagJointPackingSwapped_total
    (C : (A.sum B).FractionalPatternCover)
    (h : C.firstHeavyMass ≤ C.secondHeavyMass) :
    C.cost = ∑ p : C.SupportBin,
      (C.toFiniteTwoBagJointPackingSwapped h).mass p := by
  simpa [toFiniteTwoBagJointPackingSwapped] using C.sum_supportMass_eq_cost.symm

/-- Direct bridge from a joint finite pattern cover to the algebraic
two-bag certificate.  The hypotheses compare the chosen bundle costs with
the operational separated costs.  The orientation and every heavy-bin pair
mass are constructed here. -/
theorem toTwoBagMassCertificate
    (C : (A.sum B).FractionalPatternCover) {a b : ℝ}
    (hfirst : ∀ h : C.secondHeavyMass ≤ C.firstHeavyMass,
      a ≤ (C.toFiniteTwoBagJointPacking h).firstSeparatedCost)
    (hsecond : ∀ h : C.secondHeavyMass ≤ C.firstHeavyMass,
      b ≤ (C.toFiniteTwoBagJointPacking h).secondSeparatedCost)
    (hswappedFirst : ∀ h : C.firstHeavyMass ≤ C.secondHeavyMass,
      b ≤ (C.toFiniteTwoBagJointPackingSwapped h).firstSeparatedCost)
    (hswappedSecond : ∀ h : C.firstHeavyMass ≤ C.secondHeavyMass,
      a ≤ (C.toFiniteTwoBagJointPackingSwapped h).secondSeparatedCost) :
    TwoBagMassCertificate a b C.cost := by
  rcases le_total C.secondHeavyMass C.firstHeavyMass with h | h
  · exact (C.toFiniteTwoBagJointPacking h).toTwoBagMassCertificate
      (C.toFiniteTwoBagJointPacking_total h) (hfirst h) (hsecond h)
  · exact Or.inr ⟨(C.toFiniteTwoBagJointPackingSwapped h).toOrientedTwoBagMassCertificate
      (C.toFiniteTwoBagJointPackingSwapped_total h)
      (hswappedFirst h) (hswappedSecond h)⟩

/-- Fully unconditional finite extraction from chosen optimum bundle covers
and a joint cover.  The operational separated covers are constructed above,
so their cost comparisons follow from the two minimum-cost witnesses. -/
theorem toTwoBagMassCertificate_of_minimumCosts
    (C : (A.sum B).FractionalPatternCover)
    (CA : A.FractionalPatternCover) (CB : B.FractionalPatternCover)
    (hCA : CA.IsMinimumCost) (hCB : CB.IsMinimumCost) :
    TwoBagMassCertificate CA.cost CB.cost C.cost := by
  apply C.toTwoBagMassCertificate
  · intro h
    calc
      CA.cost ≤ (C.toPatternPresentation h).firstSeparatedCover.cost :=
        hCA _
      _ = (C.toFiniteTwoBagJointPacking h).firstSeparatedCost :=
        by simpa [toPatternPresentation] using
          (C.toPatternPresentation h).firstSeparatedCover_cost
  · intro h
    calc
      CB.cost ≤ (C.toPatternPresentation h).secondSeparatedCover.cost :=
        hCB _
      _ = (C.toFiniteTwoBagJointPacking h).secondSeparatedCost :=
        by simpa [toPatternPresentation] using
          (C.toPatternPresentation h).secondSeparatedCover_cost
  · intro h
    calc
      CB.cost ≤ (C.toPatternPresentationSwapped h).firstSeparatedCover.cost :=
        hCB _
      _ = (C.toFiniteTwoBagJointPackingSwapped h).firstSeparatedCost :=
        by simpa [toPatternPresentationSwapped] using
          (C.toPatternPresentationSwapped h).firstSeparatedCover_cost
  · intro h
    calc
      CA.cost ≤ (C.toPatternPresentationSwapped h).secondSeparatedCover.cost :=
        hCA _
      _ = (C.toFiniteTwoBagJointPackingSwapped h).secondSeparatedCost :=
        by simpa [toPatternPresentationSwapped] using
          (C.toPatternPresentationSwapped h).secondSeparatedCover_cost

end BinPackingInstance.FractionalPatternCover

end


end WeightedEdgeColoring
