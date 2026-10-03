import WeightedEdgeColoring.BPGeneralPatternTwoBagExtraction
import WeightedEdgeColoring.BPGeneralFiniteTwoBagOperationalCovers
import WeightedEdgeColoring.FiniteExactDemandPatternCover

/-!
# Two-bag extraction for exact count demands

The ordinary fractional-cover API permits overcoverage.  Here the same
finite heavy-bin pairing is fed an exact-demand joint cover.  The two
operational separated covers preserve the marginal demands exactly, so
minimum exact-demand costs satisfy the two-bag certificate.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u v

namespace BinPackingInstance.ExactDemandPatternCover

variable {A : BinPackingInstance.{u}} {B : BinPackingInstance.{v}}
variable {firstDemand : A.Item → ℕ} {secondDemand : B.Item → ℕ}

/-- Demand vector on a disjoint union, formed from its two marginals. -/
abbrev sumDemand (firstDemand : A.Item → ℕ)
    (secondDemand : B.Item → ℕ) : (A.sum B).Item → ℕ :=
  Sum.elim firstDemand secondDemand

private theorem exact_first_coverage
    (C : (A.sum B).ExactDemandPatternCover
      (sumDemand firstDemand secondDemand))
    (hfirstPos : ∀ a, 1 ≤ firstDemand a)
    (hsecondPos : ∀ b, 1 ≤ secondDemand b)
    (h :
      (C.toFractionalPatternCover (fun i ↦ by
        cases i with
        | inl a => exact hfirstPos a
        | inr b => exact hsecondPos b)).secondHeavyMass ≤
      (C.toFractionalPatternCover (fun i ↦ by
        cases i with
        | inl a => exact hfirstPos a
        | inr b => exact hsecondPos b)).firstHeavyMass)
    (a : A.Item) :
    let FC := C.toFractionalPatternCover (fun i ↦ by
      cases i with
      | inl a => exact hfirstPos a
      | inr b => exact hsecondPos b)
    ∑ p : FC.SupportBin,
      (FC.toFiniteTwoBagJointPacking h).mass p *
        (p.1.multiplicity (Sum.inl a) : ℝ) = firstDemand a := by
  dsimp
  change (∑ p : {p // p ∈ C.coeff.support},
    C.coeff p.1 * (p.1.multiplicity (Sum.inl a) : ℝ)) = firstDemand a
  calc
    (∑ p : {p // p ∈ C.coeff.support},
      C.coeff p.1 * (p.1.multiplicity (Sum.inl a) : ℝ)) =
        ∑ p ∈ C.coeff.support,
          C.coeff p * (p.multiplicity (Sum.inl a) : ℝ) :=
      (Finset.sum_subtype C.coeff.support (by intro p; rfl)
        (fun p ↦ C.coeff p *
          (p.multiplicity (Sum.inl a) : ℝ))).symm
    _ = firstDemand a := C.covers_exact (Sum.inl a)

private theorem exact_second_coverage
    (C : (A.sum B).ExactDemandPatternCover
      (sumDemand firstDemand secondDemand))
    (hfirstPos : ∀ a, 1 ≤ firstDemand a)
    (hsecondPos : ∀ b, 1 ≤ secondDemand b)
    (h :
      (C.toFractionalPatternCover (fun i ↦ by
        cases i with
        | inl a => exact hfirstPos a
        | inr b => exact hsecondPos b)).secondHeavyMass ≤
      (C.toFractionalPatternCover (fun i ↦ by
        cases i with
        | inl a => exact hfirstPos a
        | inr b => exact hsecondPos b)).firstHeavyMass)
    (b : B.Item) :
    let FC := C.toFractionalPatternCover (fun i ↦ by
      cases i with
      | inl a => exact hfirstPos a
      | inr b => exact hsecondPos b)
    ∑ p : FC.SupportBin,
      (FC.toFiniteTwoBagJointPacking h).mass p *
        (p.1.multiplicity (Sum.inr b) : ℝ) = secondDemand b := by
  dsimp
  change (∑ p : {p // p ∈ C.coeff.support},
    C.coeff p.1 * (p.1.multiplicity (Sum.inr b) : ℝ)) = secondDemand b
  calc
    (∑ p : {p // p ∈ C.coeff.support},
      C.coeff p.1 * (p.1.multiplicity (Sum.inr b) : ℝ)) =
        ∑ p ∈ C.coeff.support,
          C.coeff p * (p.multiplicity (Sum.inr b) : ℝ) :=
      (Finset.sum_subtype C.coeff.support (by intro p; rfl)
        (fun p ↦ C.coeff p *
          (p.multiplicity (Sum.inr b) : ℝ))).symm
    _ = secondDemand b := C.covers_exact (Sum.inr b)

/-- A joint exact-demand cover and minimum exact covers of its two marginals
produce the same two-bag mass certificate as in the unit-demand theory. -/
theorem toTwoBagMassCertificate_of_minimumExactCosts
    (C : (A.sum B).ExactDemandPatternCover
      (sumDemand firstDemand secondDemand))
    (hfirstPos : ∀ a, 1 ≤ firstDemand a)
    (hsecondPos : ∀ b, 1 ≤ secondDemand b)
    (CA : A.ExactDemandPatternCover firstDemand)
    (CB : B.ExactDemandPatternCover secondDemand)
    (hCA : CA.IsMinimumCost) (hCB : CB.IsMinimumCost) :
    TwoBagMassCertificate CA.cost CB.cost C.cost := by
  let hpos : ∀ i : (A.sum B).Item,
      1 ≤ sumDemand firstDemand secondDemand i := fun i ↦ by
    cases i with
    | inl a => exact hfirstPos a
    | inr b => exact hsecondPos b
  let FC := C.toFractionalPatternCover hpos
  have hFCcost : FC.cost = C.cost := rfl
  rw [← hFCcost]
  apply FC.toTwoBagMassCertificate
  · intro h
    let D := FC.toPatternPresentation h
    let E := D.firstSeparatedExactDemandCover firstDemand
      (fun a ↦ C.exact_first_coverage hfirstPos hsecondPos h a)
    calc
      CA.cost ≤ E.cost := hCA E
      _ = (FC.toFiniteTwoBagJointPacking h).firstSeparatedCost := by
        exact D.firstSeparatedExactDemandCover_cost firstDemand
          (fun a ↦ C.exact_first_coverage hfirstPos hsecondPos h a)
  · intro h
    let D := FC.toPatternPresentation h
    let E := D.secondSeparatedExactDemandCover secondDemand
      (fun b ↦ C.exact_second_coverage hfirstPos hsecondPos h b)
    calc
      CB.cost ≤ E.cost := hCB E
      _ = (FC.toFiniteTwoBagJointPacking h).secondSeparatedCost := by
        exact D.secondSeparatedExactDemandCover_cost secondDemand
          (fun b ↦ C.exact_second_coverage hfirstPos hsecondPos h b)
  · intro h
    let D := FC.toPatternPresentationSwapped h
    have hfirst : ∀ b : B.Item,
        (∑ p : FC.SupportBin,
          (FC.toFiniteTwoBagJointPackingSwapped h).mass p *
            (p.1.multiplicity (Sum.inr b) : ℝ)) = secondDemand b := by
      intro b
      change (∑ p : {p // p ∈ C.coeff.support},
        C.coeff p.1 * (p.1.multiplicity (Sum.inr b) : ℝ)) = secondDemand b
      exact (Finset.sum_subtype C.coeff.support (by intro p; rfl)
        (fun p ↦ C.coeff p *
          (p.multiplicity (Sum.inr b) : ℝ))).symm.trans
            (C.covers_exact (Sum.inr b))
    let E := D.firstSeparatedExactDemandCover secondDemand hfirst
    calc
      CB.cost ≤ E.cost := hCB E
      _ = (FC.toFiniteTwoBagJointPackingSwapped h).firstSeparatedCost := by
        exact D.firstSeparatedExactDemandCover_cost secondDemand hfirst
  · intro h
    let D := FC.toPatternPresentationSwapped h
    have hsecond : ∀ a : A.Item,
        (∑ p : FC.SupportBin,
          (FC.toFiniteTwoBagJointPackingSwapped h).mass p *
            (p.1.multiplicity (Sum.inl a) : ℝ)) = firstDemand a := by
      intro a
      change (∑ p : {p // p ∈ C.coeff.support},
        C.coeff p.1 * (p.1.multiplicity (Sum.inl a) : ℝ)) = firstDemand a
      exact (Finset.sum_subtype C.coeff.support (by intro p; rfl)
        (fun p ↦ C.coeff p *
          (p.multiplicity (Sum.inl a) : ℝ))).symm.trans
            (C.covers_exact (Sum.inl a))
    let E := D.secondSeparatedExactDemandCover firstDemand hsecond
    calc
      CA.cost ≤ E.cost := hCA E
      _ = (FC.toFiniteTwoBagJointPackingSwapped h).secondSeparatedCost := by
        exact D.secondSeparatedExactDemandCover_cost firstDemand hsecond

/-- Minimum marginal exact-demand covers can be selected canonically before
performing the two-bag extraction. -/
theorem exists_minimumExactCovers_with_twoBagMassCertificate
    (C : (A.sum B).ExactDemandPatternCover
      (sumDemand firstDemand secondDemand))
    (hfirstPos : ∀ a, 1 ≤ firstDemand a)
    (hsecondPos : ∀ b, 1 ≤ secondDemand b) :
    ∃ CA : A.ExactDemandPatternCover firstDemand,
      ∃ CB : B.ExactDemandPatternCover secondDemand,
        CA.IsMinimumCost ∧ CB.IsMinimumCost ∧
          TwoBagMassCertificate CA.cost CB.cost C.cost := by
  obtain ⟨CA, hCA⟩ := exists_minimumCost A firstDemand
  obtain ⟨CB, hCB⟩ := exists_minimumCost B secondDemand
  exact ⟨CA, CB, hCA, hCB,
    C.toTwoBagMassCertificate_of_minimumExactCosts
      hfirstPos hsecondPos CA CB hCA hCB⟩

/-- Three pairwise joint exact-demand covers bound the sum of the three
minimum marginal costs by twice their common cost bound.  This is the exact
count-demand form of the three-bundle numerical step. -/
theorem three_minimumExactCosts_le_two_mul_of_pairwiseCovers
    {Cinst : BinPackingInstance} {thirdDemand : Cinst.Item → ℕ}
    (hfirstPos : ∀ a, 1 ≤ firstDemand a)
    (hsecondPos : ∀ b, 1 ≤ secondDemand b)
    (hthirdPos : ∀ c, 1 ≤ thirdDemand c)
    (CA : A.ExactDemandPatternCover firstDemand)
    (CB : B.ExactDemandPatternCover secondDemand)
    (CC : Cinst.ExactDemandPatternCover thirdDemand)
    (hCA : CA.IsMinimumCost) (hCB : CB.IsMinimumCost)
    (hCC : CC.IsMinimumCost)
    (Jab : (A.sum B).ExactDemandPatternCover
      (sumDemand firstDemand secondDemand))
    (Jac : (A.sum Cinst).ExactDemandPatternCover
      (sumDemand firstDemand thirdDemand))
    (Jbc : (B.sum Cinst).ExactDemandPatternCover
      (sumDemand secondDemand thirdDemand))
    {n : ℝ} (hJab : Jab.cost ≤ n) (hJac : Jac.cost ≤ n)
    (hJbc : Jbc.cost ≤ n) :
    CA.cost + CB.cost + CC.cost ≤ 2 * n := by
  apply three_cost_le_two_mul_of_pairwise_massCertificates
  · exact Jab.toTwoBagMassCertificate_of_minimumExactCosts
      hfirstPos hsecondPos CA CB hCA hCB
  · exact hJab
  · exact Jac.toTwoBagMassCertificate_of_minimumExactCosts
      hfirstPos hthirdPos CA CC hCA hCC
  · exact hJac
  · exact Jbc.toTwoBagMassCertificate_of_minimumExactCosts
      hsecondPos hthirdPos CB CC hCB hCC
  · exact hJbc

/-- Natural packet counts dominated by the three minimum exact-demand costs
obey the required `2n` bound whenever each adjacent pair has a joint cover
of cost at most `n`. -/
theorem three_packetCounts_le_two_mul_of_pairwiseExactCovers
    {Cinst : BinPackingInstance} {thirdDemand : Cinst.Item → ℕ}
    (pA pB pC : ℕ)
    (hfirstPos : ∀ a, 1 ≤ firstDemand a)
    (hsecondPos : ∀ b, 1 ≤ secondDemand b)
    (hthirdPos : ∀ c, 1 ≤ thirdDemand c)
    (CA : A.ExactDemandPatternCover firstDemand)
    (CB : B.ExactDemandPatternCover secondDemand)
    (CC : Cinst.ExactDemandPatternCover thirdDemand)
    (hCA : CA.IsMinimumCost) (hCB : CB.IsMinimumCost)
    (hCC : CC.IsMinimumCost)
    (hpA : (pA : ℝ) ≤ CA.cost) (hpB : (pB : ℝ) ≤ CB.cost)
    (hpC : (pC : ℝ) ≤ CC.cost)
    (Jab : (A.sum B).ExactDemandPatternCover
      (sumDemand firstDemand secondDemand))
    (Jac : (A.sum Cinst).ExactDemandPatternCover
      (sumDemand firstDemand thirdDemand))
    (Jbc : (B.sum Cinst).ExactDemandPatternCover
      (sumDemand secondDemand thirdDemand))
    {n : ℝ} (hJab : Jab.cost ≤ n) (hJac : Jac.cost ≤ n)
    (hJbc : Jbc.cost ≤ n) :
    ((pA + pB + pC : ℕ) : ℝ) ≤ 2 * n := by
  have hcost := three_minimumExactCosts_le_two_mul_of_pairwiseCovers
    hfirstPos hsecondPos hthirdPos CA CB CC hCA hCB hCC
    Jab Jac Jbc hJab hJac hJbc
  push_cast
  linarith

/-- Integral `n`-bin packings of all three adjacent demand pairs imply the
`2n` packet-count bound, provided each packet count is dominated by the
minimum exact-demand cost of its own bundle. -/
theorem three_packetCounts_le_two_mul_of_pairwisePacksInto
    {Cinst : BinPackingInstance} {thirdDemand : Cinst.Item → ℕ}
    (pA pB pC n : ℕ)
    (hfirstPos : ∀ a, 1 ≤ firstDemand a)
    (hsecondPos : ∀ b, 1 ≤ secondDemand b)
    (hthirdPos : ∀ c, 1 ≤ thirdDemand c)
    (hpA : ∀ CA : A.ExactDemandPatternCover firstDemand,
      CA.IsMinimumCost → (pA : ℝ) ≤ CA.cost)
    (hpB : ∀ CB : B.ExactDemandPatternCover secondDemand,
      CB.IsMinimumCost → (pB : ℝ) ≤ CB.cost)
    (hpC : ∀ CC : Cinst.ExactDemandPatternCover thirdDemand,
      CC.IsMinimumCost → (pC : ℝ) ≤ CC.cost)
    (hAB : ExactDemandPatternCover.PacksInto
      (B := A.sum B) (sumDemand firstDemand secondDemand) n)
    (hAC : ExactDemandPatternCover.PacksInto
      (B := A.sum Cinst) (sumDemand firstDemand thirdDemand) n)
    (hBC : ExactDemandPatternCover.PacksInto
      (B := B.sum Cinst) (sumDemand secondDemand thirdDemand) n) :
    pA + pB + pC ≤ 2 * n := by
  obtain ⟨CA, hCA⟩ := exists_minimumCost A firstDemand
  obtain ⟨CB, hCB⟩ := exists_minimumCost B secondDemand
  obtain ⟨CC, hCC⟩ := exists_minimumCost Cinst thirdDemand
  obtain ⟨Jab, hJab⟩ := exists_cost_eq_of_packsInto hAB
  obtain ⟨Jac, hJac⟩ := exists_cost_eq_of_packsInto hAC
  obtain ⟨Jbc, hJbc⟩ := exists_cost_eq_of_packsInto hBC
  have hreal := three_packetCounts_le_two_mul_of_pairwiseExactCovers
    pA pB pC hfirstPos hsecondPos hthirdPos
    CA CB CC hCA hCB hCC (hpA CA hCA) (hpB CB hCB) (hpC CC hCC)
    Jab Jac Jbc hJab.le hJac.le hJbc.le
  exact_mod_cast hreal

end BinPackingInstance.ExactDemandPatternCover

end

end WeightedEdgeColoring
