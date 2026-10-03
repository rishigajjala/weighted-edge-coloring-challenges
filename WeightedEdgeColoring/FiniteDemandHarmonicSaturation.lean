import WeightedEdgeColoring.FiniteDemandPatternCover
import WeightedEdgeColoring.FiniteExactDemandHarmonicMinimum

/-!
# Harmonic saturation of an arbitrary demand cover

Minimum exact covers use no pattern whose harmonic charge is below one.
For linear grouping we obtain a cover with inequalities rather than exact
equalities, so it is useful to have a direct normalization that does not
appeal to minimization.

For every low-charge pattern, replace its mass by homogeneous maximal
patterns, one for each item coordinate.  This preserves every coordinate
coverage, never raises the cost, and leaves positive mass only on patterns
of harmonic charge at least one.  Consequently every integral packet
obtained by flooring the normalized coefficients pays one full unit of
harmonic charge.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance

noncomputable section

universe u

variable (B : BinPackingInstance.{u})

namespace Pattern

/-- A homogeneous maximal pattern has harmonic charge exactly one. -/
@[simp] theorem harmonicPatternCharge_harmonicPattern (i : B.Item) :
    (Pattern.harmonicPattern B i).harmonicPatternCharge = 1 := by
  unfold Pattern.harmonicPatternCharge
  rw [Finset.sum_eq_single i]
  · rw [Pattern.harmonicPattern_multiplicity,
      Pattern.harmonicCharge_eq_inv_harmonicMultiplicity]
    simp only [if_pos]
    have hne : (Pattern.harmonicMultiplicity B i : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Pattern.harmonicMultiplicity_pos B i)
    field_simp [hne]
  · intro j _hj hji
    simp [Pattern.harmonicPattern_multiplicity, hji]
  · simp

end Pattern

namespace DemandPatternCover

variable {B : BinPackingInstance.{u}} {demand : B.Item → ℕ}

/-- Labels used by harmonic saturation: retain one original pattern label,
or replace one low-charge pattern in one item coordinate. -/
abbrev HarmonicSaturationLabel (B : BinPackingInstance.{u}) :=
  B.Pattern ⊕ (B.Pattern × B.Item)

/-- Pattern named by one saturation label. -/
def harmonicSaturationPattern
    (j : HarmonicSaturationLabel B) : B.Pattern :=
  match j with
  | Sum.inl p => p
  | Sum.inr z => Pattern.harmonicPattern B z.2

/-- Mass named by one saturation label.  A low-charge original pattern is
removed and its coordinate demand is supplied by homogeneous patterns. -/
def harmonicSaturationMass (C : B.DemandPatternCover demand)
    (j : HarmonicSaturationLabel B) : ℝ :=
  match j with
  | Sum.inl p => if 1 ≤ p.harmonicPatternCharge then C.coeff p else 0
  | Sum.inr z =>
      if z.1.harmonicPatternCharge < 1 then
        C.coeff z.1 *
          ((z.1.multiplicity z.2 : ℝ) /
            Pattern.harmonicMultiplicity B z.2)
      else 0

theorem harmonicSaturationMass_nonneg
    (C : B.DemandPatternCover demand) :
    ∀ j, 0 ≤ C.harmonicSaturationMass j := by
  intro j
  cases j with
  | inl p =>
      by_cases hp : 1 ≤ p.harmonicPatternCharge
      · simp [harmonicSaturationMass, hp, C.coeff_nonneg p]
      · simp [harmonicSaturationMass, hp]
  | inr z =>
      by_cases hp : z.1.harmonicPatternCharge < 1
      · simp only [harmonicSaturationMass, hp, if_true]
        exact mul_nonneg (C.coeff_nonneg z.1)
          (div_nonneg (Nat.cast_nonneg _)
            (Nat.cast_nonneg _))
      · simp [harmonicSaturationMass, hp]

/-- The saturation labels reproduce exactly the old coverage in every
coordinate. -/
theorem sum_harmonicSaturationMass_mul_multiplicity
    (C : B.DemandPatternCover demand) (i : B.Item) :
    (∑ j : HarmonicSaturationLabel B,
      C.harmonicSaturationMass j *
        ((harmonicSaturationPattern j).multiplicity i : ℝ)) =
      ∑ p : B.Pattern,
        C.coeff p * (p.multiplicity i : ℝ) := by
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hcharge : 1 ≤ p.harmonicPatternCharge
  · have hnlow : ¬ p.harmonicPatternCharge < 1 := not_lt_of_ge hcharge
    simp [harmonicSaturationMass, harmonicSaturationPattern,
      hcharge, hnlow]
  · have hlow : p.harmonicPatternCharge < 1 := lt_of_not_ge hcharge
    have hhom :
        (∑ j : B.Item,
          (C.coeff p *
              ((p.multiplicity j : ℝ) /
                Pattern.harmonicMultiplicity B j)) *
            (((Pattern.harmonicPattern B j).multiplicity i : ℕ) : ℝ)) =
          C.coeff p * (p.multiplicity i : ℝ) := by
      rw [Finset.sum_eq_single i]
      · rw [Pattern.harmonicPattern_multiplicity]
        simp only [if_pos]
        have hne : (Pattern.harmonicMultiplicity B i : ℝ) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt (Pattern.harmonicMultiplicity_pos B i)
        field_simp [hne]
      · intro j _hj hji
        simp [Pattern.harmonicPattern_multiplicity, Ne.symm hji]
      · simp
    simp only [harmonicSaturationMass, harmonicSaturationPattern,
      hcharge, if_false, zero_mul, hlow, if_true]
    simpa using hhom

/-- Normalize a demand cover so every positive coefficient has harmonic
charge at least one. -/
def harmonicSaturate (C : B.DemandPatternCover demand) :
    B.DemandPatternCover demand :=
  DemandPatternCover.ofFinitePatterns
    harmonicSaturationPattern C.harmonicSaturationMass
    C.harmonicSaturationMass_nonneg
    (by
      intro i
      rw [C.sum_harmonicSaturationMass_mul_multiplicity i]
      calc
        (demand i : ℝ) ≤
            ∑ p ∈ C.coeff.support,
              C.coeff p * (p.multiplicity i : ℝ) := C.covers i
        _ = ∑ p : B.Pattern,
              C.coeff p * (p.multiplicity i : ℝ) := by
          exact Finsupp.sum_fintype C.coeff
            (fun p c ↦ c * (p.multiplicity i : ℝ)) (by simp))

/-- Harmonic saturation preserves the full coefficient-level coverage in
every coordinate, not only the coverage written with saturation labels. -/
theorem harmonicSaturate_coverage_eq
    (C : B.DemandPatternCover demand) (i : B.Item) :
    (∑ q : B.Pattern,
      C.harmonicSaturate.coeff q * (q.multiplicity i : ℝ)) =
      ∑ p : B.Pattern,
        C.coeff p * (p.multiplicity i : ℝ) := by
  classical
  rw [← C.sum_harmonicSaturationMass_mul_multiplicity i]
  rw [← Finsupp.sum_fintype C.harmonicSaturate.coeff
    (fun q c ↦ c * (q.multiplicity i : ℝ)) (by simp)]
  change
    ((∑ j : HarmonicSaturationLabel B,
      Finsupp.single (harmonicSaturationPattern j)
        (C.harmonicSaturationMass j)).sum
          (fun q c ↦ c * (q.multiplicity i : ℝ))) =
      ∑ j : HarmonicSaturationLabel B,
        C.harmonicSaturationMass j *
          ((harmonicSaturationPattern j).multiplicity i : ℝ)
  rw [← Finsupp.sum_finset_sum_index]
  · simp
  · intro q
    simp
  · intro q c e
    simp [add_mul]

/-- Harmonic saturation does not increase fractional cost. -/
theorem harmonicSaturate_cost_le (C : B.DemandPatternCover demand) :
    C.harmonicSaturate.cost ≤ C.cost := by
  rw [harmonicSaturate, DemandPatternCover.ofFinitePatterns_cost]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  rw [← Finset.sum_add_distrib]
  rw [← C.sum_coeff_eq_cost]
  apply Finset.sum_le_sum
  intro p _hp
  by_cases hcharge : 1 ≤ p.harmonicPatternCharge
  · have hnlow : ¬ p.harmonicPatternCharge < 1 := not_lt_of_ge hcharge
    simp [harmonicSaturationMass, hcharge, hnlow]
  · have hlow : p.harmonicPatternCharge < 1 := lt_of_not_ge hcharge
    have hsum :
        (∑ i : B.Item,
          C.coeff p *
            ((p.multiplicity i : ℝ) /
              Pattern.harmonicMultiplicity B i)) =
          C.coeff p * p.harmonicPatternCharge := by
      unfold Pattern.harmonicPatternCharge
      simp_rw [Pattern.harmonicCharge_eq_inv_harmonicMultiplicity]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    simp only [harmonicSaturationMass, hcharge, if_false, hlow, if_true]
    rw [hsum]
    have hchargeLe : p.harmonicPatternCharge ≤ 1 := hlow.le
    simpa using mul_le_mul_of_nonneg_left hchargeLe (C.coeff_nonneg p)

/-- A low-charge pattern has zero coefficient after saturation. -/
theorem harmonicSaturate_coeff_eq_zero_of_charge_lt_one
    (C : B.DemandPatternCover demand) (q : B.Pattern)
    (hq : q.harmonicPatternCharge < 1) :
    C.harmonicSaturate.coeff q = 0 := by
  classical
  unfold harmonicSaturate DemandPatternCover.ofFinitePatterns
  change
    (∑ j : HarmonicSaturationLabel B,
      Finsupp.single (harmonicSaturationPattern j)
        (C.harmonicSaturationMass j)) q = 0
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  have hnot : ¬ 1 ≤ q.harmonicPatternCharge := not_le_of_gt hq
  have hleft :
      (∑ p : B.Pattern,
        (Finsupp.applyAddHom q)
          (Finsupp.single (harmonicSaturationPattern (Sum.inl p))
            (C.harmonicSaturationMass (Sum.inl p)))) = 0 := by
    apply Finset.sum_eq_zero
    intro p _hp
    by_cases hpq : p = q
    · subst p
      simp [harmonicSaturationPattern, harmonicSaturationMass, hnot]
    · simp [harmonicSaturationPattern, hpq]
  change (Finsupp.applyAddHom q)
    ((∑ p : B.Pattern,
      Finsupp.single (harmonicSaturationPattern (Sum.inl p))
        (C.harmonicSaturationMass (Sum.inl p))) +
      (∑ p : B.Pattern, ∑ i : B.Item,
        Finsupp.single (harmonicSaturationPattern (Sum.inr (p, i)))
          (C.harmonicSaturationMass (Sum.inr (p, i))))) = 0
  rw [map_add]
  simp only [map_sum]
  rw [hleft, zero_add]
  apply Finset.sum_eq_zero
  intro p _hp
  apply Finset.sum_eq_zero
  intro i _hi
  have hneq : Pattern.harmonicPattern B i ≠ q := by
    intro heq
    have heqCharge := congrArg (Pattern.harmonicPatternCharge B) heq
    rw [Pattern.harmonicPatternCharge_harmonicPattern] at heqCharge
    linarith
  simp [harmonicSaturationPattern, hneq]

/-- Every pattern with positive mass after saturation has harmonic charge at
least one. -/
theorem harmonicPatternCharge_ge_one_of_harmonicSaturate_coeff_pos
    (C : B.DemandPatternCover demand) (q : B.Pattern)
    (hpos : 0 < C.harmonicSaturate.coeff q) :
    1 ≤ q.harmonicPatternCharge := by
  by_contra hnot
  have hlt : q.harmonicPatternCharge < 1 := lt_of_not_ge hnot
  rw [C.harmonicSaturate_coeff_eq_zero_of_charge_lt_one q hlt] at hpos
  exact lt_irrefl 0 hpos

/-- Every integral floor packet of the saturated cover carries at least one
unit of harmonic charge. -/
theorem floorPacket_harmonicPatternCharge_ge_one
    (C : B.DemandPatternCover demand)
    (q : C.harmonicSaturate.FloorPacket) :
    1 ≤ q.1.harmonicPatternCharge := by
  by_contra hnot
  have hlt : q.1.harmonicPatternCharge < 1 := lt_of_not_ge hnot
  have hz := C.harmonicSaturate_coeff_eq_zero_of_charge_lt_one q.1 hlt
  have hfloor : 0 < Nat.floor (C.harmonicSaturate.coeff q.1) :=
    Nat.pos_of_ne_zero (fun hzero ↦ by simpa [hzero] using q.2.isLt)
  rw [hz] at hfloor
  simp at hfloor

end DemandPatternCover

end

end BinPackingInstance
end WeightedEdgeColoring

#print axioms WeightedEdgeColoring.BinPackingInstance.DemandPatternCover.harmonicSaturate_cost_le
#print axioms WeightedEdgeColoring.BinPackingInstance.DemandPatternCover.harmonicSaturate_coverage_eq
#print axioms WeightedEdgeColoring.BinPackingInstance.DemandPatternCover.harmonicPatternCharge_ge_one_of_harmonicSaturate_coeff_pos
#print axioms WeightedEdgeColoring.BinPackingInstance.DemandPatternCover.floorPacket_harmonicPatternCharge_ge_one
