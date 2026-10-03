import WeightedEdgeColoring.FiniteExactDemandPatternCover
import WeightedEdgeColoring.HarmonicBinCharge

/-!
# Harmonic saturation of minimum exact-demand covers

A pattern whose total harmonic charge is below one can be replaced by the
same amount of homogeneous maximal patterns at strictly smaller cost.  Thus
such a pattern has zero coefficient in every minimum exact-demand cover.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance

noncomputable section

universe u

variable (B : BinPackingInstance.{u})

namespace Pattern

/-- Maximum feasible multiplicity of one item type. -/
def harmonicMultiplicity (i : B.Item) : ℕ :=
  Nat.floor (1 / B.weight i)

theorem harmonicMultiplicity_pos (i : B.Item) :
    0 < Pattern.harmonicMultiplicity B i := by
  apply Nat.le_floor
  rw [le_div_iff₀ (B.weight_pos i)]
  simpa using B.weight_le_one i

/-- The homogeneous bin containing as many copies of `i` as fit. -/
def harmonicPattern (i : B.Item) : B.Pattern where
  multiplicity j := if j = i then Pattern.harmonicMultiplicity B i else 0
  capacity := by
    simp only [Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h := Nat.floor_le (div_nonneg zero_le_one (B.weight_pos i).le)
    exact (le_div_iff₀ (B.weight_pos i)).mp h

@[simp] theorem harmonicPattern_multiplicity (i j : B.Item) :
    (Pattern.harmonicPattern B i).multiplicity j =
      if j = i then Pattern.harmonicMultiplicity B i else 0 := rfl

/-- Harmonic charge carried by a bin pattern. -/
def harmonicPatternCharge (p : B.Pattern) : ℝ :=
  ∑ i : B.Item, (p.multiplicity i : ℝ) * harmonicCharge (B.weight i)

theorem harmonicCharge_eq_inv_harmonicMultiplicity (i : B.Item) :
    harmonicCharge (B.weight i) =
      (1 : ℝ) / Pattern.harmonicMultiplicity B i := by
  rfl

end Pattern

namespace ExactDemandPatternCover

variable {B} {demand : B.Item → ℕ}

theorem sum_coeff_mul_multiplicity_eq
    (C : B.ExactDemandPatternCover demand) (i : B.Item) :
    (∑ p : B.Pattern, C.coeff p * (p.multiplicity i : ℝ)) = demand i := by
  calc
    _ = ∑ p ∈ C.coeff.support,
        C.coeff p * (p.multiplicity i : ℝ) := by
      symm
      exact Finsupp.sum_fintype C.coeff
        (fun p c ↦ c * (p.multiplicity i : ℝ)) (by simp)
    _ = demand i := C.covers_exact i

/-- A minimum exact-demand cover cannot put positive mass on a pattern of
harmonic charge below one. -/
theorem coeff_eq_zero_of_harmonicPatternCharge_lt_one
    (C : B.ExactDemandPatternCover demand) (hmin : C.IsMinimumCost)
    (p : B.Pattern) (hp : p.harmonicPatternCharge < 1) :
    C.coeff p = 0 := by
  by_contra hne
  have hcpos : 0 < C.coeff p := lt_of_le_of_ne (C.coeff_nonneg p) (Ne.symm hne)
  let pattern : B.Pattern ⊕ B.Item → B.Pattern
    | Sum.inl q => q
    | Sum.inr i => Pattern.harmonicPattern B i
  let mass : B.Pattern ⊕ B.Item → ℝ
    | Sum.inl q => if q = p then 0 else C.coeff q
    | Sum.inr i => C.coeff p *
        ((p.multiplicity i : ℝ) / Pattern.harmonicMultiplicity B i)
  have hmass : ∀ j, 0 ≤ mass j := by
    intro j
    cases j with
    | inl q =>
        by_cases hq : q = p <;> simp [mass, hq, C.coeff_nonneg q]
    | inr i =>
        exact mul_nonneg (C.coeff_nonneg p) (div_nonneg (Nat.cast_nonneg _)
          (Nat.cast_nonneg _))
  have hcovers : ∀ i : B.Item,
      (∑ j : B.Pattern ⊕ B.Item,
        mass j * ((pattern j).multiplicity i : ℝ)) = demand i := by
    intro i
    rw [Fintype.sum_sum_type]
    have hremove (f : B.Pattern → ℝ) :
        (∑ q : B.Pattern, if q = p then 0 else f q) =
          (∑ q : B.Pattern, f q) - f p := by
      have hadd := Finset.sum_erase_add (Finset.univ : Finset B.Pattern)
        f (Finset.mem_univ p)
      calc
        (∑ q : B.Pattern, if q = p then 0 else f q) =
            ∑ q : B.Pattern, if q ≠ p then f q else 0 := by
          apply Finset.sum_congr rfl
          intro q _hq
          by_cases hqp : q = p <;> simp [hqp]
        _ = ∑ q ∈ (Finset.univ : Finset B.Pattern).erase p, f q := by
          rw [← Finset.sum_filter]
          congr 1
          ext q
          simp
        _ = (∑ q : B.Pattern, f q) - f p := by linarith
    have hleft :
        (∑ q : B.Pattern,
          (if q = p then 0 else C.coeff q) * (q.multiplicity i : ℝ)) =
          (demand i : ℝ) - C.coeff p * (p.multiplicity i : ℝ) := by
      calc
        _ = (∑ q : B.Pattern,
              C.coeff q * (q.multiplicity i : ℝ)) -
            C.coeff p * (p.multiplicity i : ℝ) := by
          simp_rw [ite_mul, zero_mul]
          exact hremove (fun q ↦ C.coeff q * (q.multiplicity i : ℝ))
        _ = (demand i : ℝ) -
            C.coeff p * (p.multiplicity i : ℝ) := by
          rw [C.sum_coeff_mul_multiplicity_eq]
    have hright :
        (∑ j : B.Item,
          (C.coeff p * ((p.multiplicity j : ℝ) /
              Pattern.harmonicMultiplicity B j)) *
            ((Pattern.harmonicPattern B j).multiplicity i : ℝ)) =
          C.coeff p * (p.multiplicity i : ℝ) := by
      rw [Finset.sum_eq_single i]
      · simp only [Pattern.harmonicPattern_multiplicity, if_pos]
        have hr0 : (Pattern.harmonicMultiplicity B i : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (Pattern.harmonicMultiplicity_pos B i))
        field_simp [hr0]
      · intro j _hj hji
        simp [Pattern.harmonicPattern_multiplicity, hji, Ne.symm hji]
      · simp
    change
      (∑ q : B.Pattern,
        (if q = p then 0 else C.coeff q) * (q.multiplicity i : ℝ)) +
      (∑ j : B.Item,
        (C.coeff p * ((p.multiplicity j : ℝ) /
          Pattern.harmonicMultiplicity B j)) *
          ((Pattern.harmonicPattern B j).multiplicity i : ℝ)) = _
    rw [hleft, hright]
    ring
  let D : B.ExactDemandPatternCover demand :=
    ofFinitePatterns pattern mass hmass hcovers
  have hcost : D.cost =
      C.cost - C.coeff p + C.coeff p * p.harmonicPatternCharge := by
    change (ofFinitePatterns pattern mass hmass hcovers).cost = _
    rw [ofFinitePatterns_cost, Fintype.sum_sum_type]
    have hremove (f : B.Pattern → ℝ) :
        (∑ q : B.Pattern, if q = p then 0 else f q) =
          (∑ q : B.Pattern, f q) - f p := by
      have hadd := Finset.sum_erase_add (Finset.univ : Finset B.Pattern)
        f (Finset.mem_univ p)
      calc
        (∑ q : B.Pattern, if q = p then 0 else f q) =
            ∑ q : B.Pattern, if q ≠ p then f q else 0 := by
          apply Finset.sum_congr rfl
          intro q _hq
          by_cases hqp : q = p <;> simp [hqp]
        _ = ∑ q ∈ (Finset.univ : Finset B.Pattern).erase p, f q := by
          rw [← Finset.sum_filter]
          congr 1
          ext q
          simp
        _ = (∑ q : B.Pattern, f q) - f p := by linarith
    have hleft :
        (∑ q : B.Pattern, if q = p then 0 else C.coeff q) =
          C.cost - C.coeff p := by
      rw [← C.sum_coeff_eq_cost]
      exact hremove C.coeff
    rw [hleft]
    unfold Pattern.harmonicPatternCharge
    simp only [mass, Pattern.harmonicCharge_eq_inv_harmonicMultiplicity]
    rw [Finset.mul_sum]
    ring
  have hlower := hmin D
  rw [hcost] at hlower
  nlinarith

end ExactDemandPatternCover

end

end BinPackingInstance
end WeightedEdgeColoring
