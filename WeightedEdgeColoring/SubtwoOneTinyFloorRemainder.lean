import WeightedEdgeColoring.SubtwoBoundedTypeFloorResidual

/-! Coefficient floors with bounded core types and one tiny demand coordinate. -/

namespace WeightedEdgeColoring.BinPackingInstance

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000

universe u
variable {B : BinPackingInstance.{u}} {demand : B.Item → ℕ}

namespace ExactDemandPatternCover

variable (C : B.ExactDemandPatternCover demand)

private def purePatterns (tiny : B.Item) : Finset B.Pattern :=
  Finset.univ.filter fun p => p.multiplicity tiny = 0

/-- Pure-core patterns have a bounded code even if the exceptional tiny
coordinate has no reciprocal-weight bound. -/
private theorem card_purePatterns_le_pow (tiny : B.Item) (S : ℕ)
    (hcore : ∀ p : B.Pattern, ∀ i : B.Item, i ≠ tiny →
      p.multiplicity i ≤ S) :
    (purePatterns tiny).card ≤ (S + 1) ^ Fintype.card B.Item := by
  classical
  let code : {p : B.Pattern // p ∈ purePatterns tiny} →
      (∀ i : B.Item, Fin (S + 1)) := fun p i =>
    ⟨p.1.multiplicity i, by
      by_cases hi : i = tiny
      · subst i
        have hp0 := (Finset.mem_filter.mp p.2).2
        omega
      · exact Nat.lt_succ_of_le (hcore p.1 i hi)⟩
  have hinj : Function.Injective code := by
    intro p q h
    apply Subtype.ext
    cases p with | mk p hp =>
      cases q with | mk q hq =>
        have hm : p.multiplicity = q.multiplicity := by
          funext i
          exact congrArg Fin.val (congrFun h i)
        cases p with | mk pm pc =>
          cases q with | mk qm qc =>
            simp only at hm
            congr

  calc
    (purePatterns tiny).card = Fintype.card {p : B.Pattern // p ∈ purePatterns tiny} :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card (∀ i : B.Item, Fin (S + 1)) :=
      Fintype.card_le_of_injective code hinj
    _ = (S + 1) ^ Fintype.card B.Item := by simp

/-- Exact demand at the exceptional coordinate pays for all patterns that
contain it; their total coefficient mass is at most one when tiny demand is
at most one. -/
private theorem tinyPattern_coeff_mass_le (tiny : B.Item) :
    (∑ p : B.Pattern,
      if p.multiplicity tiny = 0 then 0 else C.coeff p) ≤ demand tiny := by
  calc
    _ ≤ ∑ p : B.Pattern,
        C.coeff p * (p.multiplicity tiny : ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : p.multiplicity tiny = 0
      · simp [hp, C.coeff_nonneg p]
      · have hm : 1 ≤ p.multiplicity tiny := Nat.one_le_iff_ne_zero.mpr hp
        simp only [if_neg hp]
        have hmR : (1 : ℝ) ≤ (p.multiplicity tiny : ℝ) := by exact_mod_cast hm
        nlinarith [mul_nonneg (C.coeff_nonneg p) (sub_nonneg.mpr hmR)]
    _ = demand tiny := C.sum_coeff_mul_multiplicity_eq tiny

/-- Each bounded core coordinate has a demand-independent floor remainder,
even though the exceptional tiny coordinate may have arbitrarily small
weight. -/
theorem core_floorResidualDemand_le_oneTiny
    (tiny i : B.Item) (S : ℕ) (hi : i ≠ tiny)
    (hcore : ∀ p : B.Pattern, ∀ j : B.Item, j ≠ tiny →
      p.multiplicity j ≤ S)
    (htiny : demand tiny ≤ 1) :
    C.floorResidualDemand i ≤
      (S + 1) ^ Fintype.card B.Item * S + S := by
  let δ : B.Pattern → ℝ := fun p =>
    C.coeff p - (Nat.floor (C.coeff p) : ℝ)
  have hdelta : ∀ p, 0 ≤ δ p ∧ δ p ≤ 1 ∧ δ p ≤ C.coeff p := by
    intro p
    dsimp [δ]
    constructor
    · exact sub_nonneg.mpr (Nat.floor_le (C.coeff_nonneg p))
    constructor
    · linarith [(Nat.lt_floor_add_one (C.coeff p)).le]
    · have hfloor0 : (0 : ℝ) ≤ (Nat.floor (C.coeff p) : ℝ) := by positivity
      linarith
  have heq : (C.floorResidualDemand i : ℝ) =
      ∑ p : B.Pattern, δ p * (p.multiplicity i : ℝ) := by
    have hfloor := C.floorCoveredDemand_le i
    have hcovered : (C.floorCoveredDemand i : ℝ) =
        ∑ p : B.Pattern,
          (Nat.floor (C.coeff p) : ℝ) * (p.multiplicity i : ℝ) := by
      simp [floorCoveredDemand, Nat.cast_sum, Nat.cast_mul]
    rw [floorResidualDemand, Nat.cast_sub hfloor, hcovered,
      ← C.sum_coeff_mul_multiplicity_eq i]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    dsimp [δ]
    ring
  have hterm (p : B.Pattern) :
      δ p * (p.multiplicity i : ℝ) ≤
        if p.multiplicity tiny = 0 then (S : ℝ) else C.coeff p * S := by
    have hmult : (p.multiplicity i : ℝ) ≤ S := by
      exact_mod_cast hcore p i hi
    by_cases hp : p.multiplicity tiny = 0
    · simp only [if_pos hp]
      nlinarith [hdelta p]
    · simp only [if_neg hp]
      nlinarith [hdelta p, C.coeff_nonneg p]
  have hpure :
      (∑ p : B.Pattern,
        if p.multiplicity tiny = 0 then (S : ℝ) else 0) =
      (purePatterns tiny).card * S := by
    simp [purePatterns, ← Finset.sum_filter]
  have htinyMass :
      (∑ p : B.Pattern,
        if p.multiplicity tiny = 0 then 0 else C.coeff p * S) ≤ S := by
    calc
      _ = (∑ p : B.Pattern,
          if p.multiplicity tiny = 0 then 0 else C.coeff p) * S := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _
        split <;> ring
      _ ≤ (demand tiny : ℝ) * S := by
        exact mul_le_mul_of_nonneg_right (C.tinyPattern_coeff_mass_le tiny)
          (Nat.cast_nonneg S)
      _ ≤ S := by
        exact mul_le_of_le_one_left (Nat.cast_nonneg S) (by exact_mod_cast htiny)
  have hcard : ((purePatterns tiny).card : ℝ) ≤
      ((S + 1) ^ Fintype.card B.Item : ℕ) := by
    exact_mod_cast card_purePatterns_le_pow tiny S hcore
  have hbound : (C.floorResidualDemand i : ℝ) ≤
      (((S + 1) ^ Fintype.card B.Item * S + S : ℕ) : ℝ) := by
    calc
      (C.floorResidualDemand i : ℝ) =
          ∑ p : B.Pattern, δ p * (p.multiplicity i : ℝ) := heq
      _ ≤ ∑ p : B.Pattern,
          if p.multiplicity tiny = 0 then (S : ℝ) else C.coeff p * S :=
        Finset.sum_le_sum (fun p _ => hterm p)
      _ = (purePatterns tiny).card * S +
          ∑ p : B.Pattern,
            if p.multiplicity tiny = 0 then 0 else C.coeff p * S := by
        rw [← hpure, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p _
        split <;> ring
      _ ≤ ((S + 1) ^ Fintype.card B.Item : ℝ) * S + S := by
        have hmul := mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg S)
        push_cast at hmul
        nlinarith
      _ = _ := by push_cast; ring
  exact_mod_cast hbound

/-- Summing every coordinate, including the exceptional tiny one, gives a
fixed bound on the whole coefficient-floor residual. -/
theorem sum_floorResidualDemand_le_oneTiny
    (tiny : B.Item) (D S : ℕ)
    (hcard : Fintype.card B.Item ≤ D + 1)
    (hcore : ∀ p : B.Pattern, ∀ j : B.Item, j ≠ tiny →
      p.multiplicity j ≤ S)
    (htiny : demand tiny ≤ 1) :
    (∑ i : B.Item, C.floorResidualDemand i) ≤
      (D + 1) * (((S + 1) ^ (D + 1) * S + S) + 1) := by
  have hpow : (S + 1) ^ Fintype.card B.Item ≤
      (S + 1) ^ (D + 1) :=
    Nat.pow_le_pow_right (by omega) hcard
  have hcoord : ∀ i : B.Item,
      C.floorResidualDemand i ≤
        ((S + 1) ^ (D + 1) * S + S) + 1 := by
    intro i
    by_cases hi : i = tiny
    · subst i
      calc
        C.floorResidualDemand tiny ≤ demand tiny := Nat.sub_le _ _
        _ ≤ 1 := htiny
        _ ≤ ((S + 1) ^ (D + 1) * S + S) + 1 := by omega
    · calc
        C.floorResidualDemand i ≤
            (S + 1) ^ Fintype.card B.Item * S + S :=
          C.core_floorResidualDemand_le_oneTiny tiny i S hi hcore htiny
        _ ≤ (S + 1) ^ (D + 1) * S + S := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_right S hpow) S
        _ ≤ ((S + 1) ^ (D + 1) * S + S) + 1 := by omega
  calc
    (∑ i : B.Item, C.floorResidualDemand i) ≤
        ∑ _i : B.Item, (((S + 1) ^ (D + 1) * S + S) + 1) := by
      exact Finset.sum_le_sum fun i _ => hcoord i
    _ = Fintype.card B.Item *
          (((S + 1) ^ (D + 1) * S + S) + 1) := by simp
    _ ≤ (D + 1) * (((S + 1) ^ (D + 1) * S + S) + 1) :=
      Nat.mul_le_mul_right _ hcard

end ExactDemandPatternCover
end
end WeightedEdgeColoring.BinPackingInstance
