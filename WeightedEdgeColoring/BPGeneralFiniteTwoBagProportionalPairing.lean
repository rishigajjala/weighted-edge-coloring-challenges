import WeightedEdgeColoring.BPGeneralFiniteTwoBagExtraction

/-!
# A canonical finite heavy-bin pairing

The extraction in `BPGeneralFiniteTwoBagExtraction` accepts an explicit
splitting of every second-heavy bin across first-heavy bins.  This file
constructs that splitting from the bin masses themselves.  Each second-heavy
bin is distributed proportionally over all first-heavy bins.  Thus no finite
matching or choice principle is left between finite bin data and the
`FiniteTwoBagJointPacking` witness.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Pair indices for the canonical proportional coupling of the two heavy
parts. -/
def FiniteTwoBagHeavyPair (firstWeight secondWeight : ι → ℝ) :=
  {i : ι // 1 / 2 < firstWeight i} × {i : ι // 1 / 2 < secondWeight i}

noncomputable instance (firstWeight secondWeight : ι → ℝ) :
    Fintype (FiniteTwoBagHeavyPair firstWeight secondWeight) := by
  unfold FiniteTwoBagHeavyPair
  infer_instance

noncomputable instance (firstWeight secondWeight : ι → ℝ) :
    DecidableEq (FiniteTwoBagHeavyPair firstWeight secondWeight) := by
  unfold FiniteTwoBagHeavyPair
  exact Classical.decEq _

namespace FiniteTwoBagJointPacking

/-- The mass in bins heavy for a supplied weight function. -/
def heavyMass (mass weight : ι → ℝ) : ℝ :=
  ∑ i : ι, if 1 / 2 < weight i then mass i else 0

theorem heavyMass_eq_filter_sum (mass weight : ι → ℝ) :
    heavyMass mass weight =
      ∑ i ∈ Finset.univ.filter (fun i ↦ 1 / 2 < weight i), mass i := by
  rw [heavyMass, Finset.sum_filter]

private theorem sum_firstHeavySubtype (mass firstWeight : ι → ℝ) :
    (∑ i : {i : ι // 1 / 2 < firstWeight i}, mass i.1) =
      heavyMass mass firstWeight := by
  rw [heavyMass_eq_filter_sum]
  exact (Finset.sum_subtype
    (Finset.univ.filter fun i ↦ 1 / 2 < firstWeight i)
    (by simp) (fun i ↦ mass i)).symm

private theorem sum_secondHeavySubtype (mass secondWeight : ι → ℝ) :
    (∑ i : {i : ι // 1 / 2 < secondWeight i}, mass i.1) =
      heavyMass mass secondWeight := by
  rw [heavyMass_eq_filter_sum]
  exact (Finset.sum_subtype
    (Finset.univ.filter fun i ↦ 1 / 2 < secondWeight i)
    (by simp) (fun i ↦ mass i)).symm

/-- Build the explicit joint-packing witness by coupling every second-heavy
bin to the first-heavy bins in proportion to their mass.  The hypothesis is
exactly the orientation condition: the second-heavy mass is no larger than
the first-heavy mass. -/
noncomputable def ofProportionalPairing
    (mass firstWeight secondWeight : ι → ℝ)
    (mass_nonneg : ∀ i, 0 ≤ mass i)
    (firstWeight_nonneg : ∀ i, 0 ≤ firstWeight i)
    (secondWeight_nonneg : ∀ i, 0 ≤ secondWeight i)
    (capacity : ∀ i, firstWeight i + secondWeight i ≤ 1)
    (heavy_le : heavyMass mass secondWeight ≤ heavyMass mass firstWeight) :
    FiniteTwoBagJointPacking
      (ι := ι) (κ := FiniteTwoBagHeavyPair firstWeight secondWeight) := by
  let ell := heavyMass mass firstWeight
  let pairMass : FiniteTwoBagHeavyPair firstWeight secondWeight → ℝ :=
    fun k ↦ if ell = 0 then 0 else mass k.1.1 * mass k.2.1 / ell
  refine
    { mass := mass
      firstWeight := firstWeight
      secondWeight := secondWeight
      mass_nonneg := mass_nonneg
      firstWeight_nonneg := firstWeight_nonneg
      secondWeight_nonneg := secondWeight_nonneg
      capacity := capacity
      pairMass := pairMass
      left := fun k ↦ k.1.1
      right := fun k ↦ k.2.1
      pairMass_nonneg := ?_
      left_heavy := fun k ↦ k.1.2
      right_heavy := fun k ↦ k.2.2
      left_use_le := ?_
      right_fully_used := ?_ }
  · intro k
    dsimp [pairMass]
    split_ifs with hell
    · exact le_rfl
    · have hell0 : 0 ≤ ell := by
        dsimp [ell]
        unfold heavyMass
        exact Finset.sum_nonneg fun i _hi ↦ by
          split_ifs
          · exact mass_nonneg i
          · exact le_rfl
      exact div_nonneg (mul_nonneg (mass_nonneg _) (mass_nonneg _)) hell0
  · intro i
    by_cases hi : 1 / 2 < firstWeight i
    · let ii : {j : ι // 1 / 2 < firstWeight j} := ⟨i, hi⟩
      change (∑ k : FiniteTwoBagHeavyPair firstWeight secondWeight,
        if k.1.1 = i then pairMass k else 0) ≤ mass i
      change (∑ k :
          ({j : ι // 1 / 2 < firstWeight j} ×
            {j : ι // 1 / 2 < secondWeight j}),
        if k.1.1 = i then pairMass k else 0) ≤ mass i
      rw [Fintype.sum_prod_type]
      simp only [pairMass]
      by_cases hell : ell = 0
      · simp [hell, mass_nonneg i]
      · have hellpos : 0 < ell := by
          have hell0 : 0 ≤ ell := by
            dsimp [ell]
            unfold heavyMass
            exact Finset.sum_nonneg fun j _hj ↦ by
              split_ifs
              · exact mass_nonneg j
              · exact le_rfl
          exact lt_of_le_of_ne hell0 (by
            intro h
            exact hell h.symm)
        calc
          (∑ a : {j : ι // 1 / 2 < firstWeight j},
              ∑ b : {j : ι // 1 / 2 < secondWeight j},
                if a.1 = i then
                  (if ell = 0 then 0 else mass a.1 * mass b.1 / ell)
                else 0) =
              mass i * heavyMass mass secondWeight / ell := by
                rw [show (∑ a : {j : ι // 1 / 2 < firstWeight j},
                    ∑ b : {j : ι // 1 / 2 < secondWeight j},
                      if a.1 = i then
                        (if ell = 0 then 0 else mass a.1 * mass b.1 / ell)
                      else 0) =
                    ∑ b : {j : ι // 1 / 2 < secondWeight j},
                      mass i * mass b.1 / ell by
                  rw [Fintype.sum_eq_single ii]
                  · simp [ii, hell]
                  · intro a hane
                    have hai : a.1 ≠ i := by
                      intro h
                      apply hane
                      exact Subtype.ext h
                    simp [hai]
                  ]
                rw [← Finset.sum_div, ← Finset.mul_sum,
                  sum_secondHeavySubtype]
          _ ≤ mass i * ell / ell := by
                exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left heavy_le (mass_nonneg i)) hellpos.le
          _ = mass i := by field_simp
    · change (∑ k : FiniteTwoBagHeavyPair firstWeight secondWeight,
        if k.1.1 = i then pairMass k else 0) ≤ mass i
      have hnone : ∀ k : FiniteTwoBagHeavyPair firstWeight secondWeight,
          k.1.1 ≠ i := by
        intro k h
        exact hi (h ▸ k.1.2)
      calc
        (∑ k : FiniteTwoBagHeavyPair firstWeight secondWeight,
          if k.1.1 = i then pairMass k else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro k _hk
            simp [hnone k]
        _ ≤ mass i := mass_nonneg i
  · intro i hi
    let jj : {j : ι // 1 / 2 < secondWeight j} := ⟨i, hi⟩
    change (∑ k : FiniteTwoBagHeavyPair firstWeight secondWeight,
      if k.2.1 = i then pairMass k else 0) = mass i
    change (∑ k :
        ({j : ι // 1 / 2 < firstWeight j} ×
          {j : ι // 1 / 2 < secondWeight j}),
      if k.2.1 = i then pairMass k else 0) = mass i
    rw [Fintype.sum_prod_type]
    simp only [pairMass]
    have hmpos : 0 < heavyMass mass secondWeight ∨ mass i = 0 := by
      by_cases hmi : mass i = 0
      · exact Or.inr hmi
      · left
        rw [← sum_secondHeavySubtype mass secondWeight]
        exact lt_of_lt_of_le
          (lt_of_le_of_ne (mass_nonneg i) (by
            intro h
            exact hmi h.symm))
          (Finset.single_le_sum (fun j _hj ↦ mass_nonneg j.1)
            (Finset.mem_univ jj))
    rcases hmpos with hmpos | hmi
    · have hellpos : 0 < ell := lt_of_lt_of_le hmpos heavy_le
      have hell : ell ≠ 0 := ne_of_gt hellpos
      rw [show (∑ a : {j : ι // 1 / 2 < firstWeight j},
          ∑ b : {j : ι // 1 / 2 < secondWeight j},
            if b.1 = i then
              (if ell = 0 then 0 else mass a.1 * mass b.1 / ell)
            else 0) =
          ∑ a : {j : ι // 1 / 2 < firstWeight j},
            mass a.1 * mass i / ell by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Fintype.sum_eq_single jj]
        · simp [jj, hell]
        · intro b hbne
          have hbi : b.1 ≠ i := by
            intro h
            apply hbne
            exact Subtype.ext h
          simp [hbi]
        ]
      rw [← Finset.sum_div, ← Finset.sum_mul, sum_firstHeavySubtype]
      exact mul_div_cancel_left₀ _ hell
    · rw [hmi]
      apply Finset.sum_eq_zero
      intro a _ha
      apply Finset.sum_eq_zero
      intro b _hb
      by_cases hbi : b.1 = i
      · simp [hbi, hmi]
      · simp [hbi]

@[simp] theorem ofProportionalPairing_mass
    (mass firstWeight secondWeight : ι → ℝ)
    (mass_nonneg : ∀ i, 0 ≤ mass i)
    (firstWeight_nonneg : ∀ i, 0 ≤ firstWeight i)
    (secondWeight_nonneg : ∀ i, 0 ≤ secondWeight i)
    (capacity : ∀ i, firstWeight i + secondWeight i ≤ 1)
    (heavy_le : heavyMass mass secondWeight ≤ heavyMass mass firstWeight)
    (i : ι) :
    (ofProportionalPairing mass firstWeight secondWeight mass_nonneg
      firstWeight_nonneg secondWeight_nonneg capacity heavy_le).mass i = mass i := rfl

end FiniteTwoBagJointPacking

end

end WeightedEdgeColoring
