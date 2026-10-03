import WeightedEdgeColoring.MultigraphProfileRounding

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

/-!
# Threshold preservation for a finite slot-size compression

This file isolates the order-theoretic part of the finite-profile argument.
The slot-size scan in the manuscript produces a monotone floor map.  Between
two consecutive fixed points, the total expected slot mass is less than `q`.
The lemmas below prove that an arbitrary threshold can lose mass from only
one such cell.  Adding `q` mass at a slot of size one therefore repairs all
upper tails at once.

The construction of the floor map, and the bound on the number of its fixed
points, are deliberately not assumed to be automatic here.  They are the
remaining combinatorial part of the finite-profile lemma.
-/

section FiniteSlotSizes

/-- Total expected number of original slots whose size is at least `t`. -/
noncomputable def slotUpperTail
    (support : Finset ℝ) (mass : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ b ∈ support, if t ≤ b then mass b else 0

/-- Total expected number of rounded slots whose size is at least `t`. -/
noncomputable def roundedSlotUpperTail
    (support : Finset ℝ) (mass : ℝ → ℝ) (round : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ b ∈ support, if t ≤ round b then mass b else 0

/-- The mass that crosses below `t` when slot sizes are rounded down. -/
noncomputable def thresholdCrossingMass
    (support : Finset ℝ) (mass : ℝ → ℝ) (round : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ b ∈ support, if t ≤ b ∧ round b < t then mass b else 0

/-- The non-fixed mass in the rounding cell based at `p`. -/
noncomputable def floorCellMass
    (support : Finset ℝ) (mass : ℝ → ℝ) (round : ℝ → ℝ) (p : ℝ) : ℝ :=
  ∑ b ∈ support, if round b = p ∧ p < b then mass b else 0

/-- The upper-tail contribution of a single size-one repair slot of mass
`q`. -/
noncomputable def repairSlotUpperTail (q t : ℝ) : ℝ :=
  if t ≤ 1 then q else 0

/-- Rounding down splits every original upper tail into its surviving mass
and the mass that crosses the threshold. -/
theorem slotUpperTail_eq_rounded_add_crossing
    (support : Finset ℝ) (mass : ℝ → ℝ) (round : ℝ → ℝ)
    (hround : ∀ b ∈ support, round b ≤ b) (t : ℝ) :
    slotUpperTail support mass t =
      roundedSlotUpperTail support mass round t +
        thresholdCrossingMass support mass round t := by
  classical
  unfold slotUpperTail roundedSlotUpperTail thresholdCrossingMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases htb : t ≤ b
  · by_cases htr : t ≤ round b
    · simp [htb, htr]
    · have hrt : round b < t := lt_of_not_ge htr
      simp [htb, htr, hrt]
  · have htr : ¬t ≤ round b := fun h ↦ htb (h.trans (hround b hb))
    simp [htb, htr]

/-- A monotone floor map sends all sizes that cross one threshold into the
same open cell.  Hence the crossing mass is bounded by one cell mass. -/
theorem thresholdCrossingMass_le_one_floorCell
    (support kept : Finset ℝ) (mass : ℝ → ℝ) (round : ℝ → ℝ)
    (hmass : ∀ b ∈ support, 0 ≤ mass b)
    (hmono : ∀ a ∈ support, ∀ b ∈ support, a ≤ b → round a ≤ round b)
    (hrange : ∀ b ∈ support, round b ∈ kept)
    (hgreatest : ∀ p ∈ kept, ∀ b ∈ support, p ≤ b → p ≤ round b)
    (t : ℝ) :
    thresholdCrossingMass support mass round t = 0 ∨
      ∃ p ∈ kept, thresholdCrossingMass support mass round t ≤
        floorCellMass support mass round p := by
  classical
  let above : Finset ℝ := support.filter fun b ↦ t ≤ b
  by_cases habove : above.Nonempty
  · let b₀ : ℝ := above.min' habove
    let p : ℝ := round b₀
    right
    have hb₀Above : b₀ ∈ above := Finset.min'_mem above habove
    have hb₀ : b₀ ∈ support := (Finset.mem_filter.mp hb₀Above).1
    refine ⟨p, hrange b₀ hb₀, ?_⟩
    unfold thresholdCrossingMass floorCellMass
    apply Finset.sum_le_sum
    intro b hb
    by_cases hcross : t ≤ b ∧ round b < t
    · have hbAbove : b ∈ above := by
        exact Finset.mem_filter.mpr ⟨hb, hcross.1⟩
      have hb₀le : b₀ ≤ b := Finset.min'_le above b hbAbove
      have hp_le : p ≤ round b := hmono b₀ hb₀ b hb hb₀le
      have htb₀ : t ≤ b₀ := (Finset.mem_filter.mp hb₀Above).2
      have hrb_le_b₀ : round b ≤ b₀ :=
        hcross.2.le.trans htb₀
      have hrb_le_p : round b ≤ p := by
        exact hgreatest (round b) (hrange b hb) b₀ hb₀ hrb_le_b₀
      have heq : round b = p := le_antisymm hrb_le_p hp_le
      have hpt : p < t := heq ▸ hcross.2
      have hpb : p < b := by
        calc
          p = round b := heq.symm
          _ < t := hcross.2
          _ ≤ b := hcross.1
      simp [hcross, heq, hpb, hpt]
    · simp only [hcross, ↓reduceIte]
      split
      · exact hmass b hb
      · exact le_rfl
  · left
    have hnone : ∀ b ∈ support, ¬t ≤ b := by
      intro b hb htb
      exact habove ⟨b, Finset.mem_filter.mpr ⟨hb, htb⟩⟩
    unfold thresholdCrossingMass
    have hzero : (∑ b ∈ support, if t ≤ b ∧ round b < t then mass b else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      simp [hnone b hb]
    rw [hzero]

/-- A uniform bound of `q` on open floor-cell mass gives a strict loss bound
of `q` at every threshold. -/
theorem thresholdCrossingMass_lt
    (support kept : Finset ℝ) (mass : ℝ → ℝ) (round : ℝ → ℝ)
    (hmass : ∀ b ∈ support, 0 ≤ mass b)
    (hmono : ∀ a ∈ support, ∀ b ∈ support, a ≤ b → round a ≤ round b)
    (hrange : ∀ b ∈ support, round b ∈ kept)
    (hgreatest : ∀ p ∈ kept, ∀ b ∈ support, p ≤ b → p ≤ round b)
    {q : ℝ} (hq : 0 < q)
    (hcell : ∀ p ∈ kept, floorCellMass support mass round p < q)
    (t : ℝ) :
    thresholdCrossingMass support mass round t < q := by
  rcases thresholdCrossingMass_le_one_floorCell
      support kept mass round hmass hmono hrange hgreatest t with hzero | ⟨p, hp, hle⟩
  · simpa [hzero] using hq
  · exact hle.trans_lt (hcell p hp)

/-- The threshold loss estimate in upper-tail form. -/
theorem roundedSlotUpperTail_gt_sub
    (support kept : Finset ℝ) (mass : ℝ → ℝ) (round : ℝ → ℝ)
    (hround : ∀ b ∈ support, round b ≤ b)
    (hmass : ∀ b ∈ support, 0 ≤ mass b)
    (hmono : ∀ a ∈ support, ∀ b ∈ support, a ≤ b → round a ≤ round b)
    (hrange : ∀ b ∈ support, round b ∈ kept)
    (hgreatest : ∀ p ∈ kept, ∀ b ∈ support, p ≤ b → p ≤ round b)
    {q : ℝ} (hq : 0 < q)
    (hcell : ∀ p ∈ kept, floorCellMass support mass round p < q)
    (t : ℝ) :
    slotUpperTail support mass t - q <
      roundedSlotUpperTail support mass round t := by
  rw [slotUpperTail_eq_rounded_add_crossing support mass round hround t]
  have hcross := thresholdCrossingMass_lt support kept mass round
    hmass hmono hrange hgreatest hq hcell t
  linarith

/-- Adding `s*q` mass on a size-one repair slot restores every upper tail
for thresholds in `(0,1]`, after the original law is scaled by `s`. -/
theorem scaled_tail_le_rounded_plus_repair
    (support kept : Finset ℝ) (mass : ℝ → ℝ) (round : ℝ → ℝ)
    (hround : ∀ b ∈ support, round b ≤ b)
    (hmass : ∀ b ∈ support, 0 ≤ mass b)
    (hmono : ∀ a ∈ support, ∀ b ∈ support, a ≤ b → round a ≤ round b)
    (hrange : ∀ b ∈ support, round b ∈ kept)
    (hgreatest : ∀ p ∈ kept, ∀ b ∈ support, p ≤ b → p ≤ round b)
    {q s t : ℝ} (hq : 0 < q) (hs : 0 ≤ s) (ht : t ≤ 1)
    (hcell : ∀ p ∈ kept, floorCellMass support mass round p < q) :
    s * slotUpperTail support mass t ≤
      s * roundedSlotUpperTail support mass round t +
        s * repairSlotUpperTail q t := by
  have htail : slotUpperTail support mass t ≤
      roundedSlotUpperTail support mass round t + q := by
    have := roundedSlotUpperTail_gt_sub support kept mass round hround hmass
      hmono hrange hgreatest hq hcell t
    linarith
  rw [repairSlotUpperTail, if_pos ht]
  exact (mul_le_mul_of_nonneg_left htail hs).trans_eq (by ring)

/-- The rounded sizes together with the single repair size form a menu with
at most one more entry than the prescribed kept-size set. -/
theorem rounded_repair_menu_card_le
    (support kept : Finset ℝ) (round : ℝ → ℝ)
    (hrange : ∀ b ∈ support, round b ∈ kept) :
    (insert 1 (support.image round)).card ≤ kept.card + 1 := by
  classical
  calc
    (insert 1 (support.image round)).card ≤ (support.image round).card + 1 :=
      Finset.card_insert_le 1 (support.image round)
    _ ≤ kept.card + 1 := Nat.add_le_add_right
      (Finset.card_le_card (by
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨b, hb, rfl⟩
        exact hrange b hb)) 1

theorem rounded_mem_repair_menu
    (support : Finset ℝ) (round : ℝ → ℝ) {b : ℝ} (hb : b ∈ support) :
    round b ∈ insert 1 (support.image round) := by
  classical
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, hb, rfl⟩)

@[simp] theorem one_mem_rounded_repair_menu
    (support : Finset ℝ) (round : ℝ → ℝ) :
    (1 : ℝ) ∈ insert 1 (support.image round) := by
  classical
  simp

end FiniteSlotSizes

end WeightedMultigraph
end WeightedEdgeColoring
