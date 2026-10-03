import WeightedEdgeColoring.FiniteColorPairingDoubleFiber

/-!
# Averaging two partners of a random perfect pairing

For distinct `i,j`, either they are paired together, or their partners are
two distinct colors outside `{i,j}`.  Single- and double-fiber counts give
the exact average used in the pair-moment kernel.
-/

namespace WeightedEdgeColoring.FiniteColorPairing

open scoped BigOperators

noncomputable section

variable (Color : Type*) [Fintype Color] [DecidableEq Color]

def disjointPartnerSum (i j : Color) (h : Color → Color → ℝ) : ℝ :=
  ∑ k : Color, ∑ l : Color,
    if k = i ∨ k = j ∨ l = i ∨ l = j ∨ k = l then 0 else h k l

theorem doublePartnerFiber_special {i j : Color} :
    doublePartnerFiber Color i j j i = partnerFiber Color i j := by
  ext p
  simp only [mem_doublePartnerFiber_iff, mem_partnerFiber_iff]
  constructor
  · exact fun hp ↦ hp.1
  · intro hp
    refine ⟨hp, ?_⟩
    calc
      partner Color p j = partner Color p (partner Color p i) := by rw [hp]
      _ = i := partner_partner Color p i

theorem doublePartnerFiber_empty_of_invalid
    {i j k l : Color} (hij : i ≠ j)
    (hspecial : ¬(k = j ∧ l = i))
    (hdisjoint : ¬(k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧ k ≠ l)) :
    doublePartnerFiber Color i k j l = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hd := (mem_doublePartnerFiber_iff Color p i k j l).1 hp
  have hki : k ≠ i := by rw [← hd.1]; exact partner_ne Color p i
  have hlj : l ≠ j := by rw [← hd.2]; exact partner_ne Color p j
  by_cases hkj : k = j
  · apply hspecial
    refine ⟨hkj, ?_⟩
    calc
      l = partner Color p j := hd.2.symm
      _ = partner Color p (partner Color p i) := by rw [hd.1, hkj]
      _ = i := partner_partner Color p i
  · have hli : l ≠ i := by
      intro hli
      have : k = j := by
        apply partner_injective Color p
        calc
          partner Color p k = i := by
            rw [← hd.1, partner_partner]
          _ = l := hli.symm
          _ = partner Color p j := hd.2.symm
      exact hkj this
    have hkl : k ≠ l := by
      intro hkl
      apply hij
      apply partner_injective Color p
      rw [hd.1, hd.2, hkl]
    exact hdisjoint ⟨hki, hkj, hli, hlj, hkl⟩

theorem sum_partner_partner_eq_doubleFibers
    (i j : Color) (h : Color → Color → ℝ) :
    (∑ p : Pairing Color, h (partner Color p i) (partner Color p j)) =
      ∑ k : Color, ∑ l : Color,
        ((doublePartnerFiber Color i k j l).card : ℝ) * h k l := by
  let s : Finset (Pairing Color) := Finset.univ
  let t : Finset (Color × Color) := Finset.univ
  let f : Pairing Color → Color × Color := fun p ↦
    (partner Color p i, partner Color p j)
  have hmaps : (s : Set (Pairing Color)).MapsTo f t := by
    intro p _hp
    simp [t]
  calc
    (∑ p : Pairing Color, h (partner Color p i) (partner Color p j)) =
        ∑ kl ∈ t, ∑ p ∈ s with f p = kl, h kl.1 kl.2 := by
      simpa [s, f] using
        (Finset.sum_fiberwise_of_maps_to' hmaps
          (fun kl : Color × Color ↦ h kl.1 kl.2)).symm
    _ = _ := by
      rw [show (∑ kl ∈ t, ∑ p ∈ s with f p = kl, h kl.1 kl.2) =
          ∑ kl : Color × Color,
            ((doublePartnerFiber Color i kl.1 j kl.2).card : ℝ) *
              h kl.1 kl.2 by
        apply Finset.sum_congr rfl
        intro kl _hkl
        have hfiber :
            ({p ∈ s | f p = kl} : Finset (Pairing Color)) =
              doublePartnerFiber Color i kl.1 j kl.2 := by
          ext p
          simp only [s, f, doublePartnerFiber, Finset.mem_filter,
            Finset.mem_univ, true_and]
          constructor
          · intro hp
            exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
          · rintro ⟨hp1, hp2⟩
            exact Prod.ext hp1 hp2
        rw [hfiber]
        simp]
      rw [Fintype.sum_prod_type]

/-- Exact normalized two-partner average. -/
theorem average_partner_partner
    (heven : Even (Fintype.card Color)) (hcard : 4 ≤ Fintype.card Color)
    {i j : Color} (hij : i ≠ j) (h : Color → Color → ℝ) :
    (∑ p : Pairing Color, h (partner Color p i) (partner Color p j)) /
        (Fintype.card (Pairing Color) : ℝ) =
      h j i / ((Fintype.card Color : ℝ) - 1) +
        disjointPartnerSum Color i j h /
          (((Fintype.card Color : ℝ) - 1) *
            ((Fintype.card Color : ℝ) - 3)) := by
  letI : Nonempty (Pairing Color) := nonempty_pairing_of_even_card Color heven
  have hP : (Fintype.card (Pairing Color) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcardReal : (4 : ℝ) ≤ (Fintype.card Color : ℝ) := by
    exact_mod_cast hcard
  have hK1 : ((Fintype.card Color : ℝ) - 1) ≠ 0 := by
    linarith
  have hK3 : ((Fintype.card Color : ℝ) - 3) ≠ 0 := by
    linarith
  have hterm : ∀ k l : Color,
      ((doublePartnerFiber Color i k j l).card : ℝ) /
          (Fintype.card (Pairing Color) : ℝ) * h k l =
        if k = j ∧ l = i then h k l / ((Fintype.card Color : ℝ) - 1)
        else if k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧ k ≠ l then
          h k l / (((Fintype.card Color : ℝ) - 1) *
            ((Fintype.card Color : ℝ) - 3))
        else 0 := by
    intro k l
    by_cases hs : k = j ∧ l = i
    · rcases hs with ⟨rfl, rfl⟩
      rw [doublePartnerFiber_special]
      have hc := card_partnerFiber_cast_mul Color hij
      simp only [true_and, if_true]
      field_simp
      calc
        _ = (((partnerFiber Color l k).card : ℝ) *
              ((Fintype.card Color : ℝ) - 1)) * h k l := by ring
        _ = _ := by rw [hc]
    · by_cases hd : k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧ k ≠ l
      · rw [if_neg hs, if_pos hd]
        have hc := card_doublePartnerFiber_cast_mul Color
          hd.1.symm hij hd.2.1 hd.2.2.1.symm hd.2.2.2.2
          hd.2.2.2.1.symm
        field_simp
        calc
          _ = (((doublePartnerFiber Color i k j l).card : ℝ) *
                ((Fintype.card Color : ℝ) - 3) *
                ((Fintype.card Color : ℝ) - 1)) * h k l := by ring
          _ = _ := by rw [hc]
      · rw [if_neg hs, if_neg hd,
          doublePartnerFiber_empty_of_invalid Color hij hs hd]
        simp
  rw [sum_partner_partner_eq_doubleFibers Color i j h, Finset.sum_div]
  simp_rw [Finset.sum_div]
  simp_rw [show ∀ k l : Color,
      ((doublePartnerFiber Color i k j l).card : ℝ) * h k l /
          (Fintype.card (Pairing Color) : ℝ) =
        ((doublePartnerFiber Color i k j l).card : ℝ) /
          (Fintype.card (Pairing Color) : ℝ) * h k l by
      intro k l; ring]
  simp_rw [hterm]
  rw [show
      (∑ k : Color, ∑ l : Color,
        if k = j ∧ l = i then h k l / ((Fintype.card Color : ℝ) - 1)
        else if k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧ k ≠ l then
          h k l / (((Fintype.card Color : ℝ) - 1) *
            ((Fintype.card Color : ℝ) - 3)) else 0) =
      (∑ k : Color, ∑ l : Color,
        if k = j ∧ l = i then h k l / ((Fintype.card Color : ℝ) - 1) else 0) +
      (∑ k : Color, ∑ l : Color,
        if k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧ k ≠ l then
          h k l / (((Fintype.card Color : ℝ) - 1) *
            ((Fintype.card Color : ℝ) - 3)) else 0) by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l _hl
      by_cases hs : k = j ∧ l = i
      · simp [hs]
      · simp [hs]]
  rw [show
      (∑ k : Color, ∑ l : Color,
        if k = j ∧ l = i then h k l / ((Fintype.card Color : ℝ) - 1) else 0) =
        h j i / ((Fintype.card Color : ℝ) - 1) by
      calc
        (∑ k : Color, ∑ l : Color,
          if k = j ∧ l = i then
            h k l / ((Fintype.card Color : ℝ) - 1) else 0) =
            ∑ k : Color, if k = j then
              (∑ l : Color, if l = i then
                h k l / ((Fintype.card Color : ℝ) - 1) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro k _hk
          by_cases hkj : k = j <;> simp [hkj]
        _ = h j i / ((Fintype.card Color : ℝ) - 1) := by
          simp only [Fintype.sum_ite_eq']]
  congr 1
  unfold disjointPartnerSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l _hl
  by_cases hd : k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧ k ≠ l
  · simp [hd]
  · by_cases hki : k = i
    · simp [hki]
    · by_cases hkj : k = j
      · simp [hkj]
      · by_cases hli : l = i
        · simp [hli]
        · by_cases hlj : l = j
          · simp [hlj]
          · by_cases hkl : k = l
            · simp [hkl]
            · exact (hd ⟨hki, hkj, hli, hlj, hkl⟩).elim

end

end WeightedEdgeColoring.FiniteColorPairing
