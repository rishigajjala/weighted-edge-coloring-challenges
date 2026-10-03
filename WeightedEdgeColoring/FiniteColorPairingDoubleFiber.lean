import WeightedEdgeColoring.FiniteColorPairing

/-!
# Two prescribed pairs in a finite perfect pairing

Fix three different colors `i`, `j`, and `k`, and condition on `i` being
paired with `j`.  Then the partner of `k` is uniform among the colors other
than `i`, `j`, and `k`.  This file proves the statement by finite bijections.
It is the exact counting fact that produces the `1 / (q - 3)` coefficient in
the two-color moment kernel.
-/

namespace WeightedEdgeColoring.FiniteColorPairing

open scoped BigOperators

noncomputable section

variable (Color : Type*) [Fintype Color] [DecidableEq Color]

/-- Pairings containing both prescribed ordered partner relations. -/
def doublePartnerFiber (i j k l : Color) : Finset (Pairing Color) :=
  Finset.univ.filter fun p ↦
    partner Color p i = j ∧ partner Color p k = l

theorem mem_doublePartnerFiber_iff
    (p : Pairing Color) (i j k l : Color) :
    p ∈ doublePartnerFiber Color i j k l ↔
      partner Color p i = j ∧ partner Color p k = l := by
  simp [doublePartnerFiber]

/-- Relabeling all four named colors transports a double fiber. -/
theorem conjugate_mem_doublePartnerFiber_iff
    (tau : Equiv.Perm Color) (p : Pairing Color) (i j k l : Color) :
    conjugate Color tau p ∈
        doublePartnerFiber Color (tau i) (tau j) (tau k) (tau l) ↔
      p ∈ doublePartnerFiber Color i j k l := by
  simp [doublePartnerFiber, partner_conjugate]

/-- Conjugation preserves the cardinality of a double fiber. -/
theorem card_doublePartnerFiber_eq_of_perm
    (tau : Equiv.Perm Color) (i j k l : Color) :
    (doublePartnerFiber Color (tau i) (tau j) (tau k) (tau l)).card =
      (doublePartnerFiber Color i j k l).card := by
  let e := conjugationEquiv Color tau
  symm
  exact Finset.card_bij (fun p _hp ↦ e p)
    (fun p hp ↦ by
      exact (conjugate_mem_doublePartnerFiber_iff
        Color tau p i j k l).2 hp)
    (fun p₁ _hp₁ p₂ _hp₂ h ↦ e.injective h)
    (fun p hp ↦ by
      refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
      have hp' : e (e.symm p) ∈
          doublePartnerFiber Color
            (tau i) (tau j) (tau k) (tau l) := by
        simpa using hp
      exact (conjugate_mem_doublePartnerFiber_iff
        Color tau (e.symm p) i j k l).1 hp')

/-- Swapping two allowed partners while fixing `i`, `j`, and `k` gives
equally large double fibers. -/
theorem card_doublePartnerFiber_eq
    {i j k l m : Color}
    (hil : i ≠ l) (him : i ≠ m)
    (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) :
    (doublePartnerFiber Color i j k l).card =
      (doublePartnerFiber Color i j k m).card := by
  by_cases hlm : l = m
  · subst m
    rfl
  let tau : Equiv.Perm Color := Equiv.swap l m
  have htaui : tau i = i := by
    exact Equiv.swap_apply_of_ne_of_ne hil him
  have htauj : tau j = j := by
    exact Equiv.swap_apply_of_ne_of_ne hjl hjm
  have htauk : tau k = k := by
    exact Equiv.swap_apply_of_ne_of_ne hkl hkm
  have htaul : tau l = m := by simp [tau]
  have h := card_doublePartnerFiber_eq_of_perm
    Color tau i j k l
  simpa [htaui, htauj, htauk, htaul] using h.symm

/-- Once `i` is paired with `j`, the partner of a third color `k` avoids
all three named colors. -/
theorem partner_mem_erase_three
    (p : Pairing Color) {i j k : Color}
    (hij : partner Color p i = j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    partner Color p k ∈
      (((Finset.univ : Finset Color).erase i).erase j).erase k := by
  have hpki : partner Color p k ≠ i := by
    intro hpki
    have hpji : partner Color p j = i := by
      have h := partner_partner Color p i
      simpa [hij] using h
    have hkj : k = j :=
      partner_injective Color p (hpki.trans hpji.symm)
    exact hjk hkj.symm
  have hpkj : partner Color p k ≠ j := by
    intro hpkj
    have hki : k = i :=
      partner_injective Color p (hpkj.trans hij.symm)
    exact hik hki.symm
  have hpkk : partner Color p k ≠ k := partner_ne Color p k
  simp [hpki, hpkj, hpkk]

/-- The double fibers, indexed by the allowed partner of `k`, partition the
single fiber in which `i` is paired with `j`. -/
theorem card_partnerFiber_eq_sum_doublePartnerFibers
    {i j k : Color} (hik : i ≠ k) (hjk : j ≠ k) :
    (partnerFiber Color i j).card =
      ∑ l ∈ (((Finset.univ : Finset Color).erase i).erase j).erase k,
        (doublePartnerFiber Color i j k l).card := by
  let s : Finset (Pairing Color) := partnerFiber Color i j
  let t : Finset Color :=
    (((Finset.univ : Finset Color).erase i).erase j).erase k
  let f : Pairing Color → Color := fun p ↦ partner Color p k
  have hmaps : (s : Set (Pairing Color)).MapsTo f t := by
    intro p hp
    have hij : partner Color p i = j :=
      (mem_partnerFiber_iff Color p i j).1 hp
    exact partner_mem_erase_three Color p hij hik hjk
  have hfiber := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (partnerFiber Color i j).card = s.card := rfl
    _ = ∑ l ∈ t, ({p ∈ s | f p = l} : Finset (Pairing Color)).card :=
      hfiber
    _ = ∑ l ∈ t, (doublePartnerFiber Color i j k l).card := by
      apply Finset.sum_congr rfl
      intro l _hl
      congr 1
      ext p
      simp [s, f, partnerFiber, doublePartnerFiber]
    _ = _ := rfl

/-- The allowed partner set has `|Color|-3` elements. -/
theorem card_erase_three
    {i j k : Color} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((((Finset.univ : Finset Color).erase i).erase j).erase k).card =
      Fintype.card Color - 3 := by
  have hi : i ∈ (Finset.univ : Finset Color) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ : Finset Color).erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hk : k ∈ ((Finset.univ : Finset Color).erase i).erase j :=
    Finset.mem_erase.mpr
      ⟨hjk.symm, Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩⟩
  rw [Finset.card_erase_of_mem hk, Finset.card_erase_of_mem hj,
    Finset.card_erase_of_mem hi, Finset.card_univ]
  omega

/-- Exact conditional partner count.  Among pairings with `i` paired to
`j`, every allowed partner of `k` occurs equally often. -/
theorem card_doublePartnerFiber_mul_sub_three_eq_partnerFiber
    {i j k l : Color}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) :
    (doublePartnerFiber Color i j k l).card *
        (Fintype.card Color - 3) =
      (partnerFiber Color i j).card := by
  have hpartition :=
    card_partnerFiber_eq_sum_doublePartnerFibers
      Color hik hjk
  let t : Finset Color :=
    (((Finset.univ : Finset Color).erase i).erase j).erase k
  have hl : l ∈ t := by
    simp [t, hil.symm, hjl.symm, hkl.symm]
  have hconst : ∀ m ∈ t,
      (doublePartnerFiber Color i j k m).card =
        (doublePartnerFiber Color i j k l).card := by
    intro m hm
    have hm' : m ≠ k ∧ m ≠ j ∧ m ≠ i := by
      simpa [t] using hm
    have hmi : m ≠ i := hm'.2.2
    have hmj : m ≠ j := hm'.2.1
    have hmk : m ≠ k := hm'.1
    exact card_doublePartnerFiber_eq Color
      (i := i) (j := j) (k := k) (l := m) (m := l)
      (Ne.symm hmi) hil (Ne.symm hmj) hjl (Ne.symm hmk) hkl
  calc
    (doublePartnerFiber Color i j k l).card *
          (Fintype.card Color - 3) =
        t.card * (doublePartnerFiber Color i j k l).card := by
      rw [card_erase_three Color hij hik hjk]
      exact Nat.mul_comm _ _
    _ = ∑ m ∈ t, (doublePartnerFiber Color i j k m).card := by
      symm
      exact Finset.sum_const_nat hconst
    _ = (partnerFiber Color i j).card := by
      simpa [t] using hpartition.symm

/-- Unconditional count for two prescribed disjoint pairs. -/
theorem card_doublePartnerFiber_mul_pred_mul_sub_three_eq_card
    {i j k l : Color}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) :
    (doublePartnerFiber Color i j k l).card *
          (Fintype.card Color - 3) *
          (Fintype.card Color - 1) =
      Fintype.card (Pairing Color) := by
  rw [card_doublePartnerFiber_mul_sub_three_eq_partnerFiber
    Color hij hik hjk hil hjl hkl]
  exact card_partnerFiber_mul_pred_eq_card Color i j hij

/-- Real-valued two-pair count, ready for normalized finite averages. -/
theorem card_doublePartnerFiber_cast_mul {i j k l : Color}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) :
    ((doublePartnerFiber Color i j k l).card : ℝ) *
          ((Fintype.card Color : ℝ) - 3) *
          ((Fintype.card Color : ℝ) - 1) =
      Fintype.card (Pairing Color) := by
  have h := card_doublePartnerFiber_mul_pred_mul_sub_three_eq_card
    Color hij hik hjk hil hjl hkl
  let t : Finset Color :=
    (((Finset.univ : Finset Color).erase i).erase j).erase k
  have hlmem : l ∈ t := by
    simp [t, hil.symm, hjl.symm, hkl.symm]
  have htpos : 0 < t.card := Finset.card_pos.mpr ⟨l, hlmem⟩
  have hthree : 3 ≤ Fintype.card Color := by
    rw [card_erase_three Color hij hik hjk] at htpos
    omega
  have hone : 1 ≤ Fintype.card Color := by omega
  have hr := congrArg (fun x : ℕ ↦ (x : ℝ)) h
  simpa [Nat.cast_mul, Nat.cast_sub hthree, Nat.cast_sub hone] using hr

end

end WeightedEdgeColoring.FiniteColorPairing
