import WeightedEdgeColoring.WeightedMomentPairingContraction
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Group.Even

/-!
# Finite perfect pairings of a color type

A color pairing is represented by a fixed-point-free involutive permutation.
This representation makes the uniform finite sample space and its conjugation
symmetries explicit.  The later kernel-counting file uses conjugation by color
swaps to prove that partner and double-partner fibers have equal cardinality.
-/

namespace WeightedEdgeColoring.FiniteColorPairing

open scoped BigOperators

noncomputable section

variable (Color : Type*) [Fintype Color] [DecidableEq Color]

/-- Fixed-point-free involutive permutations, i.e. perfect pairings. -/
def Pairing :=
  {p : Equiv.Perm Color //
    Function.Involutive p ∧ ∀ c, p c ≠ c}

noncomputable instance instFintypePairing : Fintype (Pairing Color) :=
  by
    classical
    unfold Pairing
    infer_instance

noncomputable instance instDecidableEqPairing : DecidableEq (Pairing Color) :=
  Classical.decEq _

/-- Partner of one color. -/
def partner (p : Pairing Color) (c : Color) : Color := p.1 c

theorem partner_partner (p : Pairing Color) (c : Color) :
    partner Color p (partner Color p c) = c := p.2.1 c

theorem partner_ne (p : Pairing Color) (c : Color) :
    partner Color p c ≠ c := p.2.2 c

theorem partner_injective (p : Pairing Color) :
    Function.Injective (partner Color p) := p.1.injective

/-- The canonical fixed-point-free involution on `Fin (2*m)`, obtained by
flipping the `Fin 2` coordinate. -/
def canonicalFinPairing (m : ℕ) : Pairing (Fin (2 * m)) := by
  let e : Fin 2 × Fin m ≃ Fin (2 * m) := finProdFinEquiv
  let flip : Equiv.Perm (Fin 2 × Fin m) :=
    (Equiv.swap (0 : Fin 2) 1).prodCongr (Equiv.refl (Fin m))
  let p : Equiv.Perm (Fin (2 * m)) := e.symm.trans (flip.trans e)
  have hflip : Function.Involutive flip := by
    intro x
    rcases x with ⟨bit, index⟩
    fin_cases bit <;> simp [flip]
  refine ⟨p, ?_, ?_⟩
  · intro c
    simpa [p] using congrArg e (hflip (e.symm c))
  · intro c hc
    have hc' : flip (e.symm c) = e.symm c := by
      simpa [p] using congrArg e.symm hc
    rcases hec : e.symm c with ⟨bit, index⟩
    rw [hec] at hc'
    fin_cases bit <;> simp [flip] at hc'

/-- Transport a pairing across an equivalence of color types. -/
def transport {Other : Type*} [Fintype Other] [DecidableEq Other]
    (e : Color ≃ Other) (p : Pairing Color) : Pairing Other := by
  let perm : Equiv.Perm Other := e.symm.trans (p.1.trans e)
  refine ⟨perm, ?_, ?_⟩
  · intro x
    apply e.symm.injective
    simpa [perm] using p.2.1 (e.symm x)
  · intro x hx
    have hx' := congrArg e.symm hx
    exact p.2.2 (e.symm x) (by simpa [perm] using hx')

/-- Every nonempty even finite color type has at least one pairing. -/
theorem nonempty_pairing_of_even_card
    (heven : Even (Fintype.card Color)) : Nonempty (Pairing Color) := by
  obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp heven
  let e0 : Color ≃ Fin (Fintype.card Color) := Fintype.equivFin Color
  let e : Color ≃ Fin (2 * m) := e0.trans (finCongr hm)
  exact ⟨WeightedEdgeColoring.FiniteColorPairing.transport
    (Color := Fin (2 * m)) (Other := Color) e.symm
    (canonicalFinPairing m)⟩

/-- Conjugating a pairing by a color permutation. -/
def conjugate (tau : Equiv.Perm Color) (p : Pairing Color) : Pairing Color := by
  let perm : Equiv.Perm Color := tau.symm.trans (p.1.trans tau)
  refine ⟨perm, ?_, ?_⟩
  · intro c
    apply tau.symm.injective
    simpa [perm] using p.2.1 (tau.symm c)
  · intro c hc
    have hc' := congrArg tau.symm hc
    exact p.2.2 (tau.symm c) (by simpa [perm] using hc')

@[simp] theorem partner_conjugate
    (tau : Equiv.Perm Color) (p : Pairing Color) (c : Color) :
    partner Color (conjugate Color tau p) c =
      tau (partner Color p (tau.symm c)) := rfl

/-- Conjugation is an equivalence of the finite pairing space. -/
def conjugationEquiv (tau : Equiv.Perm Color) :
    Pairing Color ≃ Pairing Color where
  toFun := conjugate Color tau
  invFun := conjugate Color tau.symm
  left_inv p := by
    apply Subtype.ext
    ext c
    simp [conjugate]
  right_inv p := by
    apply Subtype.ext
    ext c
    simp [conjugate]

/-- Uniform sums over pairings are invariant under color relabeling. -/
theorem sum_conjugate (tau : Equiv.Perm Color) (f : Pairing Color → ℝ) :
    (∑ p : Pairing Color, f (conjugate Color tau p)) = ∑ p, f p := by
  simpa [conjugationEquiv] using
    (Equiv.sum_comp (conjugationEquiv Color tau) f)

/-- Pairings in which `j` is the partner of `i`. -/
def partnerFiber (i j : Color) : Finset (Pairing Color) :=
  Finset.univ.filter fun p ↦ partner Color p i = j

theorem mem_partnerFiber_iff (p : Pairing Color) (i j : Color) :
    p ∈ partnerFiber Color i j ↔ partner Color p i = j := by
  simp [partnerFiber]

/-- Conjugation transports partner fibers in the expected way. -/
theorem conjugate_mem_partnerFiber_iff
    (tau : Equiv.Perm Color) (p : Pairing Color) (i j : Color) :
    conjugate Color tau p ∈ partnerFiber Color (tau i) (tau j) ↔
      p ∈ partnerFiber Color i j := by
  simp [partnerFiber, partner_conjugate]

/-- Relabeling gives a cardinality-preserving bijection between partner
fibers. -/
theorem card_partnerFiber_eq_of_perm
    (tau : Equiv.Perm Color) (i j : Color) :
    (partnerFiber Color (tau i) (tau j)).card =
      (partnerFiber Color i j).card := by
  let e := conjugationEquiv Color tau
  symm
  exact Finset.card_bij (fun p _hp ↦ e p)
    (fun p hp ↦ by
      exact (conjugate_mem_partnerFiber_iff Color tau p i j).2 hp)
    (fun p₁ _hp₁ p₂ _hp₂ h ↦ e.injective h)
    (fun p hp ↦ by
      refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
      have hp' : e (e.symm p) ∈
          partnerFiber Color (tau i) (tau j) := by simpa using hp
      exact (conjugate_mem_partnerFiber_iff Color tau (e.symm p) i j).1 hp')

/-- For fixed `i`, all allowed partners occur in equally many pairings. -/
theorem card_partnerFiber_eq {i j k : Color}
    (hij : i ≠ j) (hik : i ≠ k) :
    (partnerFiber Color i j).card = (partnerFiber Color i k).card := by
  by_cases hjk : j = k
  · subst k
    rfl
  let tau : Equiv.Perm Color := Equiv.swap j k
  have htaui : tau i = i := by
    exact Equiv.swap_apply_of_ne_of_ne hij hik
  have htauj : tau j = k := by simp [tau, hjk]
  have h := card_partnerFiber_eq_of_perm Color tau i j
  simpa [htaui, htauj] using h.symm

/-- The partner fibers over all colors other than `i` partition the pairing
space. -/
theorem card_pairing_eq_sum_partnerFibers (i : Color) :
    Fintype.card (Pairing Color) =
      ∑ j ∈ (Finset.univ : Finset Color).erase i,
        (partnerFiber Color i j).card := by
  let s : Finset (Pairing Color) := Finset.univ
  let t : Finset Color := (Finset.univ : Finset Color).erase i
  let f : Pairing Color → Color := fun p ↦ partner Color p i
  have hmaps : (s : Set (Pairing Color)).MapsTo f t := by
    intro p _hp
    simp [t, f, partner_ne]
  have hfiber := Finset.card_eq_sum_card_fiberwise hmaps
  simpa [s, t, f, partnerFiber] using hfiber

/-- Exact uniform partner count. -/
theorem card_partnerFiber_mul_pred_eq_card
    (i j : Color) (hij : i ≠ j) :
    (partnerFiber Color i j).card * (Fintype.card Color - 1) =
      Fintype.card (Pairing Color) := by
  have hpartition := card_pairing_eq_sum_partnerFibers Color i
  have hconst : ∀ k ∈ (Finset.univ : Finset Color).erase i,
      (partnerFiber Color i k).card = (partnerFiber Color i j).card := by
    intro k hk
    have hki : k ≠ i := by simpa using hk
    exact card_partnerFiber_eq Color hki.symm hij
  calc
    (partnerFiber Color i j).card * (Fintype.card Color - 1) =
        ((Finset.univ : Finset Color).erase i).card *
          (partnerFiber Color i j).card := by simp [mul_comm]
    _ = ∑ k ∈ (Finset.univ : Finset Color).erase i,
          (partnerFiber Color i k).card := by
      symm
      exact Finset.sum_const_nat hconst
    _ = Fintype.card (Pairing Color) := hpartition.symm

/-- Real-valued form of uniform partner probability, avoiding division by
the cardinality of the pairing space. -/
theorem card_partnerFiber_cast_mul {i j : Color} (hij : i ≠ j) :
    ((partnerFiber Color i j).card : ℝ) *
        ((Fintype.card Color : ℝ) - 1) =
      Fintype.card (Pairing Color) := by
  have h := card_partnerFiber_mul_pred_eq_card Color i j hij
  have hcardOne : 1 ≤ Fintype.card Color := by
    exact Fintype.card_pos_iff.mpr ⟨i⟩
  calc
    ((partnerFiber Color i j).card : ℝ) *
          ((Fintype.card Color : ℝ) - 1) =
        ((
          (partnerFiber Color i j).card * (Fintype.card Color - 1) : ℕ
        ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_sub hcardOne]
      norm_num
    _ = Fintype.card (Pairing Color) := by exact_mod_cast h

/-- Sum a function of the partner by first summing over partner fibers. -/
theorem sum_partner_eq_sum_fibers (i : Color) (g : Color → ℝ) :
    (∑ p : Pairing Color, g (partner Color p i)) =
      ∑ j ∈ (Finset.univ : Finset Color).erase i,
        ((partnerFiber Color i j).card : ℝ) * g j := by
  let s : Finset (Pairing Color) := Finset.univ
  let t : Finset Color := (Finset.univ : Finset Color).erase i
  let f : Pairing Color → Color := fun p ↦ partner Color p i
  have hmaps : (s : Set (Pairing Color)).MapsTo f t := by
    intro p _hp
    simp [t, f, partner_ne]
  calc
    (∑ p : Pairing Color, g (partner Color p i)) =
        ∑ j ∈ t, ∑ p ∈ s with f p = j, g (f p) := by
      exact (Finset.sum_fiberwise_of_maps_to hmaps
        (fun p ↦ g (f p))).symm
    _ = ∑ j ∈ t, ((partnerFiber Color i j).card : ℝ) * g j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.sum_filter]
      calc
        (∑ p ∈ s, if f p = j then g (f p) else 0) =
            ∑ p ∈ s, if f p = j then g j else 0 := by
          apply Finset.sum_congr rfl
          intro p _hp
          split <;> rename_i h
          · rw [h]
          · rfl
        _ = ((partnerFiber Color i j).card : ℝ) * g j := by
          rw [← Finset.sum_filter]
          simp [s, f, partnerFiber]
    _ = _ := rfl

/-- Exact uniform-partner averaging identity. -/
theorem average_partner {i : Color}
    (heven : Even (Fintype.card Color))
    (hcard : 2 ≤ Fintype.card Color) (g : Color → ℝ) :
    (∑ p : Pairing Color, g (partner Color p i)) /
        (Fintype.card (Pairing Color) : ℝ) =
      ((∑ j : Color, g j) - g i) /
        ((Fintype.card Color : ℝ) - 1) := by
  letI : Nonempty (Pairing Color) := nonempty_pairing_of_even_card Color heven
  obtain ⟨j, hij⟩ : ∃ j : Color, i ≠ j := by
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
    exact ⟨j, hji.symm⟩
  have hfiber := card_partnerFiber_cast_mul Color hij
  rw [sum_partner_eq_sum_fibers Color i g]
  have hconst : ∀ k ∈ (Finset.univ : Finset Color).erase i,
      ((partnerFiber Color i k).card : ℝ) =
        (partnerFiber Color i j).card := by
    intro k hk
    have hki : k ≠ i := by simpa using hk
    exact_mod_cast card_partnerFiber_eq Color hki.symm hij
  rw [show
      (∑ k ∈ (Finset.univ : Finset Color).erase i,
        ((partnerFiber Color i k).card : ℝ) * g k) =
      ∑ k ∈ (Finset.univ : Finset Color).erase i,
        ((partnerFiber Color i j).card : ℝ) * g k by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hconst k hk]]
  rw [← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  have hpairCard : (Fintype.card (Pairing Color) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcardReal : (2 : ℝ) ≤ (Fintype.card Color : ℝ) := by
    exact_mod_cast hcard
  have hcolor : ((Fintype.card Color : ℝ) - 1) ≠ 0 := by
    linarith
  field_simp
  rw [← hfiber]
  ring


end

end WeightedEdgeColoring.FiniteColorPairing
