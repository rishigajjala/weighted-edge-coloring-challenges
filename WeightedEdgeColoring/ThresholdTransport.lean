import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# Finite threshold transportation

For one-dimensional compatibility (`itemSize i ≤ slotSize j`), the upper-tail
inequalities are sufficient for a fractional transportation.  The proof
removes a largest remaining item and spreads its demand proportionally over
all compatible residual slot capacity.
-/

/-- Upper-tail mass of a finite family. -/
noncomputable def finiteUpperTail {A : Type*}
    (support : Finset A) (size mass : A → ℝ) (t : ℝ) : ℝ :=
  ∑ a ∈ support, if t ≤ size a then mass a else 0

private theorem exists_thresholdTransport_on
    {I J : Type*} [DecidableEq I] [Fintype J]
    (items : Finset I) (itemSize : I → ℝ) (slotSize : J → ℝ)
    (demand : I → ℝ) (capacity : J → ℝ)
    (hdemand : ∀ i ∈ items, 0 ≤ demand i)
    (hcapacity : ∀ j, 0 ≤ capacity j)
    (htail : ∀ t,
      finiteUpperTail items itemSize demand t ≤
        finiteUpperTail Finset.univ slotSize capacity t) :
    ∃ assign : I → J → ℝ,
      (∀ i ∈ items, ∀ j, 0 ≤ assign i j) ∧
      (∀ i ∈ items, ∀ j, 0 < assign i j → itemSize i ≤ slotSize j) ∧
      (∀ i ∈ items, ∑ j, assign i j = demand i) ∧
      (∀ j, (∑ i ∈ items, assign i j) ≤ capacity j) := by
  classical
  refine Finset.strongInduction (p := fun S : Finset I ↦
      ∀ capacity : J → ℝ,
      (∀ i ∈ S, 0 ≤ demand i) →
      (∀ j, 0 ≤ capacity j) →
      (∀ t, finiteUpperTail S itemSize demand t ≤
        finiteUpperTail Finset.univ slotSize capacity t) →
      ∃ assign : I → J → ℝ,
        (∀ i ∈ S, ∀ j, 0 ≤ assign i j) ∧
        (∀ i ∈ S, ∀ j, 0 < assign i j → itemSize i ≤ slotSize j) ∧
        (∀ i ∈ S, ∑ j, assign i j = demand i) ∧
        (∀ j, (∑ i ∈ S, assign i j) ≤ capacity j)) ?_
      items capacity hdemand hcapacity htail
  intro S ih capacity hd hc ht
  by_cases hS : S = ∅
  · subst S
    refine ⟨fun _ _ ↦ 0, by simp, by simp, by simp, ?_⟩
    intro j
    simpa using hc j
  · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    let sizeSupport : Finset ℝ := S.image itemSize
    have hsizeSupport : sizeSupport.Nonempty := hSne.image itemSize
    let top : ℝ := sizeSupport.max' hsizeSupport
    have htop_mem : top ∈ sizeSupport := Finset.max'_mem sizeSupport hsizeSupport
    rcases Finset.mem_image.mp htop_mem with ⟨i₀, hi₀, hi₀size⟩
    have hsize_le_top : ∀ i ∈ S, itemSize i ≤ top := by
      intro i hi
      exact Finset.le_max' sizeSupport (itemSize i)
        (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    let eligible : Finset J := Finset.univ.filter fun j ↦ top ≤ slotSize j
    let total : ℝ := ∑ j ∈ eligible, capacity j
    let piece : J → ℝ := fun j ↦
      if j ∈ eligible then capacity j * (demand i₀ / total) else 0
    have htotal_nonneg : 0 ≤ total := by
      dsimp [total]
      exact Finset.sum_nonneg fun j _hj ↦ hc j
    have hd_le_total : demand i₀ ≤ total := by
      have hitem_le : demand i₀ ≤ finiteUpperTail S itemSize demand top := by
        unfold finiteUpperTail
        have hterm_nonneg : ∀ i ∈ S,
            0 ≤ if top ≤ itemSize i then demand i else 0 := by
          intro i hi
          split
          · exact hd i hi
          · exact le_rfl
        have hone :
            (if top ≤ itemSize i₀ then demand i₀ else 0) = demand i₀ := by
          simp [hi₀size]
        rw [← hone]
        exact Finset.single_le_sum hterm_nonneg hi₀
      have htail_top := ht top
      have hcapacity_top :
          finiteUpperTail Finset.univ slotSize capacity top = total := by
        simp [finiteUpperTail, total, eligible, Finset.sum_filter]
      exact hitem_le.trans (htail_top.trans_eq hcapacity_top)
    have hd_nonneg : 0 ≤ demand i₀ := hd i₀ hi₀
    have hpiece_nonneg : ∀ j, 0 ≤ piece j := by
      intro j
      by_cases hj : j ∈ eligible
      · simp only [piece, hj, if_true]
        exact mul_nonneg (hc j) (div_nonneg hd_nonneg htotal_nonneg)
      · simp [piece, hj]
    have hpiece_le : ∀ j, piece j ≤ capacity j := by
      intro j
      by_cases hzero : total = 0
      · have hd_zero : demand i₀ = 0 := le_antisymm
          (hd_le_total.trans_eq hzero) hd_nonneg
        simpa [piece, hd_zero] using hc j
      · have htotal_pos : 0 < total := lt_of_le_of_ne htotal_nonneg (Ne.symm hzero)
        by_cases hj : j ∈ eligible
        · simp only [piece, hj, if_true]
          have hratio : demand i₀ / total ≤ 1 := (div_le_one htotal_pos).2 hd_le_total
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio (hc j)
        · simp [piece, hj, hc j]
    have hsum_piece : ∑ j, piece j = demand i₀ := by
      by_cases hzero : total = 0
      · have hd_zero : demand i₀ = 0 := le_antisymm
          (hd_le_total.trans_eq hzero) hd_nonneg
        simp [piece, hd_zero]
      · have htotal_ne : total ≠ 0 := hzero
        calc
          (∑ j, piece j) = ∑ j ∈ eligible,
              capacity j * (demand i₀ / total) := by
            simp [piece]
          _ = total * (demand i₀ / total) := by
            rw [Finset.sum_mul]
          _ = demand i₀ := by field_simp
    have hpiece_support : ∀ j, 0 < piece j → top ≤ slotSize j := by
      intro j hjpos
      have hj : j ∈ eligible := by
        by_contra hj
        simp [piece, hj] at hjpos
      exact (Finset.mem_filter.mp hj).2
    let residual : J → ℝ := fun j ↦ capacity j - piece j
    have hresidual_nonneg : ∀ j, 0 ≤ residual j := by
      intro j
      exact sub_nonneg.mpr (hpiece_le j)
    let rest : Finset I := S.erase i₀
    have hrest_ssub : rest ⊂ S := Finset.erase_ssubset hi₀
    have hrest_tail : ∀ t,
        finiteUpperTail rest itemSize demand t ≤
          finiteUpperTail Finset.univ slotSize residual t := by
      intro t
      by_cases httop : t ≤ top
      · have hitem_sub :
            finiteUpperTail rest itemSize demand t =
              finiteUpperTail S itemSize demand t - demand i₀ := by
          unfold finiteUpperTail
          have hi_term :
              (if t ≤ itemSize i₀ then demand i₀ else 0) = demand i₀ := by
            simp [hi₀size, httop]
          have herase := Finset.sum_erase_add S
            (fun i ↦ if t ≤ itemSize i then demand i else 0) hi₀
          have herase' :
              (∑ i ∈ S.erase i₀,
                if t ≤ itemSize i then demand i else 0) + demand i₀ =
                ∑ i ∈ S, if t ≤ itemSize i then demand i else 0 := by
            simpa [hi_term] using herase
          dsimp [rest]
          linarith
        have hcapacity_sub :
            finiteUpperTail Finset.univ slotSize residual t =
              finiteUpperTail Finset.univ slotSize capacity t - demand i₀ := by
          unfold finiteUpperTail
          have hterm : ∀ j,
              (if t ≤ slotSize j then residual j else 0) =
                (if t ≤ slotSize j then capacity j else 0) - piece j := by
            intro j
            by_cases hjpos : 0 < piece j
            · have htj : t ≤ slotSize j := httop.trans (hpiece_support j hjpos)
              simp [residual, htj]
            · have hpzero : piece j = 0 := le_antisymm (not_lt.mp hjpos) (hpiece_nonneg j)
              simp [residual, hpzero]
          simp_rw [hterm]
          rw [Finset.sum_sub_distrib, hsum_piece]
        rw [hitem_sub, hcapacity_sub]
        linarith [ht t]
      · have htop_lt : top < t := lt_of_not_ge httop
        have hitem_zero : finiteUpperTail rest itemSize demand t = 0 := by
          unfold finiteUpperTail
          apply Finset.sum_eq_zero
          intro i hi
          have hiS : i ∈ S := Finset.mem_of_mem_erase hi
          have hnot : ¬t ≤ itemSize i := by
            exact not_le_of_gt ((hsize_le_top i hiS).trans_lt htop_lt)
          simp [hnot]
        rw [hitem_zero]
        unfold finiteUpperTail
        exact Finset.sum_nonneg fun j _hj ↦ by
          split
          · exact hresidual_nonneg j
          · exact le_rfl
    rcases ih rest hrest_ssub
        residual
        (fun i hi ↦ hd i (Finset.mem_of_mem_erase hi))
        hresidual_nonneg hrest_tail with
      ⟨old, hold_nonneg, hold_support, hold_row, hold_capacity⟩
    let assign : I → J → ℝ := fun i j ↦
      if i = i₀ then piece j else old i j
    refine ⟨assign, ?_, ?_, ?_, ?_⟩
    · intro i hi j
      by_cases hii : i = i₀
      · simp [assign, hii, hpiece_nonneg j]
      · have hirest : i ∈ rest := Finset.mem_erase.mpr ⟨hii, hi⟩
        simpa [assign, hii] using hold_nonneg i hirest j
    · intro i hi j hpos
      by_cases hii : i = i₀
      · subst i
        exact hi₀size.trans_le (hpiece_support j (by simpa [assign] using hpos))
      · have hirest : i ∈ rest := Finset.mem_erase.mpr ⟨hii, hi⟩
        exact hold_support i hirest j (by simpa [assign, hii] using hpos)
    · intro i hi
      by_cases hii : i = i₀
      · subst i
        simpa [assign] using hsum_piece
      · have hirest : i ∈ rest := Finset.mem_erase.mpr ⟨hii, hi⟩
        simpa [assign, hii] using hold_row i hirest
    · intro j
      have hsplit :
          (∑ i ∈ S, assign i j) = piece j + ∑ i ∈ rest, old i j := by
        rw [← Finset.insert_erase hi₀, Finset.sum_insert (by simp)]
        simp only [assign, if_pos]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hii : i ≠ i₀ := Finset.ne_of_mem_erase hi
        simp [hii]
      rw [hsplit]
      have hold := hold_capacity j
      dsimp [residual] at hold
      linarith

/-- Finite upper-tail dominance is sufficient for a compatible fractional
transportation. -/
theorem exists_thresholdTransport
    {I J : Type*} [Fintype I] [Fintype J]
    (itemSize : I → ℝ) (slotSize : J → ℝ)
    (demand : I → ℝ) (capacity : J → ℝ)
    (hdemand : ∀ i, 0 ≤ demand i)
    (hcapacity : ∀ j, 0 ≤ capacity j)
    (htail : ∀ t,
      finiteUpperTail Finset.univ itemSize demand t ≤
        finiteUpperTail Finset.univ slotSize capacity t) :
    ∃ assign : I → J → ℝ,
      (∀ i j, 0 ≤ assign i j) ∧
      (∀ i j, 0 < assign i j → itemSize i ≤ slotSize j) ∧
      (∀ i, ∑ j, assign i j = demand i) ∧
      (∀ j, (∑ i, assign i j) ≤ capacity j) := by
  classical
  rcases exists_thresholdTransport_on Finset.univ itemSize slotSize demand capacity
      (fun i _hi ↦ hdemand i) hcapacity htail with
    ⟨assign, hnonneg, hsupport, hrow, hcol⟩
  exact ⟨assign, (fun i j ↦ hnonneg i (Finset.mem_univ i) j),
    (fun i j ↦ hsupport i (Finset.mem_univ i) j),
    (fun i ↦ hrow i (Finset.mem_univ i)), fun j ↦ by simpa using hcol j⟩

end WeightedEdgeColoring
