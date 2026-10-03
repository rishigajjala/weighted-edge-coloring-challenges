import WeightedEdgeColoring.MultigraphProfileThresholdCompression

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

section KeptSizes

private structure KeptScan
    (support : Finset ℝ) (mass : ℝ → ℝ) (q : ℝ) where
  kept : Finset ℝ
  round : ℝ → ℝ
  last : ℝ
  kept_subset : kept ⊆ support
  last_mem : last ∈ kept
  last_greatest : ∀ p ∈ kept, p ≤ last
  round_le : ∀ b ∈ support, round b ≤ b
  monotone : ∀ a ∈ support, ∀ b ∈ support, a ≤ b → round a ≤ round b
  round_mem : ∀ b ∈ support, round b ∈ kept
  greatest : ∀ p ∈ kept, ∀ b ∈ support, p ≤ b → p ≤ round b
  cell_lt : ∀ p ∈ kept, floorCellMass support mass round p < q
  budget :
    q * ((kept.card : ℝ) - 1) + floorCellMass support mass round last ≤
      ∑ b ∈ support, mass b

private theorem exists_keptScan
    (support : Finset ℝ) (mass : ℝ → ℝ) {q : ℝ}
    (hmass : ∀ b ∈ support, 0 ≤ mass b) (hq : 0 < q)
    (hne : support.Nonempty) :
    Nonempty (KeptScan support mass q) := by
  classical
  refine Finset.strongInduction (p := fun s : Finset ℝ ↦
      (∀ b ∈ s, 0 ≤ mass b) → s.Nonempty → Nonempty (KeptScan s mass q)) ?_ support hmass hne
  intro s ih hs_nonneg hs_nonempty
  let top : ℝ := s.max' hs_nonempty
  have htop : top ∈ s := Finset.max'_mem s hs_nonempty
  let rest : Finset ℝ := s.erase top
  have hrest_ssub : rest ⊂ s := Finset.erase_ssubset htop
  by_cases hrest_empty : rest = ∅
  · have hs_singleton : s = {top} := by
      ext x
      constructor
      · intro hx
        have hx_eq : x = top := by
          by_contra hne_top
          have : x ∈ rest := Finset.mem_erase.mpr ⟨hne_top, hx⟩
          simpa [hrest_empty] using this
        simpa [hx_eq]
      · intro hx
        have hx_eq : x = top := by simpa using hx
        exact hx_eq ▸ htop
    rw [hs_singleton]
    let round : ℝ → ℝ := fun _ ↦ top
    refine ⟨⟨{top}, round, top, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro x hx
      simpa using hx
    · simp
    · intro p hp
      have hp_eq : p = top := by simpa using hp
      subst p
      exact le_rfl
    · intro b hb
      have hb_eq : b = top := by simpa using hb
      subst b
      exact le_rfl
    · intro a ha b hb hab
      simp [round]
    · intro b hb
      simp [round]
    · intro p hp b hb hpb
      have hp_eq : p = top := by simpa using hp
      have hb_eq : b = top := by simpa using hb
      subst p
      subst b
      exact le_rfl
    · intro p hp
      have hp_eq : p = top := by simpa using hp
      subst p
      simp [floorCellMass, round, hq]
    · simpa [floorCellMass, round] using hs_nonneg top htop
  · have hrest_nonempty : rest.Nonempty := Finset.nonempty_iff_ne_empty.mpr hrest_empty
    have hrest_nonneg : ∀ b ∈ rest, 0 ≤ mass b := by
      intro b hb
      exact hs_nonneg b (Finset.mem_of_mem_erase hb)
    let old : KeptScan rest mass q :=
      Classical.choice (ih rest hrest_ssub hrest_nonneg hrest_nonempty)
    have htop_not_rest : top ∉ rest := by simp [rest]
    have htop_not_kept : top ∉ old.kept := fun h ↦
      htop_not_rest (old.kept_subset h)
    have hlt_top : ∀ x ∈ rest, x < top := by
      intro x hx
      have hx_s : x ∈ s := Finset.mem_of_mem_erase hx
      have hx_le : x ≤ top := Finset.le_max' s x hx_s
      exact lt_of_le_of_ne hx_le (Finset.ne_of_mem_erase hx)
    have hlast_lt_top : old.last < top :=
      hlt_top old.last (old.kept_subset old.last_mem)
    have hs_insert : insert top rest = s := Finset.insert_erase htop
    have sum_split : (∑ x ∈ s, mass x) = mass top + ∑ x ∈ rest, mass x := by
      rw [← hs_insert]
      simp [htop_not_rest]
    by_cases hsmall :
        floorCellMass rest mass old.round old.last + mass top < q
    · let round : ℝ → ℝ := fun x ↦ if x = top then old.last else old.round x
      have hcell_last :
          floorCellMass s mass round old.last =
            mass top + floorCellMass rest mass old.round old.last := by
        unfold floorCellMass
        rw [← hs_insert, Finset.sum_insert htop_not_rest]
        have htail :
            (∑ x ∈ rest, if round x = old.last ∧ old.last < x then mass x else 0) =
              ∑ x ∈ rest, if old.round x = old.last ∧ old.last < x then mass x else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          have hne : x ≠ top := Finset.ne_of_mem_erase hx
          simp [round, hne]
        rw [htail]
        simp [round, hlast_lt_top]
      have hcell_other (p : ℝ) (hp : p ∈ old.kept) (hne : p ≠ old.last) :
          floorCellMass s mass round p =
            floorCellMass rest mass old.round p := by
        unfold floorCellMass
        rw [← hs_insert, Finset.sum_insert htop_not_rest]
        have htail :
            (∑ x ∈ rest, if round x = p ∧ p < x then mass x else 0) =
              ∑ x ∈ rest, if old.round x = p ∧ p < x then mass x else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxt : x ≠ top := Finset.ne_of_mem_erase hx
          simp [round, hxt]
        rw [htail]
        simp [round, hne.symm]
      refine ⟨⟨old.kept, round, old.last, old.kept_subset.trans ?_,
        old.last_mem, old.last_greatest, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro x hx
        exact Finset.mem_of_mem_erase hx
      · intro x hx
        by_cases hxt : x = top
        · subst x
          simp [round, hlast_lt_top.le]
        · have hx_rest : x ∈ rest := Finset.mem_erase.mpr ⟨hxt, hx⟩
          simpa [round, hxt] using old.round_le x hx_rest
      · intro a ha b hb hab
        by_cases hbt : b = top
        · subst b
          by_cases hat : a = top
          · simp [round, hat]
          · have ha_rest : a ∈ rest := Finset.mem_erase.mpr ⟨hat, ha⟩
            have hra : old.round a ∈ old.kept := old.round_mem a ha_rest
            simpa [round, hat] using old.last_greatest (old.round a) hra
        · have hb_rest : b ∈ rest := Finset.mem_erase.mpr ⟨hbt, hb⟩
          have hat : a ≠ top := by
            intro ha_top
            subst a
            have hb_le : b ≤ top := (hlt_top b hb_rest).le
            exact hbt (le_antisymm hb_le hab)
          have ha_rest : a ∈ rest := Finset.mem_erase.mpr ⟨hat, ha⟩
          simpa [round, hat, hbt] using old.monotone a ha_rest b hb_rest hab
      · intro x hx
        by_cases hxt : x = top
        · simpa [round, hxt] using old.last_mem
        · exact by
            have hx_rest : x ∈ rest := Finset.mem_erase.mpr ⟨hxt, hx⟩
            simpa [round, hxt] using old.round_mem x hx_rest
      · intro p hp x hx hpx
        by_cases hxt : x = top
        · subst x
          simpa [round] using old.last_greatest p hp
        · have hx_rest : x ∈ rest := Finset.mem_erase.mpr ⟨hxt, hx⟩
          simpa [round, hxt] using old.greatest p hp x hx_rest hpx
      · intro p hp
        by_cases hp_last : p = old.last
        · subst p
          rw [hcell_last]
          linarith
        · rw [hcell_other p hp hp_last]
          exact old.cell_lt p hp
      · rw [hcell_last, sum_split]
        linarith [old.budget]
    · have hlarge : q ≤
          floorCellMass rest mass old.round old.last + mass top := le_of_not_gt hsmall
      let round : ℝ → ℝ := fun x ↦ if x = top then top else old.round x
      have hcell_old (p : ℝ) (hp : p ∈ old.kept) :
          floorCellMass s mass round p =
            floorCellMass rest mass old.round p := by
        unfold floorCellMass
        rw [← hs_insert, Finset.sum_insert htop_not_rest]
        have hpt : top ≠ p := ne_comm.mp (fun h ↦ htop_not_kept (h ▸ hp))
        have htail :
            (∑ x ∈ rest, if round x = p ∧ p < x then mass x else 0) =
              ∑ x ∈ rest, if old.round x = p ∧ p < x then mass x else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxt : x ≠ top := Finset.ne_of_mem_erase hx
          simp [round, hxt]
        rw [htail]
        simp [round, hpt]
      have hcell_top : floorCellMass s mass round top = 0 := by
        unfold floorCellMass
        rw [← hs_insert, Finset.sum_insert htop_not_rest]
        simp only [round, if_pos, lt_self_iff_false, and_false, ↓reduceIte, zero_add]
        apply Finset.sum_eq_zero
        intro x hx
        have hxt : x ≠ top := Finset.ne_of_mem_erase hx
        have hr_mem : old.round x ∈ old.kept := old.round_mem x hx
        have hr_ne : old.round x ≠ top := fun heq ↦ htop_not_kept (heq ▸ hr_mem)
        simp [hxt, hr_ne]
      refine ⟨⟨insert top old.kept, round, top, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact htop
        · exact Finset.mem_of_mem_erase (old.kept_subset hx)
      · simp
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact le_rfl
        · exact (old.last_greatest p hp).trans hlast_lt_top.le
      · intro x hx
        by_cases hxt : x = top
        · simp [round, hxt]
        · have hx_rest : x ∈ rest := Finset.mem_erase.mpr ⟨hxt, hx⟩
          simpa [round, hxt] using old.round_le x hx_rest
      · intro a ha b hb hab
        by_cases hbt : b = top
        · subst b
          by_cases hat : a = top
          · simp [round, hat]
          · have ha_rest : a ∈ rest := Finset.mem_erase.mpr ⟨hat, ha⟩
            have hra_le : round a ≤ a := by
              simpa [round, hat] using old.round_le a ha_rest
            simpa [round, hat] using hra_le.trans hab
        · have hb_rest : b ∈ rest := Finset.mem_erase.mpr ⟨hbt, hb⟩
          have hat : a ≠ top := by
            intro ha_top
            subst a
            exact hbt (le_antisymm (hlt_top b hb_rest).le hab)
          have ha_rest : a ∈ rest := Finset.mem_erase.mpr ⟨hat, ha⟩
          simpa [round, hat, hbt] using old.monotone a ha_rest b hb_rest hab
      · intro x hx
        by_cases hxt : x = top
        · simp [round, hxt]
        · have hx_rest : x ∈ rest := Finset.mem_erase.mpr ⟨hxt, hx⟩
          exact Finset.mem_insert_of_mem (by simpa [round, hxt] using old.round_mem x hx_rest)
      · intro p hp x hx hpx
        rcases Finset.mem_insert.mp hp with rfl | hp
        · have hx_le : x ≤ top := Finset.le_max' s x hx
          have hx_eq : x = top := le_antisymm hx_le hpx
          simp [round, hx_eq]
        · by_cases hxt : x = top
          · subst x
            simpa [round] using (old.last_greatest p hp).trans hlast_lt_top.le
          · have hx_rest : x ∈ rest := Finset.mem_erase.mpr ⟨hxt, hx⟩
            simpa [round, hxt] using old.greatest p hp x hx_rest hpx
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · simpa [hcell_top] using hq
        · rw [hcell_old p hp]
          exact old.cell_lt p hp
      · rw [hcell_top, sum_split]
        have hcard : ((insert top old.kept).card : ℝ) = old.kept.card + 1 := by
          simp [htop_not_kept]
        rw [hcard]
        linarith [old.budget]

/-- A finite nonnegative mass distribution admits a monotone floor map whose
open cells all have mass below `q`.  If its total mass is at most `K`, the
number of kept sizes is at most `⌊K / q⌋₊ + 1`. -/
theorem exists_keptSizes_floor
    (support : Finset ℝ) (mass : ℝ → ℝ) {K q : ℝ}
    (hmass : ∀ b ∈ support, 0 ≤ mass b)
    (htotal : (∑ b ∈ support, mass b) ≤ K) (hq : 0 < q) :
    ∃ (kept : Finset ℝ) (round : ℝ → ℝ),
      (∀ b ∈ support, round b ≤ b) ∧
      (∀ a ∈ support, ∀ b ∈ support, a ≤ b → round a ≤ round b) ∧
      (∀ b ∈ support, round b ∈ kept) ∧
      (∀ p ∈ kept, ∀ b ∈ support, p ≤ b → p ≤ round b) ∧
      (∀ p ∈ kept, floorCellMass support mass round p < q) ∧
      kept.card ≤ ⌊K / q⌋₊ + 1 := by
  classical
  by_cases hne : support.Nonempty
  · let scan : KeptScan support mass q :=
      Classical.choice (exists_keptScan support mass hmass hq hne)
    refine ⟨scan.kept, scan.round, scan.round_le, scan.monotone,
      scan.round_mem, scan.greatest, scan.cell_lt, ?_⟩
    have hcell_nonneg : 0 ≤ floorCellMass support mass scan.round scan.last := by
      unfold floorCellMass
      apply Finset.sum_nonneg
      intro b hb
      split
      · exact hmass b hb
      · exact le_rfl
    have hpaid : q * ((scan.kept.card : ℝ) - 1) ≤ K :=
      (le_add_of_nonneg_right hcell_nonneg).trans scan.budget |>.trans htotal
    have hquot : (scan.kept.card : ℝ) - 1 ≤ K / q :=
      (le_div_iff₀ hq).2 (by simpa [mul_comm] using hpaid)
    have hcard_pos : 0 < scan.kept.card := Finset.card_pos.mpr ⟨scan.last, scan.last_mem⟩
    have hfloor : scan.kept.card - 1 ≤ ⌊K / q⌋₊ := by
      apply Nat.le_floor
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hcard_pos))]
      linarith
    omega
  · have hs_empty : support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst support
    refine ⟨∅, fun _ ↦ 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp

end KeptSizes

end WeightedMultigraph
end WeightedEdgeColoring
