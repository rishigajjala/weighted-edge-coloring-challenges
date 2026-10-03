import WeightedEdgeColoring.HalfLoad

/-!
# A weighted local polytope with one-item slack

If every item has weight at most `tau`, a fractional vector whose expected
load is at most `capacity - tau` is a convex combination of feasible
zero-one subsets.  The proof is the standard two-coordinate dependent
rounding argument: preserve weighted load until one coordinate reaches zero
or one, and use the one remaining fractional coordinate's `tau` slack in the
base case.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

section WeightedSlackLocalPolytope

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem weightedSum_replace_two (w x : I → ℝ)
    {i j : I} (hij : i ≠ j) (a b : ℝ) :
    (∑ t, w t * (if t = i then a else if t = j then b else x t)) =
      (∑ t, w t * x t) - w i * x i - w j * x j + w i * a + w j * b := by
  classical
  rw [← Finset.sum_erase_add Finset.univ (fun t => w t * x t)
    (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ.erase i) (fun t => w t * x t)
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  rw [← Finset.sum_erase_add Finset.univ
    (fun t => w t * (if t = i then a else if t = j then b else x t))
    (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ.erase i)
    (fun t => w t * (if t = i then a else if t = j then b else x t))
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  have hrest :
      (∑ t ∈ (Finset.univ.erase i).erase j,
        w t * (if t = i then a else if t = j then b else x t)) =
      ∑ t ∈ (Finset.univ.erase i).erase j, w t * x t := by
    apply Finset.sum_congr rfl
    intro t ht
    have hti : t ≠ i :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
    have htj : t ≠ j := (Finset.mem_erase.mp ht).1
    simp [hti, htj]
  rw [hrest]
  simp [hij, hij.symm]
  ring

/-- A weighted box with one maximum item of unused capacity lies in the
convex hull of feasible zero-one knapsack vectors. -/
theorem weightedSlack_mem_convexHull
    (w x : I → ℝ) (capacity tau : ℝ)
    (hwpos : ∀ i, 0 < w i) (hwtau : ∀ i, w i ≤ tau)
    (htau : 0 ≤ tau)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hload : ∑ i, w i * x i ≤ capacity - tau) :
    x ∈ convexHull ℝ (feasibleIndicatorSet w capacity) := by
  classical
  let goalFor : ℕ → Prop := fun m =>
    ∀ x : I → ℝ, (fractionalSupport x).card = m →
      (∀ i, 0 ≤ x i) → (∀ i, x i ≤ 1) →
      (∑ i, w i * x i ≤ capacity - tau) →
      x ∈ convexHull ℝ (feasibleIndicatorSet w capacity)
  have hgoal : ∀ m, goalFor m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hm hx0 hx1 hload
      by_cases hmone : m ≤ 1
      · rcases Nat.eq_zero_or_pos m with rfl | hmpos
        · have hfrac : fractionalSupport x = ∅ := Finset.card_eq_zero.mp hm
          apply subset_convexHull ℝ
          refine ⟨?_, ?_⟩
          · intro i
            by_contra hi
            have hi' : x i ≠ 0 ∧ x i ≠ 1 := not_or.mp hi
            have : i ∈ fractionalSupport x := by
              simp [fractionalSupport, hi']
            simpa [hfrac] using this
          · exact hload.trans (sub_le_self capacity htau)
        · have hm1 : m = 1 := by omega
          obtain ⟨i, hfrac⟩ := Finset.card_eq_one.mp (hm1 ▸ hm)
          have hiFrac : x i ≠ 0 ∧ x i ≠ 1 := by
            have : i ∈ fractionalSupport x := by simp [hfrac]
            simpa [fractionalSupport] using this
          have hxi0 : 0 < x i :=
            lt_of_le_of_ne (hx0 i) (Ne.symm hiFrac.1)
          have hxi1 : x i < 1 :=
            lt_of_le_of_ne (hx1 i) hiFrac.2
          have hother : ∀ j, j ≠ i → x j = 0 ∨ x j = 1 := by
            intro j hji
            by_contra hj
            have hjmem : j ∈ fractionalSupport x := by
              simp [fractionalSupport, not_or.mp hj]
            have : j = i := by simpa [hfrac] using hjmem
            exact hji this
          let y0 : I → ℝ := fun j => if j = i then 0 else x j
          let y1 : I → ℝ := fun j => if j = i then 1 else x j
          have hload0 : (∑ j, w j * y0 j) =
              (∑ j, w j * x j) - w i * x i := by
            rw [← Finset.sum_erase_add Finset.univ (fun j => w j * x j)
              (Finset.mem_univ i)]
            rw [← Finset.sum_erase_add Finset.univ (fun j => w j * y0 j)
              (Finset.mem_univ i)]
            have hrest : (∑ j ∈ Finset.univ.erase i, w j * y0 j) =
                ∑ j ∈ Finset.univ.erase i, w j * x j := by
              apply Finset.sum_congr rfl
              intro j hj
              have hji : j ≠ i := (Finset.mem_erase.mp hj).1
              simp [y0, hji]
            rw [hrest]
            simp [y0]
          have hload1 : (∑ j, w j * y1 j) =
              (∑ j, w j * x j) + w i * (1 - x i) := by
            rw [← Finset.sum_erase_add Finset.univ (fun j => w j * x j)
              (Finset.mem_univ i)]
            rw [← Finset.sum_erase_add Finset.univ (fun j => w j * y1 j)
              (Finset.mem_univ i)]
            have hrest : (∑ j ∈ Finset.univ.erase i, w j * y1 j) =
                ∑ j ∈ Finset.univ.erase i, w j * x j := by
              apply Finset.sum_congr rfl
              intro j hj
              have hji : j ≠ i := (Finset.mem_erase.mp hj).1
              simp [y1, hji]
            rw [hrest]
            simp [y1]
            ring
          have hy0 : y0 ∈ feasibleIndicatorSet w capacity := by
            refine ⟨?_, ?_⟩
            · intro j
              by_cases hji : j = i
              · simp [y0, hji]
              · simpa [y0, hji] using hother j hji
            · rw [hload0]
              have hnonneg : 0 ≤ w i * x i :=
                mul_nonneg (hwpos i).le (hx0 i)
              linarith
          have hy1 : y1 ∈ feasibleIndicatorSet w capacity := by
            refine ⟨?_, ?_⟩
            · intro j
              by_cases hji : j = i
              · simp [y1, hji]
              · simpa [y1, hji] using hother j hji
            · rw [hload1]
              have hone : 0 ≤ 1 - x i := sub_nonneg.mpr (hx1 i)
              have hinc : w i * (1 - x i) ≤ tau := by
                calc
                  w i * (1 - x i) ≤ w i * 1 :=
                    mul_le_mul_of_nonneg_left (by linarith [hx0 i])
                      (hwpos i).le
                  _ = w i := by ring
                  _ ≤ tau := hwtau i
              linarith
          apply (convex_convexHull ℝ _).segment_subset
              (subset_convexHull ℝ _ hy0) (subset_convexHull ℝ _ hy1)
          refine ⟨1 - x i, x i, sub_nonneg.mpr (hx1 i), hx0 i,
            by ring, ?_⟩
          funext j
          by_cases hji : j = i
          · subst j
            simp [y0, y1]
          · simp [y0, y1, hji]
            ring
      · have hmtwo : 2 ≤ m := by omega
        have hcardtwo : 1 < (fractionalSupport x).card := by omega
        obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcardtwo
        have hiFrac : x i ≠ 0 ∧ x i ≠ 1 := by
          simpa [fractionalSupport] using hi
        have hjFrac : x j ≠ 0 ∧ x j ≠ 1 := by
          simpa [fractionalSupport] using hj
        have hxi0 : 0 < x i :=
          lt_of_le_of_ne (hx0 i) (Ne.symm hiFrac.1)
        have hxi1 : x i < 1 :=
          lt_of_le_of_ne (hx1 i) hiFrac.2
        have hxj0 : 0 < x j :=
          lt_of_le_of_ne (hx0 j) (Ne.symm hjFrac.1)
        have hxj1 : x j < 1 :=
          lt_of_le_of_ne (hx1 j) hjFrac.2
        have hwi : 0 < w i := hwpos i
        have hwj : 0 < w j := hwpos j
        let A : ℝ := min (x i / w j) ((1 - x j) / w i)
        let B : ℝ := min ((1 - x i) / w j) (x j / w i)
        have hA : 0 < A := by
          dsimp [A]
          exact lt_min (div_pos hxi0 hwj) (div_pos (sub_pos.mpr hxj1) hwi)
        have hB : 0 < B := by
          dsimp [B]
          exact lt_min (div_pos (sub_pos.mpr hxi1) hwj) (div_pos hxj0 hwi)
        let xp : I → ℝ := fun t =>
          if t = i then x i + B * w j
          else if t = j then x j - B * w i else x t
        let xm : I → ℝ := fun t =>
          if t = i then x i - A * w j
          else if t = j then x j + A * w i else x t
        have hBleft : B * w j ≤ 1 - x i := by
          exact (le_div_iff₀ hwj).mp (min_le_left _ _)
        have hBright : B * w i ≤ x j := by
          exact (le_div_iff₀ hwi).mp (min_le_right _ _)
        have hAleft : A * w j ≤ x i := by
          exact (le_div_iff₀ hwj).mp (min_le_left _ _)
        have hAright : A * w i ≤ 1 - x j := by
          exact (le_div_iff₀ hwi).mp (min_le_right _ _)
        have hxp0 : ∀ t, 0 ≤ xp t := by
          intro t
          by_cases hti : t = i
          · subst t
            simp [xp]
            positivity
          · by_cases htj : t = j
            · subst t
              simp [xp, hij.symm]
              linarith
            · simpa [xp, hti, htj] using hx0 t
        have hxp1 : ∀ t, xp t ≤ 1 := by
          intro t
          by_cases hti : t = i
          · subst t
            simp [xp]
            linarith
          · by_cases htj : t = j
            · subst t
              simp [xp, hij.symm]
              have hnonneg : 0 ≤ B * w i :=
                mul_nonneg hB.le hwi.le
              linarith [hx1 j]
            · simpa [xp, hti, htj] using hx1 t
        have hxm0 : ∀ t, 0 ≤ xm t := by
          intro t
          by_cases hti : t = i
          · subst t
            simp [xm]
            linarith
          · by_cases htj : t = j
            · subst t
              simp [xm, hij.symm]
              positivity
            · simpa [xm, hti, htj] using hx0 t
        have hxm1 : ∀ t, xm t ≤ 1 := by
          intro t
          by_cases hti : t = i
          · subst t
            simp [xm]
            have hnonneg : 0 ≤ A * w j :=
              mul_nonneg hA.le hwj.le
            linarith [hx1 i]
          · by_cases htj : t = j
            · subst t
              simp [xm, hij.symm]
              linarith
            · simpa [xm, hti, htj] using hx1 t
        have hloadp : (∑ t, w t * xp t) = ∑ t, w t * x t := by
          rw [show (∑ t, w t * xp t) =
              ∑ t, w t * (if t = i then x i + B * w j
                else if t = j then x j - B * w i else x t) by rfl]
          rw [weightedSum_replace_two w x hij
            (x i + B * w j) (x j - B * w i)]
          ring
        have hloadm : (∑ t, w t * xm t) = ∑ t, w t * x t := by
          rw [show (∑ t, w t * xm t) =
              ∑ t, w t * (if t = i then x i - A * w j
                else if t = j then x j + A * w i else x t) by rfl]
          rw [weightedSum_replace_two w x hij
            (x i - A * w j) (x j + A * w i)]
          ring
        have hfracp_sub : fractionalSupport xp ⊆ fractionalSupport x := by
          intro t ht
          by_cases hti : t = i
          · simpa [hti] using hi
          · by_cases htj : t = j
            · simpa [htj] using hj
            · have ht' : xp t ≠ 0 ∧ xp t ≠ 1 := by
                simpa [fractionalSupport] using ht
              have : x t ≠ 0 ∧ x t ≠ 1 := by
                simpa [xp, hti, htj] using ht'
              simpa [fractionalSupport] using this
        have hfracm_sub : fractionalSupport xm ⊆ fractionalSupport x := by
          intro t ht
          by_cases hti : t = i
          · simpa [hti] using hi
          · by_cases htj : t = j
            · simpa [htj] using hj
            · have ht' : xm t ≠ 0 ∧ xm t ≠ 1 := by
                simpa [fractionalSupport] using ht
              have : x t ≠ 0 ∧ x t ≠ 1 := by
                simpa [xm, hti, htj] using ht'
              simpa [fractionalSupport] using this
        have hp_boundary : xp i = 1 ∨ xp j = 0 := by
          rcases min_choice ((1 - x i) / w j) (x j / w i) with h | h
          · left
            simp [xp, B, h]
            field_simp
            ring
          · right
            simp [xp, B, h, hij.symm]
            field_simp
            ring
        have hm_boundary : xm i = 0 ∨ xm j = 1 := by
          rcases min_choice (x i / w j) ((1 - x j) / w i) with h | h
          · left
            simp [xm, A, h]
            field_simp
            ring
          · right
            simp [xm, A, h, hij.symm]
            field_simp
            ring
        have hfracp_ne : fractionalSupport xp ≠ fractionalSupport x := by
          intro heq
          rcases hp_boundary with hpi | hpj
          · have : i ∈ fractionalSupport xp := heq ▸ hi
            have hi' : xp i ≠ 0 ∧ xp i ≠ 1 := by
              simpa [fractionalSupport] using this
            exact hi'.2 hpi
          · have : j ∈ fractionalSupport xp := heq ▸ hj
            have hj' : xp j ≠ 0 ∧ xp j ≠ 1 := by
              simpa [fractionalSupport] using this
            exact hj'.1 hpj
        have hfracm_ne : fractionalSupport xm ≠ fractionalSupport x := by
          intro heq
          rcases hm_boundary with hmi | hmj
          · have : i ∈ fractionalSupport xm := heq ▸ hi
            have hi' : xm i ≠ 0 ∧ xm i ≠ 1 := by
              simpa [fractionalSupport] using this
            exact hi'.1 hmi
          · have : j ∈ fractionalSupport xm := heq ▸ hj
            have hj' : xm j ≠ 0 ∧ xm j ≠ 1 := by
              simpa [fractionalSupport] using this
            exact hj'.2 hmj
        have hcardp : (fractionalSupport xp).card < m := by
          rw [← hm]
          exact Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨hfracp_sub, hfracp_ne⟩)
        have hcardm : (fractionalSupport xm).card < m := by
          rw [← hm]
          exact Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨hfracm_sub, hfracm_ne⟩)
        have hpHull := ih (fractionalSupport xp).card hcardp xp rfl
          hxp0 hxp1 (hloadp ▸ hload)
        have hmHull := ih (fractionalSupport xm).card hcardm xm rfl
          hxm0 hxm1 (hloadm ▸ hload)
        apply (convex_convexHull ℝ _).segment_subset hpHull hmHull
        let lambda : ℝ := A / (A + B)
        refine ⟨lambda, 1 - lambda, ?_, ?_, by ring, ?_⟩
        · exact div_nonneg hA.le (add_nonneg hA.le hB.le)
        · apply sub_nonneg.mpr
          exact (div_le_one (add_pos hA hB)).2
            (le_add_of_nonneg_right hB.le)
        · funext t
          have hAB : A + B ≠ 0 := ne_of_gt (add_pos hA hB)
          by_cases hti : t = i
          · subst t
            simp [lambda, xp, xm]
            field_simp [hAB]
            ring
          · by_cases htj : t = j
            · subst t
              simp [lambda, xp, xm, hij.symm]
              field_simp [hAB]
              ring
            · simp [lambda, xp, xm, hti, htj]
              field_simp [hAB]
              ring
  exact hgoal (fractionalSupport x).card x rfl hx0 hx1 hload

/-- Distribution form of `weightedSlack_mem_convexHull`. -/
theorem weightedSlack_isAverageOfFeasibleSubsets
    (w x : I → ℝ) (capacity tau : ℝ)
    (hwpos : ∀ i, 0 < w i) (hwtau : ∀ i, w i ≤ tau)
    (htau : 0 ≤ tau)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hload : ∑ i, w i * x i ≤ capacity - tau) :
    IsAverageOfFeasibleSubsets w capacity x := by
  apply (isAverageOfFeasibleSubsets_iff_mem_convexHull w capacity x).2
  exact weightedSlack_mem_convexHull w x capacity tau hwpos hwtau htau
    hx0 hx1 hload

end WeightedSlackLocalPolytope

end WeightedEdgeColoring
