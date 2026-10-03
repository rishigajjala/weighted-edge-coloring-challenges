import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Segment
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace WeightedEdgeColoring

section HalfLoad

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Coordinates that are not already zero or one. -/
noncomputable def fractionalSupport (x : I → ℝ) : Finset I :=
  Finset.univ.filter fun i => x i ≠ 0 ∧ x i ≠ 1

/-- Zero-one vectors whose selected items have total weight at most `cap`. -/
def feasibleIndicatorSet (w : I → ℝ) (cap : ℝ) : Set (I → ℝ) :=
  {y | (∀ i, y i = 0 ∨ y i = 1) ∧ ∑ i, w i * y i ≤ cap}

/-- The zero-one vector of a finite subset. -/
def subsetIndicator (S : Finset I) : I → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- A finite probability distribution on subsets, supported on subsets of
weight at most `cap`, and having marginal vector `x`. -/
def IsAverageOfFeasibleSubsets (w : I → ℝ) (cap : ℝ)
    (x : I → ℝ) : Prop :=
  ∃ p : Finset I → ℝ,
    (∀ S, 0 ≤ p S) ∧
    (∑ S, p S = 1) ∧
    (∀ S, p S ≠ 0 → ∑ i ∈ S, w i ≤ cap) ∧
    (∀ i, (∑ S, if i ∈ S then p S else 0) = x i)

private theorem subsetIndicator_injective :
    Function.Injective (subsetIndicator : Finset I → I → ℝ) := by
  intro S T h
  ext i
  have hi := congrFun h i
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;>
    simp [subsetIndicator, hiS, hiT] at hi ⊢

private theorem feasibleIndicatorSet_eq_image (w : I → ℝ) (cap : ℝ) :
    feasibleIndicatorSet w cap =
      (Finset.univ.filter (fun S : Finset I => ∑ i ∈ S, w i ≤ cap)).image
        subsetIndicator := by
  ext y
  constructor
  · rintro ⟨hy01, hyload⟩
    let S : Finset I := Finset.univ.filter fun i => y i = 1
    have hy : subsetIndicator S = y := by
      funext i
      rcases hy01 i with hi | hi
      · simp [subsetIndicator, S, hi]
      · simp [subsetIndicator, S, hi]
    have hsum : (∑ i ∈ S, w i) = ∑ i, w i * y i := by
      dsimp [S]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _hi
      rcases hy01 i with hi | hi <;> simp [hi]
    simp only [Finset.coe_image, Set.mem_image]
    refine ⟨S, ?_, hy⟩
    simp [S, hsum, hyload]
  · intro hy
    simp only [Finset.coe_image, Set.mem_image] at hy
    rcases hy with ⟨S, hS, rfl⟩
    have hcap : ∑ i ∈ S, w i ≤ cap := by
      simpa using (Finset.mem_filter.mp hS).2
    refine ⟨fun i => by
      by_cases hi : i ∈ S <;> simp [subsetIndicator, hi], ?_⟩
    calc
      (∑ i, w i * subsetIndicator S i) = ∑ i ∈ S, w i := by
        simp [subsetIndicator]
      _ ≤ cap := hcap

/-- Convex-hull membership in the set of feasible zero-one vectors is
equivalent to a genuine finite distribution on feasible subsets. -/
theorem isAverageOfFeasibleSubsets_iff_mem_convexHull
    (w : I → ℝ) (cap : ℝ) (x : I → ℝ) :
    IsAverageOfFeasibleSubsets w cap x ↔
      x ∈ convexHull ℝ (feasibleIndicatorSet w cap) := by
  classical
  let A : Finset (Finset I) :=
    Finset.univ.filter fun S => ∑ i ∈ S, w i ≤ cap
  let V : Finset (I → ℝ) := A.image subsetIndicator
  let decode : (I → ℝ) → Finset I := fun y =>
    Finset.univ.filter fun i => y i = 1
  have hdecode (S : Finset I) : decode (subsetIndicator S) = S := by
    ext i
    by_cases hi : i ∈ S <;> simp [decode, subsetIndicator, hi]
  have hset : feasibleIndicatorSet w cap = (V : Set (I → ℝ)) := by
    simpa [A, V] using feasibleIndicatorSet_eq_image w cap
  constructor
  · rintro ⟨p, hp0, hpsum, hsupport, hmarg⟩
    rw [hset, Finset.mem_convexHull']
    let coeff : (I → ℝ) → ℝ := fun y => p (decode y)
    have hcoeff_indicator (S : Finset I) (hS : S ∈ A) :
        coeff (subsetIndicator S) = p S := by
      simp [coeff, hdecode]
    refine ⟨coeff, ?_, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨S, hS, rfl⟩
      rw [hcoeff_indicator S hS]
      exact hp0 S
    · rw [Finset.sum_image subsetIndicator_injective.injOn]
      calc
        (∑ S ∈ A, coeff (subsetIndicator S)) = ∑ S ∈ A, p S := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [hcoeff_indicator S hS]
        _ = ∑ S, p S := by
          apply Finset.sum_subset (Finset.subset_univ A)
          intro S _hSuniv hSnot
          have hbad : ¬∑ i ∈ S, w i ≤ cap := by simpa [A] using hSnot
          by_contra hp
          exact hbad (hsupport S hp)
        _ = 1 := hpsum
    · funext i
      rw [Finset.sum_image subsetIndicator_injective.injOn]
      have heval :
          ((∑ S ∈ A, coeff (subsetIndicator S) • subsetIndicator S) : I → ℝ) i =
            ∑ S ∈ A, coeff (subsetIndicator S) *
              (if i ∈ S then 1 else 0) := by
        simp [subsetIndicator]
      rw [heval]
      calc
        (∑ S ∈ A, coeff (subsetIndicator S) *
            if i ∈ S then 1 else 0) =
            ∑ S ∈ A, p S * if i ∈ S then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [hcoeff_indicator S hS]
        _ = ∑ S ∈ A, if i ∈ S then p S else 0 := by
          apply Finset.sum_congr rfl
          intro S _hS
          by_cases hiS : i ∈ S <;> simp [hiS]
        _ = ∑ S, if i ∈ S then p S else 0 := by
          apply Finset.sum_subset (Finset.subset_univ A)
          intro S _hSuniv hSnot
          have hp : p S = 0 := by
            by_contra hpne
            have := hsupport S hpne
            exact hSnot (by simpa [A] using this)
          simp [hp]
        _ = x i := hmarg i
  · intro hx
    rw [hset, Finset.mem_convexHull'] at hx
    rcases hx with ⟨coeff, hcoeff0, hcoeffsum, hcenter⟩
    let p : Finset I → ℝ := fun S => if S ∈ A then coeff (subsetIndicator S) else 0
    refine ⟨p, ?_, ?_, ?_, ?_⟩
    · intro S
      by_cases hS : S ∈ A
      · simp only [p, if_pos hS]
        exact hcoeff0 _ (Finset.mem_image.mpr ⟨S, hS, rfl⟩)
      · simp [p, hS]
    · calc
        (∑ S, p S) = ∑ S ∈ A, coeff (subsetIndicator S) := by
          have hfilter : Finset.univ.filter (fun S : Finset I => S ∈ A) = A := by
            ext S
            simp
          rw [← Finset.sum_filter]
          rw [hfilter]
        _ = ∑ y ∈ V, coeff y := by
          rw [Finset.sum_image subsetIndicator_injective.injOn]
        _ = 1 := hcoeffsum
    · intro S hp
      have hSA : S ∈ A := by
        by_contra h
        simp [p, h] at hp
      simpa [A] using (Finset.mem_filter.mp hSA).2
    · intro i
      have hi := congrFun hcenter i
      rw [Finset.sum_image subsetIndicator_injective.injOn] at hi
      have hi' :
          (∑ S ∈ A, coeff (subsetIndicator S) *
            (if i ∈ S then 1 else 0)) = x i := by
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          subsetIndicator] using hi
      calc
        (∑ S, if i ∈ S then p S else 0) =
            ∑ S ∈ A, if i ∈ S then p S else 0 := by
          symm
          apply Finset.sum_subset (Finset.subset_univ A)
          intro S _hSuniv hSnot
          have hp : p S = 0 := by simp [p, hSnot]
          simp [hp]
        _ = ∑ S ∈ A, coeff (subsetIndicator S) *
              (if i ∈ S then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro S hSA
          by_cases hiS : i ∈ S <;> simp [p, hSA, hiS]
        _ = x i := hi'

private theorem sum_replace_two (w x : I → ℝ) {i j : I} (hij : i ≠ j)
    (a b : ℝ) :
    (∑ k, w k * (if k = i then a else if k = j then b else x k)) =
      (∑ k, w k * x k) - w i * x i - w j * x j + w i * a + w j * b := by
  classical
  rw [← Finset.sum_erase_add (Finset.univ) (fun k => w k * x k)
    (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ.erase i) (fun k => w k * x k)
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  rw [← Finset.sum_erase_add (Finset.univ)
    (fun k => w k * (if k = i then a else if k = j then b else x k))
    (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ.erase i)
    (fun k => w k * (if k = i then a else if k = j then b else x k))
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  have hrest :
      (∑ k ∈ (Finset.univ.erase i).erase j,
        w k * (if k = i then a else if k = j then b else x k)) =
      ∑ k ∈ (Finset.univ.erase i).erase j, w k * x k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := by
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    simp [hki, hkj]
  rw [hrest]
  simp [hij, hij.symm]
  ring

/-- The elementary half-load lemma in convex-hull form.  A fractional
selection of items of size at most one half and fractional load at most one
half is an average of integral subsets of load at most one. -/
theorem halfLoad_mem_convexHull
    (w x : I → ℝ)
    (hw0 : ∀ i, 0 < w i) (hw : ∀ i, w i ≤ 1 / 2)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hload : ∑ i, w i * x i ≤ 1 / 2) :
    x ∈ convexHull ℝ (feasibleIndicatorSet w 1) := by
  classical
  let goalFor : ℕ → Prop := fun k =>
    ∀ x : I → ℝ, (fractionalSupport x).card = k →
      (∀ i, 0 ≤ x i) → (∀ i, x i ≤ 1) →
      (∑ i, w i * x i ≤ 1 / 2) →
      x ∈ convexHull ℝ (feasibleIndicatorSet w 1)
  have hgoal : ∀ k, goalFor k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hk hx0 hx1 hload
      by_cases hkone : k ≤ 1
      · rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · have hfrac : fractionalSupport x = ∅ := Finset.card_eq_zero.mp hk
          apply subset_convexHull ℝ
          refine ⟨?_, hload.trans (by norm_num)⟩
          intro i
          by_contra hi
          have hi' : x i ≠ 0 ∧ x i ≠ 1 := not_or.mp hi
          have : i ∈ fractionalSupport x := by simp [fractionalSupport, hi']
          simpa [hfrac] using this
        · have hk1 : k = 1 := by omega
          obtain ⟨i, hfrac⟩ := Finset.card_eq_one.mp (hk1 ▸ hk)
          have hiFrac : x i ≠ 0 ∧ x i ≠ 1 := by
            have : i ∈ fractionalSupport x := by simp [hfrac]
            simpa [fractionalSupport] using this
          have hother : ∀ j, j ≠ i → x j = 0 ∨ x j = 1 := by
            intro j hji
            by_contra hj
            have hjmem : j ∈ fractionalSupport x := by
              simp [fractionalSupport, not_or.mp hj]
            have : j = i := by simpa [hfrac] using hjmem
            exact hji this
          let y0 : I → ℝ := fun j => if j = i then 0 else x j
          let y1 : I → ℝ := fun j => if j = i then 1 else x j
          have hsum0 : (∑ j, w j * y0 j) = (∑ j, w j * x j) - w i * x i := by
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
          have hsum1 : (∑ j, w j * y1 j) =
              (∑ j, w j * x j) - w i * x i + w i := by
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
          have hy0 : y0 ∈ feasibleIndicatorSet w 1 := by
            refine ⟨?_, ?_⟩
            · intro j
              by_cases hji : j = i
              · simp [y0, hji]
              · simpa [y0, hji] using hother j hji
            · rw [hsum0]
              have : 0 ≤ w i * x i := mul_nonneg (hw0 i).le (hx0 i)
              linarith
          have hy1 : y1 ∈ feasibleIndicatorSet w 1 := by
            refine ⟨?_, ?_⟩
            · intro j
              by_cases hji : j = i
              · simp [y1, hji]
              · simpa [y1, hji] using hother j hji
            · rw [hsum1]
              have : 0 ≤ w i * x i := mul_nonneg (hw0 i).le (hx0 i)
              have hwi := hw i
              linarith
          apply (convex_convexHull ℝ _).segment_subset
              (subset_convexHull ℝ _ hy0) (subset_convexHull ℝ _ hy1)
          refine ⟨1 - x i, x i, sub_nonneg.mpr (hx1 i), hx0 i, by ring, ?_⟩
          funext j
          by_cases hji : j = i
          · subst j
            simp [y0, y1]
          · simp [y0, y1, hji]
            ring
      · have hktwo : 2 ≤ k := by omega
        have hcardtwo : 1 < (fractionalSupport x).card := by omega
        obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcardtwo
        have hiFrac : x i ≠ 0 ∧ x i ≠ 1 := by
          simpa [fractionalSupport] using hi
        have hjFrac : x j ≠ 0 ∧ x j ≠ 1 := by
          simpa [fractionalSupport] using hj
        have hxi0 : 0 < x i := lt_of_le_of_ne (hx0 i) (Ne.symm hiFrac.1)
        have hxi1 : x i < 1 := lt_of_le_of_ne (hx1 i) hiFrac.2
        have hxj0 : 0 < x j := lt_of_le_of_ne (hx0 j) (Ne.symm hjFrac.1)
        have hxj1 : x j < 1 := lt_of_le_of_ne (hx1 j) hjFrac.2
        let A : ℝ := min (x i / w j) ((1 - x j) / w i)
        let B : ℝ := min ((1 - x i) / w j) (x j / w i)
        have hA : 0 < A := by
          dsimp [A]
          exact lt_min (div_pos hxi0 (hw0 j))
            (div_pos (sub_pos.mpr hxj1) (hw0 i))
        have hB : 0 < B := by
          dsimp [B]
          exact lt_min (div_pos (sub_pos.mpr hxi1) (hw0 j))
            (div_pos hxj0 (hw0 i))
        let xp : I → ℝ := fun t =>
          if t = i then x i + B * w j
          else if t = j then x j - B * w i else x t
        let xm : I → ℝ := fun t =>
          if t = i then x i - A * w j
          else if t = j then x j + A * w i else x t
        have hBleft : B ≤ (1 - x i) / w j := min_le_left _ _
        have hBright : B ≤ x j / w i := min_le_right _ _
        have hAleft : A ≤ x i / w j := min_le_left _ _
        have hAright : A ≤ (1 - x j) / w i := min_le_right _ _
        have hxp0 : ∀ t, 0 ≤ xp t := by
          intro t
          by_cases hti : t = i
          · subst t
            simp only [xp, if_pos rfl]
            exact add_nonneg (hx0 i) (mul_nonneg hB.le (hw0 j).le)
          · by_cases htj : t = j
            · subst t
              dsimp only [xp]
              rw [if_neg hij.symm, if_pos rfl]
              have := (le_div_iff₀ (hw0 i)).mp hBright
              linarith
            · simpa [xp, hti, htj] using hx0 t
        have hxp1 : ∀ t, xp t ≤ 1 := by
          intro t
          by_cases hti : t = i
          · subst t
            simp [xp]
            have := (le_div_iff₀ (hw0 j)).mp hBleft
            linarith
          · by_cases htj : t = j
            · subst t
              dsimp only [xp]
              rw [if_neg hij.symm, if_pos rfl]
              have hprod : 0 ≤ B * w i := mul_nonneg hB.le (hw0 i).le
              linarith [hx1 j]
            · simpa [xp, hti, htj] using hx1 t
        have hxm0 : ∀ t, 0 ≤ xm t := by
          intro t
          by_cases hti : t = i
          · subst t
            simp [xm]
            have := (le_div_iff₀ (hw0 j)).mp hAleft
            linarith
          · by_cases htj : t = j
            · subst t
              dsimp only [xm]
              rw [if_neg hij.symm, if_pos rfl]
              exact add_nonneg (hx0 j) (mul_nonneg hA.le (hw0 i).le)
            · simpa [xm, hti, htj] using hx0 t
        have hxm1 : ∀ t, xm t ≤ 1 := by
          intro t
          by_cases hti : t = i
          · subst t
            simp only [xm, if_pos rfl]
            have hprod : 0 ≤ A * w j := mul_nonneg hA.le (hw0 j).le
            linarith [hx1 i]
          · by_cases htj : t = j
            · subst t
              simp [xm, hij.symm]
              have := (le_div_iff₀ (hw0 i)).mp hAright
              linarith
            · simpa [xm, hti, htj] using hx1 t
        have hloadp : (∑ t, w t * xp t) = ∑ t, w t * x t := by
          rw [show (∑ t, w t * xp t) =
              ∑ t, w t * (if t = i then x i + B * w j
                else if t = j then x j - B * w i else x t) by rfl]
          rw [sum_replace_two w x hij (x i + B * w j) (x j - B * w i)]
          ring
        have hloadm : (∑ t, w t * xm t) = ∑ t, w t * x t := by
          rw [show (∑ t, w t * xm t) =
              ∑ t, w t * (if t = i then x i - A * w j
                else if t = j then x j + A * w i else x t) by rfl]
          rw [sum_replace_two w x hij (x i - A * w j) (x j + A * w i)]
          ring
        have hfracp_sub : fractionalSupport xp ⊆ fractionalSupport x := by
          intro t ht
          by_cases hti : t = i
          · simpa [hti] using hi
          · by_cases htj : t = j
            · simpa [htj] using hj
            · have ht' : xp t ≠ 0 ∧ xp t ≠ 1 := by
                simpa [fractionalSupport] using ht
              have : x t ≠ 0 ∧ x t ≠ 1 := by simpa [xp, hti, htj] using ht'
              simpa [fractionalSupport] using this
        have hfracm_sub : fractionalSupport xm ⊆ fractionalSupport x := by
          intro t ht
          by_cases hti : t = i
          · simpa [hti] using hi
          · by_cases htj : t = j
            · simpa [htj] using hj
            · have ht' : xm t ≠ 0 ∧ xm t ≠ 1 := by
                simpa [fractionalSupport] using ht
              have : x t ≠ 0 ∧ x t ≠ 1 := by simpa [xm, hti, htj] using ht'
              simpa [fractionalSupport] using this
        have hp_boundary : xp i = 1 ∨ xp j = 0 := by
          rcases min_choice ((1 - x i) / w j) (x j / w i) with h | h
          · left
            simp [xp, B, h]
            field_simp [(hw0 j).ne']
            ring
          · right
            simp [xp, B, h, hij.symm]
            field_simp [(hw0 i).ne']
            ring
        have hm_boundary : xm i = 0 ∨ xm j = 1 := by
          rcases min_choice (x i / w j) ((1 - x j) / w i) with h | h
          · left
            simp [xm, A, h]
            field_simp [(hw0 j).ne']
            ring
          · right
            simp [xm, A, h, hij.symm]
            field_simp [(hw0 i).ne']
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
        have hcardp : (fractionalSupport xp).card < k := by
          rw [← hk]
          exact Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨hfracp_sub, hfracp_ne⟩)
        have hcardm : (fractionalSupport xm).card < k := by
          rw [← hk]
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

/-- Probability-distribution form of `halfLoad_mem_convexHull`. -/
theorem halfLoad_isAverageOfFeasibleSubsets
    (w x : I → ℝ)
    (hw0 : ∀ i, 0 < w i) (hw : ∀ i, w i ≤ 1 / 2)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hload : ∑ i, w i * x i ≤ 1 / 2) :
    IsAverageOfFeasibleSubsets w 1 x :=
  (isAverageOfFeasibleSubsets_iff_mem_convexHull w 1 x).2
    (halfLoad_mem_convexHull w x hw0 hw hx0 hx1 hload)

end HalfLoad

end WeightedEdgeColoring
