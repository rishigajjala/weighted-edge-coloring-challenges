import WeightedEdgeColoring.HalfLoad

/-!
# The cardinality local polytope

This is the elementary dependent-rounding fact used by the harmonic-class
argument.  If `0 ≤ xᵢ ≤ 1` and the sum of the coordinates is at most the
integer `k`, then `x` is the marginal vector of a distribution on subsets
of cardinality at most `k`.

The proof is finite and constructive in the usual sense: repeatedly move
mass between two fractional coordinates, preserving their sum, until one
of them reaches zero or one.  The formal statement is phrased using the
same probability-distribution interface as `HalfLoad`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

section CardinalityLocalPolytope

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Zero-one vectors selecting at most `k` coordinates. -/
def cardinalityIndicatorSet (k : ℕ) : Set (I → ℝ) :=
  {y | (∀ i, y i = 0 ∨ y i = 1) ∧ ∑ i, y i ≤ k}

private theorem sum_replace_two_unweighted (x : I → ℝ)
    {i j : I} (hij : i ≠ j) (a b : ℝ) :
    (∑ t, if t = i then a else if t = j then b else x t) =
      (∑ t, x t) - x i - x j + a + b := by
  classical
  rw [← Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ.erase i) x
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  rw [← Finset.sum_erase_add Finset.univ
    (fun t ↦ if t = i then a else if t = j then b else x t)
    (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ.erase i)
    (fun t ↦ if t = i then a else if t = j then b else x t)
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  have hrest :
      (∑ t ∈ (Finset.univ.erase i).erase j,
        if t = i then a else if t = j then b else x t) =
      ∑ t ∈ (Finset.univ.erase i).erase j, x t := by
    apply Finset.sum_congr rfl
    intro t ht
    have hti : t ≠ i :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
    have htj : t ≠ j := (Finset.mem_erase.mp ht).1
    simp [hti, htj]
  rw [hrest]
  simp [hij, hij.symm]
  ring

/-- The polytope `{x : 0 ≤ x ≤ 1, ∑ x ≤ k}` is the convex hull of
the zero-one vectors with at most `k` ones. -/
theorem cardinality_mem_convexHull (k : ℕ) (x : I → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hsum : ∑ i, x i ≤ k) :
    x ∈ convexHull ℝ (cardinalityIndicatorSet (I := I) k) := by
  classical
  let goalFor : ℕ → Prop := fun m ↦
    ∀ x : I → ℝ, (fractionalSupport x).card = m →
      (∀ i, 0 ≤ x i) → (∀ i, x i ≤ 1) →
      (∑ i, x i ≤ k) →
      x ∈ convexHull ℝ (cardinalityIndicatorSet (I := I) k)
  have hgoal : ∀ m, goalFor m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hm hx0 hx1 hsum
      by_cases hmone : m ≤ 1
      · rcases Nat.eq_zero_or_pos m with rfl | hmpos
        · have hfrac : fractionalSupport x = ∅ := Finset.card_eq_zero.mp hm
          apply subset_convexHull ℝ
          refine ⟨?_, hsum⟩
          intro i
          by_contra hi
          have hi' : x i ≠ 0 ∧ x i ≠ 1 := not_or.mp hi
          have : i ∈ fractionalSupport x := by
            simp [fractionalSupport, hi']
          simpa [hfrac] using this
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
          let y0 : I → ℝ := fun j ↦ if j = i then 0 else x j
          let y1 : I → ℝ := fun j ↦ if j = i then 1 else x j
          have hsum0 : (∑ j, y0 j) = (∑ j, x j) - x i := by
            rw [← Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)]
            rw [← Finset.sum_erase_add Finset.univ y0 (Finset.mem_univ i)]
            have hrest : (∑ j ∈ Finset.univ.erase i, y0 j) =
                ∑ j ∈ Finset.univ.erase i, x j := by
              apply Finset.sum_congr rfl
              intro j hj
              have hji : j ≠ i := (Finset.mem_erase.mp hj).1
              simp [y0, hji]
            rw [hrest]
            simp [y0]
          have hsum1 : (∑ j, y1 j) = (∑ j, x j) - x i + 1 := by
            rw [← Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)]
            rw [← Finset.sum_erase_add Finset.univ y1 (Finset.mem_univ i)]
            have hrest : (∑ j ∈ Finset.univ.erase i, y1 j) =
                ∑ j ∈ Finset.univ.erase i, x j := by
              apply Finset.sum_congr rfl
              intro j hj
              have hji : j ≠ i := (Finset.mem_erase.mp hj).1
              simp [y1, hji]
            rw [hrest]
            simp [y1]
          have hy0 : y0 ∈ cardinalityIndicatorSet (I := I) k := by
            refine ⟨?_, ?_⟩
            · intro j
              by_cases hji : j = i
              · simp [y0, hji]
              · simpa [y0, hji] using hother j hji
            · rw [hsum0]
              linarith
          have hy1zeroone : ∀ j, y1 j = 0 ∨ y1 j = 1 := by
            intro j
            by_cases hji : j = i
            · simp [y1, hji]
            · simpa [y1, hji] using hother j hji
          have hy1sum : ∑ j, y1 j ≤ k := by
            let S : Finset I := Finset.univ.filter fun j ↦ y1 j = 1
            have hsumS : (∑ j, y1 j) = (S.card : ℝ) := by
              calc
                (∑ j, y1 j) = ∑ j, if y1 j = 1 then 1 else 0 := by
                  apply Finset.sum_congr rfl
                  intro j _hj
                  rcases hy1zeroone j with hj | hj <;> simp [hj]
                _ = (S.card : ℝ) := by simp [S]
            have hlt : (S.card : ℝ) < (k : ℝ) + 1 := by
              rw [← hsumS, hsum1]
              nlinarith
            have hnat : S.card < k + 1 := by exact_mod_cast hlt
            rw [hsumS]
            exact_mod_cast (by omega : S.card ≤ k)
          have hy1 : y1 ∈ cardinalityIndicatorSet (I := I) k :=
            ⟨hy1zeroone, hy1sum⟩
          apply (convex_convexHull ℝ _).segment_subset
              (subset_convexHull ℝ _ hy0) (subset_convexHull ℝ _ hy1)
          refine ⟨1 - x i, x i, sub_nonneg.mpr (hx1 i), hx0 i, by ring, ?_⟩
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
        let A : ℝ := min (x i) (1 - x j)
        let B : ℝ := min (1 - x i) (x j)
        have hA : 0 < A := by
          dsimp [A]
          exact lt_min hxi0 (sub_pos.mpr hxj1)
        have hB : 0 < B := by
          dsimp [B]
          exact lt_min (sub_pos.mpr hxi1) hxj0
        let xp : I → ℝ := fun t ↦
          if t = i then x i + B
          else if t = j then x j - B else x t
        let xm : I → ℝ := fun t ↦
          if t = i then x i - A
          else if t = j then x j + A else x t
        have hBleft : B ≤ 1 - x i := min_le_left _ _
        have hBright : B ≤ x j := min_le_right _ _
        have hAleft : A ≤ x i := min_le_left _ _
        have hAright : A ≤ 1 - x j := min_le_right _ _
        have hxp0 : ∀ t, 0 ≤ xp t := by
          intro t
          by_cases hti : t = i
          · subst t
            simp [xp]
            exact add_nonneg (hx0 i) hB.le
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
              linarith [hx1 j, hB.le]
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
              exact add_nonneg (hx0 j) hA.le
            · simpa [xm, hti, htj] using hx0 t
        have hxm1 : ∀ t, xm t ≤ 1 := by
          intro t
          by_cases hti : t = i
          · subst t
            simp [xm]
            linarith [hx1 i, hA.le]
          · by_cases htj : t = j
            · subst t
              simp [xm, hij.symm]
              linarith
            · simpa [xm, hti, htj] using hx1 t
        have hsump : (∑ t, xp t) = ∑ t, x t := by
          rw [show (∑ t, xp t) =
              ∑ t, if t = i then x i + B
                else if t = j then x j - B else x t by rfl]
          rw [sum_replace_two_unweighted x hij (x i + B) (x j - B)]
          ring
        have hsumm : (∑ t, xm t) = ∑ t, x t := by
          rw [show (∑ t, xm t) =
              ∑ t, if t = i then x i - A
                else if t = j then x j + A else x t by rfl]
          rw [sum_replace_two_unweighted x hij (x i - A) (x j + A)]
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
          rcases min_choice (1 - x i) (x j) with h | h
          · left
            simp [xp, B, h]
          · right
            simp [xp, B, h, hij.symm]
        have hm_boundary : xm i = 0 ∨ xm j = 1 := by
          rcases min_choice (x i) (1 - x j) with h | h
          · left
            simp [xm, A, h]
          · right
            simp [xm, A, h, hij.symm]
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
          hxp0 hxp1 (hsump ▸ hsum)
        have hmHull := ih (fractionalSupport xm).card hcardm xm rfl
          hxm0 hxm1 (hsumm ▸ hsum)
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
  exact hgoal (fractionalSupport x).card x rfl hx0 hx1 hsum

/-- Distribution form of `cardinality_mem_convexHull`. -/
theorem cardinality_isAverageOfFeasibleSubsets (k : ℕ) (hk : 0 < k)
    (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hsum : ∑ i, x i ≤ k) :
    IsAverageOfFeasibleSubsets (fun _ : I ↦ (1 : ℝ) / k) 1 x := by
  apply (isAverageOfFeasibleSubsets_iff_mem_convexHull
    (fun _ : I ↦ (1 : ℝ) / k) 1 x).2
  have hset : feasibleIndicatorSet (fun _ : I ↦ (1 : ℝ) / k) 1 =
      cardinalityIndicatorSet (I := I) k := by
    ext y
    constructor
    · rintro ⟨hy, hload⟩
      refine ⟨hy, ?_⟩
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have heq : (∑ i, (1 : ℝ) / k * y i) = (1 / k) * ∑ i, y i := by
        rw [Finset.mul_sum]
      rw [heq] at hload
      have hdiv : (∑ i, y i) / (k : ℝ) ≤ 1 := by
        simpa [div_eq_mul_inv, mul_comm] using hload
      simpa using (div_le_iff₀ hkR).mp hdiv
    · rintro ⟨hy, hsum'⟩
      refine ⟨hy, ?_⟩
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      calc
        (∑ i, (1 : ℝ) / k * y i) = (1 / k) * ∑ i, y i := by
          rw [Finset.mul_sum]
        _ ≤ (1 / k) * k := mul_le_mul_of_nonneg_left hsum' (by positivity)
        _ = 1 := by field_simp
  rw [hset]
  exact cardinality_mem_convexHull k x hx0 hx1 hsum

/-! ## Mixing finitely many size classes -/

/-- The finite size-class lemma used in the harmonic-charge proof.

Class `a` contains items of weight at most `1 / capacity a`.  A class is
chosen with probability `p a`; conditional on choosing it, at most
`capacity a` of its items are selected.  The two displayed inequalities
are exactly the conditions that make the requested marginals possible.
The conclusion packages the resulting experiment as a distribution on
unit-feasible subsets. -/
theorem sizeClasses_isAverageOfFeasibleSubsets
    {K : Type*} [Fintype K] [DecidableEq K]
    (capacity : K → ℕ) (hcapacity : ∀ a, 0 < capacity a)
    (classOf : I → K) (w x : I → ℝ) (p : K → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a ≤ 1)
    (hw0 : ∀ i, 0 ≤ w i)
    (hw : ∀ i, w i ≤ (1 : ℝ) / capacity (classOf i))
    (hx0 : ∀ i, 0 ≤ x i)
    (hxpoint : ∀ i, x i ≤ p (classOf i))
    (hxclass : ∀ a,
      (∑ i, if classOf i = a then x i else 0) ≤
        (capacity a : ℝ) * p a) :
    IsAverageOfFeasibleSubsets w 1 x := by
  classical
  let y : K → I → ℝ := fun a i ↦
    if classOf i = a then x i / p a else 0
  have hy0 : ∀ a i, 0 ≤ y a i := by
    intro a i
    by_cases hi : classOf i = a
    · by_cases hpa : p a = 0
      · simp [y, hi, hpa]
      · simpa [y, hi] using div_nonneg (hx0 i) (hp0 a)
    · simp [y, hi]
  have hy1 : ∀ a i, y a i ≤ 1 := by
    intro a i
    by_cases hi : classOf i = a
    · subst a
      by_cases hp : p (classOf i) = 0
      · simp [y, hp]
      · have hppos : 0 < p (classOf i) :=
          lt_of_le_of_ne (hp0 (classOf i)) (Ne.symm hp)
        simpa [y, hp] using (div_le_one hppos).2 (hxpoint i)
    · simp [y, hi]
  have hysum : ∀ a, ∑ i, y a i ≤ capacity a := by
    intro a
    by_cases hpa : p a = 0
    · have hxzero : ∀ i, classOf i = a → x i = 0 := by
        intro i hi
        have hle : x i ≤ 0 := by simpa [hi, hpa] using hxpoint i
        exact le_antisymm hle (hx0 i)
      apply le_trans (le_of_eq ?_) (Nat.cast_nonneg (capacity a))
      apply Finset.sum_eq_zero
      intro i _hi
      by_cases hi : classOf i = a
      · simp [y, hi, hpa]
      · simp [y, hi]
    · have hppos : 0 < p a := lt_of_le_of_ne (hp0 a) (Ne.symm hpa)
      have heq : (∑ i, y a i) =
          (∑ i, if classOf i = a then x i else 0) / p a := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases hi : classOf i = a <;> simp [y, hi]
      rw [heq]
      apply (div_le_iff₀ hppos).2
      simpa [mul_comm] using hxclass a
  choose mass hmass0 hmasstotal hmasssupport hmassmarg using
    fun a ↦ cardinality_isAverageOfFeasibleSubsets
      (capacity a) (hcapacity a) (y a) (hy0 a) (hy1 a) (hysum a)
  have hmass_card : ∀ a S, mass a S ≠ 0 → S.card ≤ capacity a := by
    intro a S hne
    have hload := hmasssupport a S hne
    have hcapR : (0 : ℝ) < capacity a := by
      exact_mod_cast hcapacity a
    have heq : (∑ i ∈ S, (1 : ℝ) / capacity a) =
        (S.card : ℝ) / capacity a := by simp [div_eq_mul_inv]
    rw [heq] at hload
    have hcast : (S.card : ℝ) ≤ capacity a := by
      simpa using (div_le_iff₀ hcapR).mp hload
    exact_mod_cast hcast
  have hmass_sameClass : ∀ a S, mass a S ≠ 0 →
      ∀ i ∈ S, classOf i = a := by
    intro a S hne i hiS
    by_contra hiClass
    have hyzero : y a i = 0 := by simp [y, hiClass]
    have htermNonneg : ∀ T : Finset I,
        0 ≤ if i ∈ T then mass a T else 0 := by
      intro T
      split
      · exact hmass0 a T
      · exact le_rfl
    have hsingle : mass a S ≤
        ∑ T : Finset I, if i ∈ T then mass a T else 0 := by
      have := Finset.single_le_sum
        (fun T _hT ↦ htermNonneg T) (Finset.mem_univ S)
      simpa [hiS] using this
    rw [hmassmarg a i, hyzero] at hsingle
    have hzero : mass a S = 0 :=
      le_antisymm hsingle (hmass0 a S)
    exact hne hzero
  have hmass_feasible : ∀ a S, mass a S ≠ 0 →
      ∑ i ∈ S, w i ≤ 1 := by
    intro a S hne
    have hsame := hmass_sameClass a S hne
    have hcard := hmass_card a S hne
    have hcapR : (0 : ℝ) < capacity a := by
      exact_mod_cast hcapacity a
    calc
      (∑ i ∈ S, w i) ≤
          ∑ _i ∈ S, (1 : ℝ) / capacity a := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [hsame i hi] using hw i
      _ = (S.card : ℝ) / capacity a := by simp [div_eq_mul_inv]
      _ ≤ (capacity a : ℝ) / capacity a := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hcapR.le
      _ = 1 := by field_simp
  let leftover : ℝ := 1 - ∑ a, p a
  let combined : Finset I → ℝ := fun S ↦
    (if S = ∅ then leftover else 0) +
      ∑ a, p a * mass a S
  refine ⟨combined, ?_, ?_, ?_, ?_⟩
  · intro S
    apply add_nonneg
    · split
      · exact sub_nonneg.mpr hpsum
      · exact le_rfl
    · exact Finset.sum_nonneg fun a _ha ↦
        mul_nonneg (hp0 a) (hmass0 a S)
  · calc
      (∑ S, combined S) =
          leftover + ∑ S : Finset I, ∑ a, p a * mass a S := by
        rw [Finset.sum_add_distrib]
        have hempty :
            (∑ S : Finset I, if S = ∅ then leftover else 0) = leftover := by
          simp
        rw [hempty]
      _ = leftover + ∑ a, p a * (∑ S : Finset I, mass a S) := by
        rw [Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
      _ = 1 := by
        simp_rw [hmasstotal]
        simp [leftover]
  · intro S hcombined
    by_cases hS : S = ∅
    · subst S
      simp
    · have hsumNe : (∑ a, p a * mass a S) ≠ 0 := by
        intro hz
        apply hcombined
        simp [combined, hS, hz]
      have hex : ∃ a, p a * mass a S ≠ 0 := by
        by_contra hall
        push_neg at hall
        exact hsumNe (Finset.sum_eq_zero fun a _ha ↦ hall a)
      obtain ⟨a, ha⟩ := hex
      exact hmass_feasible a S (right_ne_zero_of_mul ha)
  · intro i
    calc
      (∑ S, if i ∈ S then combined S else 0) =
          ∑ S : Finset I, ∑ a,
            p a * (if i ∈ S then mass a S else 0) := by
        apply Finset.sum_congr rfl
        intro S _hS
        by_cases hiS : i ∈ S
        · have hSne : S ≠ ∅ := by
            intro h
            subst S
            simpa using hiS
          simp [combined, hiS, hSne]
        · simp [hiS]
      _ = ∑ a, p a *
          (∑ S : Finset I, if i ∈ S then mass a S else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
      _ = ∑ a, p a * y a i := by simp_rw [hmassmarg]
      _ = x i := by
        let a0 := classOf i
        by_cases hp : p a0 = 0
        · have hxzero : x i = 0 := by
            have hle : x i ≤ 0 := by simpa [a0, hp] using hxpoint i
            exact le_antisymm hle (hx0 i)
          rw [hxzero]
          apply Finset.sum_eq_zero
          intro a _ha
          by_cases ha0 : a = a0
          · subst a
            simp [a0, hp]
          · have hclass : classOf i ≠ a := by simpa [a0] using Ne.symm ha0
            simp [y, hclass]
        · rw [Finset.sum_eq_single a0]
          · have hclass : classOf i = a0 := rfl
            simp [y, hclass]
            field_simp [hp]
          · intro a _ha hne
            have hclass : classOf i ≠ a := by simpa [a0] using Ne.symm hne
            simp [y, hclass]
          · intro hnot
            exact (hnot (Finset.mem_univ a0)).elim

/-- A directly usable charge-and-diffuseness form of the size-class lemma.

The first term in `hbudget` is the local harmonic-class charge load.  The
second is the loss from replacing each class maximum by the common pointwise
bound `M`.  This is the exact estimate used after weighted-moment palette
mixing: the charge load is bounded away from one and `M = O(1/n)` while the
number of retained classes is fixed. -/
theorem sizeClasses_isAverageOfFeasibleSubsets_of_charge
    {K : Type*} [Fintype K] [DecidableEq K]
    (capacity : K → ℕ) (hcapacity : ∀ a, 0 < capacity a)
    (classOf : I → K) (w x : I → ℝ) (M : ℝ)
    (hw0 : ∀ i, 0 ≤ w i)
    (hw : ∀ i, w i ≤ (1 : ℝ) / capacity (classOf i))
    (hx0 : ∀ i, 0 ≤ x i) (hM0 : 0 ≤ M)
    (hxM : ∀ i, x i ≤ M)
    (hbudget :
      (∑ i, x i / (capacity (classOf i) : ℝ)) +
          (Fintype.card K : ℝ) * M ≤ 1) :
    IsAverageOfFeasibleSubsets w 1 x := by
  classical
  let classMass : K → ℝ := fun a ↦
    ∑ i, if classOf i = a then x i else 0
  let p : K → ℝ := fun a ↦
    classMass a / (capacity a : ℝ) + M
  have hclassMass0 : ∀ a, 0 ≤ classMass a := by
    intro a
    apply Finset.sum_nonneg
    intro i _hi
    split
    · exact hx0 i
    · exact le_rfl
  have hp0 : ∀ a, 0 ≤ p a := by
    intro a
    exact add_nonneg (div_nonneg (hclassMass0 a)
      (Nat.cast_nonneg (capacity a))) hM0
  have hchargeEq :
      (∑ a, classMass a / (capacity a : ℝ)) =
        ∑ i, x i / (capacity (classOf i) : ℝ) := by
    calc
      (∑ a, classMass a / (capacity a : ℝ)) =
          ∑ a, ∑ i,
            if classOf i = a then x i / (capacity a : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases hi : classOf i = a <;> simp [classMass, hi]
      _ = ∑ i, ∑ a,
          if classOf i = a then x i / (capacity a : ℝ) else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ i, x i / (capacity (classOf i) : ℝ) := by simp
  have hpsum : ∑ a, p a ≤ 1 := by
    calc
      (∑ a, p a) =
          (∑ a, classMass a / (capacity a : ℝ)) +
            (Fintype.card K : ℝ) * M := by
        simp [p, Finset.sum_add_distrib]
      _ = (∑ i, x i / (capacity (classOf i) : ℝ)) +
            (Fintype.card K : ℝ) * M := by rw [hchargeEq]
      _ ≤ 1 := hbudget
  have hxpoint : ∀ i, x i ≤ p (classOf i) := by
    intro i
    exact (hxM i).trans (le_add_of_nonneg_left
      (div_nonneg (hclassMass0 (classOf i))
        (Nat.cast_nonneg (capacity (classOf i)))))
  have hxclass : ∀ a,
      (∑ i, if classOf i = a then x i else 0) ≤
        (capacity a : ℝ) * p a := by
    intro a
    have hcap : (0 : ℝ) < capacity a := by
      exact_mod_cast hcapacity a
    change classMass a ≤ (capacity a : ℝ) *
      (classMass a / (capacity a : ℝ) + M)
    rw [mul_add]
    have hcancel : (capacity a : ℝ) *
        (classMass a / (capacity a : ℝ)) = classMass a := by
      field_simp [hcap.ne']
    rw [hcancel]
    exact le_add_of_nonneg_right (mul_nonneg hcap.le hM0)
  exact sizeClasses_isAverageOfFeasibleSubsets capacity hcapacity classOf
    w x p hp0 hpsum hw0 hw hx0 hxpoint hxclass

end CardinalityLocalPolytope

end WeightedEdgeColoring
