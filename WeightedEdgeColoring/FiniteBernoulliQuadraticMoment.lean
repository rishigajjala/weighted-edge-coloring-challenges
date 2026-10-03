import WeightedEdgeColoring.FiniteBernoulliChernoff

/-!
# Polynomial moments for finite Bernoulli coordinates

This file gives a finite-sum moment expansion for a polynomial whose
monomials only record that a prescribed finite set of coordinates is active.
The quadratic collision statistic is the special case in which every
monomial has a two-point support.

The useful feature of the expansion is that repeated appearances of a
coordinate cost only one factor of its Bernoulli parameter.  Exposing the
last monomial in a sequence therefore reduces a high-moment estimate to a
deterministic bound on `extensionLoad`.
-/

namespace WeightedEdgeColoring.FiniteBernoulliQuadraticMoment

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff

variable {I E : Type*}
  [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]

/-- Sum of monomial weights whose supports are all active. -/
noncomputable def monomialStatistic
    (support : E → Finset I) (weight : E → ℝ) (S : Finset I) : ℝ :=
  ∑ e : E, if support e ⊆ S then weight e else 0

/-- Coordinates occurring in a sequence of monomials. -/
noncomputable def sequenceSupport (support : E → Finset I) {k : ℕ}
    (f : Fin k → E) : Finset I :=
  (Finset.univ : Finset (Fin k)).biUnion fun r ↦ support (f r)

private theorem sequenceSupport_snoc (support : E → Finset I) {k : ℕ}
    (f : Fin k → E) (e : E) :
    sequenceSupport support (Fin.snoc f e) =
      sequenceSupport support f ∪ support e := by
  classical
  ext i
  simp only [sequenceSupport, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_union]
  constructor
  · rintro ⟨r, hir⟩
    cases r using Fin.lastCases with
    | last => exact Or.inr (by simpa using hir)
    | cast j => exact Or.inl ⟨j, by simpa using hir⟩
  · rintro (⟨r, hir⟩ | hie)
    · exact ⟨r.castSucc, by simpa using hir⟩
    · exact ⟨Fin.last k, by simpa using hie⟩

/-- The term in the exact `k`-th moment expansion indexed by `f`. -/
noncomputable def sequenceTerm (q : I → ℝ)
    (support : E → Finset I) (weight : E → ℝ) {k : ℕ}
    (f : Fin k → E) : ℝ :=
  (∏ r, weight (f r)) * ∏ i ∈ sequenceSupport support f, q i

/-- The deterministic load for adding one more monomial after the coordinates
in `U` have already appeared. -/
noncomputable def extensionLoad (q : I → ℝ)
    (support : E → Finset I) (weight : E → ℝ) (U : Finset I) : ℝ :=
  ∑ e : E, weight e * ∏ i ∈ support e \ U, q i

/-- Product mass of Bernoulli outcomes which contain all coordinates in `A`.
No bounds on the parameters are needed for this algebraic identity. -/
theorem sum_bernoulliMass_of_subset (q : I → ℝ) (A : Finset I) :
    (∑ S : Finset I, if A ⊆ S then bernoulliMass q S else 0) =
      ∏ i ∈ A, q i := by
  classical
  let R : Finset I := (Finset.univ : Finset I) \ A
  let massOnR : Finset I → ℝ := fun T ↦
    (∏ i ∈ T, q i) * ∏ i ∈ R \ T, (1 - q i)
  have hfilter :
      (Finset.univ : Finset (Finset I)).filter (fun S ↦ A ⊆ S) =
        R.powerset.image (fun T ↦ A ∪ T) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_powerset]
    constructor
    · intro hAS
      refine ⟨S \ A, ?_, ?_⟩
      · intro i hi
        simpa [R] using (Finset.mem_sdiff.mp hi).2
      · exact Finset.union_sdiff_of_subset hAS
    · rintro ⟨T, hTR, rfl⟩
      exact Finset.subset_union_left
  have hinj : Set.InjOn (fun T : Finset I ↦ A ∪ T) R.powerset := by
    intro T hT U hU hEq
    change A ∪ T = A ∪ U at hEq
    apply Finset.ext
    intro i
    have hiT : i ∈ T → i ∉ A := fun hi ↦
      (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hT hi)).2
    have hiU : i ∈ U → i ∉ A := fun hi ↦
      (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hU hi)).2
    constructor
    · intro hi
      have hmem : i ∈ A ∪ T := Finset.mem_union_right A hi
      rw [hEq] at hmem
      have : i ∈ A ∪ U := hmem
      rcases Finset.mem_union.mp this with hiA | hiU'
      · exact (hiT hi hiA).elim
      · exact hiU'
    · intro hi
      have hmem : i ∈ A ∪ U := Finset.mem_union_right A hi
      rw [← hEq] at hmem
      have : i ∈ A ∪ T := hmem
      rcases Finset.mem_union.mp this with hiA | hiT'
      · exact (hiU hi hiA).elim
      · exact hiT'
  have hfactor : ∀ T ∈ R.powerset,
      bernoulliMass q (A ∪ T) = (∏ i ∈ A, q i) * massOnR T := by
    intro T hT
    have hdisj : Disjoint A T := by
      refine Finset.disjoint_left.mpr ?_
      intro i hiA hiT
      exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hT hiT)).2 hiA
    have hcomp : (Finset.univ : Finset I) \ (A ∪ T) = R \ T := by
      ext i
      simp [R, and_assoc, and_left_comm, and_comm]
    simp only [bernoulliMass, massOnR, hcomp]
    rw [Finset.prod_union hdisj]
    ring
  rw [← Finset.sum_filter, hfilter, Finset.sum_image hinj]
  calc
    (∑ T ∈ R.powerset, bernoulliMass q (A ∪ T)) =
        ∑ T ∈ R.powerset, (∏ i ∈ A, q i) * massOnR T := by
      exact Finset.sum_congr rfl hfactor
    _ = (∏ i ∈ A, q i) * ∑ T ∈ R.powerset, massOnR T := by
      rw [Finset.mul_sum]
    _ = ∏ i ∈ A, q i := by
      have hmass : ∑ T ∈ R.powerset, massOnR T = 1 := by
        change (∑ T ∈ R.powerset,
          (∏ i ∈ T, q i) * ∏ i ∈ R \ T, (1 - q i)) = 1
        calc
          _ = ∏ i ∈ R, (q i + (1 - q i)) := by
            simpa using
              (Finset.prod_add q (fun i ↦ 1 - q i) R).symm
          _ = 1 := by simp
      rw [hmass, mul_one]

private theorem prod_monomial_indicator_eq
    (support : E → Finset I) (weight : E → ℝ) (S : Finset I)
    {k : ℕ} (f : Fin k → E) :
    (∏ r, if support (f r) ⊆ S then weight (f r) else 0) =
      if sequenceSupport support f ⊆ S then ∏ r, weight (f r) else 0 := by
  classical
  by_cases hsub : sequenceSupport support f ⊆ S
  · rw [if_pos hsub]
    apply Finset.prod_congr rfl
    intro r _
    rw [if_pos]
    intro i hi
    apply hsub
    exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ r, hi⟩
  · rw [if_neg hsub]
    obtain ⟨i, hi, hiS⟩ := Finset.not_subset.mp hsub
    rcases Finset.mem_biUnion.mp hi with ⟨r, _hr, hir⟩
    apply Finset.prod_eq_zero (Finset.mem_univ r)
    rw [if_neg]
    intro hsr
    exact hiS (hsr hir)

/-- Exact finite-sum formula for every ordinary moment of a Bernoulli
monomial polynomial. -/
theorem expected_monomialStatistic_pow
    (q : I → ℝ) (support : E → Finset I) (weight : E → ℝ) (k : ℕ) :
    (∑ S : Finset I, bernoulliMass q S *
      (monomialStatistic support weight S) ^ k) =
      ∑ f : Fin k → E, sequenceTerm q support weight f := by
  classical
  unfold monomialStatistic sequenceTerm
  simp_rw [Fintype.sum_pow, Finset.mul_sum]
  simp_rw [prod_monomial_indicator_eq support weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  calc
    (∑ S : Finset I, bernoulliMass q S *
        (if sequenceSupport support f ⊆ S then ∏ r, weight (f r) else 0)) =
      (∏ r, weight (f r)) *
        ∑ S : Finset I,
          (if sequenceSupport support f ⊆ S then bernoulliMass q S else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S _
        split <;> simp_all [mul_comm]
    _ = (∏ r, weight (f r)) *
        ∏ i ∈ sequenceSupport support f, q i := by
      rw [sum_bernoulliMass_of_subset]

/-- Power Markov inequality, kept division-free for later local-lemma use. -/
theorem pow_tail_mul_le_moment
    (q : I → ℝ) (support : E → Finset I) (weight : E → ℝ)
    (k : ℕ) (T : ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hw0 : ∀ e, 0 ≤ weight e) (hT : 0 ≤ T) :
    T ^ k * WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
      (upperTail (monomialStatistic support weight) T) ≤
      ∑ f : Fin k → E, sequenceTerm q support weight f := by
  rw [← expected_monomialStatistic_pow]
  unfold WeightedEdgeColoring.FiniteLocalLemma.eventMass
  rw [Finset.mul_sum]
  calc
    (∑ S ∈ upperTail (monomialStatistic support weight) T,
        T ^ k * bernoulliMass q S) ≤
      ∑ S ∈ upperTail (monomialStatistic support weight) T,
        bernoulliMass q S * (monomialStatistic support weight S) ^ k := by
      apply Finset.sum_le_sum
      intro S hS
      have htail := (Finset.mem_filter.mp hS).2
      have hstat0 : 0 ≤ monomialStatistic support weight S := by
        apply Finset.sum_nonneg
        intro e _
        by_cases he : support e ⊆ S
        · simp [he, hw0 e]
        · simp [he]
      have hpow := pow_le_pow_left₀ hT htail k
      calc
        T ^ k * bernoulliMass q S = bernoulliMass q S * T ^ k := by ring
        _ ≤ bernoulliMass q S * (monomialStatistic support weight S) ^ k :=
          mul_le_mul_of_nonneg_left hpow (bernoulliMass_nonneg q hq0 hq1 S)
    _ ≤ ∑ S : Finset I,
        bernoulliMass q S * (monomialStatistic support weight S) ^ k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro S _ _
      exact mul_nonneg (bernoulliMass_nonneg q hq0 hq1 S)
        (pow_nonneg (by
          apply Finset.sum_nonneg
          intro e _
          by_cases he : support e ⊆ S
          · simp [he, hw0 e]
          · simp [he]) _)

/-- A convenient interface for the deterministic last-monomial argument.
Applications prove the displayed extension-load bound by separating whether
zero, one, or two endpoints have appeared before. -/
theorem moment_le_of_sequence_extension_bound
    (q : I → ℝ) (support : E → Finset I) (weight : E → ℝ)
    (k : ℕ) (C : ℝ)
    (hw0 : ∀ e, 0 ≤ weight e)
    (hq0 : ∀ i, 0 ≤ q i)
    (hext : ∀ (f : Fin k → E),
      extensionLoad q support weight (sequenceSupport support f) ≤ C) :
    (∑ f : Fin (k + 1) → E, sequenceTerm q support weight f) ≤
      C * ∑ f : Fin k → E, sequenceTerm q support weight f := by
  classical
  -- Reindex by the first `k` monomials and the last monomial.  The support
  -- product for the last monomial contributes precisely the parameters of
  -- `support e \ sequenceSupport support f`.
  conv_lhs => rw [← (Fin.succFunEquiv E k).symm.sum_comp]
  simp only [Equiv.coe_fn_mk, Fintype.sum_prod_type]
  calc
    (∑ f : Fin k → E, ∑ e : E,
        sequenceTerm q support weight ((Fin.succFunEquiv E k).symm (f, e))) =
      ∑ f : Fin k → E,
        sequenceTerm q support weight f *
          extensionLoad q support weight (sequenceSupport support f) := by
        apply Finset.sum_congr rfl
        intro f _
        rw [extensionLoad, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        have hsnoc :
            (Fin.succFunEquiv E k).symm (f, e) = Fin.snoc f e := by
          change Fin.append f (fun _ : Fin 1 ↦ e) = Fin.snoc f e
          simpa using
            (Fin.append_right_eq_snoc f (fun _ : Fin 1 ↦ e))
        rw [hsnoc]
        unfold sequenceTerm
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last,
          sequenceSupport_snoc]
        rw [← Finset.union_sdiff_self_eq_union]
        rw [Finset.prod_union Finset.disjoint_sdiff]
        ring
    _ ≤ ∑ f : Fin k → E, sequenceTerm q support weight f * C := by
      apply Finset.sum_le_sum
      intro f _
      apply mul_le_mul_of_nonneg_left (hext f)
      unfold sequenceTerm
      exact mul_nonneg
        (Finset.prod_nonneg fun r _ ↦ hw0 (f r))
        (Finset.prod_nonneg fun i _ ↦ hq0 i)
    _ = C * ∑ f : Fin k → E, sequenceTerm q support weight f := by
      rw [← Finset.sum_mul]
      ring

/-- Ordered pairs of distinct coordinates.  Using a subtype avoids diagonal
terms and matches the ordered convention in `pairCollisionStatistic`. -/
abbrev OrderedPair (I : Type*) := {ab : I × I // ab.1 ≠ ab.2}

namespace OrderedPair

variable (e : OrderedPair I)

def left : I := e.1.1
def right : I := e.1.2

@[simp] theorem left_ne_right : e.left ≠ e.right := e.2

/-- The two coordinates used by an ordered quadratic monomial. -/
def support : Finset I := {e.left, e.right}

@[simp] theorem support_card : e.support.card = 2 := by
  simp [support, e.left_ne_right]

end OrderedPair

/-- A nonnegative ordered quadratic polynomial in Bernoulli indicators. -/
noncomputable def quadraticStatistic
    (weight : OrderedPair I → ℝ) (S : Finset I) : ℝ :=
  monomialStatistic OrderedPair.support weight S

/-- First moment of the ordered quadratic polynomial. -/
noncomputable def quadraticMean
    (q : I → ℝ) (weight : OrderedPair I → ℝ) : ℝ :=
  ∑ e : OrderedPair I, weight e * q e.left * q e.right

/-- Weighted expected edges incident with one fixed coordinate, counting the
two possible orientations separately. -/
noncomputable def incidentLoad
    (q : I → ℝ) (weight : OrderedPair I → ℝ) (i : I) : ℝ :=
  (∑ e : OrderedPair I, if e.left = i then weight e * q e.right else 0) +
  ∑ e : OrderedPair I, if e.right = i then weight e * q e.left else 0

/-- Total weight of ordered pairs with both endpoints in `U`. -/
noncomputable def internalWeight
    (weight : OrderedPair I → ℝ) (U : Finset I) : ℝ :=
  ∑ e : OrderedPair I,
    if e.left ∈ U ∧ e.right ∈ U then weight e else 0

/-- A uniform edge-weight bound controls the total weight internal to `U`
by the number of ordered pairs in `U`. -/
theorem internalWeight_le_card_sq_mul
    (weight : OrderedPair I → ℝ) (U : Finset I) (M : ℝ)
    (hwM : ∀ e, weight e ≤ M) (hM0 : 0 ≤ M) :
    internalWeight weight U ≤ (U.card : ℝ) ^ 2 * M := by
  classical
  let A : Finset (OrderedPair I) :=
    Finset.univ.filter fun e ↦ e.left ∈ U ∧ e.right ∈ U
  have hcard : A.card ≤ (U ×ˢ U).card := by
    apply Finset.card_le_card_of_injOn (fun e : OrderedPair I ↦ e.1)
    · intro e he
      have hmem := (Finset.mem_filter.mp he).2
      exact Finset.mem_product.mpr hmem
    · intro e _ f _ hef
      exact Subtype.ext hef
  calc
    internalWeight weight U = ∑ e ∈ A, weight e := by
      simp [internalWeight, A, Finset.sum_filter]
    _ ≤ ∑ _e ∈ A, M := by
      exact Finset.sum_le_sum fun e _ ↦ hwM e
    _ = (A.card : ℝ) * M := by simp
    _ ≤ ((U ×ˢ U).card : ℝ) * M := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM0
    _ = (U.card : ℝ) ^ 2 * M := by simp [pow_two]

/-- Zero/one/two-old-endpoint decomposition.  This is the deterministic
heart of the quadratic moment estimate.  The `internalWeight` hypothesis is
usually discharged by `weight e ≤ M`, giving `U.card^2*M`. -/
theorem extensionLoad_le_mean_incident_internal
    (q : I → ℝ) (weight : OrderedPair I → ℝ)
    (U : Finset I) (mu Lambda B : ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hw0 : ∀ e, 0 ≤ weight e)
    (hmean : quadraticMean q weight ≤ mu)
    (hincident : ∀ i, incidentLoad q weight i ≤ Lambda)
    (hLambda0 : 0 ≤ Lambda)
    (hinternal : internalWeight weight U ≤ B) :
    extensionLoad q OrderedPair.support weight U ≤
      mu + (U.card : ℝ) * Lambda + B := by
  classical
  have hpoint (e : OrderedPair I) :
      weight e * ∏ i ∈ e.support \ U, q i ≤
        weight e * q e.left * q e.right +
          (if e.left ∈ U then weight e * q e.right else 0) +
          (if e.right ∈ U then weight e * q e.left else 0) +
          (if e.left ∈ U ∧ e.right ∈ U then weight e else 0) := by
    by_cases ha : e.left ∈ U
    · by_cases hb : e.right ∈ U
      · have hprod : (∏ i ∈ e.support \ U, q i) = 1 := by
          have hs : e.support \ U = ∅ := by
            ext i
            simp only [Finset.mem_sdiff, Finset.notMem_empty, iff_false]
            rintro ⟨hi, hiU⟩
            have hor : i = e.left ∨ i = e.right := by
              simpa [OrderedPair.support] using hi
            rcases hor with rfl | rfl
            · exact hiU ha
            · exact hiU hb
          rw [hs]
          simp
        rw [hprod]
        simp [ha, hb]
        have hxy := mul_nonneg (hq0 e.left) (hq0 e.right)
        have hwxy := mul_nonneg (hw0 e) hxy
        have hwl := mul_nonneg (hw0 e) (hq0 e.left)
        have hwr := mul_nonneg (hw0 e) (hq0 e.right)
        linarith
      · have hprod : (∏ i ∈ e.support \ U, q i) = q e.right := by
          have hs : e.support \ U = {e.right} := by
            ext i
            simp only [Finset.mem_sdiff, Finset.mem_singleton]
            constructor
            · rintro ⟨hi, hiU⟩
              have hor : i = e.left ∨ i = e.right := by
                simpa [OrderedPair.support] using hi
              rcases hor with hleft | hright
              · subst i
                exact (hiU ha).elim
              · exact hright
            · intro hi
              subst i
              exact ⟨by simp [OrderedPair.support], hb⟩
          rw [hs]
          simp
        rw [hprod]
        simp [ha, hb]
        exact mul_nonneg (mul_nonneg (hw0 e) (hq0 e.left)) (hq0 e.right)
    · by_cases hb : e.right ∈ U
      · have hprod : (∏ i ∈ e.support \ U, q i) = q e.left := by
          have hs : e.support \ U = {e.left} := by
            ext i
            simp only [Finset.mem_sdiff, Finset.mem_singleton]
            constructor
            · rintro ⟨hi, hiU⟩
              have hor : i = e.left ∨ i = e.right := by
                simpa [OrderedPair.support] using hi
              rcases hor with hleft | hright
              · exact hleft
              · subst i
                exact (hiU hb).elim
            · intro hi
              subst i
              exact ⟨by simp [OrderedPair.support], ha⟩
          rw [hs]
          simp
        rw [hprod]
        simp [ha, hb]
        exact mul_nonneg (mul_nonneg (hw0 e) (hq0 e.left)) (hq0 e.right)
      · have hprod : (∏ i ∈ e.support \ U, q i) =
            q e.left * q e.right := by
          have hs : e.support \ U = e.support := by
            ext i
            constructor
            · intro hi
              exact (Finset.mem_sdiff.mp hi).1
            · intro hi
              apply Finset.mem_sdiff.mpr
              refine ⟨hi, ?_⟩
              intro hiU
              have hor : i = e.left ∨ i = e.right := by
                simpa [OrderedPair.support] using hi
              rcases hor with rfl | rfl
              · exact ha hiU
              · exact hb hiU
          rw [hs]
          simp [OrderedPair.support, e.left_ne_right]
        rw [hprod]
        simpa [ha, hb, mul_assoc]
  have hleft :
      (∑ e : OrderedPair I,
          if e.left ∈ U then weight e * q e.right else 0) =
        ∑ i ∈ U, ∑ e : OrderedPair I,
          if e.left = i then weight e * q e.right else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : e.left ∈ U
    · simp [he]
    · simp [he]
  have hright :
      (∑ e : OrderedPair I,
          if e.right ∈ U then weight e * q e.left else 0) =
        ∑ i ∈ U, ∑ e : OrderedPair I,
          if e.right = i then weight e * q e.left else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : e.right ∈ U
    · simp [he]
    · simp [he]
  have hinc :
      (∑ e : OrderedPair I,
          if e.left ∈ U then weight e * q e.right else 0) +
        (∑ e : OrderedPair I,
          if e.right ∈ U then weight e * q e.left else 0) ≤
        (U.card : ℝ) * Lambda := by
    rw [hleft, hright, ← Finset.sum_add_distrib]
    calc
      (∑ i ∈ U,
          ((∑ e : OrderedPair I,
              if e.left = i then weight e * q e.right else 0) +
            ∑ e : OrderedPair I,
              if e.right = i then weight e * q e.left else 0)) ≤
        ∑ _i ∈ U, Lambda := by
          exact Finset.sum_le_sum fun i _ ↦ hincident i
      _ = (U.card : ℝ) * Lambda := by simp
  unfold extensionLoad
  calc
    (∑ e : OrderedPair I,
        weight e * ∏ i ∈ OrderedPair.support e \ U, q i) ≤
      ∑ e : OrderedPair I,
        (weight e * q e.left * q e.right +
          (if e.left ∈ U then weight e * q e.right else 0) +
          (if e.right ∈ U then weight e * q e.left else 0) +
          (if e.left ∈ U ∧ e.right ∈ U then weight e else 0)) := by
        exact Finset.sum_le_sum fun e _ ↦ hpoint e
    _ = quadraticMean q weight +
        ((∑ e : OrderedPair I,
            if e.left ∈ U then weight e * q e.right else 0) +
          ∑ e : OrderedPair I,
            if e.right ∈ U then weight e * q e.left else 0) +
        internalWeight weight U := by
      simp only [quadraticMean, internalWeight, Finset.sum_add_distrib]
      ring
    _ ≤ mu + (U.card : ℝ) * Lambda + B := by linarith

/-- Ready-to-use quadratic extension envelope from bounds on the mean,
incident load, and one edge weight. -/
theorem extensionLoad_le_mean_incident_max
    (q : I → ℝ) (weight : OrderedPair I → ℝ)
    (U : Finset I) (mu Lambda M : ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hw0 : ∀ e, 0 ≤ weight e)
    (hmean : quadraticMean q weight ≤ mu)
    (hincident : ∀ i, incidentLoad q weight i ≤ Lambda)
    (hLambda0 : 0 ≤ Lambda) (hM0 : 0 ≤ M)
    (hwM : ∀ e, weight e ≤ M) :
    extensionLoad q OrderedPair.support weight U ≤
      mu + (U.card : ℝ) * Lambda + (U.card : ℝ) ^ 2 * M := by
  exact extensionLoad_le_mean_incident_internal q weight U mu Lambda
    ((U.card : ℝ) ^ 2 * M) hq0 hw0 hmean hincident hLambda0
    (internalWeight_le_card_sq_mul weight U M hwM hM0)

/-- Exact high-moment expansion for the ordered quadratic statistic. -/
theorem expected_quadraticStatistic_pow
    (q : I → ℝ) (weight : OrderedPair I → ℝ) (k : ℕ) :
    (∑ S : Finset I, bernoulliMass q S *
      (quadraticStatistic weight S) ^ k) =
      ∑ f : Fin k → OrderedPair I,
        sequenceTerm q OrderedPair.support weight f := by
  exact expected_monomialStatistic_pow q OrderedPair.support weight k

/-- A sequence of `k` quadratic monomials uses at most `2k` coordinates. -/
theorem sequenceSupport_orderedPair_card_le {k : ℕ}
    (f : Fin k → OrderedPair I) :
    (sequenceSupport OrderedPair.support f).card ≤ 2 * k := by
  unfold sequenceSupport
  calc
    ((Finset.univ : Finset (Fin k)).biUnion
        fun r ↦ OrderedPair.support (f r)).card ≤
      ∑ r : Fin k, (OrderedPair.support (f r)).card :=
        Finset.card_biUnion_le
    _ = ∑ _r : Fin k, 2 := by
      apply Finset.sum_congr rfl
      intro r _
      exact OrderedPair.support_card (f r)
    _ = 2 * k := by simp [Nat.mul_comm]

/-- The exact deterministic hypothesis needed at the `k`-to-`k+1` moment
step.  In applications the right side follows from the zero/one/two old
endpoint split. -/
theorem quadraticMoment_succ_le_of_extension_envelope
    (q : I → ℝ) (weight : OrderedPair I → ℝ)
    (k : ℕ) (mu Lambda M : ℝ)
    (hw0 : ∀ e, 0 ≤ weight e) (hq0 : ∀ i, 0 ≤ q i)
    (henvelope : ∀ U : Finset I,
      extensionLoad q OrderedPair.support weight U ≤
        mu + (U.card : ℝ) * Lambda + (U.card : ℝ) ^ 2 * M)
    (hLambda0 : 0 ≤ Lambda) (hM0 : 0 ≤ M) :
    (∑ f : Fin (k + 1) → OrderedPair I,
        sequenceTerm q OrderedPair.support weight f) ≤
      (mu + 2 * k * Lambda + 4 * k ^ 2 * M) *
        ∑ f : Fin k → OrderedPair I,
          sequenceTerm q OrderedPair.support weight f := by
  apply moment_le_of_sequence_extension_bound q OrderedPair.support weight k
    (mu + 2 * k * Lambda + 4 * k ^ 2 * M) hw0 hq0
  intro f
  have hcard := sequenceSupport_orderedPair_card_le f
  have hcardReal :
      ((sequenceSupport OrderedPair.support f).card : ℝ) ≤ 2 * k := by
    exact_mod_cast hcard
  calc
    extensionLoad q OrderedPair.support weight
        (sequenceSupport OrderedPair.support f) ≤
      mu + ((sequenceSupport OrderedPair.support f).card : ℝ) * Lambda +
        ((sequenceSupport OrderedPair.support f).card : ℝ) ^ 2 * M :=
          henvelope _
    _ ≤ mu + (2 * k : ℕ) * Lambda + ((2 * k : ℕ) : ℝ) ^ 2 * M := by
      gcongr
    _ = mu + 2 * k * Lambda + 4 * k ^ 2 * M := by
      push_cast
      ring

/-- Iterating a uniform extension bound gives an ordinary-moment bound. -/
theorem quadraticMoment_le_pow_of_uniform_extension
    (q : I → ℝ) (weight : OrderedPair I → ℝ)
    (k : ℕ) (C : ℝ)
    (hw0 : ∀ e, 0 ≤ weight e) (hq0 : ∀ i, 0 ≤ q i)
    (hC0 : 0 ≤ C)
    (hext : ∀ (r : ℕ), r < k → ∀ (f : Fin r → OrderedPair I),
      extensionLoad q OrderedPair.support weight
        (sequenceSupport OrderedPair.support f) ≤ C) :
    (∑ f : Fin k → OrderedPair I,
      sequenceTerm q OrderedPair.support weight f) ≤ C ^ k := by
  induction k with
  | zero => simp [sequenceTerm, sequenceSupport]
  | succ k ih =>
      have hstep := moment_le_of_sequence_extension_bound
        q OrderedPair.support weight k C hw0 hq0 (hext k (Nat.lt_succ_self k))
      calc
        (∑ f : Fin (k + 1) → OrderedPair I,
            sequenceTerm q OrderedPair.support weight f) ≤
          C * ∑ f : Fin k → OrderedPair I,
            sequenceTerm q OrderedPair.support weight f := hstep
        _ ≤ C * C ^ k := by
          apply mul_le_mul_of_nonneg_left
          · apply ih
            intro r hr
            exact hext r (hr.trans (Nat.lt_succ_self k))
          · exact hC0
        _ = C ^ (k + 1) := by simp [pow_succ, mul_comm]

/-- Explicit division-free tail bound obtained from the ordered quadratic
moment argument. -/
theorem quadratic_tail_mul_le_pow_of_uniform_extension
    (q : I → ℝ) (weight : OrderedPair I → ℝ)
    (k : ℕ) (T C : ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hw0 : ∀ e, 0 ≤ weight e) (hT : 0 ≤ T) (hC0 : 0 ≤ C)
    (hext : ∀ (r : ℕ), r < k → ∀ (f : Fin r → OrderedPair I),
      extensionLoad q OrderedPair.support weight
        (sequenceSupport OrderedPair.support f) ≤ C) :
    T ^ k * WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
      (upperTail (quadraticStatistic weight) T) ≤ C ^ k := by
  exact (pow_tail_mul_le_moment q OrderedPair.support weight k T
    hq0 hq1 hw0 hT).trans
      (quadraticMoment_le_pow_of_uniform_extension q weight k C
        hw0 hq0 hC0 hext)

/-- Closed-form ordered-quadratic moment tail.  Here `Lambda` is the full
incident load (outgoing plus incoming).  For symmetric ordered weights it is
twice the usual one-sided row load. -/
theorem quadratic_tail_mul_le_explicit
    (q : I → ℝ) (weight : OrderedPair I → ℝ)
    (k : ℕ) (T mu Lambda M : ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hw0 : ∀ e, 0 ≤ weight e) (hwM : ∀ e, weight e ≤ M)
    (hmean : quadraticMean q weight ≤ mu)
    (hincident : ∀ i, incidentLoad q weight i ≤ Lambda)
    (hT : 0 ≤ T) (hmu0 : 0 ≤ mu)
    (hLambda0 : 0 ≤ Lambda) (hM0 : 0 ≤ M) :
    T ^ k * WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
      (upperTail (quadraticStatistic weight) T) ≤
      (mu + 2 * k * Lambda + 4 * k ^ 2 * M) ^ k := by
  let C : ℝ := mu + 2 * k * Lambda + 4 * k ^ 2 * M
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  apply quadratic_tail_mul_le_pow_of_uniform_extension
    q weight k T C hq0 hq1 hw0 hT hC0
  intro r hr f
  have hcard := sequenceSupport_orderedPair_card_le f
  have hcardReal :
      ((sequenceSupport OrderedPair.support f).card : ℝ) ≤ 2 * r := by
    exact_mod_cast hcard
  have hrReal : (r : ℝ) ≤ k := by
    exact_mod_cast (Nat.le_of_lt hr)
  have hcardSq :
      ((sequenceSupport OrderedPair.support f).card : ℝ) ^ 2 ≤
        4 * (r : ℝ) ^ 2 := by
    calc
      ((sequenceSupport OrderedPair.support f).card : ℝ) ^ 2 ≤
          (2 * (r : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hcardReal 2
      _ = 4 * (r : ℝ) ^ 2 := by ring
  calc
    extensionLoad q OrderedPair.support weight
        (sequenceSupport OrderedPair.support f) ≤
      mu + ((sequenceSupport OrderedPair.support f).card : ℝ) * Lambda +
        ((sequenceSupport OrderedPair.support f).card : ℝ) ^ 2 * M := by
          exact extensionLoad_le_mean_incident_max q weight _ mu Lambda M
            hq0 hw0 hmean hincident hLambda0 hM0 hwM
    _ ≤ mu + 2 * (r : ℝ) * Lambda + 4 * (r : ℝ) ^ 2 * M := by
      have hlinear := mul_le_mul_of_nonneg_right hcardReal hLambda0
      have hquad := mul_le_mul_of_nonneg_right hcardSq hM0
      linarith
    _ ≤ mu + 2 * (k : ℝ) * Lambda + 4 * (k : ℝ) ^ 2 * M := by
      gcongr
    _ = C := by
      dsimp [C]

end WeightedEdgeColoring.FiniteBernoulliQuadraticMoment
