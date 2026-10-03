import Mathlib.Tactic

/-!
# Averaging the shared-heavy-item estimate

The endpoint distributions need only have the same mass for each heavy
type. They need not have identical conditional distributions. The proof
uses a product of two finite measures and also handles zero type mass.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo.EndpointAveraging

theorem equalMass_pair_bound {I J : Type*} [Fintype I] [Fintype J]
    (mu : I → ℝ) (nu : J → ℝ) (f : I → ℝ) (g : J → ℝ) (x B : ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (hnu : ∀ j, 0 ≤ nu j)
    (hmu_sum : ∑ i, mu i = x) (hnu_sum : ∑ j, nu j = x)
    (hpair : ∀ i j, 0 < mu i → 0 < nu j → f i + g j ≤ B) :
    (∑ i, mu i * f i) + (∑ j, nu j * g j) ≤ x * B := by
  classical
  have hx : 0 ≤ x := by
    rw [← hmu_sum]
    exact Finset.sum_nonneg fun i _ ↦ hmu i
  by_cases hx0 : x = 0
  · have hmu0 : ∀ i, mu i = 0 := by
      intro i
      apply le_antisymm _ (hmu i)
      have hi := Finset.single_le_sum (s := Finset.univ) (f := mu)
        (fun j _ ↦ hmu j) (Finset.mem_univ i)
      simpa [hmu_sum, hx0] using hi
    have hnu0 : ∀ j, nu j = 0 := by
      intro j
      apply le_antisymm _ (hnu j)
      have hj := Finset.single_le_sum (s := Finset.univ) (f := nu)
        (fun i _ ↦ hnu i) (Finset.mem_univ j)
      simpa [hnu_sum, hx0] using hj
    simp [hmu0, hnu0, hx0]
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hproduct :
      (∑ i, ∑ j, mu i * nu j * (f i + g j)) ≤
        ∑ i, ∑ j, mu i * nu j * B := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hi : mu i = 0
    · simp [hi]
    by_cases hj : nu j = 0
    · simp [hj]
    exact mul_le_mul_of_nonneg_left
      (hpair i j (lt_of_le_of_ne (hmu i) (Ne.symm hi))
        (lt_of_le_of_ne (hnu j) (Ne.symm hj))) (mul_nonneg (hmu i) (hnu j))
  have hleft : (∑ i, ∑ j, mu i * nu j * (f i + g j)) =
      x * ((∑ i, mu i * f i) + ∑ j, nu j * g j) := by
    calc
      _ = ∑ i, (mu i * f i * (∑ j, nu j) +
          mu i * (∑ j, nu j * g j)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [hnu_sum, Finset.sum_add_distrib, ← Finset.sum_mul,
          ← Finset.sum_mul, hmu_sum]
        ring
  have hright : (∑ i, ∑ j, mu i * nu j * B) = x * (x * B) := by
    calc
      _ = (∑ i, mu i) * ((∑ j, nu j) * B) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hmu_sum, hnu_sum]
  rw [hleft, hright] at hproduct
  exact (mul_le_mul_iff_right₀ hxp).mp hproduct

/-- Pure cancellation at the end of the endpoint argument. Each heavy
type pays its two endpoint budgets; the no-heavy states pay the rest. -/
theorem endpoint_budget_cancellation {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (u v : E → V) (P : V → ℝ) (mass : E → ℝ)
    (hne : ∀ e, u e ≠ v e) :
    (∑ w, P w * (1 - ∑ e, if u e = w ∨ v e = w then mass e else 0)) +
      (∑ e, mass e * (P (u e) + P (v e))) = ∑ w, P w := by
  have hinc (e : E) :
      (∑ w, P w * (if u e = w ∨ v e = w then mass e else 0)) =
        mass e * (P (u e) + P (v e)) := by
    calc
      _ = ∑ w, ((if w = u e then P w * mass e else 0) +
          (if w = v e then P w * mass e else 0)) := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases hu : w = u e <;> by_cases hv : w = v e
        · exact False.elim (hne e (hu.symm.trans hv))
        · simp [hu, hv, hne e, eq_comm]
        · simp [hu, hv, hne e, eq_comm]
        · simp [hu, hv, eq_comm]
      _ = _ := by rw [Finset.sum_add_distrib]; simp; ring
  have hsum : (∑ w, P w * (∑ e, if u e = w ∨ v e = w then mass e else 0)) =
      ∑ e, mass e * (P (u e) + P (v e)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun e _ ↦ hinc e)
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, hsum]
  ring


/-- Split a finite measure into its unlabelled part and all labelled parts. -/
theorem tag_sum {I E : Type*} [Fintype I] [Fintype E] [DecidableEq E]
    (tag : I → Option E) (f : I → ℝ) :
    (∑ i, f i) = (∑ i, if tag i = none then f i else 0) +
      ∑ e, ∑ i, if tag i = some e then f i else 0 := by
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases ht : tag i with
  | none => simp
  | some e => simp

/-- The full finite-distribution averaging step. Every labelled state
contains one heavy type. Equal label masses at its two endpoints suffice;
no common coupling of all vertex distributions is required. -/
theorem endpoint_laws_bound {V E I : Type*} [Fintype V] [Fintype E] [Fintype I]
    [DecidableEq V] [DecidableEq E]
    (u v : E → V) (P : V → ℝ) (mass : V → I → ℝ)
    (tag : V → I → Option E) (score : V → I → ℝ) (x : E → ℝ)
    (hne : ∀ e, u e ≠ v e)
    (hP : ∀ w, 0 ≤ P w) (hmass : ∀ w i, 0 ≤ mass w i)
    (htotal : ∀ w, (∑ i, mass w i) ≤ 1)
    (hincident : ∀ w i e, tag w i = some e → u e = w ∨ v e = w)
    (hlabel : ∀ w e,
      (∑ i, if tag w i = some e then mass w i else 0) =
        if u e = w ∨ v e = w then x e else 0)
    (hnone : ∀ w i, tag w i = none → 0 < mass w i → score w i ≤ P w)
    (hpair : ∀ e i j, tag (u e) i = some e → tag (v e) j = some e →
      0 < mass (u e) i → 0 < mass (v e) j →
        score (u e) i + score (v e) j ≤ P (u e) + P (v e)) :
    (∑ w, ∑ i, mass w i * score w i) ≤ ∑ w, P w := by
  classical
  let F (w : V) (e : E) : ℝ :=
    ∑ i, if tag w i = some e then mass w i * score w i else 0
  let N (w : V) : ℝ := ∑ i, if tag w i = none then mass w i * score w i else 0
  have hN (w : V) : N w ≤ P w *
      (1 - ∑ e, if u e = w ∨ v e = w then x e else 0) := by
    have hn_score : N w ≤ P w * (∑ i, if tag w i = none then mass w i else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      by_cases ht : tag w i = none
      · simp only [ht, if_true]
        by_cases hz : mass w i = 0
        · simp [hz]
        · have hs := hnone w i ht (lt_of_le_of_ne (hmass w i) (Ne.symm hz))
          nlinarith [mul_le_mul_of_nonneg_left hs (hmass w i)]
      · simp [ht]
    have hn_mass : (∑ i, if tag w i = none then mass w i else 0) ≤
        1 - ∑ e, if u e = w ∨ v e = w then x e else 0 := by
      have hsplit := tag_sum (tag w) (mass w)
      simp_rw [hlabel] at hsplit
      linarith [htotal w]
    exact hn_score.trans (mul_le_mul_of_nonneg_left hn_mass (hP w))
  have hFzero (w : V) (e : E) (hu : w ≠ u e) (hv : w ≠ v e) : F w e = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have ht : tag w i ≠ some e := by
      intro ht
      rcases hincident w i e ht with hi | hi
      · exact hu hi.symm
      · exact hv hi.symm
    simp [ht]
  have hFsum (e : E) : (∑ w, F w e) = F (u e) e + F (v e) e := by
    calc
      _ = ∑ w, ((if w = u e then F w e else 0) +
            (if w = v e then F w e else 0)) := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases hu : w = u e <;> by_cases hv : w = v e
        · exact False.elim (hne e (hu.symm.trans hv))
        · simp [hu, hne e]
        · simp [hv, Ne.symm (hne e)]
        · simp [hu, hv, hFzero w e hu hv]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have hFpair (e : E) : F (u e) e + F (v e) e ≤ x e * (P (u e) + P (v e)) := by
    have h := equalMass_pair_bound
      (fun i ↦ if tag (u e) i = some e then mass (u e) i else 0)
      (fun j ↦ if tag (v e) j = some e then mass (v e) j else 0)
      (score (u e)) (score (v e)) (x e) (P (u e) + P (v e))
      (fun i ↦ by dsimp; split_ifs; exact hmass _ _; rfl)
      (fun j ↦ by dsimp; split_ifs; exact hmass _ _; rfl)
      (by simpa using hlabel (u e) e) (by simpa using hlabel (v e) e) ?_
    · simpa only [F, ite_mul, zero_mul] using h
    intro i j hi hj
    dsimp only at hi hj
    have hti : tag (u e) i = some e := by
      by_contra ht
      simp [ht] at hi
    have htj : tag (v e) j = some e := by
      by_contra ht
      simp [ht] at hj
    rw [if_pos hti] at hi
    rw [if_pos htj] at hj
    exact hpair e i j hti htj hi hj
  have hsplit : (∑ w, ∑ i, mass w i * score w i) =
      (∑ w, N w) + ∑ e, (F (u e) e + F (v e) e) := by
    calc
      _ = ∑ w, (N w + ∑ e, F w e) := by
        exact Finset.sum_congr rfl fun w _ ↦ tag_sum (tag w) (fun i ↦ mass w i * score w i)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        exact (Finset.sum_comm).trans (Finset.sum_congr rfl fun e _ ↦ hFsum e)
  rw [hsplit]
  calc
    _ ≤ (∑ w, P w * (1 - ∑ e, if u e = w ∨ v e = w then x e else 0)) +
        ∑ e, x e * (P (u e) + P (v e)) :=
      add_le_add (Finset.sum_le_sum fun w _ ↦ hN w) (Finset.sum_le_sum fun e _ ↦ hFpair e)
    _ = ∑ w, P w := endpoint_budget_cancellation u v P x hne

end WeightedEdgeColoring.Subtwo.EndpointAveraging
