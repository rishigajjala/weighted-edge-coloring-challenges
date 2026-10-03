import WeightedEdgeColoring.SubtwoK6CycleWitness
import WeightedEdgeColoring.SubtwoK6SupportBridge
import WeightedEdgeColoring.SubtwoK6RegularMax
import WeightedEdgeColoring.SubtwoFiniteSymmetricSlack

namespace WeightedEdgeColoring.Subtwo.K6SupportReal
open K6MatchingDeficits K6SupportFinite K6SupportBridge K6CycleDirection K6CycleWitness

local instance (S : Finset Vertex) : DecidablePred (Crosses S) :=
  fun e => inferInstanceAs (Decidable ((ends e ∩ S).card = 1))

theorem support_dichotomy_real (y : Edge → ℝ)
    (h2 : ∀ v : Vertex, ∃ e f : Edge,
      e ≠ f ∧ v ∈ ends e ∧ v ∈ ends f ∧ 0 < y e ∧ 0 < y f) :
    (∃ j : Fin 105, ∀ e : Edge, direction j e ≠ 0 → 0 < y e) ∨
    (∃ t : Fin 20, ∀ e f : Edge, e ≠ f →
      Crosses triangleSets[t] e → Crosses triangleSets[t] f →
      0 < y e → 0 < y f → False) := by
  let b : Edge → Bool := fun e => decide (0 < y e)
  have hb : ∀ v : Vertex, ∃ e f : Edge,
      e ≠ f ∧ v ∈ ends e ∧ v ∈ ends f ∧ b e = true ∧ b f = true := by
    intro v
    obtain ⟨e, f, hef, hve, hvf, he, hf⟩ := h2 v
    exact ⟨e, f, hef, hve, hvf, by simpa [b] using he, by simpa [b] using hf⟩
  have hmin := minDegreeTwo_of_support b hb
  rcases support_dichotomy (supportMask b) hmin with hc | ht
  · left
    obtain ⟨j, hj⟩ := hasEvenCycle_witness b hc
    refine ⟨j, ?_⟩
    intro e he
    simpa [b] using hj e he
  · right
    obtain ⟨t, ht⟩ := hasNarrowTriangle_witness b ht
    refine ⟨t, ?_⟩
    intro e f hef hce hcf he hf
    exact ht e f hef hce hcf (by simpa [b] using he) (by simpa [b] using hf)

def crossMass (y : Edge → ℝ) (S : Finset Vertex) : ℝ :=
  ∑ e ∈ Finset.univ.filter (Crosses S), y e

theorem touches_split : ∀ S : Finset Vertex, ∀ e : Edge,
    touches S e = 2 * inside S e + if Crosses S e then 1 else 0 := by
  unfold Crosses
  decide +kernel

theorem degree_triangle_cross (y : Edge → ℝ) (S : Finset Vertex) :
    (∑ v ∈ S, degree y v) = 2 * triangleMass y S + crossMass y S := by
  rw [degree_sum_eq_coeff, mass_eq_coeff]
  simp only [crossMass, Finset.sum_filter]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hc : (touches S e : ℝ) =
      2 * (inside S e : ℝ) + (if Crosses S e then (1 : ℝ) else 0) := by
    exact_mod_cast touches_split S e
  rw [hc]
  by_cases he : Crosses S e <;> simp [he] <;> ring

theorem narrow_crossMass_le_one (y : Edge → ℝ) (hy0 : ∀ e, 0 ≤ y e)
    (hd : ∀ v, degree y v = 1) (S : Finset Vertex)
    (hn : ∀ e f : Edge, e ≠ f → Crosses S e → Crosses S f →
      0 < y e → 0 < y f → False) : crossMass y S ≤ 1 := by
  let E : Finset Edge := Finset.univ.filter (Crosses S)
  by_cases hp : ∃ e ∈ E, 0 < y e
  · obtain ⟨e, heE, hepos⟩ := hp
    have heCross : Crosses S e := (Finset.mem_filter.mp heE).2
    have hzero : ∀ f ∈ E, f ≠ e → y f = 0 := by
      intro f hfE hfe
      have hfCross : Crosses S f := (Finset.mem_filter.mp hfE).2
      have hfnot : ¬ 0 < y f := by
        intro hfpos
        exact hn e f (Ne.symm hfe) heCross hfCross hepos hfpos
      exact le_antisymm (le_of_not_gt hfnot) (hy0 f)
    have hsum : crossMass y S = y e := by
      exact Finset.sum_eq_single_of_mem e heE hzero
    rw [hsum]
    obtain ⟨v, hv⟩ := ends_nonempty e
    exact (edge_le_degree y hy0 e v hv).trans_eq (hd v)
  · have hzero : ∀ f ∈ E, y f = 0 := by
      intro f hfE
      have hfnot : ¬ 0 < y f := by
        intro hfpos
        exact hp ⟨f, hfE, hfpos⟩
      exact le_antisymm (le_of_not_gt hfnot) (hy0 f)
    have hsum : crossMass y S = 0 := Finset.sum_eq_zero hzero
    rw [hsum]
    norm_num

theorem narrow_triangle_contradiction (y : Edge → ℝ)
    (hy : RegularFeasible y)
    (hstrict : ∀ S : Finset Vertex, S.card = 3 → triangleMass y S < 1)
    (t : Fin 20)
    (hn : ∀ e f : Edge, e ≠ f → Crosses triangleSets[t] e →
      Crosses triangleSets[t] f → 0 < y e → 0 < y f → False) : False := by
  let S := triangleSets[t]
  have hS : S.card = 3 := triangleSets_card t
  have hcross : crossMass y S ≤ 1 := narrow_crossMass_le_one y hy.1 hy.2.1 S hn
  have hsum : (∑ v ∈ S, degree y v) = 3 := by
    simp [hy.2.1, hS]
  have hid := degree_triangle_cross y S
  have ht := hstrict S hS
  linarith

theorem degree_add_scaled (y d : Edge → ℝ) (a : ℝ) (v : Vertex) :
    degree (fun e => y e + a * d e) v = degree y v + a * degree d v := by
  fin_cases v <;> simp [degree] <;> ring

theorem triangleMass_add_scaled (y d : Edge → ℝ) (a : ℝ)
    (S : Finset Vertex) :
    triangleMass (fun e => y e + a * d e) S =
      triangleMass y S + a * triangleMass d S := by
  simp [triangleMass, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem symmetric_cycle_perturb (y : Edge → ℝ) (hy : RegularFeasible y)
    (hstrict : ∀ S : Finset Vertex, S.card = 3 → triangleMass y S < 1)
    (j : Fin 105)
    (hsupport : ∀ e : Edge, direction j e ≠ 0 → 0 < y e) :
    ∃ eps : ℝ, 0 < eps ∧
      RegularFeasible (fun e => y e + eps * direction j e) ∧
      RegularFeasible (fun e => y e - eps * direction j e) := by
  let value : Edge ⊕ Fin 20 → ℝ
    | .inl e => -y e
    | .inr t => triangleMass y triangleSets[t]
  let slope : Edge ⊕ Fin 20 → ℝ
    | .inl e => -direction j e
    | .inr t => triangleMass (direction j) triangleSets[t]
  let cap : Edge ⊕ Fin 20 → ℝ
    | .inl _ => 0
    | .inr _ => 1
  have hbase : ∀ r, value r ≤ cap r := by
    intro r
    cases r with
    | inl e => exact neg_nonpos.mpr (hy.1 e)
    | inr t => exact hy.2.2 _ (triangleSets_card t)
  have hstr : ∀ r, slope r ≠ 0 → value r < cap r := by
    intro r hr
    cases r with
    | inl e =>
        have hd : direction j e ≠ 0 := by simpa [slope] using hr
        dsimp [value, cap]
        linarith [hsupport e hd]
    | inr t => exact hstrict _ (triangleSets_card t)
  obtain ⟨eps, heps, hstep⟩ :=
    FinitePacking.exists_small_symmetric_step value slope cap hbase hstr
  refine ⟨eps, heps, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro e
      have h := (hstep (.inl e)).1
      dsimp [value, slope, cap] at h
      linarith
    · intro v
      rw [degree_add_scaled, hy.2.1 v, direction_degree_zero]
      ring
    · intro S hS
      obtain ⟨t, rfl⟩ := triangleSets_complete S hS
      have h := (hstep (.inr t)).1
      simpa [value, slope, cap, triangleMass_add_scaled] using h
  · refine ⟨?_, ?_, ?_⟩
    · intro e
      have h := (hstep (.inl e)).2
      dsimp [value, slope, cap] at h
      linarith
    · intro v
      have hh := degree_add_scaled y (direction j) (-eps) v
      have hfun : (fun e => y e - eps * direction j e) =
          (fun e => y e + -eps * direction j e) := by
        funext e
        ring
      rw [hfun, hh, hy.2.1 v, direction_degree_zero]
      ring
    · intro S hS
      obtain ⟨t, rfl⟩ := triangleSets_complete S hS
      have h := (hstep (.inr t)).2
      have hfun : (fun e => y e - eps * direction j e) =
          (fun e => y e + -eps * direction j e) := by
        funext e
        ring
      rw [hfun, triangleMass_add_scaled]
      simpa [value, slope, cap] using h

theorem strict_no_symmetric_implies_low_support (y : Edge → ℝ)
    (hy : RegularFeasible y)
    (hstrict : ∀ S : Finset Vertex, S.card = 3 → triangleMass y S < 1)
    (hno : ∀ d : Edge → ℝ, (∃ e, d e ≠ 0) →
      RegularFeasible (fun e => y e + d e) →
      RegularFeasible (fun e => y e - d e) → False) :
    ¬ (∀ v : Vertex, ∃ e f : Edge,
      e ≠ f ∧ v ∈ ends e ∧ v ∈ ends f ∧ 0 < y e ∧ 0 < y f) := by
  intro h2
  rcases support_dichotomy_real y h2 with ⟨j, hj⟩ | ⟨t, ht⟩
  · obtain ⟨eps, heps, hp, hm⟩ := symmetric_cycle_perturb y hy hstrict j hj
    apply hno (fun e => eps * direction j e)
    · obtain ⟨e, he⟩ := direction_nonzero j
      exact ⟨e, mul_ne_zero (ne_of_gt heps) he⟩
    · exact hp
    · exact hm
  · exact narrow_triangle_contradiction y hy hstrict t ht

theorem low_support_has_unit_edge (y : Edge → ℝ) (hy : RegularFeasible y)
    (h : ¬ (∀ v : Vertex, ∃ e f : Edge,
      e ≠ f ∧ v ∈ ends e ∧ v ∈ ends f ∧ 0 < y e ∧ 0 < y f)) :
    ∃ e : Edge, y e = 1 := by
  classical
  push_neg at h
  obtain ⟨v, hv⟩ := h
  have hsum : 0 < ∑ e : Edge, if v ∈ ends e then y e else 0 := by
    rw [← degree_eq_incidence_sum, hy.2.1 v]
    norm_num
  have hnonneg : ∀ e ∈ (Finset.univ : Finset Edge),
      0 ≤ (if v ∈ ends e then y e else 0) := by
    intro e _
    split_ifs <;> [exact hy.1 e; norm_num]
  obtain ⟨e, _, hepos⟩ := (Finset.sum_pos_iff_of_nonneg hnonneg).mp hsum
  have hve : v ∈ ends e := by
    by_contra hve
    simp [hve] at hepos
  have hey : 0 < y e := by simpa [hve] using hepos
  have hother : ∀ f : Edge, f ≠ e →
      (if v ∈ ends f then y f else 0) = 0 := by
    intro f hfe
    by_cases hvf : v ∈ ends f
    · have hfnot : ¬ 0 < y f := by
        intro hfpos
        have hle := hv e f (Ne.symm hfe) hve hvf hey
        linarith
      have hfzero : y f = 0 := le_antisymm (le_of_not_gt hfnot) (hy.1 f)
      simp [hvf, hfzero]
    · simp [hvf]
  have hdeg : degree y v = y e := by
    rw [degree_eq_incidence_sum]
    rw [Finset.sum_eq_single e]
    · simp [hve]
    · intro f _ hfe
      exact hother f hfe
    · simp
  exact ⟨e, by rw [← hdeg, hy.2.1 v]⟩

end WeightedEdgeColoring.Subtwo.K6SupportReal
