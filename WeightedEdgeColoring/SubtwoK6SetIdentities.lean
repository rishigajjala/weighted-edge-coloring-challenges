import WeightedEdgeColoring.SubtwoK6MatchingDeficits
import Mathlib

/-! Set identities for the elementary six-vertex completion proof. -/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo.K6MatchingDeficits

def inside (S : Finset Vertex) (e : Edge) : ℕ := if ends e ⊆ S then 1 else 0
def touches (S : Finset Vertex) (e : Edge) : ℕ := (ends e ∩ S).card

theorem mass_eq_coeff (x : Edge → ℝ) (S : Finset Vertex) :
    triangleMass x S = ∑ e, (inside S e : ℝ) * x e := by
  simp [triangleMass, Finset.sum_filter, inside]

theorem degree_sum_eq_coeff (x : Edge → ℝ) (S : Finset Vertex) :
    (∑ v ∈ S, degree x v) = ∑ e, (touches S e : ℝ) * x e := by
  simp_rw [degree_eq_incidence_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [touches, Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.inter_comm]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem complement_coeff : ∀ (S : Finset Vertex) (e : Edge),
    (touches S e : ℤ) = 1 + (inside S e : ℤ) - (inside Sᶜ e : ℤ) := by
  decide

theorem complement_mass (x : Edge → ℝ) (S : Finset Vertex) :
    triangleMass x Sᶜ = total x + triangleMass x S - ∑ v ∈ S, degree x v := by
  rw [degree_sum_eq_coeff, mass_eq_coeff, mass_eq_coeff]
  simp only [total, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have h : (touches S e : ℝ) = 1 + (inside S e : ℝ) - (inside Sᶜ e : ℝ) := by
    exact_mod_cast complement_coeff S e
  rw [h]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem intersection_two_coeff : ∀ (A B : Finset Vertex),
    A.card = 3 → B.card = 3 → (A ∩ B).card = 2 →
    ∀ e : Edge, inside A e + inside B e ≤ touches (A ∩ B) e := by
  decide

theorem two_triangles_le_intersection_degrees (x : Edge → ℝ)
    (hx : ∀ e, 0 ≤ x e) (A B : Finset Vertex)
    (hA : A.card = 3) (hB : B.card = 3) (hI : (A ∩ B).card = 2) :
    triangleMass x A + triangleMass x B ≤ ∑ v ∈ A ∩ B, degree x v := by
  rw [mass_eq_coeff, mass_eq_coeff, degree_sum_eq_coeff, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  have h : (inside A e : ℝ) + (inside B e : ℝ) ≤ (touches (A ∩ B) e : ℝ) := by
    exact_mod_cast intersection_two_coeff A B hA hB hI e
  nlinarith [hx e]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem intersection_one_coeff : ∀ (A B : Finset Vertex),
    (A ∩ B).card = 1 →
    ∀ e : Edge, inside A e + inside B e ≤ inside (A ∪ B) e := by
  decide

theorem two_triangles_le_union (x : Edge → ℝ)
    (hx : ∀ e, 0 ≤ x e) (A B : Finset Vertex)
    (hI : (A ∩ B).card = 1) :
    triangleMass x A + triangleMass x B ≤ triangleMass x (A ∪ B) := by
  rw [mass_eq_coeff, mass_eq_coeff, mass_eq_coeff, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  have h : (inside A e : ℝ) + (inside B e : ℝ) ≤ (inside (A ∪ B) e : ℝ) := by
    exact_mod_cast intersection_one_coeff A B hI e
  nlinarith [hx e]

end WeightedEdgeColoring.Subtwo.K6MatchingDeficits
