import Mathlib

/-! Compact attainment and an elementary coordinate-increase argument
for a finite packing system. These support the six-vertex matching proof. -/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo.FinitePacking

variable {E R : Type*} [Fintype E] [Fintype R] [DecidableEq E]

def Feasible (lower : E → ℝ) (A : R → E → ℝ) (b : R → ℝ) (x : E → ℝ) : Prop :=
  (∀ e, lower e ≤ x e) ∧ (∀ e, x e ≤ 1) ∧ ∀ r, (∑ e, A r e * x e) ≤ b r

theorem feasible_isClosed (lower : E → ℝ) (A : R → E → ℝ) (b : R → ℝ) :
    IsClosed {x | Feasible lower A b x} := by
  have hlo : IsClosed {x : E → ℝ | ∀ e, lower e ≤ x e} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun e ↦ isClosed_le continuous_const (continuous_apply e)
  have hhi : IsClosed {x : E → ℝ | ∀ e, x e ≤ 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun e ↦ isClosed_le (continuous_apply e) continuous_const
  have hrow : IsClosed {x : E → ℝ | ∀ r, (∑ e, A r e * x e) ≤ b r} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro r
    apply isClosed_le _ continuous_const
    exact continuous_finset_sum _ fun e _ ↦ continuous_const.mul (continuous_apply e)
  exact hlo.inter (hhi.inter hrow)

theorem feasible_isCompact (lower : E → ℝ) (A : R → E → ℝ) (b : R → ℝ) :
    IsCompact {x | Feasible lower A b x} := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := lower) (b := fun _ ↦ (1 : ℝ)))
    (feasible_isClosed lower A b)
  intro x hx
  exact ⟨hx.1, hx.2.1⟩

theorem exists_max_total (lower : E → ℝ) (A : R → E → ℝ) (b : R → ℝ)
    (hfeas : Feasible lower A b lower) :
    ∃ y, Feasible lower A b y ∧
      ∀ z, Feasible lower A b z → (∑ e, z e) ≤ ∑ e, y e := by
  have hcont : Continuous (fun x : E → ℝ ↦ ∑ e, x e) :=
    continuous_finset_sum _ fun e _ ↦ continuous_apply e
  obtain ⟨y, hy, hmax⟩ := (feasible_isCompact lower A b).exists_isMaxOn
    ⟨lower, hfeas⟩ hcont.continuousOn
  exact ⟨y, hy, fun z hz ↦ hmax hz⟩

theorem row_update (A : R → E → ℝ) (y : E → ℝ) (i : E) (delta : ℝ) (r : R) :
    (∑ e, A r e * (Function.update y i (y i + delta)) e) =
      (∑ e, A r e * y e) + A r i * delta := by
  classical
  have hid (e : E) : A r e * (Function.update y i (y i + delta)) e =
      A r e * y e + if e = i then A r e * delta else 0 := by
    by_cases he : e = i
    · subst e; simp [mul_add]
    · simp [Function.update_of_ne he, he]
  simp_rw [hid, Finset.sum_add_distrib]
  simp

/-- A coordinate below its cap can be increased if every row using it
has positive slack. Finitely many rows give one common positive increase. -/
theorem exists_coordinate_increase (lower : E → ℝ) (A : R → E → ℝ) (b : R → ℝ)
    (hA : ∀ r e, 0 ≤ A r e) (y : E → ℝ) (hy : Feasible lower A b y)
    (i : E) (hi : y i < 1)
    (hslack : ∀ r, 0 < A r i → (∑ e, A r e * y e) < b r) :
    ∃ delta : ℝ, 0 < delta ∧ Feasible lower A b (Function.update y i (y i + delta)) := by
  classical
  let gap (r : R) : ℝ :=
    if 0 < A r i then (b r - ∑ e, A r e * y e) / A r i else 1
  have hgap (r : R) : 0 < gap r := by
    dsimp [gap]
    split_ifs with hri
    · exact div_pos (sub_pos.mpr (hslack r hri)) hri
    · norm_num
  let S : Finset ℝ := insert (1 - y i) (Finset.univ.image gap)
  have hS : S.Nonempty := ⟨1 - y i, Finset.mem_insert_self _ _⟩
  let delta := S.min' hS
  have hdelta : 0 < delta := by
    have hm : delta ∈ S := Finset.min'_mem S hS
    rcases Finset.mem_insert.mp hm with hm | hm
    · rw [hm]; linarith
    · obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hm
      rw [← hr]
      exact hgap r
  have hd_one : delta ≤ 1 - y i := Finset.min'_le S _ (Finset.mem_insert_self _ _)
  have hd_gap (r : R) : delta ≤ gap r :=
    Finset.min'_le S _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩))
  refine ⟨delta, hdelta, ?_, ?_, ?_⟩
  · intro e
    by_cases he : e = i
    · subst e; simp only [Function.update_self]; linarith [hy.1 i]
    · simpa [Function.update_of_ne he] using hy.1 e
  · intro e
    by_cases he : e = i
    · subst e; simp only [Function.update_self]; linarith
    · simpa [Function.update_of_ne he] using hy.2.1 e
  · intro r
    rw [row_update]
    rcases eq_or_lt_of_le (hA r i) with hz | hpos
    · rw [← hz, zero_mul, add_zero]
      exact hy.2.2 r
    · have hg := hd_gap r
      dsimp [gap] at hg
      rw [if_pos hpos] at hg
      have hh := (le_div_iff₀ hpos).mp hg
      nlinarith

/-- At a maximum total extension, every coordinate below one belongs
to a tight row with positive coefficient. -/
theorem max_total_has_tight_row (lower : E → ℝ) (A : R → E → ℝ) (b : R → ℝ)
    (hA : ∀ r e, 0 ≤ A r e) (y : E → ℝ) (hy : Feasible lower A b y)
    (hmax : ∀ z, Feasible lower A b z → (∑ e, z e) ≤ ∑ e, y e)
    (i : E) (hi : y i < 1) :
    ∃ r, 0 < A r i ∧ (∑ e, A r e * y e) = b r := by
  by_contra hnot
  have hslack (r : R) (hr : 0 < A r i) : (∑ e, A r e * y e) < b r := by
    apply lt_of_le_of_ne (hy.2.2 r)
    intro heq
    exact hnot ⟨r, hr, heq⟩
  obtain ⟨delta, hd, hz⟩ := exists_coordinate_increase lower A b hA y hy i hi hslack
  have hm := hmax _ hz
  have hsum : (∑ e, (Function.update y i (y i + delta)) e) = (∑ e, y e) + delta := by
    simpa using row_update (R := Unit) (fun _ _ ↦ (1 : ℝ)) y i delta ()
  rw [hsum] at hm
  linarith

end WeightedEdgeColoring.Subtwo.FinitePacking
