import WeightedEdgeColoring.SubtwoK6MatchingDeficits
import WeightedEdgeColoring.SubtwoAnalyticBoundaryArithmetic

/-!
# The augmented six-vertex costs for the dense five-block palette

Vertex zero is the reserved-color vertex. The other five vertices are the
block vertices, so edges `5` through `14` are exactly the ten internal
bundles in lexicographic order.
-/

namespace WeightedEdgeColoring.Subtwo.K6BoundaryRows

open K6MatchingDeficits

noncomputable def internalTotal (t : Fin 10 → ℝ) : ℝ := ∑ e, t e
noncomputable def reservedTotal (q : Fin 5 → ℝ) : ℝ := ∑ v, q v

noncomputable def internalDegree (t : Fin 10 → ℝ) : Fin 5 → ℝ :=
  ![t 0 + t 1 + t 2 + t 3,
    t 0 + t 4 + t 5 + t 6,
    t 1 + t 4 + t 7 + t 8,
    t 2 + t 5 + t 7 + t 9,
    t 3 + t 6 + t 8 + t 9]

noncomputable def augmented (t : Fin 10 → ℝ) (q : Fin 5 → ℝ) (k : ℝ) :
    Edge → ℝ :=
  ![k*q 0,k*q 1,k*q 2,k*q 3,k*q 4,
    t 0,t 1,t 2,t 3,t 4,t 5,t 6,t 7,t 8,t 9]

theorem sum_internalDegree_eq_two_total (t : Fin 10 → ℝ) :
    (∑ v, internalDegree t v) = 2 * internalTotal t := by
  simp [internalDegree, internalTotal, Fin.sum_univ_succ]
  ring

theorem augmented_degree_zero (t : Fin 10 → ℝ) (q : Fin 5 → ℝ) (k : ℝ) :
    degree (augmented t q k) 0 = k * reservedTotal q := by
  simp [degree, augmented, reservedTotal, Fin.sum_univ_succ]
  ring

theorem augmented_degree_original (t : Fin 10 → ℝ) (q : Fin 5 → ℝ)
    (k : ℝ) (v : Fin 5) :
    degree (augmented t q k) ⟨v.val + 1, by omega⟩ =
      internalDegree t v + k * q v := by
  fin_cases v <;> simp [degree, augmented, internalDegree] <;> ring

theorem augmented_total (t : Fin 10 → ℝ) (q : Fin 5 → ℝ) (k : ℝ) :
    total (augmented t q k) = internalTotal t + k * reservedTotal q := by
  simp [total, augmented, internalTotal, reservedTotal, Fin.sum_univ_succ]
  ring

theorem augmented_omit_zero (t : Fin 10 → ℝ) (q : Fin 5 → ℝ) (k : ℝ) :
    omitFive (augmented t q k) 0 = internalTotal t := by
  rw [omitFive, augmented_total, augmented_degree_zero]
  ring

theorem augmented_omit_original (t : Fin 10 → ℝ) (q : Fin 5 → ℝ)
    (k : ℝ) (v : Fin 5) :
    omitFive (augmented t q k) ⟨v.val + 1, by omega⟩ =
      internalTotal t - internalDegree t v +
        k * (reservedTotal q - q v) := by
  rw [omitFive, augmented_total, augmented_degree_original]
  ring

noncomputable def degreeBound : ℝ := 16911 / 10000
noncomputable def target : ℝ := 1999 / 1000
noncomputable def envelope (T : ℝ) : ℝ := 5 * degreeBound - 2 * T
noncomputable def paletteMass (T : ℝ) : ℝ := max 2 (T / 2)
noncomputable def reserveScale (T : ℝ) : ℝ :=
  1 + (paletteMass T - degreeBound) / envelope T

theorem reservedTotal_le_envelope (t : Fin 10 → ℝ) (q : Fin 5 → ℝ)
    (hcap : ∀ v, internalDegree t v + q v ≤ degreeBound) :
    reservedTotal q ≤ envelope (internalTotal t) := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5)))
    (fun v _ ↦ hcap v)
  simp only [Finset.sum_add_distrib] at hsum
  rw [sum_internalDegree_eq_two_total] at hsum
  norm_num [reservedTotal, envelope] at *
  linarith

theorem reserveScale_gt_one (T : ℝ) (hQ0 : 0 < envelope T) :
    1 < reserveScale T := by
  have hL : 2 ≤ paletteMass T := le_max_left _ _
  have hM : degreeBound < 2 := by norm_num [degreeBound]
  dsimp [reserveScale]
  have hfrac : 0 < (paletteMass T - degreeBound) / envelope T :=
    div_pos (by linarith) hQ0
  linarith

theorem reserveScale_mul_envelope (T : ℝ) (hQ0 : 0 < envelope T) :
    reserveScale T * envelope T =
      envelope T + paletteMass T - degreeBound := by
  unfold reserveScale
  field_simp
  ring

theorem envelope_le_degreeBound_sub_one (T : ℝ)
    (hT : 2 * target ≤ T) :
    envelope T ≤ degreeBound - 1 := by
  norm_num [envelope, degreeBound, target] at *
  linarith

theorem scale_reserved_le_palette_sub_one
    (t : Fin 10 → ℝ) (q : Fin 5 → ℝ)
    (hcap : ∀ v, internalDegree t v + q v ≤ degreeBound)
    (hT : 2 * target ≤ internalTotal t)
    (hQ0 : 0 < envelope (internalTotal t)) :
    reserveScale (internalTotal t) * reservedTotal q ≤
      paletteMass (internalTotal t) - 1 := by
  have hQ := reservedTotal_le_envelope t q hcap
  have hk : 0 ≤ reserveScale (internalTotal t) := by
    linarith [reserveScale_gt_one _ hQ0]
  have hm := mul_le_mul_of_nonneg_left hQ hk
  rw [reserveScale_mul_envelope _ hQ0] at hm
  have he := envelope_le_degreeBound_sub_one _ hT
  linarith

theorem other_four_cost_le
    (t : Fin 10 → ℝ) (q : Fin 5 → ℝ)
    (hcap : ∀ v, internalDegree t v + q v ≤ degreeBound)
    (v : Fin 5) :
    2 * internalTotal t - internalDegree t v +
      reservedTotal q - q v ≤ 4 * degreeBound := by
  have hsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset (Fin 5)).erase v)
    (fun u _ ↦ hcap u)
  have hcard : ((Finset.univ : Finset (Fin 5)).erase v).card = 4 := by
    simp
  have hdSum :
      (∑ u ∈ (Finset.univ : Finset (Fin 5)).erase v,
        internalDegree t u) =
        2 * internalTotal t - internalDegree t v := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin 5))
      (internalDegree t) (Finset.mem_univ v)
    rw [sum_internalDegree_eq_two_total] at hsplit
    linarith
  have hqSum :
      (∑ u ∈ (Finset.univ : Finset (Fin 5)).erase v, q u) =
        reservedTotal q - q v := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin 5))
      q (Finset.mem_univ v)
    dsimp [reservedTotal]
    linarith
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul] at hsum
  rw [hdSum, hqSum, hcard] at hsum
  norm_num at hsum
  linarith

theorem augmented_omit_original_le_twice_palette
    (t : Fin 10 → ℝ) (q : Fin 5 → ℝ)
    (hcap : ∀ v, internalDegree t v + q v ≤ degreeBound)
    (hq : ∀ v, 0 ≤ q v)
    (hT : 2 * target ≤ internalTotal t)
    (hQ0 : 0 < envelope (internalTotal t))
    (v : Fin 5) :
    omitFive (augmented t q (reserveScale (internalTotal t)))
      ⟨v.val + 1, by omega⟩ ≤
        2 * paletteMass (internalTotal t) := by
  rw [augmented_omit_original]
  have hother := other_four_cost_le t q hcap v
  have hQ := reservedTotal_le_envelope t q hcap
  have hk := reserveScale_gt_one _ hQ0
  have hqRest : 0 ≤ reservedTotal q - q v := by
    have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin 5))
      q (Finset.mem_univ v)
    dsimp [reservedTotal]
    have hnonneg :
        0 ≤ ∑ u ∈ (Finset.univ : Finset (Fin 5)).erase v, q u :=
      Finset.sum_nonneg (fun u _ ↦ hq u)
    linarith
  have hscale :
      (reserveScale (internalTotal t) - 1) *
          (reservedTotal q - q v) ≤
        paletteMass (internalTotal t) - degreeBound := by
    have hQrest : reservedTotal q - q v ≤ envelope (internalTotal t) := by
      have hqv := hq v
      linarith
    have hm := mul_le_mul_of_nonneg_left hQrest (by linarith :
      0 ≤ reserveScale (internalTotal t) - 1)
    have hid := reserveScale_mul_envelope _ hQ0
    nlinarith
  have hlarge : 3 * degreeBound ≤
      internalTotal t + paletteMass (internalTotal t) := by
    have hL : 2 ≤ paletteMass (internalTotal t) := le_max_left _ _
    norm_num [degreeBound, target] at hT ⊢
    linarith
  nlinarith

theorem augmented_degree_le_palette
    (t : Fin 10 → ℝ) (q : Fin 5 → ℝ)
    (hcap : ∀ v, internalDegree t v + q v ≤ degreeBound)
    (hq : ∀ v, 0 ≤ q v)
    (hT : 2 * target ≤ internalTotal t)
    (hQ0 : 0 < envelope (internalTotal t)) :
    ∀ v : Vertex,
      degree (augmented t q (reserveScale (internalTotal t))) v ≤
        paletteMass (internalTotal t) := by
  have hrow (i : Fin 5) :
      degree (augmented t q (reserveScale (internalTotal t)))
        ⟨i.val + 1, by omega⟩ ≤ paletteMass (internalTotal t) := by
    rw [augmented_degree_original]
    have hqBound := reservedTotal_le_envelope t q hcap
    have hk := reserveScale_gt_one _ hQ0
    have hqv : q i ≤ reservedTotal q := by
      have hsum := Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 5)))
        (fun u _ ↦ hq u) (Finset.mem_univ i)
      simpa using hsum
    have hscale : (reserveScale (internalTotal t) - 1) * q i ≤
        paletteMass (internalTotal t) - degreeBound := by
      have hqvQ : q i ≤ envelope (internalTotal t) := hqv.trans hqBound
      have hm := mul_le_mul_of_nonneg_left hqvQ (by linarith :
        0 ≤ reserveScale (internalTotal t) - 1)
      have hid := reserveScale_mul_envelope _ hQ0
      nlinarith
    linarith [hcap i]
  intro v
  fin_cases v
  · have hbound := scale_reserved_le_palette_sub_one t q hcap hT hQ0
    have hzero :
        degree (augmented t q (reserveScale (internalTotal t))) 0 ≤
          paletteMass (internalTotal t) := by
      rw [augmented_degree_zero]
      linarith
    simpa using hzero
  · simpa using hrow 0
  · simpa using hrow 1
  · simpa using hrow 2
  · simpa using hrow 3
  · simpa using hrow 4

theorem augmented_omit_le_twice_palette
    (t : Fin 10 → ℝ) (q : Fin 5 → ℝ)
    (hcap : ∀ v, internalDegree t v + q v ≤ degreeBound)
    (hq : ∀ v, 0 ≤ q v)
    (hT : 2 * target ≤ internalTotal t)
    (hQ0 : 0 < envelope (internalTotal t)) :
    ∀ v : Vertex,
      omitFive (augmented t q (reserveScale (internalTotal t))) v ≤
        2 * paletteMass (internalTotal t) := by
  have hzero :
      omitFive (augmented t q (reserveScale (internalTotal t))) 0 ≤
        2 * paletteMass (internalTotal t) := by
    rw [augmented_omit_zero]
    have hL : internalTotal t / 2 ≤ paletteMass (internalTotal t) :=
      le_max_right _ _
    linarith
  intro v
  fin_cases v
  · simpa using hzero
  · simpa using augmented_omit_original_le_twice_palette t q hcap hq hT hQ0 0
  · simpa using augmented_omit_original_le_twice_palette t q hcap hq hT hQ0 1
  · simpa using augmented_omit_original_le_twice_palette t q hcap hq hT hQ0 2
  · simpa using augmented_omit_original_le_twice_palette t q hcap hq hT hQ0 3
  · simpa using augmented_omit_original_le_twice_palette t q hcap hq hT hQ0 4

def frontTriangle : Fin 10 → Finset Vertex :=
  ![{0,1,2},{0,1,3},{0,1,4},{0,1,5},{0,2,3},
    {0,2,4},{0,2,5},{0,3,4},{0,3,5},{0,4,5}]

def frontPair : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),
    (1,3),(1,4),(2,3),(2,4),(3,4)]

theorem frontTriangle_complete : ∀ S : Finset Vertex,
    S.card = 3 → 0 ∈ S → ∃ i : Fin 10, frontTriangle i = S := by
  decide

theorem frontTriangle_mass (t : Fin 10 → ℝ) (q : Fin 5 → ℝ)
    (k : ℝ) (i : Fin 10) :
    triangleMass (augmented t q k) (frontTriangle i) =
      k * (q (frontPair i).1 + q (frontPair i).2) + t i := by
  fin_cases i <;>
    simp [triangleMass, frontTriangle, frontPair, augmented, ends,
      Finset.sum_filter, Fin.sum_univ_succ, Finset.subset_iff] <;> ring

theorem frontPair_reserved_le (q : Fin 5 → ℝ)
    (hq : ∀ v, 0 ≤ q v) (i : Fin 10) :
    q (frontPair i).1 + q (frontPair i).2 ≤ reservedTotal q := by
  fin_cases i <;>
    simp [frontPair, reservedTotal, Fin.sum_univ_succ] <;>
    linarith [hq 0, hq 1, hq 2, hq 3, hq 4]

theorem augmented_front_triangle_le_palette
    (t : Fin 10 → ℝ) (q : Fin 5 → ℝ)
    (hcap : ∀ v, internalDegree t v + q v ≤ degreeBound)
    (hq : ∀ v, 0 ≤ q v) (ht1 : ∀ e, t e ≤ 1)
    (hT : 2 * target ≤ internalTotal t)
    (hQ0 : 0 < envelope (internalTotal t))
    (S : Finset Vertex) (hS : S.card = 3) (h0 : 0 ∈ S) :
    triangleMass (augmented t q (reserveScale (internalTotal t))) S ≤
      paletteMass (internalTotal t) := by
  obtain ⟨i, rfl⟩ := frontTriangle_complete S hS h0
  rw [frontTriangle_mass]
  have hp := frontPair_reserved_le q hq i
  have hk : 0 ≤ reserveScale (internalTotal t) := by
    linarith [reserveScale_gt_one _ hQ0]
  have hm := mul_le_mul_of_nonneg_left hp hk
  have hb := scale_reserved_le_palette_sub_one t q hcap hT hQ0
  linarith [ht1 i]

def backTriangle : Fin 10 → Finset Vertex :=
  ![{1,2,3},{1,2,4},{1,2,5},{1,3,4},{1,3,5},
    {1,4,5},{2,3,4},{2,3,5},{2,4,5},{3,4,5}]

def backTriple : Fin 10 → Fin 10 × Fin 10 × Fin 10 :=
  ![(0,1,4),(0,2,5),(0,3,6),(1,2,7),(1,3,8),
    (2,3,9),(4,5,7),(4,6,8),(5,6,9),(7,8,9)]

theorem backTriangle_complete : ∀ S : Finset Vertex,
    S.card = 3 → 0 ∉ S → ∃ i : Fin 10, backTriangle i = S := by
  decide

theorem backTriangle_mass_independent_scale
    (t : Fin 10 → ℝ) (q : Fin 5 → ℝ) (k : ℝ) (i : Fin 10) :
    triangleMass (augmented t q k) (backTriangle i) =
      triangleMass (augmented t q 0) (backTriangle i) := by
  fin_cases i <;>
    simp [triangleMass, backTriangle, augmented, ends,
      Finset.sum_filter, Fin.sum_univ_succ, Finset.subset_iff]

theorem backTriangle_mass (t : Fin 10 → ℝ) (q : Fin 5 → ℝ)
    (i : Fin 10) :
    triangleMass (augmented t q 0) (backTriangle i) =
      t (backTriple i).1 + t (backTriple i).2.1 + t (backTriple i).2.2 := by
  fin_cases i <;>
    simp [triangleMass, backTriangle, backTriple, augmented, ends,
      Finset.sum_filter, Fin.sum_univ_succ, Finset.subset_iff] <;> ring

theorem augmented_triangle_le_palette
    (t : Fin 10 → ℝ) (q : Fin 5 → ℝ)
    (hcap : ∀ v, internalDegree t v + q v ≤ degreeBound)
    (hq : ∀ v, 0 ≤ q v) (ht1 : ∀ e, t e ≤ 1)
    (hT : 2 * target ≤ internalTotal t)
    (hQ0 : 0 < envelope (internalTotal t))
    (htri : ∀ i : Fin 10,
      triangleMass (augmented t q 0) (backTriangle i) ≤ 2) :
    ∀ S : Finset Vertex, S.card = 3 →
      triangleMass (augmented t q (reserveScale (internalTotal t))) S ≤
        paletteMass (internalTotal t) := by
  intro S hS
  by_cases h0 : 0 ∈ S
  · exact augmented_front_triangle_le_palette t q hcap hq ht1 hT hQ0 S hS h0
  · obtain ⟨i, rfl⟩ := backTriangle_complete S hS h0
    rw [backTriangle_mass_independent_scale]
    exact (htri i).trans (le_max_left _ _)

theorem augmented_nonneg
    (t : Fin 10 → ℝ) (q : Fin 5 → ℝ)
    (ht : ∀ e, 0 ≤ t e) (hq : ∀ v, 0 ≤ q v)
    (hT : 2 * target ≤ internalTotal t)
    (hQ0 : 0 < envelope (internalTotal t)) :
    ∀ e : Edge, 0 ≤ augmented t q (reserveScale (internalTotal t)) e := by
  intro e
  have hk : 0 ≤ reserveScale (internalTotal t) := by
    linarith [reserveScale_gt_one _ hQ0]
  fin_cases e <;> simp [augmented, mul_nonneg hk (hq _), ht _]

end WeightedEdgeColoring.Subtwo.K6BoundaryRows
