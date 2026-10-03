import WeightedEdgeColoring.SubtwoK6SetIdentities

/-! Tight rows cannot block all increases at a vertex of maximum deficit. -/

namespace WeightedEdgeColoring.Subtwo.K6MatchingDeficits

theorem sum_deficit_on (x : Edge → ℝ) (S : Finset Vertex) :
    (∑ v ∈ S, deficit x v) = (S.card : ℝ) - ∑ v ∈ S, degree x v := by
  simp [deficit, Finset.sum_sub_distrib]

theorem tight_triangle_complement_deficit (x : Edge → ℝ) (S : Finset Vertex)
    (hS : S.card = 3) (htight : triangleMass x S = 1)
    (hcomp : triangleMass x Sᶜ ≤ 1) :
    (∑ v ∈ S, deficit x v) ≤ ∑ v ∈ Sᶜ, deficit x v := by
  have hSc : Sᶜ.card = 3 := by rw [Finset.card_compl, hS]; decide
  have hmass := complement_mass x S
  have hall := sum_degree_eq_two_total x
  have hsplit := Finset.sum_add_sum_compl S (degree x)
  rw [sum_deficit_on, sum_deficit_on, hS, hSc]
  norm_num
  linarith

theorem exists_deficient_outside_tight_triangle (x : Edge → ℝ)
    (hdegree : ∀ v, degree x v ≤ 1)
    (htriangle : ∀ S : Finset Vertex, S.card = 3 → triangleMass x S ≤ 1)
    (S : Finset Vertex) (hS : S.card = 3) (htight : triangleMass x S = 1)
    (u : Vertex) (huS : u ∈ S) (hu : 0 < deficit x u) :
    ∃ v ∈ Sᶜ, 0 < deficit x v := by
  have hd (v : Vertex) : 0 ≤ deficit x v := by
    dsimp [deficit]; linarith [hdegree v]
  have hSc : Sᶜ.card = 3 := by rw [Finset.card_compl, hS]; decide
  have hsum := Finset.single_le_sum (fun v (_ : v ∈ S) ↦ hd v) huS
  have hcmp := tight_triangle_complement_deficit x S hS htight (htriangle Sᶜ hSc)
  apply (Finset.sum_pos_iff_of_nonneg (fun v (_ : v ∈ Sᶜ) ↦ hd v)).mp
  linarith

theorem tight_triangles_agree_at_max_deficit (x : Edge → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hdegree : ∀ v, degree x v ≤ 1)
    (hfive : ∀ S : Finset Vertex, S.card = 5 → fiveMass x S ≤ 2)
    (u v : Vertex) (huv : u ≠ v) (hu : 0 < deficit x u)
    (hv : 0 < deficit x v) (hmax : ∀ w, deficit x w ≤ deficit x u)
    (A B : Finset Vertex) (hA : A.card = 3) (hB : B.card = 3)
    (hAt : triangleMass x A = 1) (hBt : triangleMass x B = 1)
    (huA : u ∈ A) (hvA : v ∈ A) (huB : u ∈ B) : A = B := by
  by_contra hne
  have huI : u ∈ A ∩ B := Finset.mem_inter.mpr ⟨huA, huB⟩
  have hiPos : 0 < (A ∩ B).card := Finset.card_pos.mpr ⟨u, huI⟩
  have hiLe : (A ∩ B).card ≤ 3 := hA ▸ Finset.card_le_card Finset.inter_subset_left
  have hiLt : (A ∩ B).card < 3 := by
    by_contra hh
    have hc : (A ∩ B).card = 3 := by omega
    have ha : A ∩ B = A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hb : A ∩ B = B := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hne (ha.symm.trans hb)
  have hcases : (A ∩ B).card = 1 ∨ (A ∩ B).card = 2 := by omega
  rcases hcases with hi | hi
  · have hU : (A ∪ B).card = 5 := by
      have hh := Finset.card_union_add_card_inter A B
      omega
    have hlo := two_triangles_le_union x hx A B hi
    have hhi := hfive (A ∪ B) hU
    have htight : fiveMass x (A ∪ B) = 2 := by
      change triangleMass x (A ∪ B) ≤ 2 at hhi
      change triangleMass x (A ∪ B) = 2
      linarith
    have hc : (A ∪ B)ᶜ.card = 1 := by rw [Finset.card_compl, hU]; decide
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc
    have heq : A ∪ B = Finset.univ.erase w := by
      have hh := congrArg (fun T : Finset Vertex ↦ Tᶜ) hw
      have hs : ({w} : Finset Vertex)ᶜ = Finset.univ.erase w := by ext z; simp
      simpa only [compl_compl, hs] using hh
    have huU : u ∈ A ∪ B := Finset.mem_union_left _ huA
    have hvU : v ∈ A ∪ B := Finset.mem_union_left _ hvA
    rw [heq] at htight huU hvU
    rw [fiveMass_compl_singleton_eq_omitFive] at htight
    exact tight_five_excludes_two_deficits x hdegree w u v
      (Ne.symm (Finset.mem_erase.mp huU).1)
      (Ne.symm (Finset.mem_erase.mp hvU).1) huv htight (hmax w) hv
  · have hbound := two_triangles_le_intersection_degrees x hx A B hA hB hi
    have hdu : degree x u < 1 := by dsimp [deficit] at hu; linarith
    have hstrict := Finset.sum_lt_sum (fun z (_ : z ∈ A ∩ B) ↦ hdegree z)
      ⟨u, huI, hdu⟩
    have hone : (∑ _v ∈ A ∩ B, (1 : ℝ)) = 2 := by simp [hi]
    rw [hone] at hstrict
    linarith

end WeightedEdgeColoring.Subtwo.K6MatchingDeficits
