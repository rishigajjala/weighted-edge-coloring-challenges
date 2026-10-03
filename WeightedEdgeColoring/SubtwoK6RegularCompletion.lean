import WeightedEdgeColoring.SubtwoK6CompletionObstructions
import WeightedEdgeColoring.SubtwoFinitePackingMax

/-! Regular completion for the fractional matching constraints on six vertices. -/

namespace WeightedEdgeColoring.Subtwo.K6MatchingDeficits

abbrev Triangle := {S : Finset Vertex // S.card = 3}
abbrev PackingRow := Vertex ⊕ (Triangle ⊕ Vertex)

def packingCoeff (r : PackingRow) (e : Edge) : ℝ :=
  match r with
  | .inl v => if v ∈ ends e then 1 else 0
  | .inr (.inl S) => inside S.val e
  | .inr (.inr v) => inside (Finset.univ.erase v) e

def packingBound : PackingRow → ℝ
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

theorem packingCoeff_nonneg (r : PackingRow) (e : Edge) : 0 ≤ packingCoeff r e := by
  rcases r with v | S | v
  · dsimp [packingCoeff]; split_ifs <;> norm_num
  · exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _

theorem ends_nonempty : ∀ e : Edge, (ends e).Nonempty := by decide

theorem edge_for_pair : ∀ u v : Vertex, u ≠ v → ∃ e : Edge, ends e = {u, v} := by
  decide

theorem edge_le_degree (x : Edge → ℝ) (hx : ∀ e, 0 ≤ x e)
    (e : Edge) (v : Vertex) (hv : v ∈ ends e) : x e ≤ degree x v := by
  rw [degree_eq_incidence_sum]
  have hh := Finset.single_le_sum
    (s := (Finset.univ : Finset Edge))
    (f := fun f ↦ if v ∈ ends f then x f else 0)
    (fun f _ ↦ by dsimp; split_ifs <;> simp [hx f]) (Finset.mem_univ e)
  simpa [hv] using hh

theorem packing_feasible_of_bounds (lower x : Edge → ℝ)
    (hlo : ∀ e, lower e ≤ x e) (hx : ∀ e, 0 ≤ x e)
    (hd : ∀ v, degree x v ≤ 1)
    (ht : ∀ S : Finset Vertex, S.card = 3 → triangleMass x S ≤ 1)
    (hf : ∀ v, omitFive x v ≤ 2) :
    FinitePacking.Feasible lower packingCoeff packingBound x := by
  refine ⟨hlo, ?_, ?_⟩
  · intro e
    obtain ⟨v, hv⟩ := ends_nonempty e
    exact (edge_le_degree x hx e v hv).trans (hd v)
  · intro r
    rcases r with v | S | v
    · simpa [packingCoeff, packingBound, degree_eq_incidence_sum] using hd v
    · simpa [packingCoeff, packingBound, mass_eq_coeff] using ht S.val S.property
    · have hh := hf v
      rw [← fiveMass_compl_singleton_eq_omitFive] at hh
      change triangleMass x (Finset.univ.erase v) ≤ 2 at hh
      simpa [packingCoeff, packingBound, mass_eq_coeff] using hh

theorem packing_feasible_degree (lower x : Edge → ℝ)
    (hx : FinitePacking.Feasible lower packingCoeff packingBound x) (v : Vertex) :
    degree x v ≤ 1 := by
  simpa [packingCoeff, packingBound, degree_eq_incidence_sum] using hx.2.2 (.inl v)

theorem packing_feasible_triangle (lower x : Edge → ℝ)
    (hx : FinitePacking.Feasible lower packingCoeff packingBound x)
    (S : Finset Vertex) (hS : S.card = 3) : triangleMass x S ≤ 1 := by
  simpa [packingCoeff, packingBound, mass_eq_coeff] using hx.2.2 (.inr (.inl ⟨S, hS⟩))

theorem packing_feasible_five (lower x : Edge → ℝ)
    (hx : FinitePacking.Feasible lower packingCoeff packingBound x) (v : Vertex) :
    omitFive x v ≤ 2 := by
  rw [← fiveMass_compl_singleton_eq_omitFive]
  change triangleMass x (Finset.univ.erase v) ≤ 2
  simpa [packingCoeff, packingBound, mass_eq_coeff] using hx.2.2 (.inr (.inr v))

theorem five_bound_of_omit (x : Edge → ℝ) (hf : ∀ v, omitFive x v ≤ 2)
    (S : Finset Vertex) (hS : S.card = 5) : fiveMass x S ≤ 2 := by
  have hc : Sᶜ.card = 1 := by rw [Finset.card_compl, hS]; decide
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
  have heq : S = Finset.univ.erase v := by
    have hh := congrArg (fun T : Finset Vertex ↦ Tᶜ) hv
    have hs : ({v} : Finset Vertex)ᶜ = Finset.univ.erase v := by ext z; simp
    simpa only [compl_compl, hs] using hh
  rw [heq, fiveMass_compl_singleton_eq_omitFive]
  exact hf v

theorem exists_other_deficient (x : Edge → ℝ)
    (hd : ∀ v, degree x v ≤ 1) (hf : ∀ v, omitFive x v ≤ 2)
    (u : Vertex) (hu : 0 < deficit x u) :
    ∃ v, v ≠ u ∧ 0 < deficit x v := by
  have hsum := sum_deficit_eq x
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset Vertex) (deficit x)
    (Finset.mem_univ u)
  have hfu := hf u
  have hpos : 0 < ∑ v ∈ (Finset.univ : Finset Vertex).erase u, deficit x v := by
    dsimp [omitFive, deficit] at hfu hu hsum hsplit ⊢
    linarith
  obtain ⟨v, hv, hvp⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun v (_ : v ∈ (Finset.univ : Finset Vertex).erase u) ↦
      show 0 ≤ deficit x v by dsimp [deficit]; linarith [hd v])).mp hpos
  exact ⟨v, (Finset.mem_erase.mp hv).1, hvp⟩

theorem max_total_tight_triangle_between (lower y : Edge → ℝ)
    (hy : FinitePacking.Feasible lower packingCoeff packingBound y)
    (hy0 : ∀ e, 0 ≤ y e)
    (hmax : ∀ z, FinitePacking.Feasible lower packingCoeff packingBound z →
      (∑ e, z e) ≤ ∑ e, y e)
    (u v : Vertex) (huv : u ≠ v) (hu : 0 < deficit y u)
    (hv : 0 < deficit y v) (hdef : ∀ w, deficit y w ≤ deficit y u) :
    ∃ S : Finset Vertex, S.card = 3 ∧ triangleMass y S = 1 ∧ u ∈ S ∧ v ∈ S := by
  have hd := packing_feasible_degree lower y hy
  obtain ⟨e, he⟩ := edge_for_pair u v huv
  have hue : u ∈ ends e := by simp [he]
  have hve : v ∈ ends e := by simp [he]
  have hlt : y e < 1 := by
    have hh := edge_le_degree y hy0 e u hue
    dsimp [deficit] at hu
    linarith
  obtain ⟨r, hr, htight⟩ := FinitePacking.max_total_has_tight_row
    lower packingCoeff packingBound packingCoeff_nonneg y hy hmax e hlt
  rcases r with w | S | w
  · have hw : w ∈ ends e := by
      by_contra hh
      simp [packingCoeff, hh] at hr
    have hdw : degree y w = 1 := by
      simpa [packingCoeff, packingBound, degree_eq_incidence_sum] using htight
    have hwuv : w = u ∨ w = v := by simpa [he] using hw
    rcases hwuv with rfl | rfl <;> dsimp [deficit] at hu hv <;> linarith
  · have hsub : ends e ⊆ S.val := by
      by_contra hh
      simp [packingCoeff, inside, hh] at hr
    refine ⟨S.val, S.property, ?_, hsub hue, hsub hve⟩
    simpa [packingCoeff, packingBound, mass_eq_coeff] using htight
  · have hsub : ends e ⊆ Finset.univ.erase w := by
      by_contra hh
      simp [packingCoeff, inside, hh] at hr
    have htf : omitFive y w = 2 := by
      rw [← fiveMass_compl_singleton_eq_omitFive]
      change triangleMass y (Finset.univ.erase w) = 2
      simpa [packingCoeff, packingBound, mass_eq_coeff] using htight
    exact (tight_five_excludes_two_deficits y hd w u v
      (Ne.symm (Finset.mem_erase.mp (hsub hue)).1)
      (Ne.symm (Finset.mem_erase.mp (hsub hve)).1) huv htf (hdef w) hv).elim

/-- Every feasible fractional matching on `K₆` extends coordinatewise to
one with all six degrees exactly one. -/
theorem exists_regular_completion (x : Edge → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hd : ∀ v, degree x v ≤ 1)
    (ht : ∀ S : Finset Vertex, S.card = 3 → triangleMass x S ≤ 1)
    (hf : ∀ v, omitFive x v ≤ 2) :
    ∃ y : Edge → ℝ, (∀ e, x e ≤ y e) ∧ (∀ e, 0 ≤ y e) ∧
      (∀ v, degree y v = 1) ∧
      (∀ S : Finset Vertex, S.card = 3 → triangleMass y S ≤ 1) := by
  have hfeas := packing_feasible_of_bounds x x (fun _ ↦ le_rfl) hx hd ht hf
  obtain ⟨y, hy, hmax⟩ := FinitePacking.exists_max_total x packingCoeff packingBound hfeas
  have hy0 (e : Edge) : 0 ≤ y e := (hx e).trans (hy.1 e)
  have hyd := packing_feasible_degree x y hy
  have hyt := packing_feasible_triangle x y hy
  have hyf := packing_feasible_five x y hy
  refine ⟨y, hy.1, hy0, ?_, hyt⟩
  intro z
  apply le_antisymm (hyd z)
  by_contra hz
  have hdz : 0 < deficit y z := by dsimp [deficit]; linarith
  obtain ⟨u, _, hdef⟩ := Finset.exists_max_image (Finset.univ : Finset Vertex)
    (deficit y) ⟨z, Finset.mem_univ z⟩
  have hdu : 0 < deficit y u := hdz.trans_le (hdef z (Finset.mem_univ z))
  have hdef' (w : Vertex) : deficit y w ≤ deficit y u := hdef w (Finset.mem_univ w)
  obtain ⟨v, hvu, hdv⟩ := exists_other_deficient y hyd hyf u hdu
  obtain ⟨S, hS, hSt, huS, hvS⟩ :=
    max_total_tight_triangle_between x y hy hy0 hmax u v (Ne.symm hvu) hdu hdv hdef'
  obtain ⟨w, hwS, hdw⟩ :=
    exists_deficient_outside_tight_triangle y hyd hyt S hS hSt u huS hdu
  have hwu : u ≠ w := by
    intro heq
    subst w
    exact (Finset.mem_compl.mp hwS) huS
  obtain ⟨T, hT, hTt, huT, hwT⟩ :=
    max_total_tight_triangle_between x y hy hy0 hmax u w hwu hdu hdw hdef'
  have heq := tight_triangles_agree_at_max_deficit y hy0 hyd
    (five_bound_of_omit y hyf) u v (Ne.symm hvu) hdu hdv hdef'
    S T hS hT hSt hTt huS hvS huT
  exact (Finset.mem_compl.mp hwS) (heq.symm ▸ hwT)

end WeightedEdgeColoring.Subtwo.K6MatchingDeficits
