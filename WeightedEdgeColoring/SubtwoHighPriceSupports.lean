import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# The shapes of high-price supports

An intersecting family of two-element sets is a star or is contained in a
triangle. This is the structural reduction behind the high-price roots of
the dense-five certificate. The statement is proved for any vertex type.
-/

namespace WeightedEdgeColoring.Subtwo

variable {V : Type*} [DecidableEq V]

private theorem pair_of_card_two_of_mem {e : Finset V} {a : V}
    (he : e.card = 2) (ha : a ∈ e) :
    ∃ b, a ≠ b ∧ e = {a, b} := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp he
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨y, hxy, rfl⟩
  · exact ⟨x, hxy.symm, by ext z; simp [or_comm]⟩

private theorem pair_eq_of_two_members {e : Finset V} {a b : V}
    (he : e.card = 2) (hab : a ≠ b) (ha : a ∈ e) (hb : b ∈ e) :
    e = {a, b} := by
  have hsub : ({a, b} : Finset V) ⊆ e := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hc : ({a, b} : Finset V).card = e.card := by simp [hab, he]
  exact (Finset.eq_of_subset_of_card_le hsub hc.ge).symm

private theorem member_of_meets_pair {e : Finset V} {a b : V}
    (h : (e ∩ {a, b}).Nonempty) : a ∈ e ∨ b ∈ e := by
  obtain ⟨x, hx⟩ := h
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx.2 with rfl | rfl
  · exact Or.inl hx.1
  · exact Or.inr hx.1

/-- Every nonempty intersecting family of pairs is a star or is supported
on the three edges of one triangle. No enumeration or external checker is
used in this classification. -/
theorem intersecting_pairs_star_or_triangle
    (F : Finset (Finset V)) (hne : F.Nonempty)
    (hcard : ∀ e ∈ F, e.card = 2)
    (hinter : ∀ e ∈ F, ∀ f ∈ F, (e ∩ f).Nonempty) :
    (∃ a, ∀ e ∈ F, a ∈ e) ∨
      ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        ∀ e ∈ F, e = {a, b} ∨ e = {a, c} ∨ e = {b, c} := by
  classical
  by_cases hstar : ∃ a, ∀ e ∈ F, a ∈ e
  · exact Or.inl hstar
  apply Or.inr
  obtain ⟨e, he⟩ := hne
  obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp (hcard e he)
  have habF : ({a, b} : Finset V) ∈ F := heq ▸ he
  have hncommon (v : V) : ∃ f ∈ F, v ∉ f := by
    by_contra hn
    push_neg at hn
    exact hstar ⟨v, hn⟩
  obtain ⟨f, hf, haf⟩ := hncommon a
  have hbf : b ∈ f :=
    (member_of_meets_pair (hinter f hf {a, b} habF)).resolve_left haf
  obtain ⟨c, hbc, hfeq⟩ := pair_of_card_two_of_mem (hcard f hf) hbf
  have hac : a ≠ c := by
    intro h
    apply haf
    simp [hfeq, h]
  have hbcF : ({b, c} : Finset V) ∈ F := hfeq ▸ hf
  obtain ⟨g, hg, hbg⟩ := hncommon b
  have hag : a ∈ g :=
    (member_of_meets_pair (hinter g hg {a, b} habF)).resolve_right hbg
  have hcg : c ∈ g :=
    (member_of_meets_pair (hinter g hg {b, c} hbcF)).resolve_left hbg
  have hgeq : g = {a, c} := pair_eq_of_two_members (hcard g hg) hac hag hcg
  have hacF : ({a, c} : Finset V) ∈ F := hgeq ▸ hg
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  intro k hk
  by_cases hak : a ∈ k
  · by_cases hbk : b ∈ k
    · exact Or.inl (pair_eq_of_two_members (hcard k hk) hab hak hbk)
    · have hck : c ∈ k :=
        (member_of_meets_pair (hinter k hk {b, c} hbcF)).resolve_left hbk
      exact Or.inr (Or.inl (pair_eq_of_two_members (hcard k hk) hac hak hck))
  · have hbk : b ∈ k :=
      (member_of_meets_pair (hinter k hk {a, b} habF)).resolve_left hak
    have hck : c ∈ k :=
      (member_of_meets_pair (hinter k hk {a, c} hacF)).resolve_left hak
    exact Or.inr (Or.inr (pair_eq_of_two_members (hcard k hk) hbc hbk hck))

/-- Disjoint packets fit together, so two prices strictly above one half
must share an endpoint. -/
theorem high_price_pairs_intersect
    (F : Finset (Finset V)) (m : Finset V → ℝ)
    (hdisjoint : ∀ e ∈ F, ∀ f ∈ F, Disjoint e f → m e + m f ≤ 1)
    {e f : Finset V} (he : e ∈ F) (hf : f ∈ F)
    (hme : (1 / 2 : ℝ) < m e) (hmf : (1 / 2 : ℝ) < m f) :
    (e ∩ f).Nonempty := by
  by_contra h
  have hempty : e ∩ f = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hd : Disjoint e f := Finset.disjoint_iff_inter_eq_empty.mpr hempty
  have hsum := hdisjoint e he f hf hd
  linarith

/-- Apply the classification directly to the edges whose packet price
exceeds one half. This covers all possible supports, including boundary
prices being left out of the high-price family. -/
theorem high_price_support_star_or_triangle
    (F : Finset (Finset V)) (m : Finset V → ℝ)
    (hcard : ∀ e ∈ F, e.card = 2)
    (hdisjoint : ∀ e ∈ F, ∀ f ∈ F, Disjoint e f → m e + m f ≤ 1)
    (hne : ∃ e ∈ F, (1 / 2 : ℝ) < m e) :
    (∃ a, ∀ e ∈ F, (1 / 2 : ℝ) < m e → a ∈ e) ∨
      ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        ∀ e ∈ F, (1 / 2 : ℝ) < m e →
          e = {a, b} ∨ e = {a, c} ∨ e = {b, c} := by
  classical
  let H := F.filter fun e ↦ (1 / 2 : ℝ) < m e
  have hnH : H.Nonempty := by
    obtain ⟨e, he, hm⟩ := hne
    exact ⟨e, Finset.mem_filter.mpr ⟨he, hm⟩⟩
  have hcH : ∀ e ∈ H, e.card = 2 := by
    intro e he
    exact hcard e (Finset.mem_filter.mp he).1
  have hiH : ∀ e ∈ H, ∀ f ∈ H, (e ∩ f).Nonempty := by
    intro e he f hf
    obtain ⟨heF, hme⟩ := Finset.mem_filter.mp he
    obtain ⟨hfF, hmf⟩ := Finset.mem_filter.mp hf
    exact high_price_pairs_intersect F m hdisjoint heF hfF hme hmf
  simpa [H] using intersecting_pairs_star_or_triangle H hnH hcH hiH

end WeightedEdgeColoring.Subtwo
