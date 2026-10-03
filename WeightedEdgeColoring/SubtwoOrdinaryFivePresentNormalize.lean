import WeightedEdgeColoring.SubtwoOrdinaryFivePresentState

/-!
# Moving an adjacent boundary-color pair to the omitted-edge endpoints
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.exists_external_endpoint_state_of_cycle_pair
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hcneA : c ≠ a) (hcneB : c ≠ b)
    (hnot : FivePathState.NotTwoInternalColor G s c)
    (hpair :
      (FivePathState.HasExternalColorAt G s c s.left ∧
        FivePathState.HasExternalColorAt G s c s.right) ∨
      (FivePathState.HasExternalColorAt G s c s.left ∧
        FivePathState.HasExternalColorAt G s c (s.path.1.getVert 1)) ∨
      (FivePathState.HasExternalColorAt G s c (s.path.1.getVert 1) ∧
        FivePathState.HasExternalColorAt G s c (s.path.1.getVert 2)) ∨
      (FivePathState.HasExternalColorAt G s c (s.path.1.getVert 2) ∧
        FivePathState.HasExternalColorAt G s c (s.path.1.getVert 3)) ∨
      (FivePathState.HasExternalColorAt G s c (s.path.1.getVert 3) ∧
        FivePathState.HasExternalColorAt G s c s.right)) :
    ∃ a' b' : Fin k, ∃ t : G.FivePathState F k a' b',
      t.path.1.support.toFinset = s.path.1.support.toFinset ∧
      FivePathState.HasExternalColorAt G t c t.left ∧
      FivePathState.HasExternalColorAt G t c t.right ∧
      FivePathState.NotTwoInternalColor G t c := by
  rcases hpair with hends | hfirst | hmiddleLeft | hmiddleRight | hlast
  · exact ⟨a, b, s, rfl, hends.1, hends.2, hnot⟩
  · let sr := s.reverse
    have hL := FivePathState.reverse_external G s hfirst.1
    have h1 := FivePathState.reverse_external G s hfirst.2
    obtain ⟨t, _, htleft, htright, htsupport, _, _, _, ht1, htL,
        hnotT⟩ :=
      FivePathState.exists_shiftLast_preserving_external_not_two
        G sr hcritical hcneB h1 hL
        (FivePathState.reverse_not_two_internal G s hnot)
    have hsr3 : sr.path.1.getVert 3 = s.path.1.getVert 1 := by
      rw [FivePathState.reverse_getVert G s 3]
    refine ⟨b, a, t, ?_, ?_, ?_, hnotT⟩
    · exact htsupport.trans (FivePathState.reverse_support G s)
    · simpa [htleft, hsr3] using ht1
    · simpa [htright] using htL
  · let sr := s.reverse
    have h1 := FivePathState.reverse_external G s hmiddleLeft.1
    have h2 := FivePathState.reverse_external G s hmiddleLeft.2
    obtain ⟨t₁, _, ht₁left, _, ht₁support, ht₁one, _, _,
        ht₁at1, ht₁at2, hnotT₁⟩ :=
      FivePathState.exists_shiftLast_preserving_external_not_two
        G sr hcritical hcneB h1 h2
        (FivePathState.reverse_not_two_internal G s hnot)
    let tr := t₁.reverse
    have h1r := FivePathState.reverse_external G t₁ ht₁at1
    have h2r := FivePathState.reverse_external G t₁ ht₁at2
    obtain ⟨t₂, _, ht₂left, ht₂right, ht₂support, _, _, _,
        ht₂at1, ht₂at2, hnotT₂⟩ :=
      FivePathState.exists_shiftLast_preserving_external_not_two
        G tr hcritical hcneA h1r h2r
        (FivePathState.reverse_not_two_internal G t₁ hnotT₁)
    have hsr3 : sr.path.1.getVert 3 = s.path.1.getVert 1 := by
      rw [FivePathState.reverse_getVert G s 3]
    have hsr2 : sr.path.1.getVert 2 = s.path.1.getVert 2 := by
      rw [FivePathState.reverse_getVert G s 2]
    have htr3 : tr.path.1.getVert 3 = t₁.path.1.getVert 1 := by
      rw [FivePathState.reverse_getVert G t₁ 3]
    have ht₂L : t₂.left = s.path.1.getVert 2 :=
      ht₂left.trans (htr3.trans (ht₁one.trans hsr2))
    have ht₂R : t₂.right = s.path.1.getVert 1 :=
      ht₂right.trans (ht₁left.trans hsr3)
    refine ⟨a, b, t₂, ?_, ?_, ?_, hnotT₂⟩
    · exact ht₂support.trans ((FivePathState.reverse_support G t₁).trans
        (ht₁support.trans (FivePathState.reverse_support G s)))
    · simpa [ht₂L] using ht₂at2
    · simpa [ht₂R] using ht₂at1
  · obtain ⟨t₁, _, ht₁left, _, ht₁support, ht₁one, _, _,
        ht₁at2, ht₁at3, hnotT₁⟩ :=
      FivePathState.exists_shiftLast_preserving_external_not_two
        G s hcritical hcneA hmiddleRight.1 hmiddleRight.2 hnot
    let tr := t₁.reverse
    have h2r := FivePathState.reverse_external G t₁ ht₁at2
    have h3r := FivePathState.reverse_external G t₁ ht₁at3
    obtain ⟨t₂, _, ht₂left, ht₂right, ht₂support, _, _, _,
        ht₂at2, ht₂at3, hnotT₂⟩ :=
      FivePathState.exists_shiftLast_preserving_external_not_two
        G tr hcritical hcneB h2r h3r
        (FivePathState.reverse_not_two_internal G t₁ hnotT₁)
    have htr3 : tr.path.1.getVert 3 = t₁.path.1.getVert 1 := by
      rw [FivePathState.reverse_getVert G t₁ 3]
    have ht₂L : t₂.left = s.path.1.getVert 2 :=
      ht₂left.trans (htr3.trans ht₁one)
    have ht₂R : t₂.right = s.path.1.getVert 3 :=
      ht₂right.trans ht₁left
    refine ⟨b, a, t₂, ?_, ?_, ?_, hnotT₂⟩
    · exact ht₂support.trans ((FivePathState.reverse_support G t₁).trans
        ht₁support)
    · simpa [ht₂L] using ht₂at2
    · simpa [ht₂R] using ht₂at3
  · obtain ⟨t, _, htleft, htright, htsupport, _, _, _, ht3, htR,
        hnotT⟩ :=
      FivePathState.exists_shiftLast_preserving_external_not_two
        G s hcritical hcneA hlast.1 hlast.2 hnot
    refine ⟨a, b, t, htsupport, ?_, ?_, hnotT⟩
    · simpa [htleft] using ht3
    · simpa [htright] using htR

end WeightedEdgeColoring.WeightedMultigraph
