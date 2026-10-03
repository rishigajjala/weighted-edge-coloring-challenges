import WeightedEdgeColoring.BPGeneralOddSetDensity
import WeightedEdgeColoring.BPGeneralTwoBagMassCertificate

/-!
# Turning three bundle bounds into the triangle constraint

An internal edge of a three-vertex set lies on exactly one of its three
unordered vertex pairs.  This file proves that elementary graph bridge and
then feeds the finite two-bag mass certificates into the triangle hypothesis
used by the odd-set calculation.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Edges of `F` joining the unordered vertex pair `{u,v}`. -/
def edgesBetween (F : Finset G.E) (u v : G.V) : Finset G.E :=
  F.filter fun e ↦
    (G.fst e = u ∧ G.snd e = v) ∨
      (G.fst e = v ∧ G.snd e = u)

theorem edgesBetween_comm (F : Finset G.E) (u v : G.V) :
    G.edgesBetween F u v = G.edgesBetween F v u := by
  ext e
  simp only [edgesBetween, Finset.mem_filter]
  tauto

/-- On three distinct vertices, the internal edges are the disjoint union
of the three parallel bundles. -/
theorem internalEdges_triple_eq_union_edgesBetween
    (F : Finset G.E) {a b c : G.V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.internalEdges F {a, b, c} =
      (G.edgesBetween F a b ∪ G.edgesBetween F a c) ∪
        G.edgesBetween F b c := by
  ext e
  simp only [internalEdges, edgesBetween, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
  constructor
  · rintro ⟨heF, hfst, hsnd⟩
    rcases hfst with hfa | hfb | hfc <;>
      rcases hsnd with hsa | hsb | hsc
    · exact (G.noLoop e (hfa.trans hsa.symm)).elim
    · exact Or.inl (Or.inl ⟨heF, Or.inl ⟨hfa, hsb⟩⟩)
    · exact Or.inl (Or.inr ⟨heF, Or.inl ⟨hfa, hsc⟩⟩)
    · exact Or.inl (Or.inl ⟨heF, Or.inr ⟨hfb, hsa⟩⟩)
    · exact (G.noLoop e (hfb.trans hsb.symm)).elim
    · exact Or.inr ⟨heF, Or.inl ⟨hfb, hsc⟩⟩
    · exact Or.inl (Or.inr ⟨heF, Or.inr ⟨hfc, hsa⟩⟩)
    · exact Or.inr ⟨heF, Or.inr ⟨hfc, hsb⟩⟩
    · exact (G.noLoop e (hfc.trans hsc.symm)).elim
  · aesop

theorem edgesBetween_pairwise_disjoint
    (F : Finset G.E) {a b c : G.V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Disjoint (G.edgesBetween F a b) (G.edgesBetween F a c) ∧
      Disjoint (G.edgesBetween F a b) (G.edgesBetween F b c) ∧
      Disjoint (G.edgesBetween F a c) (G.edgesBetween F b c) := by
  constructor
  · rw [Finset.disjoint_left]
    intro e heAB heAC
    simp only [edgesBetween, Finset.mem_filter] at heAB heAC
    rcases heAB.2 with ⟨hfa, hsb⟩ | ⟨hfb, hsa⟩ <;>
      rcases heAC.2 with ⟨hfa', hsc⟩ | ⟨hfc, hsa'⟩
    · exact hbc (hsb.symm.trans hsc)
    · exact hac (hfa.symm.trans hfc)
    · exact hab (hfa'.symm.trans hfb)
    · exact hbc (hfb.symm.trans hfc)
  constructor
  · rw [Finset.disjoint_left]
    intro e heAB heBC
    simp only [edgesBetween, Finset.mem_filter] at heAB heBC
    rcases heAB.2 with ⟨hfa, hsb⟩ | ⟨hfb, hsa⟩ <;>
      rcases heBC.2 with ⟨hfb', hsc⟩ | ⟨hfc, hsb'⟩
    · exact hab (hfa.symm.trans hfb')
    · exact hac (hfa.symm.trans hfc)
    · exact hac (hsa.symm.trans hsc)
    · exact hab (hsa.symm.trans hsb')
  · rw [Finset.disjoint_left]
    intro e heAC heBC
    simp only [edgesBetween, Finset.mem_filter] at heAC heBC
    rcases heAC.2 with ⟨hfa, hsc⟩ | ⟨hfc, hsa⟩ <;>
      rcases heBC.2 with ⟨hfb, hsc'⟩ | ⟨hfc', hsb⟩
    · exact hab (hfa.symm.trans hfb)
    · exact hbc (hsb.symm.trans hsc)
    · exact hbc (hfb.symm.trans hfc)
    · exact hab (hsa.symm.trans hsb)

theorem card_internalEdges_triple
    (F : Finset G.E) {a b c : G.V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (G.internalEdges F {a, b, c}).card =
      (G.edgesBetween F a b).card +
        (G.edgesBetween F a c).card +
          (G.edgesBetween F b c).card := by
  rw [G.internalEdges_triple_eq_union_edgesBetween F hab hac hbc]
  obtain ⟨hABAC, hABBC, hACBC⟩ :=
    G.edgesBetween_pairwise_disjoint F hab hac hbc
  rw [Finset.card_union_of_disjoint
    (Finset.disjoint_union_left.mpr ⟨hABBC, hACBC⟩),
    Finset.card_union_of_disjoint hABAC]

/-- Finite data sufficient for the exact `2n` triangle bound.  It records
the three fractional bundle costs and the two-bag witnesses supplied by the
three local pair packings. -/
def HasTriangleBundleMassCertificates (F : Finset G.E) (n : ℝ) : Prop :=
  ∀ a b c : G.V, a ≠ b → a ≠ c → b ≠ c →
    ∃ A B C Tab Tac Tbc : ℝ,
      ((G.edgesBetween F a b).card : ℝ) ≤ A ∧
      ((G.edgesBetween F a c).card : ℝ) ≤ B ∧
      ((G.edgesBetween F b c).card : ℝ) ≤ C ∧
      TwoBagMassCertificate A B Tab ∧ Tab ≤ n ∧
      TwoBagMassCertificate A C Tac ∧ Tac ≤ n ∧
      TwoBagMassCertificate B C Tbc ∧ Tbc ≤ n

theorem triangleEdgeCountAtMost_of_bundleMassCertificates
    (F : Finset G.E) (n : ℝ)
    (hcert : G.HasTriangleBundleMassCertificates F n) :
    G.TriangleEdgeCountAtMost F (2 * n) := by
  intro S hS
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS
  obtain ⟨A, B, C, Tab, Tac, Tbc,
    hA, hB, hC, hAB, hTab, hAC, hTac, hBC, hTbc⟩ :=
      hcert a b c hab hac hbc
  rw [G.card_internalEdges_triple F hab hac hbc]
  exact three_packetCounts_le_two_mul_of_pairwise_massCertificates
    _ _ _ hA hB hC hAB hTab hAC hTac hBC hTbc

end WeightedMultigraph
end WeightedEdgeColoring
