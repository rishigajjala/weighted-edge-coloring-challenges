import WeightedEdgeColoring.BPOrdinaryCriticalTriangle

/-!
# Turning a saturated critical triangle into an odd-set certificate

Suppose an edge `e` is omitted from a colouring and both ends of `e` lie
in a three-vertex set `S`.  If every one of the `k` colours occurs on an
internal edge of `S` after deleting `e`, then those coloured edges number
at least `k`.  The omitted edge is one more internal edge, so `S` has at
least `k + 1` internal edges in the original edge set.  Since `S` has
three vertices, this is precisely the strict odd-set inequality at level
`k`.

This counting argument does not use properness of the colouring.  The
recolouring part of the Andersen argument is responsible only for proving
that every colour occurs in the triangle.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Restoring an omitted internal edge increases the available internal
edge count by at least one. -/
theorem card_internalEdges_erase_add_one_le
    {F : Finset G.E} {S : Finset G.V} {e : G.E}
    (heF : e ∈ F)
    (heS : G.fst e ∈ S ∧ G.snd e ∈ S) :
    (G.internalEdges (F.erase e) S).card + 1 ≤
      (G.internalEdges F S).card := by
  classical
  have heNot : e ∉ G.internalEdges (F.erase e) S := by
    intro he
    have heErase : e ∈ F.erase e := (Finset.mem_filter.mp he).1
    simpa using heErase
  have hsubset :
      insert e (G.internalEdges (F.erase e) S) ⊆
        G.internalEdges F S := by
    intro g hg
    rcases Finset.mem_insert.mp hg with hge | hgInternal
    · subst g
      exact Finset.mem_filter.mpr ⟨heF, heS⟩
    · rcases Finset.mem_filter.mp hgInternal with
        ⟨hgErase, hgS⟩
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_erase.mp hgErase).2, hgS⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_insert_of_notMem heNot] at hcard
  exact hcard

/-- If every value in a `k`-colour palette occurs on an edge of `I`, then
`I` contains at least `k` edges.  No properness assumption is needed: one
edge has only one colour. -/
theorem palette_card_le_of_allColors_on_internalEdges
    {F : Finset G.E} {S : Finset G.V} {k : ℕ}
    (color : G.E → Fin k)
    (hall : ∀ c : Fin k, ∃ g,
      g ∈ G.internalEdges F S ∧ color g = c) :
    k ≤ (G.internalEdges F S).card := by
  classical
  have huniv : (Finset.univ : Finset (Fin k)) ⊆
      (G.internalEdges F S).image color := by
    intro c _hc
    obtain ⟨g, hg, hgc⟩ := hall c
    exact Finset.mem_image.mpr ⟨g, hg, hgc⟩
  have hcolors : k ≤ ((G.internalEdges F S).image color).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card huniv
  exact hcolors.trans Finset.card_image_le

/-- A three-vertex set containing an omitted edge and all `k` colours
violates the odd-set inequality at level `k`. -/
theorem oddSetCertificate_at_of_allColors_internal_three
    {F : Finset G.E} {S : Finset G.V} {e : G.E} {k : ℕ}
    (color : G.E → Fin k)
    (hS : S.card = 3)
    (heF : e ∈ F)
    (heS : G.fst e ∈ S ∧ G.snd e ∈ S)
    (hall : ∀ c : Fin k, ∃ g,
      g ∈ G.internalEdges (F.erase e) S ∧ color g = c) :
    Odd S.card ∧ 3 ≤ S.card ∧
      (k : ℝ) * ((S.card : ℝ) - 1) <
        (2 : ℝ) * (G.internalEdges F S).card := by
  have hpalette :
      k ≤ (G.internalEdges (F.erase e) S).card :=
    G.palette_card_le_of_allColors_on_internalEdges color hall
  have hrestore := G.card_internalEdges_erase_add_one_le heF heS
  have hstrictNat : k < (G.internalEdges F S).card := by omega
  have hstrictReal :
      (k : ℝ) < ((G.internalEdges F S).card : ℝ) := by
    exact_mod_cast hstrictNat
  refine ⟨?_, ?_, ?_⟩
  · simpa [hS] using (show Odd (3 : ℕ) by decide)
  · omega
  · rw [hS]
    norm_num
    nlinarith

/-- Existential form matching the obstruction certificate used by the
`m = 5` density theorem. -/
theorem exists_oddSetCertificate_of_allColors_internal_three
    {F : Finset G.E} {S : Finset G.V} {e : G.E} {k : ℕ}
    (color : G.E → Fin k)
    (hS : S.card = 3)
    (heF : e ∈ F)
    (heS : G.fst e ∈ S ∧ G.snd e ∈ S)
    (hall : ∀ c : Fin k, ∃ g,
      g ∈ G.internalEdges (F.erase e) S ∧ color g = c) :
    ∃ T : Finset G.V, Odd T.card ∧ 3 ≤ T.card ∧
      (k : ℝ) * ((T.card : ℝ) - 1) <
        (2 : ℝ) * (G.internalEdges F T).card := by
  exact ⟨S,
    G.oddSetCertificate_at_of_allColors_internal_three
      color hS heF heS hall⟩

end WeightedMultigraph
end WeightedEdgeColoring
