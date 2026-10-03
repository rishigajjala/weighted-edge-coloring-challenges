import WeightedEdgeColoring.BPOrdinaryCriticalPaletteDisjoint

/-!
# Counting the disjoint palettes of a critical chain

The missing-colour sets on a critical path are pairwise disjoint.  Their
total size is therefore at most the number of colours.  If the original
critical graph has maximum degree `d`, every path vertex contributes at
least `k-d` missing colours, and the two endpoints contribute one extra
colour each because the critical edge has been deleted.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Deleting an incident selected edge lowers the selected degree by one. -/
theorem degreeOn_erase_add_one_of_mem_inc
    {F : Finset G.E} {e : G.E} (heF : e ∈ F)
    {v : G.V} (hve : G.Inc v e) :
    G.degreeOn (F.erase e) v + 1 = G.degreeOn F v := by
  classical
  unfold degreeOn
  rw [Finset.filter_erase]
  have heStar : e ∈ F.filter (G.Inc v) :=
    Finset.mem_filter.mpr ⟨heF, hve⟩
  rw [Finset.card_erase_of_mem heStar]
  have hpos : 0 < (F.filter (G.Inc v)).card :=
    Finset.card_pos.mpr ⟨e, heStar⟩
  omega

/-- Pairwise disjoint finite palettes fit inside the full finite colour
set, so the sum of their sizes is at most the number of colours. -/
private theorem sum_card_le_fintype_card_of_pairwiseDisjoint
    {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (S : Finset α) (palette : α → Finset β)
    (hpair : (S : Set α).PairwiseDisjoint palette) :
    (∑ x ∈ S, (palette x).card) ≤ Fintype.card β := by
  have hsum :
      (∑ x ∈ S, (palette x).card) = (S.biUnion palette).card := by
    rw [← Finset.card_biUnion]
    exact hpair
  rw [hsum]
  exact Finset.card_le_card (fun c _ ↦ Finset.mem_univ c)

/-- The palettes on a critical path occupy at most all `k` colours. -/
theorem sum_card_missingColorsAt_criticalPath_le
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hdegree : ∀ z, G.degreeOn (F.erase e) z < k) :
    (∑ z ∈ p.1.support.toFinset,
      (G.missingColorsAt (F.erase e) color z).card) ≤ k := by
  classical
  let D : Finset G.V := p.1.support.toFinset
  let palette : G.V → Finset (Fin k) :=
    fun z ↦ G.missingColorsAt (F.erase e) color z
  have hpair : (D : Set G.V).PairwiseDisjoint palette := by
    intro u hu v hv huv
    apply G.disjoint_missingColorsAt_of_mem_criticalPath_support
      hcritical heF hproper ha hb p hdegree
    · simpa [D] using hu
    · simpa [D] using hv
    · exact huv
  simpa [D, palette] using
    (sum_card_le_fintype_card_of_pairwiseDisjoint D palette hpair)

/-- Andersen's palette count for one critical chain.  If all degrees in
the critical graph are at most `d < k`, then a critical path with `h`
vertices satisfies `h (k-d) + 2 ≤ k`. -/
theorem criticalPath_card_mul_sub_add_two_le
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hdk : d < k) (hdegree : ∀ z, G.degreeOn F z ≤ d) :
    p.1.support.toFinset.card * (k - d) + 2 ≤ k := by
  classical
  let D : Finset G.V := p.1.support.toFinset
  let x := G.fst e
  let y := G.snd e
  let T : Finset G.V := (D.erase x).erase y
  let palette : G.V → Finset (Fin k) :=
    fun z ↦ G.missingColorsAt (F.erase e) color z
  have hxy : x ≠ y := G.noLoop e
  have hxD : x ∈ D := by simp [D, x]
  have hyD : y ∈ D := by simp [D, y]
  have hdegreeErase : ∀ z, G.degreeOn (F.erase e) z < k := by
    intro z
    exact (G.degreeOn_mono_critical (Finset.erase_subset e F) z).trans_lt
      ((hdegree z).trans_lt hdk)
  have hpaletteSum : (∑ z ∈ D, (palette z).card) ≤ k := by
    simpa [D, palette] using
      G.sum_card_missingColorsAt_criticalPath_le
        hcritical heF hproper ha hb p hdegreeErase
  have hxDegree : G.degreeOn (F.erase e) x + 1 ≤ d := by
    rw [G.degreeOn_erase_add_one_of_mem_inc heF (Or.inl rfl)]
    exact hdegree x
  have hyDegree : G.degreeOn (F.erase e) y + 1 ≤ d := by
    rw [G.degreeOn_erase_add_one_of_mem_inc heF (Or.inr rfl)]
    exact hdegree y
  have hxPalette : k - d + 1 ≤ (palette x).card := by
    rw [G.card_missingColorsAt (F.erase e) color hproper x]
    omega
  have hyPalette : k - d + 1 ≤ (palette y).card := by
    rw [G.card_missingColorsAt (F.erase e) color hproper y]
    omega
  have hbasePalette (z : G.V) : k - d ≤ (palette z).card := by
    rw [G.card_missingColorsAt (F.erase e) color hproper z]
    have hzDegree : G.degreeOn (F.erase e) z ≤ d :=
      (G.degreeOn_mono_critical (Finset.erase_subset e F) z).trans (hdegree z)
    omega
  have hDdecomp : D = insert x (insert y T) := by
    ext z
    simp only [T, Finset.mem_insert, Finset.mem_erase]
    constructor
    · intro hzD
      by_cases hzx : z = x
      · exact Or.inl hzx
      · by_cases hzy : z = y
        · exact Or.inr (Or.inl hzy)
        · exact Or.inr (Or.inr ⟨hzy, hzx, hzD⟩)
    · rintro (rfl | rfl | ⟨_, _, hzD⟩)
      · exact hxD
      · exact hyD
      · exact hzD
  have hxT : x ∉ T := by simp [T]
  have hyT : y ∉ T := by simp [T]
  have hsumT : T.card * (k - d) ≤ ∑ z ∈ T, (palette z).card := by
    calc
      T.card * (k - d) = ∑ z ∈ T, (k - d) := by simp
      _ ≤ ∑ z ∈ T, (palette z).card :=
        Finset.sum_le_sum fun z _ ↦ hbasePalette z
  have hcardD : D.card = T.card + 2 := by
    rw [hDdecomp]
    simp [hxT, hyT, hxy, Nat.add_assoc]
  have hsumD : (∑ z ∈ D, (palette z).card) =
      (palette x).card + (palette y).card +
        ∑ z ∈ T, (palette z).card := by
    rw [hDdecomp]
    simp [hxT, hyT, hxy, Nat.add_assoc]
  have hlower : D.card * (k - d) + 2 ≤
      ∑ z ∈ D, (palette z).card := by
    rw [hsumD, hcardD]
    ring_nf
    omega
  exact hlower.trans hpaletteSum

/-- At the strict `m = 5` threshold, a critical chain has fewer than five
vertices. -/
theorem criticalPath_support_card_lt_five
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hdk : d < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 5 * d < 4 * k + 2) :
    p.1.support.toFinset.card < 5 := by
  have hcount := G.criticalPath_card_mul_sub_add_two_le
    hcritical heF hproper ha hb p hdk hdegree
  by_contra hnot
  have hfive : 5 ≤ p.1.support.toFinset.card := by omega
  have hmul : 5 * (k - d) ≤
      p.1.support.toFinset.card * (k - d) :=
    Nat.mul_le_mul_right (k - d) hfive
  omega

end WeightedMultigraph
end WeightedEdgeColoring
