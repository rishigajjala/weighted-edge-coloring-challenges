import WeightedEdgeColoring.SubtwoOrdinaryFiveMiddleColors

/-!
# The remaining present-everywhere color case

If a color fails to occur twice inside the five-chain, Theorem 5(ii)
forces it to be present at every one of the five vertices. At least three
of those vertices then use that color on an edge leaving the chain.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem present_at_every_fivePath_vertex_of_not_two_internal_edges
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {c : Fin k}
    (hnot : ¬∃ r s, r ≠ s ∧
      r ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      s ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      color r = c ∧ color s = c) :
    ∀ v ∈ p.1.support,
      c ∉ G.missingColorsAt (F.erase e) color v := by
  intro v hv hc
  exact hnot (G.two_internal_edges_of_missing_some_fivePath
    hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold hv hc)

/-- A five-vertex set with a color present everywhere but on fewer than
two internal edges has at least three vertices whose color edge leaves it. -/
theorem three_external_vertices_of_present_unsaturated_color
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {S : Finset G.V} (hS : S.card = 5) {c : Fin k}
    (hpresent : ∀ v ∈ S, c ∉ G.missingColorsAt F color v)
    (hnot : ¬∃ r s, r ≠ s ∧
      r ∈ G.internalEdges F S ∧ s ∈ G.internalEdges F S ∧
      color r = c ∧ color s = c) :
    ∃ T : Finset G.V, T ⊆ S ∧ 3 ≤ T.card ∧
      ∀ v ∈ T, ∃ g, g ∈ F ∧ G.Inc v g ∧ color g = c ∧
        g ∉ G.internalEdges F S := by
  classical
  let E := (G.internalEdges F S).filter (fun g ↦ color g = c)
  have hEcard : E.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro g hg r hr
    by_contra hne
    exact hnot ⟨g,r,hne,(Finset.mem_filter.mp hg).1,
      (Finset.mem_filter.mp hr).1,(Finset.mem_filter.mp hg).2,
      (Finset.mem_filter.mp hr).2⟩
  let U := S.filter (fun v ↦ ∃ g ∈ E, G.Inc v g)
  have hUcard : U.card ≤ 2 := by
    by_cases hE : E.Nonempty
    · obtain ⟨g₀,hg₀⟩ := hE
      have hsub : U ⊆ ({G.fst g₀, G.snd g₀} : Finset G.V) := by
        intro v hv
        obtain ⟨g,hgE,hvg⟩ := (Finset.mem_filter.mp hv).2
        have hgeq : g = g₀ :=
          Finset.card_le_one.mp hEcard g hgE g₀ hg₀
        subst g
        rcases hvg with hf | hs
        · simp [hf.symm]
        · simp [hs.symm]
      exact (Finset.card_le_card hsub).trans (by
        by_cases h : G.fst g₀ = G.snd g₀ <;> simp [h])
    · have hEmpty : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
      have hUempty : U = ∅ := by
        ext v
        simp [U, hEmpty]
      simp [hUempty]
  let T := S \ U
  have hTsub : T ⊆ S := Finset.sdiff_subset
  have hTcard : 3 ≤ T.card := by
    have hdecomp := Finset.card_sdiff_add_card_eq_card
      (show U ⊆ S from Finset.filter_subset _ _)
    change T.card + U.card = S.card at hdecomp
    omega
  refine ⟨T, hTsub, hTcard, ?_⟩
  intro v hvT
  have hvS : v ∈ S := hTsub hvT
  have hvNotU : v ∉ U := (Finset.mem_sdiff.mp hvT).2
  obtain ⟨g,hgF,hvg,hgc⟩ :=
    G.exists_edge_of_not_missingColor (hpresent v hvS)
  refine ⟨g,hgF,hvg,hgc, ?_⟩
  intro hgInternal
  apply hvNotU
  apply Finset.mem_filter.mpr
  refine ⟨hvS, g, ?_, hvg⟩
  exact Finset.mem_filter.mpr ⟨hgInternal,hgc⟩

/-- No three vertices of a five-cycle can be pairwise nonadjacent. -/
theorem fin5_three_contains_cycle_neighbors
    (T : Finset (Fin 5)) (hT : 3 ≤ T.card) :
    ∃ i : Fin 5, i ∈ T ∧ i + 1 ∈ T := by
  have hfinite : ∀ U : Finset (Fin 5),
      3 ≤ U.card → ∃ i : Fin 5, i ∈ U ∧ i + 1 ∈ U := by
    decide
  exact hfinite T hT

/-- Any three vertices of a simple five-edge path support include two
consecutive vertices of the five-cycle formed by the path and omitted edge. -/
theorem fivePath_three_vertices_have_cycle_neighbor_pair
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    {a b : Fin k}
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (T : Finset G.V) (hTsub : T ⊆ p.1.support.toFinset)
    (hTcard : 3 ≤ T.card) :
    ∃ i : Fin 5,
      p.1.getVert i.val ∈ T ∧ p.1.getVert (i + 1).val ∈ T := by
  classical
  let f : Fin 5 → G.V := fun i ↦ p.1.getVert i.val
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact p.property.getVert_injOn
      (Set.mem_Iic.mpr (by have := i.isLt; omega))
      (Set.mem_Iic.mpr (by have := j.isLt; omega)) hij
  have hsubImage : (Finset.univ.image f) ⊆ p.1.support.toFinset := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    change p.1.getVert i.val ∈ p.1.support.toFinset
    simpa only [List.mem_toFinset] using p.1.getVert_mem_support i.val
  have himageCard : (Finset.univ.image f).card = 5 := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hpCard : p.1.support.toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup p.property.support_nodup,
      p.1.length_support, hpLen]
  have himage : Finset.univ.image f = p.1.support.toFinset :=
    Finset.eq_of_subset_of_card_le hsubImage (by omega)
  let I : Finset (Fin 5) := Finset.univ.filter (fun i ↦ f i ∈ T)
  have hTI : T = I.image f := by
    ext v
    constructor
    · intro hv
      have hvImage : v ∈ Finset.univ.image f := by
        rw [himage]
        exact hTsub hv
      obtain ⟨i, _, hfi⟩ := Finset.mem_image.mp hvImage
      exact Finset.mem_image.mpr ⟨i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfi ▸ hv⟩, hfi⟩
    · intro hv
      obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hv
      exact hfi ▸ (Finset.mem_filter.mp hi).2
  have hIcard : 3 ≤ I.card := by
    have hc : T.card = I.card := by
      rw [hTI, Finset.card_image_of_injective _ hf]
    omega
  obtain ⟨i, hi, hinext⟩ := fin5_three_contains_cycle_neighbors I hIcard
  exact ⟨i, (Finset.mem_filter.mp hi).2,
    (Finset.mem_filter.mp hinext).2⟩

/-- A color not used twice inside the fixed five-chain has two boundary
edges based at consecutive vertices of its underlying five-cycle. -/
theorem unsaturated_color_has_adjacent_external_vertices
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {c : Fin k}
    (hnot : ¬∃ r s, r ≠ s ∧
      r ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      s ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      color r = c ∧ color s = c) :
    ∃ i : Fin 5,
      (∃ g, g ∈ F.erase e ∧ G.Inc (p.1.getVert i.val) g ∧
        color g = c ∧
        g ∉ G.internalEdges (F.erase e) p.1.support.toFinset) ∧
      (∃ h, h ∈ F.erase e ∧ G.Inc (p.1.getVert (i + 1).val) h ∧
        color h = c ∧
        h ∉ G.internalEdges (F.erase e) p.1.support.toFinset) := by
  have hpresent := G.present_at_every_fivePath_vertex_of_not_two_internal_edges
    hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold hnot
  have hpCard : p.1.support.toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup p.property.support_nodup,
      p.1.length_support, hpLen]
  obtain ⟨T, hTsub, hTcard, hText⟩ :=
    G.three_external_vertices_of_present_unsaturated_color hpCard
      (by intro v hv; exact hpresent v (by simpa using hv)) hnot
  obtain ⟨i, hi, hinext⟩ :=
    G.fivePath_three_vertices_have_cycle_neighbor_pair
      p hpLen T hTsub hTcard
  exact ⟨i, hText _ hi, hText _ hinext⟩

end WeightedEdgeColoring.WeightedMultigraph
