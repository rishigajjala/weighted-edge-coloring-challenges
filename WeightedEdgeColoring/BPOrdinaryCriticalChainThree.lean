import WeightedEdgeColoring.BPOrdinaryCriticalPaletteCount

/-!
# A critical chain has three vertices in the `m = 5` range

The palette count makes the chain shorter than five vertices.  A critical
chain cannot have one edge: its only edge would have one of the two colours
missing at an endpoint.  It also cannot have three edges: properness makes
the two colours alternate, so the last edge again has the colour missing at
its endpoint.  Hence the chain has two edges and three vertices.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Two selected edges incident with `v` and leading to different other
endpoints receive different colours in a proper edge colouring. -/
theorem color_ne_of_isProperOn_of_incident_otherEndpoints_ne
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    (hproper : G.IsProperOn F color)
    {u v w : G.V} (hvu : v ≠ u) (hvw : v ≠ w) (huw : u ≠ w)
    {g r : G.E}
    (hgF : g ∈ F) (hrF : r ∈ F)
    (hgv : G.Inc v g) (hgu : G.Inc u g)
    (hrv : G.Inc v r) (hrw : G.Inc w r) :
    color g ≠ color r := by
  intro hsame
  have hgmem : g ∈ (F.filter (G.Inc v) : Set G.E) :=
    Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgv⟩)
  have hrmem : r ∈ (F.filter (G.Inc v) : Set G.E) :=
    Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hrv⟩)
  have hgr : g = r := hproper v hgmem hrmem hsame
  have hguOther : G.kempeOtherEndpoint v g = u :=
    G.kempeOtherEndpoint_eq_of_incident hgv hgu hvu
  have hrwOther : G.kempeOtherEndpoint v r = w :=
    G.kempeOtherEndpoint_eq_of_incident hrv hrw hvw
  apply huw
  calc
    u = G.kempeOtherEndpoint v g := hguOther.symm
    _ = G.kempeOtherEndpoint v r := by rw [hgr]
    _ = w := hrwOther

/-- The two endpoints of a critical chain are not adjacent in their
two-colour graph. -/
theorem not_adj_critical_endpoints_twoColorGraph
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e)) :
    ¬(G.twoColorGraph (F.erase e) color a b).Adj
      (G.fst e) (G.snd e) := by
  intro hxy
  rcases G.exists_twoColorWitnessEdge (F.erase e) color a b hxy with
    ⟨g, hgF, hgx, hgy, hga | hgb⟩
  · exact (G.color_ne_of_mem_missingColorsAt
      (F.erase e) color (G.fst e) a ha hgF hgx) hga
  · exact (G.color_ne_of_mem_missingColorsAt
      (F.erase e) color (G.snd e) b hb hgF hgy) hgb

/-- A critical two-colour endpoint path cannot have three edges. -/
theorem criticalPath_length_ne_three
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) :
    p.1.length ≠ 3 := by
  intro hlen
  let z := p.1.getVert 1
  let w := p.1.getVert 2
  have h0 : 0 < p.1.length := by omega
  have h1 : 1 < p.1.length := by omega
  have h2 : 2 < p.1.length := by omega
  have hxz : (G.twoColorGraph (F.erase e) color a b).Adj
      (G.fst e) z := by
    simpa [z] using p.1.adj_getVert_succ (i := 0) h0
  have hzw : (G.twoColorGraph (F.erase e) color a b).Adj z w := by
    simpa [z, w] using p.1.adj_getVert_succ (i := 1) h1
  have hend : p.1.getVert 3 = G.snd e := by
    simpa [hlen] using p.1.getVert_length
  have hwy : (G.twoColorGraph (F.erase e) color a b).Adj
      w (G.snd e) := by
    simpa [w, hend] using p.1.adj_getVert_succ (i := 2) h2
  have hxw : G.fst e ≠ w := by
    intro hxw
    have hverts : p.1.getVert 0 = p.1.getVert 2 := by
      simpa [w] using hxw
    have hidx : (0 : ℕ) = 2 := p.property.getVert_injOn
      (by simp [hlen]) (by simp [hlen]) hverts
    omega
  have hzy : z ≠ G.snd e := by
    intro hzy
    have hverts : p.1.getVert 1 = p.1.getVert 3 := by
      simpa [z, hend] using hzy
    have hidx : (1 : ℕ) = 3 := p.property.getVert_injOn
      (by simp [hlen]) (by simp [hlen]) hverts
    omega
  rcases G.exists_twoColorWitnessEdge
      (F.erase e) color a b hxz with
    ⟨g₁, hg₁F, hg₁x, hg₁z, hg₁color⟩
  rcases G.exists_twoColorWitnessEdge
      (F.erase e) color a b hzw with
    ⟨g₂, hg₂F, hg₂z, hg₂w, hg₂color⟩
  rcases G.exists_twoColorWitnessEdge
      (F.erase e) color a b hwy with
    ⟨g₃, hg₃F, hg₃w, hg₃y, hg₃color⟩
  have hg₁neA : color g₁ ≠ a :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase e) color (G.fst e) a ha hg₁F hg₁x
  have hg₁B : color g₁ = b := hg₁color.resolve_left hg₁neA
  have hg₃neB : color g₃ ≠ b :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase e) color (G.snd e) b hb hg₃F hg₃y
  have hg₃A : color g₃ = a := hg₃color.resolve_right hg₃neB
  have hg₁g₂ : color g₁ ≠ color g₂ :=
    G.color_ne_of_isProperOn_of_incident_otherEndpoints_ne hproper
      hxz.ne.symm hzw.ne hxw hg₁F hg₂F hg₁z hg₁x hg₂z hg₂w
  have hg₂neB : color g₂ ≠ b := by
    intro hg₂B
    exact hg₁g₂ (hg₁B.trans hg₂B.symm)
  have hg₂A : color g₂ = a := hg₂color.resolve_right hg₂neB
  have hg₂g₃ : color g₂ ≠ color g₃ :=
    G.color_ne_of_isProperOn_of_incident_otherEndpoints_ne hproper
      hzw.ne.symm hwy.ne hzy hg₂F hg₃F hg₂w hg₂z hg₃w hg₃y
  exact hg₂g₃ (hg₂A.trans hg₃A.symm)

/-- Under the strict `m = 5` degree threshold, every critical chain has
exactly three vertices. -/
theorem criticalPath_support_card_eq_three
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
    p.1.support.toFinset.card = 3 := by
  have hcardLt := G.criticalPath_support_card_lt_five
    hcritical heF hproper ha hb p hdk hdegree hthreshold
  have hcardLength : p.1.support.toFinset.card = p.1.support.length :=
    List.toFinset_card_of_nodup p.property.support_nodup
  have hlengthSupport : p.1.support.length = p.1.length + 1 :=
    p.1.length_support
  have hlengthLt : p.1.length < 4 := by omega
  have hlengthPos : 0 < p.1.length := by
    by_contra hzero
    have hlen0 : p.1.length = 0 := by omega
    exact G.noLoop e (SimpleGraph.Walk.eq_of_length_eq_zero hlen0)
  have hlengthNeOne : p.1.length ≠ 1 := by
    intro hone
    exact G.not_adj_critical_endpoints_twoColorGraph
      hcritical heF hproper ha hb
        (SimpleGraph.Walk.adj_of_length_eq_one hone)
  have hlengthNeThree : p.1.length ≠ 3 :=
    G.criticalPath_length_ne_three hcritical heF hproper ha hb p
  have hlength : p.1.length = 2 := by omega
  omega

/-- Equivalent edge-length form of the preceding three-vertex result. -/
theorem criticalPath_length_eq_two
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
    p.1.length = 2 := by
  have hcard := G.criticalPath_support_card_eq_three
    hcritical heF hproper ha hb p hdk hdegree hthreshold
  have hcardLength : p.1.support.toFinset.card = p.1.support.length :=
    List.toFinset_card_of_nodup p.property.support_nodup
  have hlengthSupport : p.1.support.length = p.1.length + 1 :=
    p.1.length_support
  omega

end WeightedMultigraph
end WeightedEdgeColoring
