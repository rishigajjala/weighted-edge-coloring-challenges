import WeightedEdgeColoring.SubtwoOrdinaryFans
import WeightedEdgeColoring.SubtwoOrdinaryChainSeven
import WeightedEdgeColoring.BPOrdinaryCriticalPaletteDisjoint
import WeightedEdgeColoring.BPOrdinaryCriticalSwitch
import WeightedEdgeColoring.BPOrdinaryCriticalTriangle

/-!
# Andersen's union of critical chains

The first and last internal vertices of any critical endpoint path lie in
one-step fans at opposite ends of the omitted edge. Missing colors at an
internal chain vertex are absent from *all* missing colors at both endpoints.
These are the geometric and palette facts used when switching between two
different critical chains.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- The first internal vertex of a critical path is in the one-step fan
at the first endpoint. -/
theorem criticalPath_first_inOneStepFan
    {F : Finset G.E} {k : ℕ}
    {e : G.E} {color : G.E → Fin k}
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hlen : 2 ≤ p.1.length) :
    G.InOneStepFan F e color (G.fst e) (G.snd e)
      (p.1.getVert 1) := by
  let z := p.1.getVert 1
  have hadj : (G.twoColorGraph (F.erase e) color a b).Adj
      (G.fst e) z := by
    simpa [z] using p.1.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g, hgF, hgx, hgz, hgcol⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) color a b hadj
  have hne : color g ≠ a :=
    G.color_ne_of_mem_missingColorsAt (F.erase e) color
      (G.fst e) a ha hgF hgx
  have hgb : color g = b := hgcol.resolve_left hne
  refine ⟨hadj.ne.symm, Or.inr ⟨g, hgF, hgx, hgz, ?_⟩⟩
  rw [hgb]
  exact hb

/-- The last internal vertex lies in the opposite one-step fan. -/
theorem criticalPath_last_inOneStepFan
    {F : Finset G.E} {k : ℕ}
    {e : G.E} {color : G.E → Fin k}
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hlen : 2 ≤ p.1.length) :
    G.InOneStepFan F e color (G.snd e) (G.fst e)
      (p.1.getVert (p.1.length - 1)) := by
  let z := p.1.getVert (p.1.length - 1)
  have hend : p.1.length - 1 + 1 = p.1.length := by omega
  have hadj : (G.twoColorGraph (F.erase e) color a b).Adj
      z (G.snd e) := by
    simpa [z, hend] using
      p.1.adj_getVert_succ (i := p.1.length - 1) (by omega)
  obtain ⟨g, hgF, hgz, hgy, hgcol⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) color a b hadj
  have hne : color g ≠ b :=
    G.color_ne_of_mem_missingColorsAt (F.erase e) color
      (G.snd e) b hb hgF hgy
  have hga : color g = a := hgcol.resolve_right hne
  refine ⟨hadj.ne, Or.inr ⟨g, hgF, hgy, hgz, ?_⟩⟩
  rw [hga]
  exact ha

theorem criticalPath_first_internal
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    {a b : Fin k}
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hlen : 2 ≤ p.1.length) :
    p.1.getVert 1 ∈ p.1.support ∧
      p.1.getVert 1 ≠ G.fst e ∧
      p.1.getVert 1 ≠ G.snd e := by
  refine ⟨p.1.getVert_mem_support 1, ?_, ?_⟩
  · have h := p.property.getVert_injOn
      (show 1 ∈ Set.Iic p.1.length by exact Set.mem_Iic.mpr (by omega))
      (show 0 ∈ Set.Iic p.1.length by simp)
    intro heq
    have hz : (1 : ℕ) = 0 := h (by simpa using heq)
    omega
  · have h := p.property.getVert_injOn
      (show 1 ∈ Set.Iic p.1.length by exact Set.mem_Iic.mpr (by omega))
      (show p.1.length ∈ Set.Iic p.1.length by simp)
    intro heq
    have hz : 1 = p.1.length := h (by simpa using heq)
    omega

theorem criticalPath_last_internal
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    {a b : Fin k}
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hlen : 2 ≤ p.1.length) :
    p.1.getVert (p.1.length - 1) ∈ p.1.support ∧
      p.1.getVert (p.1.length - 1) ≠ G.fst e ∧
      p.1.getVert (p.1.length - 1) ≠ G.snd e := by
  refine ⟨p.1.getVert_mem_support _, ?_, ?_⟩
  · have h := p.property.getVert_injOn
      (show p.1.length - 1 ∈ Set.Iic p.1.length by
        exact Set.mem_Iic.mpr (by omega))
      (show 0 ∈ Set.Iic p.1.length by simp)
    intro heq
    have hz : p.1.length - 1 = 0 := h (by simpa using heq)
    omega
  · have h := p.property.getVert_injOn
      (show p.1.length - 1 ∈ Set.Iic p.1.length by
        exact Set.mem_Iic.mpr (by omega))
      (show p.1.length ∈ Set.Iic p.1.length by simp)
    intro heq
    have hz : p.1.length - 1 = p.1.length := h (by simpa using heq)
    omega

/-- A two-edge critical path has a unique internal vertex. -/
theorem criticalPath_internal_eq_first_of_length_two
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    {a b : Fin k}
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hlen : p.1.length = 2)
    {z : G.V} (hz : z ∈ p.1.support)
    (hzx : z ≠ G.fst e) (hzy : z ≠ G.snd e) :
    z = p.1.getVert 1 := by
  classical
  let u := p.1.getVert 1
  have hu := G.criticalPath_first_internal p (by omega)
  have hxy : G.fst e ≠ G.snd e := G.noLoop e
  have hux : u ≠ G.fst e := hu.2.1
  have huy : u ≠ G.snd e := hu.2.2
  have hthree : ({G.fst e, u, G.snd e} : Finset G.V).card = 3 := by
    simp [hux.symm, huy, hxy]
  have hsubset : ({G.fst e, u, G.snd e} : Finset G.V) ⊆
      p.1.support.toFinset := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · simp only [List.mem_toFinset]
      exact p.1.start_mem_support
    · simp only [List.mem_toFinset]
      exact hu.1
    · simp only [List.mem_toFinset]
      exact p.1.end_mem_support
  have hcard : p.1.support.toFinset.card = 3 := by
    rw [List.toFinset_card_of_nodup p.property.support_nodup,
      p.1.length_support, hlen]
  have heq : ({G.fst e, u, G.snd e} : Finset G.V) =
      p.1.support.toFinset :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)
  have hzThree : z ∈ ({G.fst e, u, G.snd e} : Finset G.V) := by
    rw [heq]
    simpa using hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzThree
  rcases hzThree with h | h | h
  · exact False.elim (hzx h)
  · exact h
  · exact False.elim (hzy h)

/-- Two different internal chain vertices force at least one distinct
pair among the first/last fan neighbors of the two chains. -/
theorem criticalPaths_have_distinct_fan_neighbors
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    {a b c d : Fin k}
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (q : (G.twoColorGraph (F.erase e) color c d).Path
      (G.fst e) (G.snd e))
    (hpLen : 2 ≤ p.1.length) (hqLen : 2 ≤ q.1.length)
    {u v : G.V}
    (hu : u ∈ p.1.support) (hv : v ∈ q.1.support)
    (hux : u ≠ G.fst e) (huy : u ≠ G.snd e)
    (hvx : v ≠ G.fst e) (hvy : v ≠ G.snd e)
    (huv : u ≠ v) :
    p.1.getVert 1 ≠ q.1.getVert 1 ∨
      p.1.getVert 1 ≠ q.1.getVert (q.1.length - 1) ∨
      p.1.getVert (p.1.length - 1) ≠ q.1.getVert 1 := by
  by_cases h11 : p.1.getVert 1 ≠ q.1.getVert 1
  · exact Or.inl h11
  by_cases h1l : p.1.getVert 1 ≠ q.1.getVert (q.1.length - 1)
  · exact Or.inr (Or.inl h1l)
  by_cases hl1 : p.1.getVert (p.1.length - 1) ≠ q.1.getVert 1
  · exact Or.inr (Or.inr hl1)
  have hpeq : p.1.getVert 1 = p.1.getVert (p.1.length - 1) :=
    (not_ne_iff.mp h11).trans (not_ne_iff.mp hl1).symm
  have hqeq : q.1.getVert 1 = q.1.getVert (q.1.length - 1) :=
    (not_ne_iff.mp h11).symm.trans (not_ne_iff.mp h1l)
  have hpIndex := p.property.getVert_injOn
    (show 1 ∈ Set.Iic p.1.length by exact Set.mem_Iic.mpr (by omega))
    (show p.1.length - 1 ∈ Set.Iic p.1.length by
      exact Set.mem_Iic.mpr (by omega)) hpeq
  have hqIndex := q.property.getVert_injOn
    (show 1 ∈ Set.Iic q.1.length by exact Set.mem_Iic.mpr (by omega))
    (show q.1.length - 1 ∈ Set.Iic q.1.length by
      exact Set.mem_Iic.mpr (by omega)) hqeq
  have hpTwo : p.1.length = 2 := by omega
  have hqTwo : q.1.length = 2 := by omega
  have hueq := G.criticalPath_internal_eq_first_of_length_two
    p hpTwo hu hux huy
  have hveq := G.criticalPath_internal_eq_first_of_length_two
    q hqTwo hv hvx hvy
  have hUV : u = v := hueq.trans ((not_ne_iff.mp h11).trans hveq.symm)
  exact False.elim (huv hUV)

/-- A color missing at an internal chain vertex is excluded from the
entire endpoint palettes, not only from the two colors defining that chain. -/
theorem criticalPath_internal_missing_away_endpoints
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hdegree : ∀ z, G.degreeOn (F.erase e) z < k)
    {z : G.V} (hz : z ∈ p.1.support)
    (hzx : z ≠ G.fst e) (hzy : z ≠ G.snd e)
    {c : Fin k} (hzc : c ∈ G.missingColorsAt (F.erase e) color z) :
    c ∉ G.missingColorsAt (F.erase e) color (G.fst e) ∧
      c ∉ G.missingColorsAt (F.erase e) color (G.snd e) := by
  constructor
  · intro hxc
    have hdis := G.disjoint_missingColorsAt_of_mem_criticalPath_support
      hcritical heF hproper ha hb p hdegree
      hz p.1.start_mem_support hzx
    exact (Finset.disjoint_left.mp hdis) hzc hxc
  · intro hyc
    have hdis := G.disjoint_missingColorsAt_of_mem_criticalPath_support
      hcritical heF hproper ha hb p hdegree
      hz p.1.end_mem_support hzy
    exact (Finset.disjoint_left.mp hdis) hzc hyc

/-- Switching two colors absent from the endpoint missing palettes keeps
every endpoint color missing and every endpoint-defined two-color chain. -/
theorem exists_propagating_switch_preserving_endpoint_chains
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {c f : Fin k} {u v z : G.V}
    (huv : u ≠ v) (huz : u ≠ z) (hvz : v ≠ z)
    (huc : c ∈ G.missingColorsAt (F.erase e) color u)
    (hvc : c ∈ G.missingColorsAt (F.erase e) color v)
    (hzf : f ∈ G.missingColorsAt (F.erase e) color z)
    (hzc : c ∉ G.missingColorsAt (F.erase e) color z)
    (hcx : c ∉ G.missingColorsAt (F.erase e) color (G.fst e))
    (hcy : c ∉ G.missingColorsAt (F.erase e) color (G.snd e))
    (hfx : f ∉ G.missingColorsAt (F.erase e) color (G.fst e))
    (hfy : f ∉ G.missingColorsAt (F.erase e) color (G.snd e)) :
    ∃ switched : G.E → Fin k,
      G.IsProperOn (F.erase e) switched ∧
      c ∈ G.missingColorsAt (F.erase e) switched z ∧
      (c ∈ G.missingColorsAt (F.erase e) switched u ∨
        c ∈ G.missingColorsAt (F.erase e) switched v) ∧
      (∀ a ∈ G.missingColorsAt (F.erase e) color (G.fst e),
        a ∈ G.missingColorsAt (F.erase e) switched (G.fst e)) ∧
      (∀ b ∈ G.missingColorsAt (F.erase e) color (G.snd e),
        b ∈ G.missingColorsAt (F.erase e) switched (G.snd e)) ∧
      (∀ a ∈ G.missingColorsAt (F.erase e) color (G.fst e),
        ∀ b ∈ G.missingColorsAt (F.erase e) color (G.snd e),
          G.twoColorGraph (F.erase e) switched a b =
            G.twoColorGraph (F.erase e) color a b) := by
  obtain ⟨switched, hproper', hzc', hcommon, hfixed, hgraph⟩ :=
    G.exists_kempeSwitch_propagating_common_missingColor
      hproper huv huz hvz huc hvc hzf hzc
  refine ⟨switched, hproper', hzc', hcommon, ?_, ?_, ?_⟩
  · intro a ha
    apply (hfixed a (G.fst e) (by
      intro h; subst a; exact hcx ha) (by
      intro h; subst a; exact hfx ha)).mpr
    exact ha
  · intro b hb
    apply (hfixed b (G.snd e) (by
      intro h; subst b; exact hcy hb) (by
      intro h; subst b; exact hfy hb)).mpr
    exact hb
  · intro a ha b hb
    apply hgraph a b
    · intro h; subst a; exact hcx ha
    · intro h; subst a; exact hfx ha
    · intro h; subst b; exact hcy hb
    · intro h; subst b; exact hfy hb

/-- Transport a fixed critical path when a switch leaves its two-color
graph unchanged. Its walk, support, and indexed vertices stay the same. -/
noncomputable def pathCast
    {H J : SimpleGraph G.V} (h : J = H)
    {x y : G.V} (p : H.Path x y) : J.Path x y :=
  h.symm ▸ p

theorem pathCast_support
    {H J : SimpleGraph G.V} (h : J = H)
    {x y : G.V} (p : H.Path x y) :
    (G.pathCast h p).1.support = p.1.support := by
  cases h
  rfl

theorem pathCast_getVert
    {H J : SimpleGraph G.V} (h : J = H)
    {x y : G.V} (p : H.Path x y) (i : ℕ) :
    (G.pathCast h p).1.getVert i = p.1.getVert i := by
  cases h
  rfl

theorem pathCast_length
    {H J : SimpleGraph G.V} (h : J = H)
    {x y : G.V} (p : H.Path x y) :
    (G.pathCast h p).1.length = p.1.length := by
  cases h
  rfl

noncomputable def criticalPathOfTwoColorGraphEq
    {F : Finset G.E} {k : ℕ} {e : G.E}
    {color color' : G.E → Fin k} {a b : Fin k}
    (hgraph : G.twoColorGraph (F.erase e) color' a b =
      G.twoColorGraph (F.erase e) color a b)
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) :
    (G.twoColorGraph (F.erase e) color' a b).Path
      (G.fst e) (G.snd e) :=
  G.pathCast hgraph p

theorem criticalPathOfTwoColorGraphEq_support
    {F : Finset G.E} {k : ℕ} {e : G.E}
    {color color' : G.E → Fin k} {a b : Fin k}
    (hgraph : G.twoColorGraph (F.erase e) color' a b =
      G.twoColorGraph (F.erase e) color a b)
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) :
    (G.criticalPathOfTwoColorGraphEq hgraph p).1.support =
      p.1.support := by
  exact G.pathCast_support hgraph p

theorem criticalPathOfTwoColorGraphEq_getVert
    {F : Finset G.E} {k : ℕ} {e : G.E}
    {color color' : G.E → Fin k} {a b : Fin k}
    (hgraph : G.twoColorGraph (F.erase e) color' a b =
      G.twoColorGraph (F.erase e) color a b)
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (i : ℕ) :
    (G.criticalPathOfTwoColorGraphEq hgraph p).1.getVert i =
      p.1.getVert i := by
  exact G.pathCast_getVert hgraph p i

theorem criticalPathOfTwoColorGraphEq_length
    {F : Finset G.E} {k : ℕ} {e : G.E}
    {color color' : G.E → Fin k} {a b : Fin k}
    (hgraph : G.twoColorGraph (F.erase e) color' a b =
      G.twoColorGraph (F.erase e) color a b)
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) :
    (G.criticalPathOfTwoColorGraphEq hgraph p).1.length =
      p.1.length := by
  exact G.pathCast_length hgraph p

def InCriticalPathFan
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    {a b : Fin k}
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (z : G.V) : Prop :=
  z = p.1.getVert 1 ∨ z = p.1.getVert (p.1.length - 1)

theorem inCriticalPathFan_of_graph_eq
    {F : Finset G.E} {k : ℕ} {e : G.E}
    {color color' : G.E → Fin k} {a b : Fin k}
    (hgraph : G.twoColorGraph (F.erase e) color' a b =
      G.twoColorGraph (F.erase e) color a b)
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) {z : G.V}
    (hz : G.InCriticalPathFan p z) :
    G.InCriticalPathFan (G.criticalPathOfTwoColorGraphEq hgraph p) z := by
  rcases hz with hz | hz
  · left
    rw [hz, G.criticalPathOfTwoColorGraphEq_getVert]
  · right
    rw [hz, G.criticalPathOfTwoColorGraphEq_length,
      G.criticalPathOfTwoColorGraphEq_getVert]

theorem criticalPathFan_in_oneStepFan_or_opposite
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hlen : 2 ≤ p.1.length)
    {z : G.V} (hz : G.InCriticalPathFan p z) :
    G.InOneStepFan F e color (G.fst e) (G.snd e) z ∨
      G.InOneStepFan F e color (G.snd e) (G.fst e) z := by
  rcases hz with rfl | rfl
  · exact Or.inl (G.criticalPath_first_inOneStepFan ha hb p hlen)
  · exact Or.inr (G.criticalPath_last_inOneStepFan ha hb p hlen)

/-- Any two distinct first/last chain neighbors have disjoint missing
palettes, whether their fans are centered at the same or opposite endpoints. -/
theorem disjoint_missingColorsAt_of_two_chain_fan_neighbors
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {z w : G.V} (hzw : z ≠ w)
    (hz : G.InOneStepFan F e color (G.fst e) (G.snd e) z ∨
      G.InOneStepFan F e color (G.snd e) (G.fst e) z)
    (hw : G.InOneStepFan F e color (G.fst e) (G.snd e) w ∨
      G.InOneStepFan F e color (G.snd e) (G.fst e) w)
    (hxcard : 1 < (G.missingColorsAt (F.erase e) color (G.fst e)).card)
    (hycard : 1 < (G.missingColorsAt (F.erase e) color (G.snd e)).card)
    (hxdegree : G.degreeOn (F.erase e) (G.fst e) < k)
    (hydegree : G.degreeOn (F.erase e) (G.snd e) < k) :
    Disjoint (G.missingColorsAt (F.erase e) color z)
      (G.missingColorsAt (F.erase e) color w) := by
  have hxy : G.fst e ≠ G.snd e := G.noLoop e
  have hxmissing : (G.missingColorsAt (F.erase e) color (G.fst e)).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hymissing : (G.missingColorsAt (F.erase e) color (G.snd e)).Nonempty :=
    Finset.card_pos.mp (by omega)
  rcases hz with hz | hz <;> rcases hw with hw | hw
  · exact G.disjoint_missingColorsAt_of_oneStepFan hcritical heF hproper
      hxy (Or.inl rfl) (Or.inr rfl) hz hw hzw hxmissing
  · exact G.disjoint_missingColorsAt_of_opposite_oneStepFans
      hcritical heF hproper hxy (Or.inl rfl) (Or.inr rfl)
      hz hw hzw hxcard hydegree
  · exact G.disjoint_missingColorsAt_of_opposite_oneStepFans
      hcritical heF hproper hxy.symm (Or.inr rfl) (Or.inl rfl)
      hz hw hzw hycard hxdegree
  · exact G.disjoint_missingColorsAt_of_oneStepFan hcritical heF hproper
      hxy.symm (Or.inr rfl) (Or.inl rfl) hz hw hzw hymissing

/-- Move a common missing color from a chain vertex `u` to another
internal vertex `z` while retaining it at an external vertex `v`.
The switch preserves all endpoint-defined critical chains. -/
theorem exists_switch_moving_common_missing_to_chain_vertex
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hdegree : ∀ t, G.degreeOn (F.erase e) t < k)
    {u v z : G.V}
    (hu : u ∈ p.1.support) (hz : z ∈ p.1.support)
    (hux : u ≠ G.fst e) (huy : u ≠ G.snd e)
    (hzx : z ≠ G.fst e) (hzy : z ≠ G.snd e)
    (huv : u ≠ v) (huz : u ≠ z) (hvz : v ≠ z)
    {c : Fin k}
    (huc : c ∈ G.missingColorsAt (F.erase e) color u)
    (hvc : c ∈ G.missingColorsAt (F.erase e) color v) :
    ∃ switched : G.E → Fin k,
      G.IsProperOn (F.erase e) switched ∧
      (∀ α ∈ G.missingColorsAt (F.erase e) color (G.fst e),
        α ∈ G.missingColorsAt (F.erase e) switched (G.fst e)) ∧
      (∀ β ∈ G.missingColorsAt (F.erase e) color (G.snd e),
        β ∈ G.missingColorsAt (F.erase e) switched (G.snd e)) ∧
      (∀ α ∈ G.missingColorsAt (F.erase e) color (G.fst e),
        ∀ β ∈ G.missingColorsAt (F.erase e) color (G.snd e),
          G.twoColorGraph (F.erase e) switched α β =
            G.twoColorGraph (F.erase e) color α β) ∧
      c ∈ G.missingColorsAt (F.erase e) switched z ∧
      c ∈ G.missingColorsAt (F.erase e) switched v := by
  have hcxcy := G.criticalPath_internal_missing_away_endpoints
    hcritical heF hproper ha hb p hdegree hu hux huy huc
  have hdis := G.disjoint_missingColorsAt_of_mem_criticalPath_support
    hcritical heF hproper ha hb p hdegree hu hz huz
  have hzc : c ∉ G.missingColorsAt (F.erase e) color z := by
    intro hzc
    exact (Finset.disjoint_left.mp hdis) huc hzc
  obtain ⟨f, hzf⟩ :=
    G.exists_mem_missingColorsAt_of_degreeOn_lt hproper (hdegree z)
  have hfxfy := G.criticalPath_internal_missing_away_endpoints
    hcritical heF hproper ha hb p hdegree hz hzx hzy hzf
  obtain ⟨switched, hp', hzc', hcommon, hkeepX, hkeepY, hgraph⟩ :=
    G.exists_propagating_switch_preserving_endpoint_chains
      hproper huv huz hvz huc hvc hzf hzc
      hcxcy.1 hcxcy.2 hfxfy.1 hfxfy.2
  have ha' := hkeepX a ha
  have hb' := hkeepY b hb
  have hgraphab := hgraph a ha b hb
  let p' := G.criticalPathOfTwoColorGraphEq hgraphab p
  have hu' : u ∈ p'.1.support := by
    rw [G.criticalPathOfTwoColorGraphEq_support]
    exact hu
  have hz' : z ∈ p'.1.support := by
    rw [G.criticalPathOfTwoColorGraphEq_support]
    exact hz
  have hvc' : c ∈ G.missingColorsAt (F.erase e) switched v := by
    rcases hcommon with huc' | hvc'
    · have hdis' := G.disjoint_missingColorsAt_of_mem_criticalPath_support
        hcritical heF hp' ha' hb' p' hdegree hu' hz' huz
      exact False.elim ((Finset.disjoint_left.mp hdis') huc' hzc')
    · exact hvc'
  exact ⟨switched, hp', hkeepX, hkeepY, hgraph, hzc', hvc'⟩

/-- The distinct first/last neighbors extracted from two chains. -/
theorem criticalPaths_exist_distinct_fan_anchors
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    {a b c d : Fin k}
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (q : (G.twoColorGraph (F.erase e) color c d).Path
      (G.fst e) (G.snd e))
    (hpLen : 2 ≤ p.1.length) (hqLen : 2 ≤ q.1.length)
    {u v : G.V}
    (hu : u ∈ p.1.support) (hv : v ∈ q.1.support)
    (hux : u ≠ G.fst e) (huy : u ≠ G.snd e)
    (hvx : v ≠ G.fst e) (hvy : v ≠ G.snd e)
    (huv : u ≠ v) :
    ∃ z w : G.V, G.InCriticalPathFan p z ∧
      G.InCriticalPathFan q w ∧ z ≠ w ∧
      z ∈ p.1.support ∧ w ∈ q.1.support ∧
      z ≠ G.fst e ∧ z ≠ G.snd e ∧
      w ≠ G.fst e ∧ w ≠ G.snd e := by
  obtain h | h | h := G.criticalPaths_have_distinct_fan_neighbors
    p q hpLen hqLen hu hv hux huy hvx hvy huv
  · obtain ⟨hz, hzx, hzy⟩ := G.criticalPath_first_internal p hpLen
    obtain ⟨hw, hwx, hwy⟩ := G.criticalPath_first_internal q hqLen
    exact ⟨_, _, Or.inl rfl, Or.inl rfl, h, hz, hw, hzx, hzy, hwx, hwy⟩
  · obtain ⟨hz, hzx, hzy⟩ := G.criticalPath_first_internal p hpLen
    obtain ⟨hw, hwx, hwy⟩ := G.criticalPath_last_internal q hqLen
    exact ⟨_, _, Or.inl rfl, Or.inr rfl, h, hz, hw, hzx, hzy, hwx, hwy⟩
  · obtain ⟨hz, hzx, hzy⟩ := G.criticalPath_last_internal p hpLen
    obtain ⟨hw, hwx, hwy⟩ := G.criticalPath_first_internal q hqLen
    exact ⟨_, _, Or.inr rfl, Or.inl rfl, h, hz, hw, hzx, hzy, hwx, hwy⟩

/-- The same color migration also covers the case where the chosen fan
neighbor already is the vertex carrying the missing color. -/
theorem exists_move_common_missing_to_chain_vertex
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hdegree : ∀ t, G.degreeOn (F.erase e) t < k)
    {u v z : G.V}
    (hu : u ∈ p.1.support) (hz : z ∈ p.1.support)
    (hux : u ≠ G.fst e) (huy : u ≠ G.snd e)
    (hzx : z ≠ G.fst e) (hzy : z ≠ G.snd e)
    (huv : u ≠ v) (hvz : v ≠ z)
    {c : Fin k}
    (huc : c ∈ G.missingColorsAt (F.erase e) color u)
    (hvc : c ∈ G.missingColorsAt (F.erase e) color v) :
    ∃ switched : G.E → Fin k,
      G.IsProperOn (F.erase e) switched ∧
      (∀ α ∈ G.missingColorsAt (F.erase e) color (G.fst e),
        α ∈ G.missingColorsAt (F.erase e) switched (G.fst e)) ∧
      (∀ β ∈ G.missingColorsAt (F.erase e) color (G.snd e),
        β ∈ G.missingColorsAt (F.erase e) switched (G.snd e)) ∧
      (∀ α ∈ G.missingColorsAt (F.erase e) color (G.fst e),
        ∀ β ∈ G.missingColorsAt (F.erase e) color (G.snd e),
          G.twoColorGraph (F.erase e) switched α β =
            G.twoColorGraph (F.erase e) color α β) ∧
      c ∈ G.missingColorsAt (F.erase e) switched z ∧
      c ∈ G.missingColorsAt (F.erase e) switched v := by
  by_cases huz : u = z
  · subst z
    exact ⟨color, hproper, (by intros; assumption),
      (by intros; assumption), (by intros; rfl), huc, hvc⟩
  · exact G.exists_switch_moving_common_missing_to_chain_vertex
      hcritical heF hproper ha hb p hdegree hu hz hux huy hzx hzy
      huv huz hvz huc hvc

theorem criticalPath_length_at_least_two
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) : 2 ≤ p.1.length := by
  have hn : 0 < p.1.length := by
    by_contra h
    have hz : p.1.length = 0 := by omega
    exact G.noLoop e (SimpleGraph.Walk.eq_of_length_eq_zero hz)
  obtain ⟨r, hr⟩ := G.criticalPath_even_length hcritical heF hproper ha hb p
  omega

/-- Missing palettes of vertices on arbitrary endpoint critical chains
are pairwise disjoint. The two chains may use different endpoint colors. -/
theorem disjoint_missingColorsAt_of_two_criticalPaths
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c d : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hd : d ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (q : (G.twoColorGraph (F.erase e) color c d).Path
      (G.fst e) (G.snd e))
    (hdegree : ∀ t, G.degreeOn (F.erase e) t + 2 ≤ k)
    {u v : G.V} (hu : u ∈ p.1.support) (hv : v ∈ q.1.support)
    (huv : u ≠ v) :
    Disjoint (G.missingColorsAt (F.erase e) color u)
      (G.missingColorsAt (F.erase e) color v) := by
  have hdeg : ∀ t, G.degreeOn (F.erase e) t < k := by
    intro t; have h := hdegree t; omega
  by_cases hvp : v ∈ p.1.support
  · exact G.disjoint_missingColorsAt_of_mem_criticalPath_support
      hcritical heF hproper ha hb p hdeg hu hvp huv
  by_cases huq : u ∈ q.1.support
  · exact G.disjoint_missingColorsAt_of_mem_criticalPath_support
      hcritical heF hproper hc hd q hdeg huq hv huv
  rw [Finset.disjoint_left]
  intro t htu htv
  have hux : u ≠ G.fst e := by
    intro h; subst u; exact huq q.1.start_mem_support
  have huy : u ≠ G.snd e := by
    intro h; subst u; exact huq q.1.end_mem_support
  have hvx : v ≠ G.fst e := by
    intro h; subst v; exact hvp p.1.start_mem_support
  have hvy : v ≠ G.snd e := by
    intro h; subst v; exact hvp p.1.end_mem_support
  have hpLen := G.criticalPath_length_at_least_two hcritical heF hproper ha hb p
  have hqLen := G.criticalPath_length_at_least_two hcritical heF hproper hc hd q
  obtain ⟨z, w, hzFan, hwFan, hzw, hz, hw, hzx, hzy, hwx, hwy⟩ :=
    G.criticalPaths_exist_distinct_fan_anchors p q hpLen hqLen
      hu hv hux huy hvx hvy huv
  have hvz : v ≠ z := by intro h; exact hvp (h ▸ hz)
  obtain ⟨color₁, hproper₁, hkeepX₁, hkeepY₁, hgraph₁, htz₁, htv₁⟩ :=
    G.exists_move_common_missing_to_chain_vertex
      hcritical heF hproper ha hb p hdeg hu hz hux huy hzx hzy
      huv hvz htu htv
  have ha₁ := hkeepX₁ a ha
  have hb₁ := hkeepY₁ b hb
  have hc₁ := hkeepX₁ c hc
  have hd₁ := hkeepY₁ d hd
  let p₁ := G.criticalPathOfTwoColorGraphEq (hgraph₁ a ha b hb) p
  let q₁ := G.criticalPathOfTwoColorGraphEq (hgraph₁ c hc d hd) q
  have hzFan₁ : G.InCriticalPathFan p₁ z :=
    G.inCriticalPathFan_of_graph_eq (hgraph₁ a ha b hb) p hzFan
  have hwFan₁ : G.InCriticalPathFan q₁ w :=
    G.inCriticalPathFan_of_graph_eq (hgraph₁ c hc d hd) q hwFan
  have hw₁ : w ∈ q₁.1.support := by
    rw [G.criticalPathOfTwoColorGraphEq_support]; exact hw
  have hv₁ : v ∈ q₁.1.support := by
    rw [G.criticalPathOfTwoColorGraphEq_support]; exact hv
  obtain ⟨color₂, hproper₂, hkeepX₂, hkeepY₂, hgraph₂, htw₂, htz₂⟩ :=
    G.exists_move_common_missing_to_chain_vertex
      hcritical heF hproper₁ hc₁ hd₁ q₁ hdeg hv₁ hw₁ hvx hvy hwx hwy
      hvz hzw htv₁ htz₁
  let p₂ := G.criticalPathOfTwoColorGraphEq (hgraph₂ a ha₁ b hb₁) p₁
  let q₂ := G.criticalPathOfTwoColorGraphEq (hgraph₂ c hc₁ d hd₁) q₁
  have hzFan₂ : G.InCriticalPathFan p₂ z :=
    G.inCriticalPathFan_of_graph_eq (hgraph₂ a ha₁ b hb₁) p₁ hzFan₁
  have hwFan₂ : G.InCriticalPathFan q₂ w :=
    G.inCriticalPathFan_of_graph_eq (hgraph₂ c hc₁ d hd₁) q₁ hwFan₁
  have hlenp₂ : 2 ≤ p₂.1.length := by
    rw [G.criticalPathOfTwoColorGraphEq_length,
      G.criticalPathOfTwoColorGraphEq_length]; exact hpLen
  have hlenq₂ : 2 ≤ q₂.1.length := by
    rw [G.criticalPathOfTwoColorGraphEq_length,
      G.criticalPathOfTwoColorGraphEq_length]; exact hqLen
  have ha₂ := hkeepX₂ a ha₁
  have hb₂ := hkeepY₂ b hb₁
  have hc₂ := hkeepX₂ c hc₁
  have hd₂ := hkeepY₂ d hd₁
  have hxcard : 1 < (G.missingColorsAt (F.erase e) color₂ (G.fst e)).card := by
    rw [G.card_missingColorsAt (F.erase e) color₂ hproper₂]
    have h := hdegree (G.fst e); omega
  have hycard : 1 < (G.missingColorsAt (F.erase e) color₂ (G.snd e)).card := by
    rw [G.card_missingColorsAt (F.erase e) color₂ hproper₂]
    have h := hdegree (G.snd e); omega
  have hdis := G.disjoint_missingColorsAt_of_two_chain_fan_neighbors
    hcritical heF hproper₂ hzw
    (G.criticalPathFan_in_oneStepFan_or_opposite ha₂ hb₂ p₂ hlenp₂ hzFan₂)
    (G.criticalPathFan_in_oneStepFan_or_opposite hc₂ hd₂ q₂ hlenq₂ hwFan₂)
    hxcard hycard (hdeg _) (hdeg _)
  exact (Finset.disjoint_left.mp hdis) htz₂ htw₂

/-- Membership in the union of all critical endpoint chains formed from
missing colors at the two endpoints of the omitted edge. -/
def InCriticalChainUnion
    {F : Finset G.E} {k : ℕ} (e : G.E) (color : G.E → Fin k)
    (z : G.V) : Prop :=
  ∃ a b : Fin k,
    a ∈ G.missingColorsAt (F.erase e) color (G.fst e) ∧
    b ∈ G.missingColorsAt (F.erase e) color (G.snd e) ∧
    ∃ p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e), z ∈ p.1.support

noncomputable def criticalChainUnion
    {F : Finset G.E} {k : ℕ} (e : G.E) (color : G.E → Fin k) :
    Finset G.V := by
  classical
  exact Finset.univ.filter (G.InCriticalChainUnion (F := F) e color)

theorem mem_criticalChainUnion_iff
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    {z : G.V} :
    z ∈ G.criticalChainUnion (F := F) e color ↔
      G.InCriticalChainUnion (F := F) e color z := by
  classical
  simp [criticalChainUnion]

/-- The whole union has pairwise disjoint missing palettes, even though
its constituent chains may use different pairs of endpoint colors. -/
theorem criticalChainUnion_pairwise_disjoint_missingColorsAt
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    (hdegree : ∀ t, G.degreeOn (F.erase e) t + 2 ≤ k) :
    ((G.criticalChainUnion (F := F) e color : Finset G.V) : Set G.V).PairwiseDisjoint
      (G.missingColorsAt (F.erase e) color) := by
  intro u hu v hv huv
  change u ∈ G.criticalChainUnion (F := F) e color at hu
  change v ∈ G.criticalChainUnion (F := F) e color at hv
  rw [G.mem_criticalChainUnion_iff] at hu hv
  obtain ⟨a,b,ha,hb,p,hup⟩ := hu
  obtain ⟨c,d,hc,hd,q,hvq⟩ := hv
  exact G.disjoint_missingColorsAt_of_two_criticalPaths
    hcritical heF hproper ha hb hc hd p q hdegree hup hvq huv

/-- The two endpoints belong to the union whenever each has a missing
color. -/
theorem criticalChainUnion_endpoints_mem
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    (hdegree : ∀ t, G.degreeOn (F.erase e) t < k) :
    G.fst e ∈ G.criticalChainUnion (F := F) e color ∧
      G.snd e ∈ G.criticalChainUnion (F := F) e color := by
  obtain ⟨a, ha⟩ := G.exists_mem_missingColorsAt_of_degreeOn_lt
    hproper (hdegree (G.fst e))
  obtain ⟨b, hb⟩ := G.exists_mem_missingColorsAt_of_degreeOn_lt
    hproper (hdegree (G.snd e))
  obtain ⟨p, _⟩ := G.exists_criticalEndpointPath hcritical heF hproper ha hb
  constructor <;> rw [G.mem_criticalChainUnion_iff]
  · exact ⟨a,b,ha,hb,p,p.1.start_mem_support⟩
  · exact ⟨a,b,ha,hb,p,p.1.end_mem_support⟩

/-- Palette counting on the *union* of every endpoint critical chain.
The extra two colors come from deleting the omitted edge at its endpoints. -/
theorem criticalChainUnion_card_mul_sub_add_two_le
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d) :
    (G.criticalChainUnion (F := F) e color).card * (k - d) + 2 ≤ k := by
  classical
  let D := G.criticalChainUnion (F := F) e color
  let x := G.fst e
  let y := G.snd e
  let T := (D.erase x).erase y
  let palette : G.V → Finset (Fin k) :=
    fun z ↦ G.missingColorsAt (F.erase e) color z
  have hxy : x ≠ y := G.noLoop e
  have hdegreeEraseLe : ∀ z, G.degreeOn (F.erase e) z ≤ d := by
    intro z
    exact (G.degreeOn_mono_critical (Finset.erase_subset e F) z).trans
      (hdegree z)
  have hdegreeErase : ∀ z, G.degreeOn (F.erase e) z + 2 ≤ k := by
    intro z; have hz := hdegreeEraseLe z; omega
  have hdegreeEraseLt : ∀ z, G.degreeOn (F.erase e) z < k := by
    intro z; have hz := hdegreeErase z; omega
  obtain ⟨hxD, hyD⟩ := G.criticalChainUnion_endpoints_mem
    hcritical heF hproper hdegreeEraseLt
  have hpair : (D : Set G.V).PairwiseDisjoint palette := by
    simpa [D, palette] using
      G.criticalChainUnion_pairwise_disjoint_missingColorsAt
        hcritical heF hproper hdegreeErase
  have hpaletteSum : (∑ z ∈ D, (palette z).card) ≤ k := by
    have hsum : (∑ z ∈ D, (palette z).card) =
        (D.biUnion palette).card := by
      rw [← Finset.card_biUnion]
      exact hpair
    rw [hsum]
    simpa using
      (Finset.card_le_card
        (show D.biUnion palette ⊆ (Finset.univ : Finset (Fin k)) from
          fun c _ ↦ Finset.mem_univ c))
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
    have hzDegree := hdegreeEraseLe z
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

theorem criticalChainUnion_card_lt_seven
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2) :
    (G.criticalChainUnion (F := F) e color).card < 7 := by
  have hcount := G.criticalChainUnion_card_mul_sub_add_two_le
    hcritical heF hproper hdk hdegree
  by_contra hnot
  have hseven : 7 ≤ (G.criticalChainUnion (F := F) e color).card := by omega
  have hmul := Nat.mul_le_mul_right (k - d) hseven
  omega

/-- A one-step fan survives any recoloring that preserves the endpoint
missing colors and all endpoint-defined two-color graphs. -/
theorem inOneStepFan_of_preserved_endpoint_graphs
    {F : Finset G.E} {k : ℕ} {e : G.E}
    {color color' : G.E → Fin k} {x y z : G.V}
    (hfan : G.InOneStepFan F e color x y z)
    (hmissingX : (G.missingColorsAt (F.erase e) color x).Nonempty)
    (hkeepX : ∀ a ∈ G.missingColorsAt (F.erase e) color x,
      a ∈ G.missingColorsAt (F.erase e) color' x)
    (hkeepY : ∀ b ∈ G.missingColorsAt (F.erase e) color y,
      b ∈ G.missingColorsAt (F.erase e) color' y)
    (hgraph : ∀ a ∈ G.missingColorsAt (F.erase e) color x,
      ∀ b ∈ G.missingColorsAt (F.erase e) color y,
        G.twoColorGraph (F.erase e) color' a b =
          G.twoColorGraph (F.erase e) color a b) :
    G.InOneStepFan F e color' x y z := by
  obtain ⟨hzx, hzy | ⟨g, hgF, hgx, hgz, hgb⟩⟩ := hfan
  · exact ⟨hzx, Or.inl hzy⟩
  obtain ⟨a, ha⟩ := hmissingX
  have hadj : (G.twoColorGraph (F.erase e) color a (color g)).Adj x z := by
    have h := G.twoColorGraph_adj_fst_snd
      (F.erase e) color a (color g) hgF (Or.inr rfl)
    rcases hgx with hfx | hsx <;> rcases hgz with hfz | hsz
    · exact False.elim (hzx (hfx.symm.trans hfz).symm)
    · simpa [hfx, hsz] using h
    · simpa [hsx, hfz] using h.symm
    · exact False.elim (hzx (hsx.symm.trans hsz).symm)
  have hadj' : (G.twoColorGraph (F.erase e) color' a (color g)).Adj x z := by
    rw [hgraph a ha (color g) hgb]
    exact hadj
  obtain ⟨g', hgF', hgx', hgz', hgcol'⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) color' a (color g) hadj'
  have hne : color' g' ≠ a :=
    G.color_ne_of_mem_missingColorsAt (F.erase e) color' x a
      (hkeepX a ha) hgF' hgx'
  have heq : color' g' = color g := hgcol'.resolve_left hne
  exact ⟨hzx, Or.inr ⟨g', hgF', hgx', hgz', heq ▸ hkeepY (color g) hgb⟩⟩

/-- A vertex on a critical chain and a distinct vertex in either endpoint
fan have disjoint missing palettes. -/
theorem disjoint_missingColorsAt_of_criticalPath_and_fan
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hdegree : ∀ t, G.degreeOn (F.erase e) t + 2 ≤ k)
    {u v : G.V} (hu : u ∈ p.1.support)
    (hvfan : G.InOneStepFan F e color (G.fst e) (G.snd e) v ∨
      G.InOneStepFan F e color (G.snd e) (G.fst e) v)
    (huv : u ≠ v) :
    Disjoint (G.missingColorsAt (F.erase e) color u)
      (G.missingColorsAt (F.erase e) color v) := by
  have hdeg : ∀ t, G.degreeOn (F.erase e) t < k := by
    intro t; have h := hdegree t; omega
  by_cases hvp : v ∈ p.1.support
  · exact G.disjoint_missingColorsAt_of_mem_criticalPath_support
      hcritical heF hproper ha hb p hdeg hu hvp huv
  have hxcard : 1 < (G.missingColorsAt (F.erase e) color (G.fst e)).card := by
    rw [G.card_missingColorsAt (F.erase e) color hproper]
    have h := hdegree (G.fst e); omega
  have hycard : 1 < (G.missingColorsAt (F.erase e) color (G.snd e)).card := by
    rw [G.card_missingColorsAt (F.erase e) color hproper]
    have h := hdegree (G.snd e); omega
  have hxmissing : (G.missingColorsAt (F.erase e) color (G.fst e)).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hymissing : (G.missingColorsAt (F.erase e) color (G.snd e)).Nonempty :=
    Finset.card_pos.mp (by omega)
  by_cases hux : u = G.fst e
  · subst u
    have hUFan : G.InOneStepFan F e color (G.fst e) (G.snd e) (G.fst e) ∨
        G.InOneStepFan F e color (G.snd e) (G.fst e) (G.fst e) :=
      Or.inr ⟨G.noLoop e, Or.inl rfl⟩
    exact G.disjoint_missingColorsAt_of_two_chain_fan_neighbors
      hcritical heF hproper huv hUFan hvfan hxcard hycard
      (hdeg _) (hdeg _)
  by_cases huy : u = G.snd e
  · subst u
    have hUFan : G.InOneStepFan F e color (G.fst e) (G.snd e) (G.snd e) ∨
        G.InOneStepFan F e color (G.snd e) (G.fst e) (G.snd e) :=
      Or.inl ⟨(G.noLoop e).symm, Or.inl rfl⟩
    exact G.disjoint_missingColorsAt_of_two_chain_fan_neighbors
      hcritical heF hproper huv hUFan hvfan hxcard hycard
      (hdeg _) (hdeg _)
  rw [Finset.disjoint_left]
  intro t htu htv
  have hlen := G.criticalPath_length_at_least_two hcritical heF hproper ha hb p
  let z := p.1.getVert 1
  obtain ⟨hz, hzx, hzy⟩ := G.criticalPath_first_internal p hlen
  have hvz : v ≠ z := by intro h; exact hvp (h ▸ hz)
  obtain ⟨color', hproper', hkeepX, hkeepY, hgraph, htz, htv⟩ :=
    G.exists_move_common_missing_to_chain_vertex
      hcritical heF hproper ha hb p hdeg hu hz hux huy hzx hzy
      huv hvz htu htv
  have ha' := hkeepX a ha
  have hb' := hkeepY b hb
  let p' := G.criticalPathOfTwoColorGraphEq (hgraph a ha b hb) p
  have hzFan' : G.InCriticalPathFan p' z :=
    G.inCriticalPathFan_of_graph_eq (hgraph a ha b hb) p (Or.inl rfl)
  have hlen' : 2 ≤ p'.1.length := by
    rw [G.criticalPathOfTwoColorGraphEq_length]; exact hlen
  have hgraphSwap : ∀ β ∈ G.missingColorsAt (F.erase e) color (G.snd e),
      ∀ α ∈ G.missingColorsAt (F.erase e) color (G.fst e),
        G.twoColorGraph (F.erase e) color' β α =
          G.twoColorGraph (F.erase e) color β α := by
    intro β hβ α hα
    calc
      _ = G.twoColorGraph (F.erase e) color' α β :=
        G.twoColorGraph_swap color' β α
      _ = G.twoColorGraph (F.erase e) color α β := hgraph α hα β hβ
      _ = G.twoColorGraph (F.erase e) color β α :=
        (G.twoColorGraph_swap color β α).symm
  have hvfan' : G.InOneStepFan F e color' (G.fst e) (G.snd e) v ∨
      G.InOneStepFan F e color' (G.snd e) (G.fst e) v := by
    rcases hvfan with hvfan | hvfan
    · exact Or.inl (G.inOneStepFan_of_preserved_endpoint_graphs
        hvfan hxmissing hkeepX hkeepY hgraph)
    · exact Or.inr (G.inOneStepFan_of_preserved_endpoint_graphs
        hvfan hymissing hkeepY hkeepX hgraphSwap)
  have hxcard' : 1 < (G.missingColorsAt (F.erase e) color' (G.fst e)).card := by
    rw [G.card_missingColorsAt (F.erase e) color' hproper']
    have h := hdegree (G.fst e); omega
  have hycard' : 1 < (G.missingColorsAt (F.erase e) color' (G.snd e)).card := by
    rw [G.card_missingColorsAt (F.erase e) color' hproper']
    have h := hdegree (G.snd e); omega
  have hdis := G.disjoint_missingColorsAt_of_two_chain_fan_neighbors
    hcritical heF hproper' hvz.symm
    (G.criticalPathFan_in_oneStepFan_or_opposite ha' hb' p' hlen' hzFan')
    hvfan' hxcard' hycard' (hdeg _) (hdeg _)
  exact (Finset.disjoint_left.mp hdis) htz htv

/-- Andersen's set `A_X ∪ A_Y ∪ D`, with `D` the union of all critical
endpoint chains and `A_X,A_Y` the one-step fans. -/
def InCriticalNeighborhood
    {F : Finset G.E} {k : ℕ} (e : G.E) (color : G.E → Fin k)
    (z : G.V) : Prop :=
  G.InCriticalChainUnion (F := F) e color z ∨
    G.InOneStepFan F e color (G.fst e) (G.snd e) z ∨
      G.InOneStepFan F e color (G.snd e) (G.fst e) z

noncomputable def criticalNeighborhood
    {F : Finset G.E} {k : ℕ} (e : G.E) (color : G.E → Fin k) :
    Finset G.V := by
  classical
  exact Finset.univ.filter (G.InCriticalNeighborhood (F := F) e color)

theorem mem_criticalNeighborhood_iff
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    {z : G.V} :
    z ∈ G.criticalNeighborhood (F := F) e color ↔
      G.InCriticalNeighborhood (F := F) e color z := by
  classical
  simp [criticalNeighborhood]

/-- All distinct vertices in Andersen's combined critical neighborhood
have disjoint missing palettes. -/
theorem criticalNeighborhood_pairwise_disjoint_missingColorsAt
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    (hdegree : ∀ t, G.degreeOn (F.erase e) t + 2 ≤ k) :
    ((G.criticalNeighborhood (F := F) e color : Finset G.V) : Set G.V).PairwiseDisjoint
      (G.missingColorsAt (F.erase e) color) := by
  intro u hu v hv huv
  change u ∈ G.criticalNeighborhood (F := F) e color at hu
  change v ∈ G.criticalNeighborhood (F := F) e color at hv
  rw [G.mem_criticalNeighborhood_iff] at hu hv
  have hfanpair : ∀ {s t : G.V}, s ≠ t →
      (G.InOneStepFan F e color (G.fst e) (G.snd e) s ∨
        G.InOneStepFan F e color (G.snd e) (G.fst e) s) →
      (G.InOneStepFan F e color (G.fst e) (G.snd e) t ∨
        G.InOneStepFan F e color (G.snd e) (G.fst e) t) →
      Disjoint (G.missingColorsAt (F.erase e) color s)
        (G.missingColorsAt (F.erase e) color t) := by
    intro s t hst hs ht
    have hxcard : 1 < (G.missingColorsAt (F.erase e) color (G.fst e)).card := by
      rw [G.card_missingColorsAt (F.erase e) color hproper]
      have h := hdegree (G.fst e); omega
    have hycard : 1 < (G.missingColorsAt (F.erase e) color (G.snd e)).card := by
      rw [G.card_missingColorsAt (F.erase e) color hproper]
      have h := hdegree (G.snd e); omega
    exact G.disjoint_missingColorsAt_of_two_chain_fan_neighbors
      hcritical heF hproper hst hs ht hxcard hycard
      (by have h := hdegree (G.fst e); omega)
      (by have h := hdegree (G.snd e); omega)
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · obtain ⟨a,b,ha,hb,p,hup⟩ := hu
    obtain ⟨c,d,hc,hd,q,hvq⟩ := hv
    exact G.disjoint_missingColorsAt_of_two_criticalPaths
      hcritical heF hproper ha hb hc hd p q hdegree hup hvq huv
  · obtain ⟨a,b,ha,hb,p,hup⟩ := hu
    exact G.disjoint_missingColorsAt_of_criticalPath_and_fan
      hcritical heF hproper ha hb p hdegree hup hv huv
  · obtain ⟨a,b,ha,hb,q,hvq⟩ := hv
    exact (G.disjoint_missingColorsAt_of_criticalPath_and_fan
      hcritical heF hproper ha hb q hdegree hvq hu huv.symm).symm
  · exact hfanpair huv hu hv

/-- A finite set with pairwise disjoint palettes and both endpoints obeys
Andersen's cardinality inequality. -/
theorem card_mul_sub_add_two_le_of_pairwise_missingColors
    {F : Finset G.E} {k d : ℕ} {e : G.E} (heF : e ∈ F)
    {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    (hdk : d < k)
    (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (S : Finset G.V)
    (hxS : G.fst e ∈ S) (hyS : G.snd e ∈ S)
    (hpair : (S : Set G.V).PairwiseDisjoint
      (G.missingColorsAt (F.erase e) color)) :
    S.card * (k - d) + 2 ≤ k := by
  classical
  let x := G.fst e
  let y := G.snd e
  let T := (S.erase x).erase y
  let palette : G.V → Finset (Fin k) :=
    fun z ↦ G.missingColorsAt (F.erase e) color z
  have hxy : x ≠ y := G.noLoop e
  have hpaletteSum : (∑ z ∈ S, (palette z).card) ≤ k := by
    have hsum : (∑ z ∈ S, (palette z).card) =
        (S.biUnion palette).card := by
      rw [← Finset.card_biUnion]
      exact hpair
    rw [hsum]
    simpa using
      (Finset.card_le_card
        (show S.biUnion palette ⊆ (Finset.univ : Finset (Fin k)) from
          fun c _ ↦ Finset.mem_univ c))
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
      (G.degreeOn_mono_critical (Finset.erase_subset e F) z).trans
        (hdegree z)
    omega
  have hSdecomp : S = insert x (insert y T) := by
    ext z
    simp only [T, Finset.mem_insert, Finset.mem_erase]
    constructor
    · intro hzS
      by_cases hzx : z = x
      · exact Or.inl hzx
      · by_cases hzy : z = y
        · exact Or.inr (Or.inl hzy)
        · exact Or.inr (Or.inr ⟨hzy, hzx, hzS⟩)
    · rintro (rfl | rfl | ⟨_, _, hzS⟩)
      · exact hxS
      · exact hyS
      · exact hzS
  have hxT : x ∉ T := by simp [T]
  have hyT : y ∉ T := by simp [T]
  have hsumT : T.card * (k - d) ≤ ∑ z ∈ T, (palette z).card := by
    calc
      T.card * (k - d) = ∑ z ∈ T, (k - d) := by simp
      _ ≤ ∑ z ∈ T, (palette z).card :=
        Finset.sum_le_sum fun z _ ↦ hbasePalette z
  have hcardS : S.card = T.card + 2 := by
    rw [hSdecomp]
    simp [hxT, hyT, hxy, Nat.add_assoc]
  have hsumS : (∑ z ∈ S, (palette z).card) =
      (palette x).card + (palette y).card +
        ∑ z ∈ T, (palette z).card := by
    rw [hSdecomp]
    simp [hxT, hyT, hxy, Nat.add_assoc]
  have hlower : S.card * (k - d) + 2 ≤
      ∑ z ∈ S, (palette z).card := by
    rw [hsumS, hcardS]
    ring_nf
    omega
  exact hlower.trans hpaletteSum

/-- Andersen's Corollary 4 for `m=7`: every one-step fan vertex and every
vertex on any endpoint critical chain lies in a set of at most six vertices. -/
theorem criticalNeighborhood_card_lt_seven
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2) :
    (G.criticalNeighborhood (F := F) e color).card < 7 := by
  have hdegreeErase : ∀ z, G.degreeOn (F.erase e) z + 2 ≤ k := by
    intro z
    have hz := (G.degreeOn_mono_critical (Finset.erase_subset e F) z).trans
      (hdegree z)
    omega
  have hdegreeLt : ∀ z, G.degreeOn (F.erase e) z < k := by
    intro z; have h := hdegreeErase z; omega
  obtain ⟨hxD, hyD⟩ := G.criticalChainUnion_endpoints_mem
    hcritical heF hproper hdegreeLt
  have hxS : G.fst e ∈ G.criticalNeighborhood (F := F) e color := by
    rw [G.mem_criticalNeighborhood_iff]
    exact Or.inl ((G.mem_criticalChainUnion_iff).mp hxD)
  have hyS : G.snd e ∈ G.criticalNeighborhood (F := F) e color := by
    rw [G.mem_criticalNeighborhood_iff]
    exact Or.inl ((G.mem_criticalChainUnion_iff).mp hyD)
  have hpair := G.criticalNeighborhood_pairwise_disjoint_missingColorsAt
    hcritical heF hproper hdegreeErase
  have hcount := G.card_mul_sub_add_two_le_of_pairwise_missingColors
    heF hproper (by omega) hdegree
    (G.criticalNeighborhood (F := F) e color) hxS hyS hpair
  by_contra hnot
  have hseven : 7 ≤ (G.criticalNeighborhood (F := F) e color).card := by
    omega
  have hmul := Nat.mul_le_mul_right (k - d) hseven
  omega

/-- A five-vertex critical chain leaves room for at most one other vertex
in Andersen's combined critical neighborhood. -/
theorem criticalNeighborhood_outside_fivePath_card_le_one
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hfive : p.1.support.toFinset.card = 5)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2) :
    ((G.criticalNeighborhood (F := F) e color) \ p.1.support.toFinset).card ≤ 1 := by
  have hsubset : p.1.support.toFinset ⊆
      G.criticalNeighborhood (F := F) e color := by
    intro z hz
    rw [G.mem_criticalNeighborhood_iff]
    left
    exact ⟨a, b, ha, hb, p, by simpa using hz⟩
  have hcard := G.criticalNeighborhood_card_lt_seven
    hcritical heF hproper hdk hdegree hthreshold
  have hdiff := Finset.card_sdiff_add_card_eq_card hsubset
  rw [hfive] at hdiff
  omega

theorem eq_of_mem_criticalNeighborhood_outside_fivePath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hfive : p.1.support.toFinset.card = 5)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {u v : G.V}
    (huN : u ∈ G.criticalNeighborhood (F := F) e color)
    (hvN : v ∈ G.criticalNeighborhood (F := F) e color)
    (huout : u ∉ p.1.support.toFinset)
    (hvout : v ∉ p.1.support.toFinset) : u = v := by
  have hbound := G.criticalNeighborhood_outside_fivePath_card_le_one
    hcritical heF hproper ha hb p hfive hdk hdegree hthreshold
  exact Finset.card_le_one.mp hbound u
    (Finset.mem_sdiff.mpr ⟨huN, huout⟩) v
    (Finset.mem_sdiff.mpr ⟨hvN, hvout⟩)

end WeightedEdgeColoring.WeightedMultigraph
