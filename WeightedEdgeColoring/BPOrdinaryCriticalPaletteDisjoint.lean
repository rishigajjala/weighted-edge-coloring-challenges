import WeightedEdgeColoring.BPOrdinaryCriticalPalette
import WeightedEdgeColoring.BPOrdinaryCriticalSwitch

/-!
# Pairwise disjoint palettes on a critical chain

This file completes the recolouring part of Andersen's Lemma 3.  Suppose
two different vertices of the critical two-colour path miss the same colour.
Move from the first vertex toward the second one.  If the next vertex also
misses that colour, the adjacent-palette theorem gives a contradiction.  If
it does not, a Kempe switch makes it miss the colour while preserving the
whole critical path.  One of the original two vertices still misses the
colour.  Thus either the contradiction is immediate or the distance between
the two vertices has gone down by one.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Every vertex on a path has the same connected-component name as the
initial vertex. -/
theorem connectedComponentMk_eq_path_start_of_mem_support
    {H : SimpleGraph G.V} {x y z : G.V}
    (p : H.Path x y) (hz : z ∈ p.1.support) :
    H.connectedComponentMk z = H.connectedComponentMk x := by
  have hreach : H.Reachable x z := ⟨p.1.takeUntil z hz⟩
  exact (SimpleGraph.ConnectedComponent.sound hreach).symm

/-- Version of the adjacent-palette theorem in which the ambient
two-colour graph has been given a separate name.  This small wrapper keeps
the graph fixed while the colouring changes in the induction below. -/
private theorem not_common_missing_of_mem_criticalPath_edge_of_graph_eq
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {a b : Fin k}
    {H : SimpleGraph G.V} {color : G.E → Fin k}
    (hgraph : G.twoColorGraph (F.erase e) color a b = H)
    (hproper : G.IsProperOn (F.erase e) color)
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : H.Path (G.fst e) (G.snd e))
    {u v : G.V} (hpathEdge : s(u, v) ∈ p.1.edges)
    {c : Fin k}
    (huc : c ∈ G.missingColorsAt (F.erase e) color u)
    (hvc : c ∈ G.missingColorsAt (F.erase e) color v) :
    False := by
  subst H
  exact G.not_common_missing_of_mem_criticalPath_edge
    hcritical heF hproper ha hb p hpathEdge huc hvc

/-- Distance form of pairwise palette disjointness.  The walk `q` is the
part of the critical path between the two vertices.  The explicit length
parameter makes the decreasing Kempe-switch argument transparent to Lean. -/
private theorem not_common_missing_of_criticalPath_subwalk_length
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {a b : Fin k}
    {H : SimpleGraph G.V} {color : G.E → Fin k}
    (hgraph : G.twoColorGraph (F.erase e) color a b = H)
    (hproper : G.IsProperOn (F.erase e) color)
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : H.Path (G.fst e) (G.snd e))
    {u v : G.V} (q : H.Walk u v) (hqsub : q.IsSubwalk p.1)
    (huv : u ≠ v) {c : Fin k}
    (huc : c ∈ G.missingColorsAt (F.erase e) color u)
    (hvc : c ∈ G.missingColorsAt (F.erase e) color v)
    (hdegree : ∀ z, G.degreeOn (F.erase e) z < k)
    (n : ℕ) (hlen : q.length = n) :
    False := by
  induction n using Nat.strong_induction_on generalizing color u v q with
  | h n ih =>
      cases q with
      | nil => exact huv rfl
      | @cons u z v huz q =>
          have hfirstInFull : s(u, z) ∈ (q.cons huz).edges := by simp
          have hfirstInPath : s(u, z) ∈ p.1.edges :=
            hqsub.edges_subset hfirstInFull
          have hfullPath : (q.cons huz).IsPath :=
            SimpleGraph.Walk.isPath_of_isSubwalk hqsub p.property
          have hqPath : q.IsPath := hfullPath.of_cons
          by_cases hqnil : q.Nil
          · have hzv : z = v := hqnil.eq
            subst v
            exact G.not_common_missing_of_mem_criticalPath_edge_of_graph_eq
              hcritical heF hgraph hproper ha hb p hfirstInPath huc hvc
          · have hzv : z ≠ v := by
              intro hzv
              subst v
              have hqeq : q = .nil :=
                (SimpleGraph.Walk.isPath_iff_eq_nil q).mp hqPath
              apply hqnil
              rw [hqeq]
              exact .nil
            have hqsubPath : q.IsSubwalk p.1 := by
              exact (SimpleGraph.Walk.isSubwalk_cons q huz).trans hqsub
            have huPath : u ∈ p.1.support :=
              p.1.fst_mem_support_of_mem_edges hfirstInPath
            have hzPath : z ∈ p.1.support :=
              p.1.snd_mem_support_of_mem_edges hfirstInPath
            have hvPath : v ∈ p.1.support :=
              hqsub.support_subset (q.cons huz).end_mem_support
            have hucomponentH :
                H.connectedComponentMk u =
                  H.connectedComponentMk (G.fst e) :=
              G.connectedComponentMk_eq_path_start_of_mem_support p huPath
            have hvcomponentH :
                H.connectedComponentMk v =
                  H.connectedComponentMk (G.fst e) :=
              G.connectedComponentMk_eq_path_start_of_mem_support p hvPath
            have hzcomponentH :
                H.connectedComponentMk z =
                  H.connectedComponentMk (G.fst e) :=
              G.connectedComponentMk_eq_path_start_of_mem_support p hzPath
            have hucomponent :
                (G.twoColorGraph (F.erase e) color a b).connectedComponentMk u =
                  (G.twoColorGraph (F.erase e) color a b).connectedComponentMk
                    (G.fst e) := by
              simpa [hgraph] using hucomponentH
            have hvcomponent :
                (G.twoColorGraph (F.erase e) color a b).connectedComponentMk v =
                  (G.twoColorGraph (F.erase e) color a b).connectedComponentMk
                    (G.fst e) := by
              simpa [hgraph] using hvcomponentH
            have hzcomponent :
                (G.twoColorGraph (F.erase e) color a b).connectedComponentMk z =
                  (G.twoColorGraph (F.erase e) color a b).connectedComponentMk
                    (G.fst e) := by
              simpa [hgraph] using hzcomponentH
            obtain ⟨ru, rv, hpdecomp⟩ := hqsub
            have hdecompPath :
                ((ru.append (q.cons huz)).append rv).IsPath := by
              rw [← hpdecomp]
              exact p.property
            have hleftPath : (ru.append (q.cons huz)).IsPath :=
              hdecompPath.of_append_left
            have hzfst : z ≠ G.fst e := by
              have hfstz : G.fst e ≠ z :=
                hleftPath.ne_of_mem_support_of_append huz.ne.symm
                  ru.start_mem_support (by simp)
              exact hfstz.symm
            have hzsnd : z ≠ G.snd e := by
              by_cases hvend : v = G.snd e
              · intro hzend
                exact hzv (hzend.trans hvend.symm)
              · have hzleft : z ∈ (ru.append (q.cons huz)).support :=
                  SimpleGraph.Walk.subset_support_append_right ru
                    (q.cons huz) (by simp)
                exact hdecompPath.ne_of_mem_support_of_append
                  (fun h ↦ hvend h.symm)
                  hzleft rv.end_mem_support
            by_cases hzc :
                c ∈ G.missingColorsAt (F.erase e) color z
            · exact G.not_common_missing_of_mem_criticalPath_edge_of_graph_eq
                hcritical heF hgraph hproper ha hb p hfirstInPath huc hzc
            · obtain ⟨switched, hproperSwitched, haSwitched, hbSwitched,
                  hgraphSwitched, hzcSwitched, hcommonSwitched⟩ :=
                G.exists_criticalChainSwitch_propagating_common_missingColor
                  hcritical heF hproper ha hb huv huz.ne hzv.symm
                    hucomponent hvcomponent hzcomponent
                    hzfst hzsnd huc hvc hzc (hdegree z)
              have hswitchedH :
                  G.twoColorGraph (F.erase e) switched a b = H :=
                hgraphSwitched.trans hgraph
              rcases hcommonSwitched with huzCommon | hzvCommon
              · exact G.not_common_missing_of_mem_criticalPath_edge_of_graph_eq
                  hcritical heF hswitchedH hproperSwitched haSwitched
                    hbSwitched p hfirstInPath huzCommon hzcSwitched
              · refine ih q.length ?_ (color := switched) (u := z) (v := v)
                  hswitchedH hproperSwitched haSwitched hbSwitched q
                    hqsubPath hzv hzcSwitched hzvCommon rfl
                simp only [SimpleGraph.Walk.length_cons] at hlen
                omega

/-- Any two different vertices on a critical chain have disjoint sets of
missing colours, provided every vertex has fewer selected edges than the
number of available colours. -/
theorem disjoint_missingColorsAt_of_mem_criticalPath_support
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hdegree : ∀ z, G.degreeOn (F.erase e) z < k)
    {u v : G.V} (hu : u ∈ p.1.support) (hv : v ∈ p.1.support)
    (huv : u ≠ v) :
    Disjoint (G.missingColorsAt (F.erase e) color u)
      (G.missingColorsAt (F.erase e) color v) := by
  rw [Finset.disjoint_left]
  intro c huc hvc
  obtain ⟨before, after, _hbeforePath, _hafterPath, hpdecomp⟩ :=
    p.property.mem_support_iff_exists_append.mp hu
  have hvEither : v ∈ before.support ∨ v ∈ after.support := by
    rw [hpdecomp, SimpleGraph.Walk.mem_support_append_iff] at hv
    exact hv
  rcases hvEither with hvBefore | hvAfter
  · let q := before.dropUntil v hvBefore
    have hqsubBefore : q.IsSubwalk before := by
      exact before.isSubwalk_dropUntil hvBefore
    have hbeforeSub : before.IsSubwalk p.1 :=
      SimpleGraph.Walk.isSubwalk_of_append_left hpdecomp
    have hqsub : q.IsSubwalk p.1 := hqsubBefore.trans hbeforeSub
    exact G.not_common_missing_of_criticalPath_subwalk_length
      hcritical heF rfl hproper ha hb p q hqsub huv.symm hvc huc
        hdegree q.length rfl
  · let q := after.takeUntil v hvAfter
    have hqsubAfter : q.IsSubwalk after := by
      exact after.isSubwalk_takeUntil hvAfter
    have hafterSub : after.IsSubwalk p.1 :=
      SimpleGraph.Walk.isSubwalk_of_append_right hpdecomp
    have hqsub : q.IsSubwalk p.1 := hqsubAfter.trans hafterSub
    exact G.not_common_missing_of_criticalPath_subwalk_length
      hcritical heF rfl hproper ha hb p q hqsub huv huc hvc
        hdegree q.length rfl

end WeightedMultigraph
end WeightedEdgeColoring
