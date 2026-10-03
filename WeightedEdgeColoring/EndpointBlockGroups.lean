import WeightedEdgeColoring.WeightedGraph
import Mathlib.Order.Partition.Finpartition

/-!
# Blocks chosen independently at the two endpoints

If every vertex partitions its incident edges into local blocks, the local
blocks form a global group family.  Every edge lies in exactly one block at
each of its two endpoints, hence in at most two global groups.  This is the
incidence bound required by the group Harris round.
-/

namespace WeightedEdgeColoring.WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})

/-- The finite set of edge indices incident with a vertex. -/
def starEdgeSet (v : G.V) : Finset G.E :=
  Finset.univ.filter (G.Inc v)

@[simp] theorem mem_starEdgeSet (v : G.V) (e : G.E) :
    e ∈ G.starEdgeSet v ↔ G.Inc v e := by
  simp [starEdgeSet]

/-- A global group is a vertex together with one part of that vertex's
partition of its incident edges. -/
abbrev EndpointBlockGroup
    (P : ∀ v, Finpartition (G.starEdgeSet v)) :=
  Σ v, (P v).parts

-- Keep the finite enumeration local to this concrete dependent sum.
noncomputable instance endpointBlockGroupFintype
    (P : ∀ v, Finpartition (G.starEdgeSet v)) :
    Fintype (G.EndpointBlockGroup P) where
  elems := Finset.univ.sigma (fun v ↦ (P v).parts.attach)
  complete g := by
    rcases g with ⟨v, T⟩
    simp

/-- The edges belonging to an endpoint block. -/
def endpointBlockMembers
    {P : ∀ v, Finpartition (G.starEdgeSet v)} :
    G.EndpointBlockGroup P → Finset G.E :=
  fun g ↦ g.2.1

theorem endpointBlockMembers_subset_star
    {P : ∀ v, Finpartition (G.starEdgeSet v)}
    (g : G.EndpointBlockGroup P) :
    G.endpointBlockMembers g ⊆ G.starEdgeSet g.1 := by
  exact (P g.1).le g.2.2

theorem endpointBlock_vertex_incident_of_mem
    {P : ∀ v, Finpartition (G.starEdgeSet v)}
    (g : G.EndpointBlockGroup P) {e : G.E}
    (he : e ∈ G.endpointBlockMembers g) :
    G.Inc g.1 e := by
  exact (G.mem_starEdgeSet g.1 e).mp
    (G.endpointBlockMembers_subset_star g he)

/-- Among groups containing a fixed edge, projection to the group vertex is
injective because a partition has a unique part containing that edge. -/
theorem endpointBlock_vertex_injective_on_incidence
    {P : ∀ v, Finpartition (G.starEdgeSet v)} (e : G.E) :
    Set.InjOn (fun g : G.EndpointBlockGroup P ↦ g.1)
      {g | e ∈ G.endpointBlockMembers g} := by
  intro g hg h hh hv
  rcases g with ⟨v, ⟨Tg, hgpart⟩⟩
  rcases h with ⟨w, ⟨Th, hhpart⟩⟩
  dsimp at hv
  subst w
  have heStar : e ∈ G.starEdgeSet v :=
    G.endpointBlockMembers_subset_star ⟨v, ⟨Tg, hgpart⟩⟩ hg
  obtain ⟨T, hT, huniq⟩ := (P v).existsUnique_mem heStar
  have hgT : Tg = T := huniq Tg ⟨hgpart, hg⟩
  have hhT : Th = T := huniq Th ⟨hhpart, hh⟩
  subst Tg
  subst Th
  rfl

/-- Every edge belongs to at most two endpoint blocks. -/
theorem endpointBlock_incidence_card_le_two
    {P : ∀ v, Finpartition (G.starEdgeSet v)} (e : G.E) :
    ((Finset.univ : Finset (G.EndpointBlockGroup P)).filter
      (fun g ↦ e ∈ G.endpointBlockMembers g)).card ≤ 2 := by
  classical
  let A : Finset (G.EndpointBlockGroup P) :=
    Finset.univ.filter (fun g ↦ e ∈ G.endpointBlockMembers g)
  have hinj : Set.InjOn (fun g : G.EndpointBlockGroup P ↦ g.1) A := by
    intro g hg h hh heq
    apply G.endpointBlock_vertex_injective_on_incidence e
    · exact (Finset.mem_filter.mp hg).2
    · exact (Finset.mem_filter.mp hh).2
    · exact heq
  have himage : A.image (fun g ↦ g.1) ⊆ {G.fst e, G.snd e} := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨g, hgA, rfl⟩
    have hinc := G.endpointBlock_vertex_incident_of_mem g
      (Finset.mem_filter.mp hgA).2
    rcases hinc with hf | hs
    · simp [← hf]
    · simp [← hs]
  calc
    ((Finset.univ : Finset (G.EndpointBlockGroup P)).filter
        (fun g ↦ e ∈ G.endpointBlockMembers g)).card = A.card := rfl
    _ = (A.image (fun g ↦ g.1)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ({G.fst e, G.snd e} : Finset G.V).card :=
      Finset.card_le_card himage
    _ = 2 := by simp [G.noLoop e]

end WeightedEdgeColoring.WeightedSimpleGraph
