import WeightedEdgeColoring.EndpointBlockGroups

/-!
# Endpoint blocks on a changing active edge set

Residual matching rounds repartition only the jobs that remain uncovered.
This file is the active-set version of `EndpointBlockGroups`: every active
edge belongs to at most one block at each endpoint, hence to at most two
global blocks.  A subtype keeps only blocks above a requested size.
-/

namespace WeightedEdgeColoring.WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})

/-- Active edges incident with one vertex. -/
def activeStarEdgeSet (active : Finset G.E) (v : G.V) : Finset G.E :=
  active.filter (G.Inc v)

@[simp] theorem mem_activeStarEdgeSet
    (active : Finset G.E) (v : G.V) (e : G.E) :
    e ∈ G.activeStarEdgeSet active v ↔ e ∈ active ∧ G.Inc v e := by
  simp [activeStarEdgeSet]

/-- A block is tagged by the endpoint whose active-star partition contains
it. -/
abbrev ActiveEndpointBlockGroup
    (active : Finset G.E)
    (P : ∀ v, Finpartition (G.activeStarEdgeSet active v)) :=
  Σ v, (P v).parts

noncomputable instance activeEndpointBlockGroupFintype
    (active : Finset G.E)
    (P : ∀ v, Finpartition (G.activeStarEdgeSet active v)) :
    Fintype (G.ActiveEndpointBlockGroup active P) where
  elems := Finset.univ.sigma (fun v ↦ (P v).parts.attach)
  complete g := by
    rcases g with ⟨v, T⟩
    simp

def activeEndpointBlockMembers
    {active : Finset G.E}
    {P : ∀ v, Finpartition (G.activeStarEdgeSet active v)} :
    G.ActiveEndpointBlockGroup active P → Finset G.E :=
  fun g ↦ g.2.1

theorem activeEndpointBlockMembers_subset_star
    {active : Finset G.E}
    {P : ∀ v, Finpartition (G.activeStarEdgeSet active v)}
    (g : G.ActiveEndpointBlockGroup active P) :
    G.activeEndpointBlockMembers g ⊆ G.activeStarEdgeSet active g.1 := by
  exact (P g.1).le g.2.2

theorem activeEndpointBlock_vertex_injective_on_incidence
    {active : Finset G.E}
    {P : ∀ v, Finpartition (G.activeStarEdgeSet active v)} (e : G.E) :
    Set.InjOn (fun g : G.ActiveEndpointBlockGroup active P ↦ g.1)
      {g | e ∈ G.activeEndpointBlockMembers g} := by
  intro g hg h hh hv
  rcases g with ⟨v, ⟨Tg, hgpart⟩⟩
  rcases h with ⟨w, ⟨Th, hhpart⟩⟩
  dsimp at hv
  subst w
  have heStar : e ∈ G.activeStarEdgeSet active v :=
    G.activeEndpointBlockMembers_subset_star
      ⟨v, ⟨Tg, hgpart⟩⟩ hg
  obtain ⟨T, hT, huniq⟩ := (P v).existsUnique_mem heStar
  have hgT : Tg = T := huniq Tg ⟨hgpart, hg⟩
  have hhT : Th = T := huniq Th ⟨hhpart, hh⟩
  subst Tg
  subst Th
  rfl

/-- Every edge occurs in at most two active endpoint blocks. -/
theorem activeEndpointBlock_incidence_card_le_two
    {active : Finset G.E}
    {P : ∀ v, Finpartition (G.activeStarEdgeSet active v)} (e : G.E) :
    ((Finset.univ : Finset (G.ActiveEndpointBlockGroup active P)).filter
      (fun g ↦ e ∈ G.activeEndpointBlockMembers g)).card ≤ 2 := by
  classical
  let A : Finset (G.ActiveEndpointBlockGroup active P) :=
    Finset.univ.filter (fun g ↦ e ∈ G.activeEndpointBlockMembers g)
  have hinj : Set.InjOn (fun g : G.ActiveEndpointBlockGroup active P ↦ g.1) A := by
    intro g hg h hh heq
    exact G.activeEndpointBlock_vertex_injective_on_incidence e
      (Finset.mem_filter.mp hg).2 (Finset.mem_filter.mp hh).2 heq
  have himage : A.image (fun g ↦ g.1) ⊆ {G.fst e, G.snd e} := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨g, hgA, rfl⟩
    have hstar := G.activeEndpointBlockMembers_subset_star g
      (Finset.mem_filter.mp hgA).2
    have hinc := (G.mem_activeStarEdgeSet active g.1 e).mp hstar |>.2
    rcases hinc with hf | hs
    · simp [← hf]
    · simp [← hs]
  calc
    ((Finset.univ : Finset (G.ActiveEndpointBlockGroup active P)).filter
        (fun g ↦ e ∈ G.activeEndpointBlockMembers g)).card = A.card := rfl
    _ = (A.image (fun g ↦ g.1)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ({G.fst e, G.snd e} : Finset G.V).card :=
      Finset.card_le_card himage
    _ = 2 := by simp [G.noLoop e]

/-- The subtype of active endpoint blocks with at least `K` members. -/
abbrev ActiveEndpointLargeBlockGroup
    (active : Finset G.E)
    (P : ∀ v, Finpartition (G.activeStarEdgeSet active v))
    (K : ℕ) :=
  {g : G.ActiveEndpointBlockGroup active P //
    K ≤ (G.activeEndpointBlockMembers g).card}

def activeEndpointLargeBlockMembers
    {active : Finset G.E}
    {P : ∀ v, Finpartition (G.activeStarEdgeSet active v)}
    {K : ℕ} :
    G.ActiveEndpointLargeBlockGroup active P K → Finset G.E :=
  fun g ↦ G.activeEndpointBlockMembers g.1

theorem activeEndpointLargeBlock_card_ge
    {active : Finset G.E}
    {P : ∀ v, Finpartition (G.activeStarEdgeSet active v)}
    {K : ℕ} (g : G.ActiveEndpointLargeBlockGroup active P K) :
    K ≤ (G.activeEndpointLargeBlockMembers g).card := g.2

/-- Discarding small blocks cannot increase the incidence of an edge. -/
theorem activeEndpointLargeBlock_incidence_card_le_two
    {active : Finset G.E}
    {P : ∀ v, Finpartition (G.activeStarEdgeSet active v)}
    {K : ℕ} (e : G.E) :
    ((Finset.univ : Finset (G.ActiveEndpointLargeBlockGroup active P K)).filter
      (fun g ↦ e ∈ G.activeEndpointLargeBlockMembers g)).card ≤ 2 := by
  classical
  let emb : G.ActiveEndpointLargeBlockGroup active P K ↪
      G.ActiveEndpointBlockGroup active P := ⟨Subtype.val, Subtype.val_injective⟩
  let L : Finset (G.ActiveEndpointLargeBlockGroup active P K) :=
    Finset.univ.filter (fun g ↦ e ∈ G.activeEndpointLargeBlockMembers g)
  let A : Finset (G.ActiveEndpointBlockGroup active P) :=
    Finset.univ.filter (fun g ↦ e ∈ G.activeEndpointBlockMembers g)
  have hsub : L.map emb ⊆ A := by
    intro g hg
    rcases Finset.mem_map.mp hg with ⟨q, hq, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩
  calc
    ((Finset.univ : Finset (G.ActiveEndpointLargeBlockGroup active P K)).filter
        (fun g ↦ e ∈ G.activeEndpointLargeBlockMembers g)).card = L.card := rfl
    _ = (L.map emb).card := (Finset.card_map emb).symm
    _ ≤ A.card := Finset.card_le_card hsub
    _ ≤ 2 := G.activeEndpointBlock_incidence_card_le_two e

end WeightedEdgeColoring.WeightedSimpleGraph
