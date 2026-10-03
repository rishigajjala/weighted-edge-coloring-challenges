import WeightedEdgeColoring.ActiveEndpointDyadicGroups
import WeightedEdgeColoring.WeightedMultigraph

/-!
# Endpoint dyadic groups for weighted multigraphs

The endpoint-block construction depends only on indexed edges, looplessness,
and weights.  Parallel edges remain distinct members of each local star.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

def activeStarEdgeSet (active : Finset G.E) (v : G.V) : Finset G.E :=
  active.filter (G.Inc v)

@[simp] theorem mem_activeStarEdgeSet
    (active : Finset G.E) (v : G.V) (e : G.E) :
    e ∈ G.activeStarEdgeSet active v ↔ e ∈ active ∧ G.Inc v e := by
  simp [activeStarEdgeSet]

abbrev ActiveEndpointBlockGroup
    (active : Finset G.E)
    (P : ∀ v, Finpartition (G.activeStarEdgeSet active v)) :=
  Σ v, (P v).parts

noncomputable instance activeEndpointBlockGroupFintype
    (active : Finset G.E)
    (P : ∀ v, Finpartition (G.activeStarEdgeSet active v)) :
    Fintype (G.ActiveEndpointBlockGroup active P) where
  elems := Finset.univ.sigma (fun v ↦ (P v).parts.attach)
  complete g := by rcases g with ⟨v, T⟩; simp

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
  obtain ⟨T, _hT, huniq⟩ := (P v).existsUnique_mem heStar
  have hgT : Tg = T := huniq Tg ⟨hgpart, hg⟩
  have hhT : Th = T := huniq Th ⟨hhpart, hh⟩
  subst Tg
  subst Th
  rfl

theorem activeEndpointBlock_incidence_card_le_two
    {active : Finset G.E}
    {P : ∀ v, Finpartition (G.activeStarEdgeSet active v)} (e : G.E) :
    ((Finset.univ : Finset (G.ActiveEndpointBlockGroup active P)).filter
      (fun g ↦ e ∈ G.activeEndpointBlockMembers g)).card ≤ 2 := by
  classical
  let A : Finset (G.ActiveEndpointBlockGroup active P) :=
    Finset.univ.filter (fun g ↦ e ∈ G.activeEndpointBlockMembers g)
  have hinj : Set.InjOn
      (fun g : G.ActiveEndpointBlockGroup active P ↦ g.1) A := by
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
    _ = A.card := rfl
    _ = (A.image (fun g ↦ g.1)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ({G.fst e, G.snd e} : Finset G.V).card :=
      Finset.card_le_card himage
    _ = 2 := by simp [G.noLoop e]

abbrev ActiveEndpointLargeBlockGroup
    (active : Finset G.E)
    (P : ∀ v, Finpartition (G.activeStarEdgeSet active v)) (K : ℕ) :=
  {g : G.ActiveEndpointBlockGroup active P //
    K ≤ (G.activeEndpointBlockMembers g).card}

def activeEndpointLargeBlockMembers
    {active : Finset G.E}
    {P : ∀ v, Finpartition (G.activeStarEdgeSet active v)} {K : ℕ} :
    G.ActiveEndpointLargeBlockGroup active P K → Finset G.E :=
  fun g ↦ G.activeEndpointBlockMembers g.1

theorem activeEndpointLargeBlock_incidence_card_le_two
    {active : Finset G.E}
    {P : ∀ v, Finpartition (G.activeStarEdgeSet active v)}
    {K : ℕ} (e : G.E) :
    ((Finset.univ : Finset (G.ActiveEndpointLargeBlockGroup active P K)).filter
      (fun g ↦ e ∈ G.activeEndpointLargeBlockMembers g)).card ≤ 2 := by
  classical
  let emb : G.ActiveEndpointLargeBlockGroup active P K ↪
      G.ActiveEndpointBlockGroup active P :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let Q : Finset (G.ActiveEndpointLargeBlockGroup active P K) :=
    Finset.univ.filter (fun g ↦ e ∈ G.activeEndpointLargeBlockMembers g)
  let A : Finset (G.ActiveEndpointBlockGroup active P) :=
    Finset.univ.filter (fun g ↦ e ∈ G.activeEndpointBlockMembers g)
  have hsub : Q.map emb ⊆ A := by
    intro g hg
    rcases Finset.mem_map.mp hg with ⟨q, hq, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩
  calc
    _ = Q.card := rfl
    _ = (Q.map emb).card := (Finset.card_map emb).symm
    _ ≤ A.card := Finset.card_le_card hsub
    _ ≤ 2 := G.activeEndpointBlock_incidence_card_le_two e

structure ActiveEndpointDyadicGrouping
    (active : Finset G.E) (β : ℝ) (L K : ℕ) where
  partition : ∀ v, Finpartition (G.activeStarEdgeSet active v)
  block_spec : ∀ v T, T ∈ (partition v).parts →
    ((K ≤ T.card ∧ T.card ≤ 2 * K - 1) ∨ T.card < K) ∧
    (∃ i : Fin (L + 1),
      T ⊆ WeightedEdgeColoring.weightClass (G.activeStarEdgeSet active v)
        (WeightedEdgeColoring.dyadicBucket β L G.weight) i) ∧
    (∀ e ∈ T, ∀ f ∈ T, G.weight e ≤ 2 * G.weight f)
  small_block_is_bucket : ∀ v i T,
    T ∈ (partition v).parts → T.card < K →
    T ⊆ WeightedEdgeColoring.weightClass (G.activeStarEdgeSet active v)
      (WeightedEdgeColoring.dyadicBucket β L G.weight) i →
    T = WeightedEdgeColoring.weightClass (G.activeStarEdgeSet active v)
      (WeightedEdgeColoring.dyadicBucket β L G.weight) i
  discarded_weight_le : ∀ v,
    (∑ T ∈ (partition v).parts.filter (fun T ↦ T.card < K),
      ∑ e ∈ T, G.weight e) ≤ (((L + 1) * (K - 1) : ℕ) : ℝ)

theorem exists_activeEndpointDyadicGrouping
    (active : Finset G.E) (β : ℝ) (L K : ℕ)
    (hβ : 0 < β) (hcover : 1 ≤ WeightedEdgeColoring.dyadicScale β L)
    (hwlower : ∀ e ∈ active, β ≤ G.weight e) (hK : 0 < K) :
    Nonempty (G.ActiveEndpointDyadicGrouping active β L K) := by
  classical
  have hexists : ∀ v, ∃ P : Finpartition (G.activeStarEdgeSet active v),
      (∀ T ∈ P.parts,
        ((K ≤ T.card ∧ T.card ≤ 2 * K - 1) ∨ T.card < K) ∧
        (∃ i : Fin (L + 1),
          T ⊆ WeightedEdgeColoring.weightClass (G.activeStarEdgeSet active v)
            (WeightedEdgeColoring.dyadicBucket β L G.weight) i) ∧
        (∀ e ∈ T, ∀ f ∈ T, G.weight e ≤ 2 * G.weight f)) ∧
      (∀ i T, T ∈ P.parts → T.card < K →
        T ⊆ WeightedEdgeColoring.weightClass (G.activeStarEdgeSet active v)
          (WeightedEdgeColoring.dyadicBucket β L G.weight) i →
        T = WeightedEdgeColoring.weightClass (G.activeStarEdgeSet active v)
          (WeightedEdgeColoring.dyadicBucket β L G.weight) i) ∧
      (∑ T ∈ P.parts.filter (fun T ↦ T.card < K),
        ∑ e ∈ T, G.weight e) ≤ (((L + 1) * (K - 1) : ℕ) : ℝ) := by
    intro v
    apply WeightedEdgeColoring.exists_dyadic_block_finpartition_small_weight_bound
    · exact hβ
    · exact hcover
    · intro e he
      exact hwlower e ((G.mem_activeStarEdgeSet active v e).mp he).1
    · intro e _he
      exact G.weight_le_one e
    · exact hK
  let P : ∀ v, Finpartition (G.activeStarEdgeSet active v) :=
    fun v ↦ Classical.choose (hexists v)
  have hP (v) := Classical.choose_spec (hexists v)
  exact ⟨{
    partition := P
    block_spec := fun v ↦ (hP v).1
    small_block_is_bucket := fun v ↦ (hP v).2.1
    discarded_weight_le := fun v ↦ (hP v).2.2
  }⟩

abbrev ActiveEndpointDyadicLargeGroup
    {active : Finset G.E} {β : ℝ} {L K : ℕ}
    (D : G.ActiveEndpointDyadicGrouping active β L K) :=
  G.ActiveEndpointLargeBlockGroup active D.partition K

def activeEndpointDyadicLargeMembers
    {active : Finset G.E} {β : ℝ} {L K : ℕ}
    {D : G.ActiveEndpointDyadicGrouping active β L K} :
    G.ActiveEndpointDyadicLargeGroup D → Finset G.E :=
  fun g ↦ G.activeEndpointLargeBlockMembers g

theorem activeEndpointDyadicLarge_card_between
    {active : Finset G.E} {β : ℝ} {L K : ℕ}
    {D : G.ActiveEndpointDyadicGrouping active β L K}
    (g : G.ActiveEndpointDyadicLargeGroup D) :
    K ≤ (G.activeEndpointDyadicLargeMembers g).card ∧
      (G.activeEndpointDyadicLargeMembers g).card ≤ 2 * K - 1 := by
  have hsize := (D.block_spec g.1.1 g.1.2.1 g.1.2.2).1
  refine ⟨g.2, ?_⟩
  rcases hsize with h | h
  · exact h.2
  · have hg : K ≤ g.1.2.1.card := by
      simpa [activeEndpointDyadicLargeMembers,
        activeEndpointLargeBlockMembers, activeEndpointBlockMembers] using g.2
    exact (not_lt_of_ge hg h).elim

theorem activeEndpointDyadicLarge_weight_le_two_mul
    {active : Finset G.E} {β : ℝ} {L K : ℕ}
    {D : G.ActiveEndpointDyadicGrouping active β L K}
    (g : G.ActiveEndpointDyadicLargeGroup D)
    {e f : G.E} (he : e ∈ G.activeEndpointDyadicLargeMembers g)
    (hf : f ∈ G.activeEndpointDyadicLargeMembers g) :
    G.weight e ≤ 2 * G.weight f := by
  exact (D.block_spec g.1.1 g.1.2.1 g.1.2.2).2.2 e he f hf

theorem activeEndpointDyadicLarge_incidence_card_le_two
    {active : Finset G.E} {β : ℝ} {L K : ℕ}
    {D : G.ActiveEndpointDyadicGrouping active β L K} (e : G.E) :
    ((Finset.univ : Finset (G.ActiveEndpointDyadicLargeGroup D)).filter
      (fun g ↦ e ∈ G.activeEndpointDyadicLargeMembers g)).card ≤ 2 := by
  exact G.activeEndpointLargeBlock_incidence_card_le_two e

theorem activeEndpointDyadic_discarded_weight_le
    {active : Finset G.E} {β : ℝ} {L K : ℕ}
    (D : G.ActiveEndpointDyadicGrouping active β L K) (v : G.V) :
    (∑ T ∈ (D.partition v).parts.filter (fun T ↦ T.card < K),
      ∑ e ∈ T, G.weight e) ≤ (((L + 1) * (K - 1) : ℕ) : ℝ) :=
  D.discarded_weight_le v

end

end WeightedEdgeColoring.WeightedMultigraph
