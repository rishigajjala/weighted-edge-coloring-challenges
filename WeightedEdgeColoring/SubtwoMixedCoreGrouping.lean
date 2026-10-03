import WeightedEdgeColoring.SubtwoGlobalLinearGroupingTypes
import WeightedEdgeColoring.BPEdgeRestriction
import WeightedEdgeColoring.SubtwoMonotoneColorLifting

/-!
# Group the finite core and leave the small edges untouched

The two injections have different jobs: heavier predecessors preserve all
local bin packings, while smaller targets recover actual physical colors.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 160000
open scoped BigOperators Sym2
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
namespace SubtwoMixedCoreGrouping

variable (G : WeightedMultigraph.{u}) (F : Finset G.E) (M : ℕ)

abbrev Core := SubtwoGlobalLinearGrouping.graph (G.edgeRestriction F) M
abbrev Edge := (Core G F M).E ⊕ {e : G.E // e ∉ F}

def source : Edge G F M → G.E
  | Sum.inl e => (SubtwoGlobalLinearGrouping.source (G.edgeRestriction F) M e).val
  | Sum.inr e => e.val

def target : Edge G F M → G.E
  | Sum.inl e => (SubtwoGlobalLinearGrouping.target (G.edgeRestriction F) M e).val
  | Sum.inr e => e.val

def weight : Edge G F M → ℝ
  | Sum.inl e => (Core G F M).weight e
  | Sum.inr e => G.weight e.val

def graph : WeightedMultigraph.{u} where
  V := G.V
  E := Edge G F M
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := Classical.decEq _
  fst := fun e => G.fst (target G F M e)
  snd := fun e => G.snd (target G F M e)
  noLoop := fun e => G.noLoop (target G F M e)
  weight := weight G F M
  weight_pos := by
    intro e
    cases e with
    | inl e => exact (Core G F M).weight_pos e
    | inr e => exact G.weight_pos e.val
  weight_le_one := by
    intro e
    cases e with
    | inl e => exact (Core G F M).weight_le_one e
    | inr e => exact G.weight_le_one e.val

theorem source_injective (hM : 0 < M) : Function.Injective (source G F M) := by
  intro e f hef
  cases e with
  | inl e =>
      cases f with
      | inl f =>
          exact congrArg Sum.inl (SubtwoGlobalLinearGrouping.source_injective
            (G.edgeRestriction F) M hM (Subtype.ext hef))
      | inr f =>
          dsimp only [source] at hef
          exact (f.property (hef ▸
            (SubtwoGlobalLinearGrouping.source (G.edgeRestriction F) M e).property)).elim
  | inr e =>
      cases f with
      | inl f =>
          dsimp only [source] at hef
          exact (e.property (hef.symm ▸
            (SubtwoGlobalLinearGrouping.source (G.edgeRestriction F) M f).property)).elim
      | inr f => exact congrArg Sum.inr (Subtype.ext hef)

theorem target_injective : Function.Injective (target G F M) := by
  intro e f hef
  cases e with
  | inl e =>
      cases f with
      | inl f =>
          exact congrArg Sum.inl (SubtwoGlobalLinearGrouping.target_injective
            (G.edgeRestriction F) M (Subtype.ext hef))
      | inr f =>
          dsimp only [target] at hef
          exact (f.property (hef ▸
            (SubtwoGlobalLinearGrouping.target (G.edgeRestriction F) M e).property)).elim
  | inr e =>
      cases f with
      | inl f =>
          dsimp only [target] at hef
          exact (e.property (hef.symm ▸
            (SubtwoGlobalLinearGrouping.target (G.edgeRestriction F) M f).property)).elim
      | inr f => exact congrArg Sum.inr (Subtype.ext hef)

theorem source_inc (v : G.V) (e : Edge G F M) :
    G.Inc v (source G F M e) ↔ (graph G F M).Inc v e := by
  cases e with
  | inl e => exact SubtwoGlobalLinearGrouping.source_inc (G.edgeRestriction F) M v e
  | inr e => exact Iff.rfl

theorem target_inc (v : G.V) (e : Edge G F M) :
    (graph G F M).Inc v e ↔ G.Inc v (target G F M e) := Iff.rfl

theorem weight_le_source (hM : 0 < M) (e : Edge G F M) :
    (graph G F M).weight e ≤ G.weight (source G F M e) := by
  cases e with
  | inl e => exact SubtwoGlobalLinearGrouping.weight_le_source (G.edgeRestriction F) M hM e
  | inr e => exact le_rfl

theorem target_weight_le (e : Edge G F M) :
    G.weight (target G F M e) ≤ (graph G F M).weight e := by
  cases e with
  | inl e => exact SubtwoGlobalLinearGrouping.target_weight_le (G.edgeRestriction F) M e
  | inr e => exact le_rfl

theorem locallyPacksInto (hM : 0 < M) {n : ℕ}
    (hlocal : G.LocallyPacksInto n) : (graph G F M).LocallyPacksInto n :=
  G.locallyPacksInto_of_injective_heavier_edges (graph G F M) id (source G F M)
    (source_injective G F M hM) (fun v e h => (source_inc G F M v e).mpr h)
    (weight_le_source G F M hM) hlocal

def retained : Finset G.E := Finset.univ.image (target G F M)

theorem omitted_eq_core_image :
    Finset.univ \ retained G F M =
      (Finset.univ \ SubtwoGlobalLinearGrouping.retained (G.edgeRestriction F) M).image
        (fun e : (G.edgeRestriction F).E => e.val) := by
  classical
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro he
    have heF : e ∈ F := by
      by_contra h
      apply he
      exact Finset.mem_image.mpr ⟨Sum.inr ⟨e,h⟩, Finset.mem_univ _, rfl⟩
    refine ⟨⟨e,heF⟩, ?_, rfl⟩
    intro hc
    obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hc
    apply he
    exact Finset.mem_image.mpr ⟨Sum.inl f, Finset.mem_univ _, congrArg Subtype.val hf⟩
  · rintro ⟨e,he,rfl⟩ hret
    obtain ⟨f,_,hf⟩ := Finset.mem_image.mp hret
    cases f with
    | inl f =>
        exact he (Finset.mem_image.mpr ⟨f,Finset.mem_univ _,Subtype.ext hf⟩)
    | inr f =>
        dsimp only [target] at hf
        exact f.property (hf.symm ▸ e.property)

theorem omitted_weight_le (hM : 0 < M) (S : ℕ) (hS : 0 < S)
    (hlower : ∀ e ∈ F, (1 : ℝ)/S ≤ G.weight e) {n : ℕ}
    (hlocal : G.LocallyPacksInto n) (v : G.V) :
    (∑ e ∈ Finset.univ \ retained G F M, if G.Inc v e then G.weight e else 0) ≤
      (2*(S : ℝ)/M)*n := by
  rw [omitted_eq_core_image, Finset.sum_image Subtype.val_injective.injOn]
  exact SubtwoGlobalLinearGrouping.omitted_weight_le (G.edgeRestriction F) M hM S hS
    (fun e => hlower e.val e.property) (G.edgeRestriction_locallyPacksInto F hlocal) v

theorem core_weight_ge (S : ℕ) (hlower : ∀ e ∈ F, (1 : ℝ)/S ≤ G.weight e)
    (e : (Core G F M).E) :
    (1 : ℝ)/S ≤ (graph G F M).weight (Sum.inl e) :=
  SubtwoGlobalLinearGrouping.weight_ge (G.edgeRestriction F) M S
    (fun e => hlower e.val e.property) e

/-- Edges below the core cutoff are still the original ungrouped small edges. -/
theorem below_endpoint_injective (tau : ℝ)
    (hlower : ∀ e ∈ F, tau ≤ G.weight e)
    (hsmall : Function.Injective (fun e : {e : G.E // e ∉ F} => s(G.fst e.val, G.snd e.val))) :
    Function.Injective (fun e : {e : (graph G F M).E // (graph G F M).weight e < tau} =>
      s((graph G F M).fst e.val, (graph G F M).snd e.val)) := by
  intro e f hef
  have hcore : ∀ a : (Core G F M).E, tau ≤ (Core G F M).weight a := by
    intro a
    cases a with
    | inl a => exact hlower a.val.val a.val.property
    | inr a => exact hlower a.1.representative.val a.1.representative.property
  apply Subtype.ext
  rcases e with ⟨e,he⟩
  rcases f with ⟨f,hf⟩
  cases e with
  | inl e => exact (not_lt_of_ge (hcore e) he).elim
  | inr e =>
      cases f with
      | inl f => exact (not_lt_of_ge (hcore f) hf).elim
      | inr f => exact congrArg Sum.inr (hsmall hef)

end SubtwoMixedCoreGrouping
end
end WeightedEdgeColoring.WeightedMultigraph
