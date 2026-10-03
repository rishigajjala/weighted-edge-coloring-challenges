import WeightedEdgeColoring.SubtwoLinearGroupedGraph
import WeightedEdgeColoring.BPGeneralPhysicalDegreeBound

/-!
# Linear grouping with small parallel classes kept intact

Every ordered endpoint pair containing fewer than `M` edges is kept as it
is. In every larger pair we keep the later linear groups, rounded to their
largest weight. Distinct heavier predecessor edges pay for all new edges.
Only first groups are lost. The loss at a vertex is at most `2/M` times
its original degree, independently of the number of vertices or pairs.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 160000
open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u

namespace SubtwoGlobalLinearGrouping

open SubtwoLinearGrouping
open BinPackingInstance.KeyedLinearRoundedCover

variable (G : WeightedMultigraph.{u}) (M : ℕ)

abbrev InactiveEdge :=
  {e : G.E // (cell (key G) (key G e)).card < M}

abbrev Edge := InactiveEdge G M ⊕ Occurrence G M

def source : Edge G M → G.E
  | Sum.inl e => e.val
  | Sum.inr o => SubtwoLinearGrouping.source G M o

def target : Edge G M → G.E
  | Sum.inl e => e.val
  | Sum.inr o => SubtwoLinearGrouping.target G M o

def roundedWeight : Edge G M → ℝ
  | Sum.inl e => G.weight e.val
  | Sum.inr o => (typeGraph G M).weight o.1

theorem source_key (e : Edge G M) : key G (source G M e) = key G (target G M e) := by
  cases e with
  | inl e => rfl
  | inr o =>
      exact (key_predecessorItem (key G) M o).trans
        (key_targetItem (key G) M o).symm

theorem source_injective (hM : 0 < M) : Function.Injective (source G M) := by
  intro e f hef
  cases e with
  | inl e =>
      cases f with
      | inl f => exact congrArg Sum.inl (Subtype.ext hef)
      | inr o =>
          have hk := key_predecessorItem (key G) M o
          have he : key G e.val = o.1.keyValue := by
            change e.val = SubtwoLinearGrouping.source G M o at hef
            rw [hef]
            exact hk
          have hi := e.property
          rw [he] at hi
          exact (Nat.not_lt_of_ge o.1.active hi).elim
  | inr o =>
      cases f with
      | inl f =>
          have hk := key_predecessorItem (key G) M o
          have hf : key G f.val = o.1.keyValue := by
            change SubtwoLinearGrouping.source G M o = f.val at hef
            rw [← hef]
            exact hk
          have hi := f.property
          rw [hf] at hi
          exact (Nat.not_lt_of_ge o.1.active hi).elim
      | inr p =>
          exact congrArg Sum.inr (predecessorItem_injective (key G) M hM hef)

theorem target_injective : Function.Injective (target G M) := by
  intro e f hef
  cases e with
  | inl e =>
      cases f with
      | inl f => exact congrArg Sum.inl (Subtype.ext hef)
      | inr o =>
          have he : key G e.val = o.1.keyValue := by
            change e.val = SubtwoLinearGrouping.target G M o at hef
            rw [hef]
            exact key_targetItem (key G) M o
          have hi := e.property
          rw [he] at hi
          exact (Nat.not_lt_of_ge o.1.active hi).elim
  | inr o =>
      cases f with
      | inl f =>
          have hf : key G f.val = o.1.keyValue := by
            change SubtwoLinearGrouping.target G M o = f.val at hef
            rw [← hef]
            exact key_targetItem (key G) M o
          have hi := f.property
          rw [hf] at hi
          exact (Nat.not_lt_of_ge o.1.active hi).elim
      | inr p => exact congrArg Sum.inr (targetItem_injective (key G) M hef)

def graph : WeightedMultigraph.{u} where
  V := G.V
  E := Edge G M
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := Classical.decEq _
  fst := fun e => G.fst (target G M e)
  snd := fun e => G.snd (target G M e)
  noLoop := fun e => G.noLoop (target G M e)
  weight := roundedWeight G M
  weight_pos := by
    intro e
    cases e with
    | inl e => exact G.weight_pos e.val
    | inr o => exact (typeGraph G M).weight_pos o.1
  weight_le_one := by
    intro e
    cases e with
    | inl e => exact G.weight_le_one e.val
    | inr o => exact (typeGraph G M).weight_le_one o.1

theorem source_inc (v : G.V) (e : Edge G M) :
    G.Inc v (source G M e) ↔ (graph G M).Inc v e := by
  have h := source_key G M e
  have hf := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  change (G.fst (source G M e) = v ∨ G.snd (source G M e) = v) ↔
    (G.fst (target G M e) = v ∨ G.snd (target G M e) = v)
  exact or_congr (congrArg (fun x => x = v) hf |> Eq.to_iff)
    (congrArg (fun x => x = v) hs |> Eq.to_iff)

theorem target_inc (v : G.V) (e : Edge G M) :
    (graph G M).Inc v e ↔ G.Inc v (target G M e) := Iff.rfl

theorem weight_le_source (hM : 0 < M) (e : Edge G M) :
    (graph G M).weight e ≤ G.weight (source G M e) := by
  cases e with
  | inl e => exact le_rfl
  | inr o => exact roundedWeight_le_predecessorItem (key G) M hM o

theorem target_weight_le (e : Edge G M) :
    G.weight (target G M e) ≤ (graph G M).weight e := by
  cases e with
  | inl e => exact le_rfl
  | inr o => exact targetItem_weight_le_roundedWeight (key G) M o

theorem weight_ge (S : ℕ) (hlower : ∀ e, (1 : ℝ)/S ≤ G.weight e)
    (e : Edge G M) : (1 : ℝ)/S ≤ (graph G M).weight e := by
  cases e with
  | inl e => exact hlower e.val
  | inr o => exact SubtwoLinearGrouping.type_weight_ge G M S hlower o.1

def retained : Finset G.E := Finset.univ.image (target G M)

theorem omitted_subset_exceptions (hM : 0 < M) :
    Finset.univ \ retained G M ⊆
      keyedLinearExceptions Finset.univ (key G) G.weight M := by
  intro e he
  have hnot := (Finset.mem_sdiff.mp he).2
  by_cases ha : M ≤ (cell (key G) (key G e)).card
  · by_contra hex
    have hlocal : e ∉ linearCellExceptions (cell (key G) (key G e)) G.weight M := by
      intro h
      apply hex
      exact Finset.mem_biUnion.mpr ⟨key G e, Finset.mem_univ _, h⟩
    have ht := mem_targetItems_of_active_of_not_linearCellExceptions (key G) M hM e ha hlocal
    obtain ⟨o, _, ho⟩ := Finset.mem_image.mp ht
    apply hnot
    exact Finset.mem_image.mpr ⟨Sum.inr o, Finset.mem_univ _, ho⟩
  · exfalso
    apply hnot
    exact Finset.mem_image.mpr
      ⟨Sum.inl ⟨e, Nat.lt_of_not_ge ha⟩, Finset.mem_univ _, rfl⟩

theorem omitted_degree_le (hM : 0 < M) (v : G.V) :
    M * ((Finset.univ \ retained G M).filter (G.Inc v)).card ≤
      2 * ((Finset.univ : Finset G.E).filter (G.Inc v)).card := by
  classical
  have hc : PredicateConstantOnKeyCells (Finset.univ : Finset G.E) (key G) (G.Inc v) := by
    intro e _ f _ hef
    have hf := congrArg Prod.fst hef
    have hs := congrArg Prod.snd hef
    change (G.fst e = v ∨ G.snd e = v) ↔ (G.fst f = v ∨ G.snd f = v)
    rw [show G.fst e = G.fst f from hf, show G.snd e = G.snd f from hs]
  exact (Nat.mul_le_mul_left M (Finset.card_le_card
    (Finset.filter_subset_filter (G.Inc v) (omitted_subset_exceptions G M hM)))).trans
    (mul_card_filter_keyedLinearExceptions_le_two_mul
      Finset.univ (key G) G.weight (G.Inc v) hM hc)

theorem omitted_weight_le (hM : 0 < M) (S : ℕ) (hS : 0 < S)
    (hlower : ∀ e, (1 : ℝ)/S ≤ G.weight e) {n : ℕ}
    (hlocal : G.LocallyPacksInto n) (v : G.V) :
    (∑ e ∈ Finset.univ \ retained G M, if G.Inc v e then G.weight e else 0) ≤
      (2*(S : ℝ)/M)*n := by
  classical
  have hd := (omitted_degree_le G M hM v).trans
    (Nat.mul_le_mul_left 2 (G.degreeOn_univ_le_mul_of_reciprocal_weight_floor
      hS hlower hlocal v))
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hdR : (M : ℝ)*(((Finset.univ \ retained G M).filter (G.Inc v)).card : ℝ) ≤
      2*((n : ℝ)*S) := by exact_mod_cast hd
  have hcard : (((Finset.univ \ retained G M).filter (G.Inc v)).card : ℝ) ≤
      (2*(S : ℝ)/M)*n := by
    calc
      _ ≤ 2*((n : ℝ)*S)/M := (le_div_iff₀ hMR).2 (by nlinarith)
      _ = _ := by ring
  calc
    _ = ∑ e ∈ (Finset.univ \ retained G M).filter (G.Inc v), G.weight e := by
      rw [Finset.sum_filter]
    _ ≤ ∑ _e ∈ (Finset.univ \ retained G M).filter (G.Inc v), (1 : ℝ) :=
      Finset.sum_le_sum (fun e _ => G.weight_le_one e)
    _ = (((Finset.univ \ retained G M).filter (G.Inc v)).card : ℝ) := by simp
    _ ≤ _ := hcard

end SubtwoGlobalLinearGrouping
end
end WeightedEdgeColoring.WeightedMultigraph
