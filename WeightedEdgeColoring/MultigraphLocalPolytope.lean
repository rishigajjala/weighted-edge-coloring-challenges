import WeightedEdgeColoring.CardinalityLocalPolytope
import WeightedEdgeColoring.WeightedMultigraph

/-!
# Local packing polytopes for indexed multigraphs

Parallel edges cause no difficulty in a single vertex star: they remain
distinct members of the finite subtype `StarEdge v`.  This file gives the
multigraph analogue of `LocalPolytope` and connects the finite size-class
lemma to that interface.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- A subset of one multigraph star that fits in a unit color. -/
def StarFeasible (v : G.V) (S : Finset (G.StarEdge v)) : Prop :=
  ∑ e ∈ S, G.weight e.1 ≤ 1

/-- A local proposal is in the star packing polytope if it is the marginal
vector of a finite distribution on feasible star subsets. -/
def IsAverageOfStarFeasibleSets (v : G.V)
    (x : G.StarEdge v → ℝ) : Prop :=
  ∃ (m : ℕ) (p : Fin m → ℝ)
      (outcome : Fin m → Finset (G.StarEdge v)),
    (∀ i, 0 ≤ p i) ∧
    (∑ i, p i = 1) ∧
    (∀ i, G.StarFeasible v (outcome i)) ∧
    (∀ e, (∑ i, if e ∈ outcome i then p i else 0) = x e)

/-- The fiber of one local bin is a feasible star subset. -/
theorem starFeasible_binFiber
    {v : G.V} {n : ℕ} (bin : G.StarEdge v → Fin n)
    (hbin : ∀ i, G.starBinLoad bin i ≤ 1) (i : Fin n) :
    G.StarFeasible v (Finset.univ.filter fun e => bin e = i) := by
  simpa only [StarFeasible, starBinLoad, Finset.sum_filter] using hbin i

/-- A local packing gives the uniform reciprocal marginal vector. -/
theorem uniform_average_of_packsStarInto
    {v : G.V} {n : ℕ} (hn : 0 < n) (hpack : G.PacksStarInto v n) :
    G.IsAverageOfStarFeasibleSets v (fun _ => 1 / (n : ℝ)) := by
  rcases hpack with ⟨bin, hbin⟩
  let outcome : Fin n → Finset (G.StarEdge v) :=
    fun i => Finset.univ.filter fun e => bin e = i
  refine ⟨n, (fun _ => 1 / (n : ℝ)), outcome, ?_, ?_, ?_, ?_⟩
  · intro i
    exact one_div_nonneg.mpr (Nat.cast_nonneg n)
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    simp [hn0]
  · intro i
    exact G.starFeasible_binFiber bin hbin i
  · intro e
    simp [outcome]

/-- Uniform proposals belong to every locally packed multigraph star. -/
theorem uniform_local_proposals_of_locallyPacksInto
    {n : ℕ} (hn : 0 < n) (hpack : G.LocallyPacksInto n) :
    ∀ v, G.IsAverageOfStarFeasibleSets v (fun _ => 1 / (n : ℝ)) := by
  intro v
  exact G.uniform_average_of_packsStarInto hn (hpack v)

/-- Reindex a distribution on all finite subsets by a finite sample space. -/
theorem isAverageOfStarFeasibleSets_of_subsetAverage
    {v : G.V} {x : G.StarEdge v → ℝ}
    (h : IsAverageOfFeasibleSubsets
      (fun e : G.StarEdge v ↦ G.weight e.1) 1 x) :
    G.IsAverageOfStarFeasibleSets v x := by
  classical
  rcases h with ⟨mass, hmass0, htotal, hsupport, hmarg⟩
  let equiv := Fintype.equivFin (Finset (G.StarEdge v))
  let m := Fintype.card (Finset (G.StarEdge v))
  let raw : Fin m → Finset (G.StarEdge v) := fun i ↦ equiv.symm i
  let outcome : Fin m → Finset (G.StarEdge v) := fun i ↦
    if mass (raw i) = 0 then ∅ else raw i
  let p : Fin m → ℝ := fun i ↦ mass (raw i)
  refine ⟨m, p, outcome, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hmass0 (raw i)
  · calc
      (∑ i, p i) = ∑ S : Finset (G.StarEdge v), mass S := by
        simpa [p, raw, equiv, m] using equiv.symm.sum_comp mass
      _ = 1 := htotal
  · intro i
    unfold StarFeasible
    by_cases hi : mass (raw i) = 0
    · simp [outcome, hi]
    · simpa [outcome, hi] using hsupport (raw i) hi
  · intro e
    calc
      (∑ i, if e ∈ outcome i then p i else 0) =
          ∑ i, if e ∈ raw i then mass (raw i) else 0 := by
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases hz : mass (raw i) = 0 <;>
          simp [outcome, p, hz]
      _ = ∑ S : Finset (G.StarEdge v),
          if e ∈ S then mass S else 0 := by
        simpa [raw, equiv, m] using equiv.symm.sum_comp
          (fun S : Finset (G.StarEdge v) ↦ if e ∈ S then mass S else 0)
      _ = x e := hmarg e

/-- Finitely many harmonic size classes give a point of the exact local
star packing polytope.  Class `a` is allowed to contribute at most
`capacity a` edges in an outcome. -/
theorem sizeClasses_isAverageOfStarFeasibleSets
    {v : G.V} {K : Type*} [Fintype K] [DecidableEq K]
    (capacity : K → ℕ) (hcapacity : ∀ a, 0 < capacity a)
    (classOf : G.StarEdge v → K)
    (x : G.StarEdge v → ℝ) (p : K → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a ≤ 1)
    (hw : ∀ e, G.weight e.1 ≤ (1 : ℝ) / capacity (classOf e))
    (hx0 : ∀ e, 0 ≤ x e)
    (hxpoint : ∀ e, x e ≤ p (classOf e))
    (hxclass : ∀ a,
      (∑ e, if classOf e = a then x e else 0) ≤
        (capacity a : ℝ) * p a) :
    G.IsAverageOfStarFeasibleSets v x := by
  apply G.isAverageOfStarFeasibleSets_of_subsetAverage
  exact sizeClasses_isAverageOfFeasibleSubsets capacity hcapacity classOf
    (fun e : G.StarEdge v ↦ G.weight e.1) x p hp0 hpsum
    (fun e ↦ (G.weight_pos e.1).le) hw hx0 hxpoint hxclass

/-- Charge-and-diffuseness form of the multigraph star lemma.  This is the
local conclusion needed by a bounded-multiplicity whole-edge rounder after
weighted-moment mixing. -/
theorem sizeClasses_isAverageOfStarFeasibleSets_of_charge
    {v : G.V} {K : Type*} [Fintype K] [DecidableEq K]
    (capacity : K → ℕ) (hcapacity : ∀ a, 0 < capacity a)
    (classOf : G.StarEdge v → K)
    (x : G.StarEdge v → ℝ) (M : ℝ)
    (hw : ∀ e, G.weight e.1 ≤ (1 : ℝ) / capacity (classOf e))
    (hx0 : ∀ e, 0 ≤ x e) (hM0 : 0 ≤ M)
    (hxM : ∀ e, x e ≤ M)
    (hbudget :
      (∑ e, x e / (capacity (classOf e) : ℝ)) +
          (Fintype.card K : ℝ) * M ≤ 1) :
    G.IsAverageOfStarFeasibleSets v x := by
  apply G.isAverageOfStarFeasibleSets_of_subsetAverage
  exact sizeClasses_isAverageOfFeasibleSubsets_of_charge
    capacity hcapacity classOf
    (fun e : G.StarEdge v ↦ G.weight e.1) x M
    (fun e ↦ (G.weight_pos e.1).le) hw hx0 hM0 hxM hbudget

end WeightedMultigraph
end WeightedEdgeColoring
