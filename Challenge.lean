import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Sym.Sym2

/-!
# Five weighted edge-coloring challenges

This file is self-contained apart from Mathlib.  It contains the graph model,
the three parameters used in the statements and the
five main problem statements from the manuscript.

The graph is edge-indexed, so distinct edges may have the same two endpoints.
Every edge has a weight in `(0, 1]`, and loops are forbidden.

Authors: Rishikesh Gajjala (NYU Abu Dhabi) and Arindam Khan (IISc).
-/

open scoped BigOperators

namespace WeightedEdgeColoringChallenge

universe u

/-- A finite loopless weighted multigraph.  Parallel edges are represented by
distinct elements of `E` with the same endpoints. -/
structure WeightedGraph where
  V : Type u
  E : Type u
  instFintypeV : Fintype V
  instFintypeE : Fintype E
  instDecidableEqV : DecidableEq V
  instDecidableEqE : DecidableEq E
  fst : E → V
  snd : E → V
  noLoop : ∀ e, fst e ≠ snd e
  weight : E → ℝ
  weight_pos : ∀ e, 0 < weight e
  weight_le_one : ∀ e, weight e ≤ 1

attribute [instance]
  WeightedGraph.instFintypeV
  WeightedGraph.instFintypeE
  WeightedGraph.instDecidableEqV
  WeightedGraph.instDecidableEqE

namespace WeightedGraph

variable (G : WeightedGraph.{u})

/-- Vertex-edge incidence. -/
def Inc (v : G.V) (e : G.E) : Prop :=
  G.fst e = v ∨ G.snd e = v

instance instDecidableInc (v : G.V) (e : G.E) : Decidable (G.Inc v e) := by
  unfold Inc
  infer_instance

/-- The indexed edges incident with `v`. -/
abbrev StarEdge (v : G.V) := {e : G.E // G.Inc v e}

/-- The total weight incident with `v`. -/
def starWeight (v : G.V) : ℝ :=
  ∑ e : G.StarEdge v, G.weight e.1

/-- The graph has no parallel edges.  The unordered endpoint map is injective. -/
def IsSimple : Prop :=
  Function.Injective (fun e : G.E ↦ s(G.fst e, G.snd e))

/-- A bipartition certificate. -/
structure Bipartition where
  side : G.V → Bool
  opposite : ∀ e, side (G.fst e) ≠ side (G.snd e)

/-- The graph is bipartite. -/
def IsBipartite : Prop := Nonempty G.Bipartition

/-- The load of color `i` at vertex `v`. -/
def colorLoad {q : ℕ} (color : G.E → Fin q) (v : G.V) (i : Fin q) : ℝ :=
  ∑ e : G.StarEdge v, if color e.1 = i then G.weight e.1 else 0

/-- A weighted coloring is feasible when every vertex-color load is at most
one. -/
def IsWeightedColoring {q : ℕ} (color : G.E → Fin q) : Prop :=
  ∀ v i, G.colorLoad color v i ≤ 1

/-- The graph has a feasible weighted edge coloring with `q` colors. -/
def HasWeightedColoring (q : ℕ) : Prop :=
  ∃ color : G.E → Fin q, G.IsWeightedColoring color

/-- The load of local bin `i` in a packing of the star at `v`. -/
def starBinLoad {n : ℕ} {v : G.V} (bin : G.StarEdge v → Fin n)
    (i : Fin n) : ℝ :=
  ∑ e : G.StarEdge v, if bin e = i then G.weight e.1 else 0

/-- The edges incident with `v` fit into `n` unit bins. -/
def PacksStarInto (v : G.V) (n : ℕ) : Prop :=
  ∃ bin : G.StarEdge v → Fin n, ∀ i, G.starBinLoad bin i ≤ 1

/-- Every vertex star fits into the same `n` unit bins. -/
def LocallyPacksInto (n : ℕ) : Prop :=
  ∀ v, G.PacksStarInto v n

/-- Giving every edge a distinct color is always feasible. -/
theorem hasWeightedColoring_card :
    G.HasWeightedColoring (Fintype.card G.E) := by
  let color : G.E → Fin (Fintype.card G.E) := Fintype.equivFin G.E
  refine ⟨color, ?_⟩
  intro v i
  rw [colorLoad, ← Finset.sum_filter]
  have hinj : Function.Injective color := (Fintype.equivFin G.E).injective
  have hcard :
      (Finset.univ.filter fun e : G.StarEdge v ↦ color e.1 = i).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    apply Subtype.ext
    exact hinj ((Finset.mem_filter.mp ha).2.trans
      (Finset.mem_filter.mp hb).2.symm)
  calc
    (∑ e ∈ Finset.univ.filter (fun e : G.StarEdge v ↦ color e.1 = i),
        G.weight e.1)
        ≤ ∑ _e ∈ Finset.univ.filter
            (fun e : G.StarEdge v ↦ color e.1 = i), (1 : ℝ) := by
          exact Finset.sum_le_sum fun e _he ↦ G.weight_le_one e.1
    _ = ((Finset.univ.filter
          (fun e : G.StarEdge v ↦ color e.1 = i)).card : ℝ) := by simp
    _ ≤ 1 := by exact_mod_cast hcard

/-- A global coloring restricts to a packing of every star. -/
theorem locallyPacksInto_of_hasWeightedColoring {q : ℕ}
    (h : G.HasWeightedColoring q) : G.LocallyPacksInto q := by
  rcases h with ⟨color, hcolor⟩
  intro v
  refine ⟨fun e ↦ color e.1, ?_⟩
  intro i
  simpa only [starBinLoad, colorLoad] using hcolor v i

theorem exists_hasWeightedColoring : ∃ q, G.HasWeightedColoring q :=
  ⟨Fintype.card G.E, G.hasWeightedColoring_card⟩

theorem exists_locallyPacksInto : ∃ n, G.LocallyPacksInto n :=
  ⟨Fintype.card G.E,
    G.locallyPacksInto_of_hasWeightedColoring G.hasWeightedColoring_card⟩

/-- `bp(G)`: the least common number of unit bins needed by all vertex
stars. -/
noncomputable def bp : ℕ := by
  classical
  exact Nat.find G.exists_locallyPacksInto

/-- `chi'_w(G)`: the least number of feasible weighted edge colors. -/
noncomputable def chiW : ℕ := by
  classical
  exact Nat.find G.exists_hasWeightedColoring

/-- The finite set of star weights, with zero included for an empty vertex
type. -/
def starWeightsWithZero : Set ℝ :=
  Set.range G.starWeight ∪ {0}

/-- `Delta_w(G)`: the maximum total weight incident with one vertex. -/
noncomputable def deltaW : ℝ :=
  sSup G.starWeightsWithZero

end WeightedGraph

/-!
## The five problems

Every little-oh term below is uniform.  Its threshold may depend on the
requested error `ε`, but not on the number of vertices, the number of
parallel edges, or the smallest positive edge weight.
-/

/-- **Problem 1: simple graphs, local bin packing.**

Prove `chi'_w(G) <= bp(G) + o(bp(G))` for every finite simple weighted
graph. -/
def Problem1SimpleBP : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ G : WeightedGraph.{u},
    G.IsSimple →
    N ≤ G.bp →
    (G.chiW : ℝ) ≤ (1 + ε) * (G.bp : ℝ)

/-- **Problem 2: bipartite multigraphs, weighted degree.**

Prove `chi'_w(G) <= 2 Delta_w(G) + o(Delta_w(G))`. -/
def Problem2BipartiteDelta : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ G : WeightedGraph.{u},
    G.IsBipartite →
    (N : ℝ) ≤ G.deltaW →
    (G.chiW : ℝ) ≤ (2 + ε) * G.deltaW

/-- **Problem 3: bipartite multigraphs, local bin packing.**

Prove `chi'_w(G) <= (81/50) bp(G) + o(bp(G))`. -/
def Problem3BipartiteBP : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ G : WeightedGraph.{u},
    G.IsBipartite →
    N ≤ G.bp →
    (G.chiW : ℝ) ≤ ((81 / 50 : ℝ) + ε) * (G.bp : ℝ)

/-- **Problem 4: general multigraphs, weighted degree.**

Prove the exact bound `chi'_w(G) <= 3 * ceil(Delta_w(G))`. -/
def Problem4GeneralDelta : Prop :=
  ∀ G : WeightedGraph.{u},
    G.chiW ≤ 3 * Nat.ceil G.deltaW

/-- **Problem 5: general multigraphs, local bin packing.**

Prove `chi'_w(G) <= (1999/1000) bp(G) + o(bp(G))` for every finite
loopless weighted multigraph. `Solutions.lean` proves this statement by
transporting the unrestricted theorem to this self-contained graph model. -/
def Problem5GeneralBP : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ G : WeightedGraph.{u},
    N ≤ G.bp →
    (G.chiW : ℝ) ≤ ((1999 / 1000 : ℝ) + ε) * (G.bp : ℝ)

/-- A convenient bundle for work that addresses all five problems. -/
structure Solutions where
  problem1 : Problem1SimpleBP.{u}
  problem2 : Problem2BipartiteDelta.{u}
  problem3 : Problem3BipartiteBP.{u}
  problem4 : Problem4GeneralDelta.{u}
  problem5 : Problem5GeneralBP.{u}

end WeightedEdgeColoringChallenge
