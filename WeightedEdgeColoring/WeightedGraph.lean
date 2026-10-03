import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Sym2

/-!
# Finite weighted simple graphs

This file gives a concrete, edge-indexed model for the graphs in the paper.
Using an edge index type keeps equal-weight edges distinct.  Injectivity of
the unordered endpoint map rules out parallel edges, while `noLoop` rules out
loops.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

universe u

/-- A finite simple graph with a weight in `(0, 1]` on every edge. -/
structure WeightedSimpleGraph where
  V : Type u
  E : Type u
  instFintypeV : Fintype V
  instFintypeE : Fintype E
  instDecidableEqV : DecidableEq V
  instDecidableEqE : DecidableEq E
  fst : E → V
  snd : E → V
  noLoop : ∀ e, fst e ≠ snd e
  simple : Function.Injective (fun e => s(fst e, snd e))
  weight : E → ℝ
  weight_pos : ∀ e, 0 < weight e
  weight_le_one : ∀ e, weight e ≤ 1

attribute [instance]
  WeightedSimpleGraph.instFintypeV
  WeightedSimpleGraph.instFintypeE
  WeightedSimpleGraph.instDecidableEqV
  WeightedSimpleGraph.instDecidableEqE

namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph)

/-- The two endpoint names of an edge, regarded as an unordered pair. -/
def endpoints (e : G.E) : Sym2 G.V := s(G.fst e, G.snd e)

theorem endpoints_injective : Function.Injective G.endpoints := G.simple

/-- Incidence of a vertex and an edge. -/
def Inc (v : G.V) (e : G.E) : Prop := G.fst e = v ∨ G.snd e = v

instance instDecidableInc (v : G.V) (e : G.E) : Decidable (G.Inc v e) := by
  unfold Inc
  infer_instance

/-- The indexed edges in the star at `v`. -/
abbrev StarEdge (v : G.V) := {e : G.E // G.Inc v e}

/-- Total weight of a star. -/
def starWeight (v : G.V) : ℝ := ∑ e : G.StarEdge v, G.weight e.1

theorem weight_nonneg (e : G.E) : 0 ≤ G.weight e := (G.weight_pos e).le

/-- A finite edge set is feasible as one weighted color. -/
def FeasibleColor (C : Finset G.E) : Prop :=
  ∀ v : G.V, ∑ e ∈ C.filter (G.Inc v), G.weight e ≤ 1

/-- The load of color `i` at vertex `v`. -/
def colorLoad {q : ℕ} (color : G.E → Fin q) (v : G.V) (i : Fin q) : ℝ :=
  ∑ e : G.StarEdge v, if color e.1 = i then G.weight e.1 else 0

/-- A partition of all edges into `q` feasible weighted colors. -/
def IsWeightedColoring {q : ℕ} (color : G.E → Fin q) : Prop :=
  ∀ v i, G.colorLoad color v i ≤ 1

/-- The graph has a weighted edge coloring with `q` colors. -/
def HasWeightedColoring (q : ℕ) : Prop :=
  ∃ color : G.E → Fin q, G.IsWeightedColoring color

/-- The load of bin `i` in a packing of the star at `v`. -/
def starBinLoad {n : ℕ} {v : G.V} (bin : G.StarEdge v → Fin n) (i : Fin n) : ℝ :=
  ∑ e : G.StarEdge v, if bin e = i then G.weight e.1 else 0

/-- The star at `v` can be packed into `n` unit bins. -/
def PacksStarInto (v : G.V) (n : ℕ) : Prop :=
  ∃ bin : G.StarEdge v → Fin n, ∀ i, G.starBinLoad bin i ≤ 1

/-- Every vertex star can be packed into the same `n` unit bins. -/
def LocallyPacksInto (n : ℕ) : Prop := ∀ v, G.PacksStarInto v n

/-- A two-shore certificate.  Isolated vertices may lie on either shore. -/
structure Bipartition where
  side : G.V → Bool
  opposite : ∀ e, side (G.fst e) ≠ side (G.snd e)

/-- The graph is bipartite if it admits a two-shore certificate. -/
def IsBipartite : Prop := Nonempty G.Bipartition

/-- The weight of a star is at most the number of bins in any star packing. -/
theorem starWeight_le_of_packsStarInto {v : G.V} {n : ℕ}
    (h : G.PacksStarInto v n) : G.starWeight v ≤ n := by
  rcases h with ⟨bin, hbin⟩
  calc
    G.starWeight v = ∑ i : Fin n, G.starBinLoad bin i := by
      simp only [starWeight, starBinLoad]
      rw [Finset.sum_comm]
      simp only [Fintype.sum_ite_eq]
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
      exact Finset.sum_le_sum fun i _hi => hbin i
    _ = n := by simp

/-- Equation (3) in the paper, in certificate form. -/
theorem starWeight_le_of_locallyPacksInto {n : ℕ}
    (h : G.LocallyPacksInto n) (v : G.V) : G.starWeight v ≤ n :=
  G.starWeight_le_of_packsStarInto (h v)

/-- A star packing remains valid after adding unused bins. -/
theorem packsStarInto_mono {v : G.V} {n m : ℕ} (hnm : n ≤ m)
    (h : G.PacksStarInto v n) : G.PacksStarInto v m := by
  rcases h with ⟨bin, hbin⟩
  refine ⟨fun e => Fin.castLE hnm (bin e), ?_⟩
  intro j
  by_cases hj : ∃ i : Fin n, Fin.castLE hnm i = j
  · rcases hj with ⟨i, rfl⟩
    simpa only [starBinLoad, Fin.castLE_inj] using hbin i
  · have hne : ∀ e : G.StarEdge v, Fin.castLE hnm (bin e) ≠ j := by
      intro e he
      exact hj ⟨bin e, he⟩
    simp only [starBinLoad, if_neg (hne _), Finset.sum_const_zero]
    exact zero_le_one

/-- A common local packing remains valid after adding unused bins. -/
theorem locallyPacksInto_mono {n m : ℕ} (hnm : n ≤ m)
    (h : G.LocallyPacksInto n) : G.LocallyPacksInto m :=
  fun v => G.packsStarInto_mono hnm (h v)

/-- Restricting a global coloring to a star gives a local bin packing. -/
theorem locallyPacksInto_of_hasWeightedColoring {q : ℕ}
    (h : G.HasWeightedColoring q) : G.LocallyPacksInto q := by
  rcases h with ⟨color, hcolor⟩
  intro v
  refine ⟨fun e => color e.1, ?_⟩
  intro i
  simpa only [starBinLoad, colorLoad] using hcolor v i

/-- A weighted coloring remains valid after adding unused color names. -/
theorem hasWeightedColoring_mono {q r : ℕ} (hqr : q ≤ r)
    (h : G.HasWeightedColoring q) : G.HasWeightedColoring r := by
  rcases h with ⟨color, hcolor⟩
  refine ⟨fun e => Fin.castLE hqr (color e), ?_⟩
  intro v j
  by_cases hj : ∃ i : Fin q, Fin.castLE hqr i = j
  · rcases hj with ⟨i, rfl⟩
    simpa only [colorLoad, Fin.castLE_inj] using hcolor v i
  · have hne : ∀ e : G.StarEdge v, Fin.castLE hqr (color e.1) ≠ j := by
      intro e he
      exact hj ⟨color e.1, he⟩
    simp only [colorLoad, if_neg (hne _), Finset.sum_const_zero]
    exact zero_le_one

/-- A subset of a feasible color remains feasible. -/
theorem feasibleColor_mono {C D : Finset G.E} (hC : G.FeasibleColor C)
    (hDC : D ⊆ C) : G.FeasibleColor D := by
  intro v
  refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (hC v)
  · intro e he
    exact Finset.mem_filter.mpr ⟨hDC (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  · intro e _heC _heD
    exact G.weight_nonneg e

/-- Every singleton edge is a feasible color. -/
theorem feasibleColor_singleton (e : G.E) : G.FeasibleColor {e} := by
  intro v
  by_cases h : G.Inc v e
  · rw [Finset.filter_singleton, if_pos h, Finset.sum_singleton]
    exact G.weight_le_one e
  · rw [Finset.filter_singleton, if_neg h, Finset.sum_empty]
    exact zero_le_one

/-- Assigning a distinct color to every edge always gives a coloring. -/
theorem hasWeightedColoring_card : G.HasWeightedColoring (Fintype.card G.E) := by
  let color : G.E → Fin (Fintype.card G.E) := Fintype.equivFin G.E
  refine ⟨color, ?_⟩
  intro v i
  rw [colorLoad, ← Finset.sum_filter]
  have hinj : Function.Injective color := (Fintype.equivFin G.E).injective
  have hcard : (Finset.univ.filter fun e : G.StarEdge v => color e.1 = i).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    apply Subtype.ext
    exact hinj ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  calc
    (∑ e ∈ Finset.univ.filter fun e : G.StarEdge v => color e.1 = i, G.weight e.1)
        ≤ ∑ _e ∈ Finset.univ.filter fun e : G.StarEdge v => color e.1 = i, (1 : ℝ) := by
          exact Finset.sum_le_sum fun e _he => G.weight_le_one e.1
    _ = ((Finset.univ.filter fun e : G.StarEdge v => color e.1 = i).card : ℝ) := by simp
    _ ≤ 1 := by
      have hcast := (Nat.cast_le.2 hcard :
        ((Finset.univ.filter fun e : G.StarEdge v => color e.1 = i).card : ℝ) ≤ ((1 : ℕ) : ℝ))
      simpa only [Nat.cast_one] using hcast

/-- There is always some common local bin bound. -/
theorem exists_locallyPacksInto : ∃ n, G.LocallyPacksInto n :=
  ⟨Fintype.card G.E, G.locallyPacksInto_of_hasWeightedColoring G.hasWeightedColoring_card⟩

/-- There is always some weighted coloring. -/
theorem exists_hasWeightedColoring : ∃ q, G.HasWeightedColoring q :=
  ⟨Fintype.card G.E, G.hasWeightedColoring_card⟩

/-- The minimum common number of bins needed by the vertex stars. -/
noncomputable def localBinNumber : ℕ := by
  classical
  exact Nat.find G.exists_locallyPacksInto

/-- The minimum number of feasible weighted colors. -/
noncomputable def weightedChromaticIndex : ℕ := by
  classical
  exact Nat.find G.exists_hasWeightedColoring

theorem locallyPacksInto_localBinNumber : G.LocallyPacksInto G.localBinNumber :=
  by
    classical
    exact Nat.find_spec G.exists_locallyPacksInto

theorem hasWeightedColoring_weightedChromaticIndex :
    G.HasWeightedColoring G.weightedChromaticIndex :=
  by
    classical
    exact Nat.find_spec G.exists_hasWeightedColoring

theorem localBinNumber_le_of_locallyPacksInto {n : ℕ}
    (h : G.LocallyPacksInto n) : G.localBinNumber ≤ n := by
  classical
  exact Nat.find_min' G.exists_locallyPacksInto h

theorem weightedChromaticIndex_le_of_hasWeightedColoring {q : ℕ}
    (h : G.HasWeightedColoring q) : G.weightedChromaticIndex ≤ q := by
  classical
  exact Nat.find_min' G.exists_hasWeightedColoring h

/-- Certificate and optimum forms of the local-bin hypothesis are equivalent. -/
theorem locallyPacksInto_iff_localBinNumber_le {n : ℕ} :
    G.LocallyPacksInto n ↔ G.localBinNumber ≤ n := by
  constructor
  · exact G.localBinNumber_le_of_locallyPacksInto
  · intro h
    exact G.locallyPacksInto_mono h G.locallyPacksInto_localBinNumber

/-- Certificate and optimum forms of the weighted-coloring conclusion are equivalent. -/
theorem hasWeightedColoring_iff_weightedChromaticIndex_le {q : ℕ} :
    G.HasWeightedColoring q ↔ G.weightedChromaticIndex ≤ q := by
  constructor
  · exact G.weightedChromaticIndex_le_of_hasWeightedColoring
  · intro h
    exact G.hasWeightedColoring_mono h G.hasWeightedColoring_weightedChromaticIndex

theorem weightedChromaticIndex_le_card :
    G.weightedChromaticIndex ≤ Fintype.card G.E :=
  G.weightedChromaticIndex_le_of_hasWeightedColoring G.hasWeightedColoring_card

/-- The paper's natural local lower bound. -/
theorem localBinNumber_le_weightedChromaticIndex :
    G.localBinNumber ≤ G.weightedChromaticIndex :=
  G.localBinNumber_le_of_locallyPacksInto
    (G.locallyPacksInto_of_hasWeightedColoring G.hasWeightedColoring_weightedChromaticIndex)

end WeightedSimpleGraph

end WeightedEdgeColoring
