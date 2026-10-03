import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The three parameters for weighted edge coloring

This file formalizes the notation used in the weighted-edge-coloring
manuscript.  Edges have their own finite index type, so parallel edges remain
distinct.  Loops are forbidden.  Every edge has one weight in `(0,1]`, used at
both endpoints.

The main definitions are:

* `deltaW G`, the maximum total incident weight `Δ_w(G)`;
* `bpAt G v`, the bin-packing number of the star at `v`;
* `bp G`, the maximum local bin-packing number `bp(G)`;
* `chiW G`, the weighted chromatic index `χ'_w(G)`.

The last two optima are represented with `Nat.find`.  The theorem `bp_le_iff`
shows that the resulting common local optimum is exactly the maximum of the
individual star optima.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

universe u

/-- A finite loopless weighted multigraph.  Distinct edge indices may have the
same unordered pair of endpoints, so parallel edges are allowed. -/
structure WeightedMultigraph where
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
  WeightedMultigraph.instFintypeV
  WeightedMultigraph.instFintypeE
  WeightedMultigraph.instDecidableEqV
  WeightedMultigraph.instDecidableEqE

namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- Incidence of a vertex and an indexed edge. -/
def Inc (v : G.V) (e : G.E) : Prop := G.fst e = v ∨ G.snd e = v

instance instDecidableInc (v : G.V) (e : G.E) : Decidable (G.Inc v e) := by
  unfold Inc
  infer_instance

/-- The indexed edges incident with `v`. -/
abbrev StarEdge (v : G.V) := {e : G.E // G.Inc v e}

/-- `W_G(v)`: the sum of the weights incident with `v`. -/
def starWeight (v : G.V) : ℝ := ∑ e : G.StarEdge v, G.weight e.1

theorem weight_nonneg (e : G.E) : 0 ≤ G.weight e := (G.weight_pos e).le

/-- The load of weighted color `i` at vertex `v`. -/
def colorLoad {q : ℕ} (color : G.E → Fin q) (v : G.V) (i : Fin q) : ℝ :=
  ∑ e : G.StarEdge v, if color e.1 = i then G.weight e.1 else 0

/-- An edge-color assignment is feasible when every vertex-color load is at
most the unit capacity. -/
def IsWeightedColoring {q : ℕ} (color : G.E → Fin q) : Prop :=
  ∀ v i, G.colorLoad color v i ≤ 1

/-- The multigraph admits a feasible weighted edge coloring with `q` colors. -/
def HasWeightedColoring (q : ℕ) : Prop :=
  ∃ color : G.E → Fin q, G.IsWeightedColoring color

/-- The load of local bin `i` in a packing of the star at `v`. -/
def starBinLoad {n : ℕ} {v : G.V} (bin : G.StarEdge v → Fin n)
    (i : Fin n) : ℝ :=
  ∑ e : G.StarEdge v, if bin e = i then G.weight e.1 else 0

/-- The incident weights at `v` fit into `n` unit bins. -/
def PacksStarInto (v : G.V) (n : ℕ) : Prop :=
  ∃ bin : G.StarEdge v → Fin n, ∀ i, G.starBinLoad bin i ≤ 1

/-- Every vertex star fits into the same `n` unit bins. -/
def LocallyPacksInto (n : ℕ) : Prop := ∀ v, G.PacksStarInto v n

/-- A two-shore certificate.  Parallel edges may cross the same pair of
vertices; every indexed edge must cross the two shores. -/
structure Bipartition where
  side : G.V → Bool
  opposite : ∀ e, side (G.fst e) ≠ side (G.snd e)

/-- The weighted multigraph is bipartite if it has a two-shore certificate. -/
def IsBipartite : Prop := Nonempty G.Bipartition

/-- The total star weight is at most the number of bins in any local packing. -/
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

/-- Restricting a global coloring to one star gives a local bin packing. -/
theorem locallyPacksInto_of_hasWeightedColoring {q : ℕ}
    (h : G.HasWeightedColoring q) : G.LocallyPacksInto q := by
  rcases h with ⟨color, hcolor⟩
  intro v
  refine ⟨fun e => color e.1, ?_⟩
  intro i
  simpa only [starBinLoad, colorLoad] using hcolor v i

/-- Adding unused local bins preserves a packing. -/
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

/-- Adding unused common bins preserves all local packings. -/
theorem locallyPacksInto_mono {n m : ℕ} (hnm : n ≤ m)
    (h : G.LocallyPacksInto n) : G.LocallyPacksInto m :=
  fun v => G.packsStarInto_mono hnm (h v)

/-- Adding unused color names preserves a weighted coloring. -/
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

/-- Giving every indexed edge its own color is always feasible.  This remains
true with parallel edges because the edge indices, rather than their endpoint
pairs, receive colors. -/
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
        ≤ ∑ _e ∈ Finset.univ.filter fun e : G.StarEdge v => color e.1 = i,
            (1 : ℝ) := by
          exact Finset.sum_le_sum fun e _he => G.weight_le_one e.1
    _ = ((Finset.univ.filter fun e : G.StarEdge v => color e.1 = i).card : ℝ) := by
          simp
    _ ≤ 1 := by
      exact_mod_cast hcard

theorem exists_hasWeightedColoring : ∃ q, G.HasWeightedColoring q :=
  ⟨Fintype.card G.E, G.hasWeightedColoring_card⟩

theorem exists_locallyPacksInto : ∃ n, G.LocallyPacksInto n :=
  ⟨Fintype.card G.E,
    G.locallyPacksInto_of_hasWeightedColoring G.hasWeightedColoring_card⟩

theorem exists_packsStarInto (v : G.V) : ∃ n, G.PacksStarInto v n :=
  ⟨Fintype.card G.E,
    G.locallyPacksInto_of_hasWeightedColoring G.hasWeightedColoring_card v⟩

/-- `bp_v(G)`: the minimum number of unit bins needed at vertex `v`. -/
noncomputable def bpAt (v : G.V) : ℕ := by
  classical
  exact Nat.find (G.exists_packsStarInto v)

/-- `bp(G)`: the minimum common number of unit bins for all vertex stars.
The theorem `bp_le_iff` below characterizes it as `max_v bp_v(G)`. -/
noncomputable def bp : ℕ := by
  classical
  exact Nat.find G.exists_locallyPacksInto

/-- `χ'_w(G)`: the minimum number of feasible weighted edge colors. -/
noncomputable def chiW : ℕ := by
  classical
  exact Nat.find G.exists_hasWeightedColoring

theorem packsStarInto_bpAt (v : G.V) : G.PacksStarInto v (G.bpAt v) := by
  classical
  exact Nat.find_spec (G.exists_packsStarInto v)

theorem locallyPacksInto_bp : G.LocallyPacksInto G.bp := by
  classical
  exact Nat.find_spec G.exists_locallyPacksInto

theorem hasWeightedColoring_chiW : G.HasWeightedColoring G.chiW := by
  classical
  exact Nat.find_spec G.exists_hasWeightedColoring

theorem bpAt_le_of_packsStarInto {v : G.V} {n : ℕ}
    (h : G.PacksStarInto v n) : G.bpAt v ≤ n := by
  classical
  exact Nat.find_min' (G.exists_packsStarInto v) h

theorem bp_le_of_locallyPacksInto {n : ℕ} (h : G.LocallyPacksInto n) :
    G.bp ≤ n := by
  classical
  exact Nat.find_min' G.exists_locallyPacksInto h

theorem chiW_le_of_hasWeightedColoring {q : ℕ} (h : G.HasWeightedColoring q) :
    G.chiW ≤ q := by
  classical
  exact Nat.find_min' G.exists_hasWeightedColoring h

/-- Every individual star optimum is bounded by `bp(G)`. -/
theorem bpAt_le_bp (v : G.V) : G.bpAt v ≤ G.bp :=
  G.bpAt_le_of_packsStarInto (G.locallyPacksInto_bp v)

/-- This is the exact maximum characterization
`bp(G) = max_v bp_v(G)`, stated without imposing a nonempty vertex type. -/
theorem bp_le_iff {n : ℕ} : G.bp ≤ n ↔ ∀ v, G.bpAt v ≤ n := by
  constructor
  · intro h v
    exact (G.bpAt_le_bp v).trans h
  · intro h
    apply G.bp_le_of_locallyPacksInto
    intro v
    exact G.packsStarInto_mono (h v) (G.packsStarInto_bpAt v)

theorem locallyPacksInto_iff_bp_le {n : ℕ} :
    G.LocallyPacksInto n ↔ G.bp ≤ n := by
  constructor
  · exact G.bp_le_of_locallyPacksInto
  · intro h
    exact G.locallyPacksInto_mono h G.locallyPacksInto_bp

theorem hasWeightedColoring_iff_chiW_le {q : ℕ} :
    G.HasWeightedColoring q ↔ G.chiW ≤ q := by
  constructor
  · exact G.chiW_le_of_hasWeightedColoring
  · intro h
    exact G.hasWeightedColoring_mono h G.hasWeightedColoring_chiW

/-- The bounded finite set whose supremum defines `Δ_w(G)`.  The inserted
zero makes the definition agree with `0` when `G` has no vertices. -/
def starWeightsWithZero : Set ℝ := Set.range G.starWeight ∪ {0}

theorem starWeightsWithZero_nonempty : G.starWeightsWithZero.Nonempty := by
  exact ⟨0, by simp [starWeightsWithZero]⟩

theorem starWeightsWithZero_bddAbove : BddAbove G.starWeightsWithZero := by
  refine ⟨(Fintype.card G.E : ℝ), ?_⟩
  intro x hx
  simp only [starWeightsWithZero, Set.mem_union, Set.mem_range,
    Set.mem_singleton_iff] at hx
  rcases hx with ⟨v, rfl⟩ | rfl
  · exact G.starWeight_le_of_packsStarInto
      (G.locallyPacksInto_of_hasWeightedColoring G.hasWeightedColoring_card v)
  · exact_mod_cast Nat.zero_le (Fintype.card G.E)

/-- `Δ_w(G) = max_v W_G(v)`, with value zero for the empty graph. -/
noncomputable def deltaW : ℝ := sSup G.starWeightsWithZero

theorem starWeight_le_deltaW (v : G.V) : G.starWeight v ≤ G.deltaW := by
  apply le_csSup G.starWeightsWithZero_bddAbove
  exact Set.mem_union_left _ ⟨v, rfl⟩

theorem deltaW_nonneg : 0 ≤ G.deltaW := by
  apply le_csSup G.starWeightsWithZero_bddAbove
  exact Set.mem_union_right _ (Set.mem_singleton 0)

/-- Exact upper-bound characterization of the maximum weighted degree. -/
theorem deltaW_le_iff {x : ℝ} :
    G.deltaW ≤ x ↔ 0 ≤ x ∧ ∀ v, G.starWeight v ≤ x := by
  constructor
  · intro h
    exact ⟨G.deltaW_nonneg.trans h, fun v => (G.starWeight_le_deltaW v).trans h⟩
  · rintro ⟨hzero, hstar⟩
    apply csSup_le G.starWeightsWithZero_nonempty
    intro y hy
    simp only [starWeightsWithZero, Set.mem_union, Set.mem_range,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨v, rfl⟩ | rfl
    · exact hstar v
    · exact hzero

/-- Any common local `n`-bin packing gives `Δ_w(G) ≤ n`. -/
theorem deltaW_le_of_locallyPacksInto {n : ℕ} (h : G.LocallyPacksInto n) :
    G.deltaW ≤ n := by
  apply csSup_le G.starWeightsWithZero_nonempty
  intro x hx
  simp only [starWeightsWithZero, Set.mem_union, Set.mem_range,
    Set.mem_singleton_iff] at hx
  rcases hx with ⟨v, rfl⟩ | rfl
  · exact G.starWeight_le_of_packsStarInto (h v)
  · exact_mod_cast Nat.zero_le n

/-- The first standard inequality: `Δ_w(G) ≤ bp(G)`. -/
theorem deltaW_le_bp : G.deltaW ≤ G.bp :=
  G.deltaW_le_of_locallyPacksInto G.locallyPacksInto_bp

/-- The second standard inequality: `bp(G) ≤ χ'_w(G)`. -/
theorem bp_le_chiW : G.bp ≤ G.chiW :=
  G.bp_le_of_locallyPacksInto
    (G.locallyPacksInto_of_hasWeightedColoring G.hasWeightedColoring_chiW)

/-- The manuscript's complete chain `Δ_w(G) ≤ bp(G) ≤ χ'_w(G)`. -/
theorem deltaW_le_bp_and_bp_le_chiW :
    G.deltaW ≤ G.bp ∧ G.bp ≤ G.chiW :=
  ⟨G.deltaW_le_bp, G.bp_le_chiW⟩

end WeightedMultigraph

end WeightedEdgeColoring
