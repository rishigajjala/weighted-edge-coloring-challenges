import WeightedEdgeColoring.WeightedGraph
import WeightedEdgeColoring.WeightedMultigraph
import WeightedEdgeColoring.HarmonicConstant
import Mathlib.Algebra.Order.Floor.Ring

/-!
# The three main asymptotic targets

The little-oh terms in the manuscript are uniform over all finite graphs.
We therefore state each result in epsilon--threshold form.  In particular,
the threshold cannot depend on the number of vertices, the number of
parallel edges, or the smallest edge weight.

The three definitions below are theorem statements.  A declaration of type
one of these propositions is a proof; merely defining the proposition is not.
-/

namespace WeightedEdgeColoring

universe u

/-- Uniform meaning of
`chi'_w(G) ≤ bp(G) + o(bp(G))` for finite simple weighted graphs. -/
def SimpleVizingAsymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ G : WeightedSimpleGraph.{u},
    N ≤ G.localBinNumber →
    (G.weightedChromaticIndex : ℝ) ≤
      (1 + ε) * (G.localBinNumber : ℝ)

/-- Uniform meaning of
`chi'_w(G) ≤ (81 / 50) bp(G) + o(bp(G))` for finite bipartite weighted
multigraphs. -/
def BipartiteMultigraphBPAsymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ G : WeightedMultigraph.{u},
    G.IsBipartite →
    N ≤ G.bp →
    (G.chiW : ℝ) ≤ ((81 / 50 : ℝ) + ε) * (G.bp : ℝ)

/-- Uniform meaning of
`chi'_w(G) ≤ (h + 2 / 5) bp(G) + o(bp(G))` for all finite loopless
weighted multigraphs.  The parameter `h` is intended to be the harmonic
bin-packing constant `h∞`. -/
def GeneralMultigraphBPAsymptoticAt (h : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ G : WeightedMultigraph.{u},
    N ≤ G.bp →
    (G.chiW : ℝ) ≤ (h + (2 / 5 : ℝ) + ε) * (G.bp : ℝ)

/-- The manuscript's additive-constant form of the general multigraph
bin-packing bound.  The constant may depend on the requested accuracy but is
uniform in the graph order, parallel multiplicities, and edge weights. -/
def GeneralMultigraphBPAdditiveAt (h : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ G : WeightedMultigraph.{u},
    (G.chiW : ℝ) ≤
      (h + (2 / 5 : ℝ) + ε) * (G.bp : ℝ) + C

/-- A graph-independent additive constant is absorbed by half of the requested
linear error once `bp(G)` is large enough. -/
theorem generalMultigraphBPAsymptoticAt_of_additive (h : ℝ)
    (hadd : GeneralMultigraphBPAdditiveAt.{u} h) :
    GeneralMultigraphBPAsymptoticAt.{u} h := by
  intro ε hε
  obtain ⟨C, hC⟩ := hadd (ε / 2) (half_pos hε)
  let N : ℕ := Nat.ceil (2 * max C 0 / ε)
  refine ⟨N, ?_⟩
  intro G hN
  have hratio : 2 * max C 0 / ε ≤ (G.bp : ℝ) := by
    calc
      2 * max C 0 / ε ≤ (N : ℝ) := by
        exact Nat.le_ceil (2 * max C 0 / ε)
      _ ≤ (G.bp : ℝ) := by exact_mod_cast hN
  have htwice : 2 * max C 0 ≤ (G.bp : ℝ) * ε :=
    (div_le_iff₀ hε).mp hratio
  have hCsmall : C ≤ (ε / 2) * (G.bp : ℝ) := by
    calc
      C ≤ max C 0 := le_max_left C 0
      _ = (2 * max C 0) / 2 := by ring
      _ ≤ ((G.bp : ℝ) * ε) / 2 := by gcongr
      _ = (ε / 2) * (G.bp : ℝ) := by ring
  calc
    (G.chiW : ℝ) ≤
        (h + (2 / 5 : ℝ) + ε / 2) * (G.bp : ℝ) + C := hC G
    _ ≤ (h + (2 / 5 : ℝ) + ε / 2) * (G.bp : ℝ) +
        (ε / 2) * (G.bp : ℝ) := by gcongr
    _ = (h + (2 / 5 : ℝ) + ε) * (G.bp : ℝ) := by ring

/-- The exact general-multigraph target from the manuscript, specialized to
the Sylvester-series harmonic bin-packing constant. -/
def GeneralMultigraphBPAsymptotic : Prop :=
  GeneralMultigraphBPAsymptoticAt.{u} harmonicBinPackingConstant

/-- Additive-constant form of the exact harmonic general-multigraph target. -/
def GeneralMultigraphBPAdditive : Prop :=
  GeneralMultigraphBPAdditiveAt.{u} harmonicBinPackingConstant

theorem generalMultigraphBPAsymptotic_of_additive
    (hadd : GeneralMultigraphBPAdditive.{u}) :
    GeneralMultigraphBPAsymptotic.{u} :=
  generalMultigraphBPAsymptoticAt_of_additive
    harmonicBinPackingConstant hadd

/-- Uniform meaning of
`chi'_w(G) ≤ 2 Delta_w(G) + o(Delta_w(G))` for bipartite weighted
multigraphs. -/
def BipartiteMultigraphDeltaAsymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ G : WeightedMultigraph.{u},
    G.IsBipartite →
    (N : ℝ) ≤ G.deltaW →
    (G.chiW : ℝ) ≤ (2 + ε) * G.deltaW

/-- Uniform meaning of
`chi'_w(G) ≤ 3 Delta_w(G) + o(Delta_w(G))` for all finite loopless
weighted multigraphs. -/
def GeneralMultigraphDeltaAsymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ G : WeightedMultigraph.{u},
    (N : ℝ) ≤ G.deltaW →
    (G.chiW : ℝ) ≤ (3 + ε) * G.deltaW

/-- The stronger exact statement behind the general-multigraph asymptotic
bound.  Its combinatorial proof is the Shannon-style greedy-skeleton proof. -/
def GeneralMultigraphThreeCeil : Prop :=
  ∀ G : WeightedMultigraph.{u}, G.chiW ≤ 3 * Nat.ceil G.deltaW

/-- The exact `3 * ceil Delta_w` bound implies the uniform asymptotic
coefficient-three theorem.  This theorem discharges all ceiling and
little-oh bookkeeping; the remaining content is combinatorial. -/
theorem generalMultigraphDeltaAsymptotic_of_threeCeil
    (h : GeneralMultigraphThreeCeil.{u}) :
    GeneralMultigraphDeltaAsymptotic.{u} := by
  intro ε hε
  let N : ℕ := Nat.ceil (3 / ε)
  refine ⟨N, ?_⟩
  intro G hN
  have hthree_div : 3 / ε ≤ G.deltaW := by
    calc
      3 / ε ≤ (N : ℝ) := by
        exact Nat.le_ceil (3 / ε)
      _ ≤ G.deltaW := hN
  have hthree : 3 ≤ ε * G.deltaW := by
    simpa [mul_comm] using (div_le_iff₀ hε).mp hthree_div
  have hceil : ((Nat.ceil G.deltaW : ℕ) : ℝ) ≤ G.deltaW + 1 :=
    (Nat.ceil_lt_add_one G.deltaW_nonneg).le
  calc
    (G.chiW : ℝ) ≤ (3 * Nat.ceil G.deltaW : ℕ) := by
      exact_mod_cast h G
    _ = 3 * (Nat.ceil G.deltaW : ℝ) := by norm_num
    _ ≤ 3 * (G.deltaW + 1) := by gcongr
    _ = 3 * G.deltaW + 3 := by ring
    _ ≤ 3 * G.deltaW + ε * G.deltaW := by gcongr
    _ = (3 + ε) * G.deltaW := by ring

end WeightedEdgeColoring
