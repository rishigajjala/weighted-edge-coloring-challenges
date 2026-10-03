import Challenge
import WeightedEdgeColoring.SubtwoUnrestrictedProof
import WeightedEdgeColoring.ShannonBridge
import WeightedEdgeColoring.BipartiteHarmonicChargeColoringUnconditional
import WeightedEdgeColoring.BipartiteTotalWeightAsymptotic
import WeightedEdgeColoring.SimpleUniformMultiplePartialRoundingProof

/-! Bridges the self-contained challenge graph to the verified WeightedEdgeColoring graph. -/

namespace WeightedEdgeColoringChallenge

universe u

noncomputable def WeightedGraph.toMultigraph (G : WeightedGraph.{u}) :
    WeightedEdgeColoring.WeightedMultigraph.{u} where
  V := G.V
  E := G.E
  instFintypeV := G.instFintypeV
  instFintypeE := G.instFintypeE
  instDecidableEqV := G.instDecidableEqV
  instDecidableEqE := G.instDecidableEqE
  fst := G.fst
  snd := G.snd
  noLoop := G.noLoop
  weight := G.weight
  weight_pos := G.weight_pos
  weight_le_one := G.weight_le_one

private theorem bp_eq (G : WeightedGraph.{u}) : G.toMultigraph.bp = G.bp := by
  rfl

private theorem chiW_eq (G : WeightedGraph.{u}) : G.toMultigraph.chiW = G.chiW := by
  rfl

private theorem deltaW_eq (G : WeightedGraph.{u}) : G.toMultigraph.deltaW = G.deltaW := by
  rfl

noncomputable def WeightedGraph.toSimpleGraph (G : WeightedGraph.{u})
    (hsimple : G.IsSimple) : WeightedEdgeColoring.WeightedSimpleGraph.{u} where
  V := G.V
  E := G.E
  instFintypeV := G.instFintypeV
  instFintypeE := G.instFintypeE
  instDecidableEqV := G.instDecidableEqV
  instDecidableEqE := G.instDecidableEqE
  fst := G.fst
  snd := G.snd
  noLoop := G.noLoop
  simple := hsimple
  weight := G.weight
  weight_pos := G.weight_pos
  weight_le_one := G.weight_le_one

private theorem simple_bp_eq (G : WeightedGraph.{u}) (hsimple : G.IsSimple) :
    (G.toSimpleGraph hsimple).localBinNumber = G.bp := by
  rfl

private theorem simple_chiW_eq (G : WeightedGraph.{u}) (hsimple : G.IsSimple) :
    (G.toSimpleGraph hsimple).weightedChromaticIndex = G.chiW := by
  rfl

private theorem bipartite (G : WeightedGraph.{u}) (h : G.IsBipartite) :
    G.toMultigraph.IsBipartite := by
  obtain ⟨b⟩ := h
  exact ⟨{ side := b.side, opposite := b.opposite }⟩

theorem solve_problem_1 : Problem1SimpleBP.{u} := by
  intro ε hε
  obtain ⟨N, hN⟩ := WeightedEdgeColoring.simpleVizingAsymptotic_proved ε hε
  refine ⟨N, ?_⟩
  intro G hsimple hbp
  have h : N ≤ (G.toSimpleGraph hsimple).localBinNumber := by
    rw [simple_bp_eq]; exact hbp
  have hbound := hN (G.toSimpleGraph hsimple) h
  rwa [simple_chiW_eq, simple_bp_eq] at hbound

theorem solve_problem_2 : Problem2BipartiteDelta.{u} := by
  intro ε hε
  obtain ⟨N, hN⟩ :=
    WeightedEdgeColoring.bipartiteMultigraphDeltaAsymptotic_of_harmonicChargeColoring
      WeightedEdgeColoring.bipartiteHarmonicChargeColoring_proved ε hε
  refine ⟨N, ?_⟩
  intro G hbip hdelta
  have h : (N : ℝ) ≤ G.toMultigraph.deltaW := by
    rwa [deltaW_eq]
  have hbound := hN G.toMultigraph (bipartite G hbip) h
  rwa [chiW_eq, deltaW_eq] at hbound

theorem solve_problem_3 : Problem3BipartiteBP.{u} := by
  intro ε hε
  obtain ⟨N, hN⟩ := WeightedEdgeColoring.bipartiteMultigraphBPAsymptotic_proved ε hε
  refine ⟨N, ?_⟩
  intro G hbip hbp
  have h : N ≤ G.toMultigraph.bp := by rw [bp_eq]; exact hbp
  have hbound := hN G.toMultigraph (bipartite G hbip) h
  rwa [chiW_eq, bp_eq] at hbound

theorem solve_problem_4 : Problem4GeneralDelta.{u} := by
  intro G
  have h := WeightedEdgeColoring.WeightedMultigraph.generalMultigraphThreeCeil_proved G.toMultigraph
  rwa [chiW_eq, deltaW_eq] at h

theorem solve_problem_5 : Problem5GeneralBP.{u} := by
  intro ε hε
  obtain ⟨N, hN⟩ := WeightedEdgeColoring.chiW_le_1999_add_epsilon_mul_bp ε hε
  refine ⟨N, ?_⟩
  intro G hbp
  have h : N ≤ G.toMultigraph.bp := by rw [bp_eq]; exact hbp
  have hbound := hN G.toMultigraph h
  rwa [chiW_eq, bp_eq] at hbound

end WeightedEdgeColoringChallenge
