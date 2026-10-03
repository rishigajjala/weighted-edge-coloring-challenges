import WeightedEdgeColoring.BipartitePackets

/-!
# Scaling all edge weights

This small adapter lets us reuse packetization after restricting to edges
below a fixed threshold.  The vertex and edge types and both endpoint maps
are unchanged; only the common weight function is multiplied by a positive
factor.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- Multiply every edge weight by `s`.  The caller supplies the unit-capacity
bound required of a weighted multigraph. -/
def scaleWeights (s : ℝ) (hs : 0 < s)
    (hupper : ∀ e, s * G.weight e ≤ 1) : WeightedMultigraph.{u} where
  V := G.V
  E := G.E
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := inferInstance
  fst := G.fst
  snd := G.snd
  noLoop := G.noLoop
  weight e := s * G.weight e
  weight_pos e := mul_pos hs (G.weight_pos e)
  weight_le_one := hupper

@[simp] theorem scaleWeights_fst (s : ℝ) (hs : 0 < s)
    (hupper : ∀ e, s * G.weight e ≤ 1) (e : G.E) :
    (G.scaleWeights s hs hupper).fst e = G.fst e := rfl

@[simp] theorem scaleWeights_snd (s : ℝ) (hs : 0 < s)
    (hupper : ∀ e, s * G.weight e ≤ 1) (e : G.E) :
    (G.scaleWeights s hs hupper).snd e = G.snd e := rfl

@[simp] theorem scaleWeights_weight (s : ℝ) (hs : 0 < s)
    (hupper : ∀ e, s * G.weight e ≤ 1) (e : G.E) :
    (G.scaleWeights s hs hupper).weight e = s * G.weight e := rfl

@[simp] theorem scaleWeights_inc (s : ℝ) (hs : 0 < s)
    (hupper : ∀ e, s * G.weight e ≤ 1) (v : G.V) (e : G.E) :
    (G.scaleWeights s hs hupper).Inc v e ↔ G.Inc v e := Iff.rfl

/-- A bipartition is unchanged by scaling weights. -/
def Bipartition.scaleWeights (b : G.Bipartition) (s : ℝ) (hs : 0 < s)
    (hupper : ∀ e, s * G.weight e ≤ 1) :
    (G.scaleWeights s hs hupper).Bipartition where
  side := b.side
  opposite := b.opposite

@[simp] theorem Bipartition.scaleWeights_side (b : G.Bipartition)
    (s : ℝ) (hs : 0 < s) (hupper : ∀ e, s * G.weight e ≤ 1)
    (v : G.V) :
    (Bipartition.scaleWeights (G := G) b s hs hupper).side v = b.side v := rfl

/-- Scaling multiplies every star weight by the same factor. -/
theorem scaleWeights_starWeight (s : ℝ) (hs : 0 < s)
    (hupper : ∀ e, s * G.weight e ≤ 1) (v : G.V) :
    (G.scaleWeights s hs hupper).starWeight v = s * G.starWeight v := by
  unfold starWeight
  rw [Finset.mul_sum]
  rfl

end

end WeightedMultigraph
end WeightedEdgeColoring
