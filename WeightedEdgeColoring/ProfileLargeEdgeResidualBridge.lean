import WeightedEdgeColoring.ProfileLargeEdgePackage

/-!
# Initial residual bounds for the profile large-edge system

This file records the part of the connection to the residual matching
iteration that does not use a global ordinary-slot capacity estimate.
Quantization gives every job degree at most `N`, since its fractional fibre
mass is one.  The lower floor is `N` minus a uniform bound on the number of
base options in one fibre.

The slot-degree and final colored-weight parts of the connection are kept out
of this file: the former needs the selected-profile capacity estimate, while
the latter must distinguish ordinary choices from leave-uncolored choices.
-/

namespace WeightedEdgeColoring

noncomputable section

universe u w₁ w₂

namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph.{u})
variable {Color : Type w₁} {Class : Type w₂}
  [Fintype Color] [DecidableEq Color]
  [Fintype Class] [DecidableEq Class]

variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → Color → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- Unit fractional fibre mass gives the exact reference upper job scale
`J = N` for the quantized profile large-edge system. -/
theorem profileLargeEdge_quantizedJobDegree_upper
    (bucket : G.E → Class) (gamma : ℝ) {t : ℕ} (ht : 0 < t)
    (N : ℕ) (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (hretained : ∀ e,
      (∑ c, G.profileRetainedMass s β proposal e c) ≤ 1)
    (e : G.E) :
    (G.profileLargeEdgeOptionSystem proposal bucket gamma t).quantizedJobDegree
        N (G.profileLargeEdgeMass proposal R bucket gamma t) e ≤ N := by
  let H := G.profileLargeEdgeOptionSystem
    (s := s) (β := β) (q := q) (r := r) proposal bucket gamma t
  let mass := G.profileLargeEdgeMass proposal R bucket gamma t
  have hmass0 : ∀ z, 0 ≤ mass z := by
    intro z
    exact G.profileLargeEdgeMass_nonneg proposal R bucket gamma t
      hs hp hretained z
  have hupper := H.quantizedJobDegree_upper N mass e (fun z _hz ↦ hmass0 z)
  have hsum : (∑ z ∈ H.fiber e, mass z) = 1 := by
    exact G.sum_profileLargeEdgeMass_fiber_eq_one proposal R bucket gamma ht e
  rw [hsum, mul_one] at hupper
  exact_mod_cast hupper

/-- If `C` bounds the number of base choices owned by every edge, then the
initial quantized job floor is the natural number `N - C`.  Together with
`profileLargeEdge_quantizedJobDegree_upper`, this identifies the iteration
parameters `d 0 = N - C` and `J = N`. -/
theorem profileLargeEdge_quantizedJobDegree_lower_nat
    (bucket : G.E → Class) (gamma : ℝ) {t : ℕ} (ht : 0 < t)
    (N C : ℕ) (hCN : C ≤ N)
    (hchoices : ∀ e,
      (Fintype.card Color * explicitLargeSlotBound β q r *
          explicitLargeSlotBound β q r : ℕ) +
        G.graphExtraSlotCount bucket (G.profileResidual s β proposal) gamma t
            (G.fst e) (bucket e) *
          G.graphExtraSlotCount bucket (G.profileResidual s β proposal) gamma t
            (G.snd e) (bucket e) ≤ C)
    (e : G.E) :
    N - C ≤
      (G.profileLargeEdgeOptionSystem proposal bucket gamma t).quantizedJobDegree
        N (G.profileLargeEdgeMass proposal R bucket gamma t) e := by
  have hbase := G.profileLargeEdge_quantizedJobDegree_lower
    proposal R bucket gamma ht N e
  have hchoiceR :
      (((Fintype.card Color * explicitLargeSlotBound β q r *
          explicitLargeSlotBound β q r : ℕ) +
        G.graphExtraSlotCount bucket (G.profileResidual s β proposal) gamma t
            (G.fst e) (bucket e) *
          G.graphExtraSlotCount bucket (G.profileResidual s β proposal) gamma t
            (G.snd e) (bucket e) : ℕ) : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hchoices e
  have hreal : ((N - C : ℕ) : ℝ) ≤
      ((G.profileLargeEdgeOptionSystem proposal bucket gamma t).quantizedJobDegree
        N (G.profileLargeEdgeMass proposal R bucket gamma t) e : ℝ) := by
    rw [Nat.cast_sub hCN]
    exact le_trans (sub_le_sub_left hchoiceR N) hbase
  exact_mod_cast hreal

end WeightedSimpleGraph

end

end WeightedEdgeColoring
