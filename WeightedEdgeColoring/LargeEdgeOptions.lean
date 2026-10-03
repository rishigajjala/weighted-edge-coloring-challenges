import WeightedEdgeColoring.OrdinarySlotOptions
import WeightedEdgeColoring.ExtraSlotOptions
import WeightedEdgeColoring.SeparatedOptionSystems
import WeightedEdgeColoring.SeparatedPairUnique
import WeightedEdgeColoring.SimpleOrdinaryPairUnique
import WeightedEdgeColoring.SimpleExtraPairUnique

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# The combined large-edge option family

This module joins the two concrete choices used for a large edge.  An
ordinary choice gives the edge a colour and uses one profile place at each
endpoint.  An extra choice leaves it uncoloured and uses one counting slot at
each endpoint.  The two slot types are kept disjoint.
-/

noncomputable section

universe u w₁ w₂

namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph.{u})
variable {Color : Type w₁} {Class : Type w₂}
  [Fintype Color] [DecidableEq Color]
  [Fintype Class] [DecidableEq Class]

variable (K : ℕ) (bucket : G.E → Class) (B : G.V → Class → ℕ)

/-- Concrete slots in the combined family. -/
abbrev LargeEdgeSlot :=
  OrdinarySlot G.V Color K ⊕ ExtraSlot G.V Class B

/-- Concrete options in the combined family. -/
abbrev LargeEdgeOption :=
  OrdinarySlotChoice G.E Color K ⊕
    ExtraSlotChoice G.E G.V Class G.fst G.snd bucket B

/-- Ordinary and leave-uncoloured choices on disjoint slot types. -/
def largeEdgeOptionSystem :
    RankThreeOptionSystem G.E
      (G.LargeEdgeSlot (Color := Color) K B)
      (G.LargeEdgeOption (Color := Color) K bucket B) :=
  (OrdinarySlotChoice.system G.fst G.snd K).separatedSum
    (ExtraSlotChoice.system G.fst G.snd bucket B)

/-- Put an ordinary mass array and an unused mass on the two summands. -/
def largeEdgeMass
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ) :
    G.LargeEdgeOption (Color := Color) K bucket B → ℝ :=
  RankThreeOptionSystem.sumMass (OrdinarySlotChoice.mass K x)
    (ExtraSlotChoice.mass G.fst G.snd bucket B residual)

theorem largeEdgeMass_nonneg
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (hx : ∀ e c i j, 0 ≤ x e c i j)
    (hr : ∀ e, 0 ≤ residual e) :
    ∀ z : G.LargeEdgeOption (Color := Color) K bucket B,
      0 ≤ G.largeEdgeMass K bucket B x residual z := by
  apply RankThreeOptionSystem.sumMass_nonneg
  · exact OrdinarySlotChoice.mass_nonneg K x hx
  · exact ExtraSlotChoice.mass_nonneg G.fst G.snd bucket B residual hr

/-- The two families together have exactly the ordinary captured mass plus
the unused mass of each edge. -/
theorem sum_largeEdgeMass_fiber
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (hleft : ∀ e, 0 < B (G.fst e) (bucket e))
    (hright : ∀ e, 0 < B (G.snd e) (bucket e))
    (e : G.E) :
    (∑ z ∈ (G.largeEdgeOptionSystem K bucket B).fiber e,
      G.largeEdgeMass K bucket B x residual z) =
      (∑ c, ∑ i, ∑ j, x e c i j) + residual e := by
  change
    (∑ z ∈ (((OrdinarySlotChoice.system G.fst G.snd K).liftSlotsLeft).sum
      ((ExtraSlotChoice.system G.fst G.snd bucket B).liftSlotsRight)).fiber e,
      RankThreeOptionSystem.sumMass (OrdinarySlotChoice.mass K x)
        (ExtraSlotChoice.mass G.fst G.snd bucket B residual) z) = _
  rw [RankThreeOptionSystem.sum_sumMass_fiber]
  change
    (∑ q ∈ (OrdinarySlotChoice.system G.fst G.snd K).fiber e,
        OrdinarySlotChoice.mass K x q) +
      (∑ p ∈ (ExtraSlotChoice.system G.fst G.snd bucket B).fiber e,
        ExtraSlotChoice.mass G.fst G.snd bucket B residual p) = _
  rw [OrdinarySlotChoice.sum_mass_fiber G.fst G.snd K x e,
    ExtraSlotChoice.sum_mass_fiber G.fst G.snd bucket B residual
      hleft hright e]

/-- In particular, ordinary mass plus residual equal to one makes every job
fibre a probability distribution. -/
theorem sum_largeEdgeMass_fiber_eq_one
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (hleft : ∀ e, 0 < B (G.fst e) (bucket e))
    (hright : ∀ e, 0 < B (G.snd e) (bucket e))
    (htotal : ∀ e, (∑ c, ∑ i, ∑ j, x e c i j) + residual e = 1)
    (e : G.E) :
    (∑ z ∈ (G.largeEdgeOptionSystem K bucket B).fiber e,
      G.largeEdgeMass K bucket B x residual z) = 1 := by
  rw [G.sum_largeEdgeMass_fiber K bucket B x residual hleft hright e,
    htotal e]

/-- The combined option family is pair-unique. -/
theorem largeEdgeOptionSystem_pairUnique :
    (G.largeEdgeOptionSystem (Color := Color) (Class := Class)
      K bucket B).PairUnique := by
  apply RankThreeOptionSystem.separatedSum_pairUnique
  · exact G.ordinarySlotChoice_pairUnique K
  · exact G.extraSlotChoice_pairUnique bucket B

/-- A combined ordinary job--slot codegree has the same bound as the
ordinary component. -/
theorem largeEdge_quantized_jobSlotCodegree_inl_le
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (hx : ∀ e c i j, 0 ≤ x e c i j)
    (N : ℕ) (e : G.E) (s : OrdinarySlot G.V Color K) :
    (((G.largeEdgeOptionSystem K bucket B).quantized N
        (G.largeEdgeMass K bucket B x residual)).jobSlotCodegree
          e (Sum.inl s) : ℝ) ≤
      (N : ℝ) * ∑ i, ∑ j, x e s.color i j := by
  unfold largeEdgeOptionSystem largeEdgeMass
  rw [RankThreeOptionSystem.separatedSum_quantized_jobSlotCodegree_inl]
  exact OrdinarySlotChoice.quantized_jobSlotCodegree_upper_colorTotal
    G.fst G.snd K x hx G.noLoop N e s

/-- A combined extra job--slot codegree has the one-endpoint-share bound of
the extra component. -/
theorem largeEdge_quantized_jobSlotCodegree_inr_le
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (hr : ∀ e, 0 ≤ residual e)
    (hleft : ∀ e, 0 < B (G.fst e) (bucket e))
    (hright : ∀ e, 0 < B (G.snd e) (bucket e))
    (N : ℕ) (e : G.E) (s : ExtraSlot G.V Class B) :
    (((G.largeEdgeOptionSystem K bucket B).quantized N
        (G.largeEdgeMass K bucket B x residual)).jobSlotCodegree
          e (Sum.inr s) : ℝ) ≤
      (N : ℝ) *
        (if s.1 = (G.fst e, bucket e) then
          residual e / B (G.fst e) (bucket e)
        else if s.1 = (G.snd e, bucket e) then
          residual e / B (G.snd e) (bucket e) else 0) := by
  unfold largeEdgeOptionSystem largeEdgeMass
  rw [RankThreeOptionSystem.separatedSum_quantized_jobSlotCodegree_inr]
  exact ExtraSlotChoice.quantized_jobSlotCodegree_upper_oneEndpoint
    G.fst G.snd bucket B residual hr hleft hright G.noLoop N e s

/-- A combined ordinary slot has exactly the ordinary component's copied
degree, hence the ordinary fractional-load upper bound. -/
theorem largeEdge_quantized_slotDegree_inl_le
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (hx : ∀ e c i j, 0 ≤ x e c i j)
    (N : ℕ) (s : OrdinarySlot G.V Color K) :
    ((((G.largeEdgeOptionSystem K bucket B).quantized N
        (G.largeEdgeMass K bucket B x residual)).slotDegree
          (Sum.inl s) : ℕ) : ℝ) ≤
      (N : ℝ) * ∑ e,
        ((if s.vertex = G.fst e then ∑ j, x e s.color s.place j else 0) +
          if s.vertex = G.snd e then ∑ i, x e s.color i s.place else 0) := by
  unfold largeEdgeOptionSystem largeEdgeMass
  rw [RankThreeOptionSystem.separatedSum_quantized_slotDegree_inl]
  exact OrdinarySlotChoice.quantized_slotDegree_upper
    G.fst G.snd K x hx N s

/-- A combined extra slot has exactly the extra component's copied degree,
hence its endpoint-share upper bound. -/
theorem largeEdge_quantized_slotDegree_inr_le
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (hr : ∀ e, 0 ≤ residual e)
    (hleft : ∀ e, 0 < B (G.fst e) (bucket e))
    (hright : ∀ e, 0 < B (G.snd e) (bucket e))
    (N : ℕ) (s : ExtraSlot G.V Class B) :
    ((((G.largeEdgeOptionSystem K bucket B).quantized N
        (G.largeEdgeMass K bucket B x residual)).slotDegree
          (Sum.inr s) : ℕ) : ℝ) ≤
      (N : ℝ) * ∑ e,
        ((if s.1 = (G.fst e, bucket e) then
            residual e / B (G.fst e) (bucket e) else 0) +
          if s.1 = (G.snd e, bucket e) then
            residual e / B (G.snd e) (bucket e) else 0) := by
  unfold largeEdgeOptionSystem largeEdgeMass
  rw [RankThreeOptionSystem.separatedSum_quantized_slotDegree_inr]
  exact ExtraSlotChoice.quantized_slotDegree_upper
    G.fst G.snd bucket B residual hr hleft hright N s

/-- A uniform pointwise mass bound gives the required replicated pair
codegree bound for every two distinct combined slots. -/
theorem largeEdge_quantized_slotPairCodegree_le
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (tau : ℝ) (htau : 0 ≤ tau)
    (hx0 : ∀ e c i j, 0 ≤ x e c i j)
    (hxtau : ∀ e c i j, x e c i j ≤ tau)
    (hr0 : ∀ e, 0 ≤ residual e)
    (hrextra : ∀ e,
      residual e /
        ((B (G.fst e) (bucket e) : ℕ) *
          B (G.snd e) (bucket e) : ℕ) ≤ tau)
    (N : ℕ) {s t : G.LargeEdgeSlot (Color := Color) K B}
    (hst : s ≠ t) :
    ((((G.largeEdgeOptionSystem K bucket B).quantized N
        (G.largeEdgeMass K bucket B x residual)).slotPairCodegree s t : ℕ) : ℝ) ≤
      (N : ℝ) * tau := by
  apply (G.largeEdgeOptionSystem K bucket B).quantized_slotPairCodegree_le
    (G.largeEdgeOptionSystem_pairUnique K bucket B)
    N (G.largeEdgeMass K bucket B x residual) tau htau
  · exact G.largeEdgeMass_nonneg K bucket B x residual hx0 hr0
  · intro z
    cases z with
    | inl q =>
        exact hxtau q.job q.color q.leftPlace q.rightPlace
    | inr p =>
        exact hrextra p.1
  · exact hst

/-- The copied degree of a combined job loses at most the number of its
ordinary base choices plus the size of its endpoint extra-slot grid. -/
theorem largeEdge_quantizedJobDegree_lower
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (hleft : ∀ e, 0 < B (G.fst e) (bucket e))
    (hright : ∀ e, 0 < B (G.snd e) (bucket e))
    (N : ℕ) (e : G.E) :
    (N : ℝ) * ((∑ c, ∑ i, ∑ j, x e c i j) + residual e) -
        ((Fintype.card Color * K * K : ℕ) +
          B (G.fst e) (bucket e) * B (G.snd e) (bucket e)) ≤
      ((G.largeEdgeOptionSystem K bucket B).quantizedJobDegree N
        (G.largeEdgeMass K bucket B x residual) e : ℝ) := by
  have hord := OrdinarySlotChoice.quantizedJobDegree_lower
    G.fst G.snd K x N e
  have hextra := ExtraSlotChoice.quantizedJobDegree_lower
    G.fst G.snd bucket B residual hleft hright N e
  unfold largeEdgeOptionSystem largeEdgeMass
  unfold RankThreeOptionSystem.separatedSum
  rw [RankThreeOptionSystem.sum_quantizedJobDegree]
  have hliftOrd :
      ((OrdinarySlotChoice.system G.fst G.snd K).liftSlotsLeft
        (Slot₂ := ExtraSlot G.V Class B)).quantizedJobDegree
          N (OrdinarySlotChoice.mass K x) e =
        (OrdinarySlotChoice.system G.fst G.snd K).quantizedJobDegree
          N (OrdinarySlotChoice.mass K x) e := rfl
  have hliftExtra :
      ((ExtraSlotChoice.system G.fst G.snd bucket B).liftSlotsRight
        (Slot₁ := OrdinarySlot G.V Color K)).quantizedJobDegree
          N (ExtraSlotChoice.mass G.fst G.snd bucket B residual) e =
        (ExtraSlotChoice.system G.fst G.snd bucket B).quantizedJobDegree
          N (ExtraSlotChoice.mass G.fst G.snd bucket B residual) e := rfl
  rw [hliftOrd, hliftExtra]
  push_cast at hord hextra ⊢
  change _ ≤
    ((OrdinarySlotChoice.system G.fst G.snd K).quantizedJobDegree N
        (OrdinarySlotChoice.mass K x) e : ℝ) +
      ((ExtraSlotChoice.system G.fst G.snd bucket B).quantizedJobDegree N
        (ExtraSlotChoice.mass G.fst G.snd bucket B residual) e : ℝ)
  linarith

end WeightedSimpleGraph

end

end WeightedEdgeColoring
