import WeightedEdgeColoring.CyclicExtraSlotOptions
import WeightedEdgeColoring.OrdinarySlotOptions
import WeightedEdgeColoring.SeparatedPairUnique
import WeightedEdgeColoring.SimpleOrdinaryPairUnique

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# Large-edge options with coupled extra choices

This is the ordinary profile option family joined to the linearly sized
cyclic extra family.  It is the replacement for the Cartesian extra grid in
the asymptotic simple-graph argument.
-/

noncomputable section

universe u w₁ w₂

namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph.{u})
variable {Color : Type w₁} {Class : Type w₂}
  [Fintype Color] [DecidableEq Color]
  [Fintype Class] [DecidableEq Class]

variable (K t : ℕ) (bucket : G.E → Class)

abbrev CyclicLargeEdgeSlot :=
  OrdinarySlot G.V Color K ⊕ CyclicExtraSlot G.V Class t

abbrev CyclicLargeEdgeOption :=
  OrdinarySlotChoice G.E Color K ⊕ CyclicExtraChoice G.E t

/-- Ordinary choices and cyclic extra choices, placed on disjoint slot
types. -/
def cyclicLargeEdgeOptionSystem :
    RankThreeOptionSystem G.E
      (G.CyclicLargeEdgeSlot (Color := Color) (Class := Class) K t)
      (G.CyclicLargeEdgeOption (Color := Color) K t) :=
  (OrdinarySlotChoice.system G.fst G.snd K).separatedSum
    (CyclicExtraChoice.system G.fst G.snd bucket t)

def cyclicLargeEdgeMass
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (residual : G.E → ℝ) :
    G.CyclicLargeEdgeOption (Color := Color) K t → ℝ :=
  RankThreeOptionSystem.sumMass (OrdinarySlotChoice.mass K x)
    (CyclicExtraChoice.mass t residual)

theorem cyclicLargeEdgeMass_nonneg
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (residual : G.E → ℝ)
    (hx : ∀ e c i j, 0 ≤ x e c i j) (hr : ∀ e, 0 ≤ residual e) :
    ∀ z, 0 ≤ G.cyclicLargeEdgeMass K t x residual z := by
  apply RankThreeOptionSystem.sumMass_nonneg
  · exact OrdinarySlotChoice.mass_nonneg K x hx
  · exact CyclicExtraChoice.mass_nonneg t residual hr

theorem sum_cyclicLargeEdgeMass_fiber
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (residual : G.E → ℝ) (ht : 0 < t) (e : G.E) :
    (∑ z ∈ (G.cyclicLargeEdgeOptionSystem K t bucket).fiber e,
      G.cyclicLargeEdgeMass K t x residual z) =
      (∑ c, ∑ i, ∑ j, x e c i j) + residual e := by
  change
    (∑ z ∈ (((OrdinarySlotChoice.system G.fst G.snd K).liftSlotsLeft).sum
      ((CyclicExtraChoice.system G.fst G.snd bucket t).liftSlotsRight)).fiber e,
      RankThreeOptionSystem.sumMass (OrdinarySlotChoice.mass K x)
        (CyclicExtraChoice.mass t residual) z) = _
  rw [RankThreeOptionSystem.sum_sumMass_fiber]
  change
    (∑ q ∈ (OrdinarySlotChoice.system G.fst G.snd K).fiber e,
      OrdinarySlotChoice.mass K x q) +
    (∑ p ∈ (CyclicExtraChoice.system G.fst G.snd bucket t).fiber e,
      CyclicExtraChoice.mass t residual p) = _
  rw [OrdinarySlotChoice.sum_mass_fiber G.fst G.snd K x e,
    CyclicExtraChoice.sum_mass_fiber G.fst G.snd bucket t residual ht e]

theorem sum_cyclicLargeEdgeMass_fiber_eq_one
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (residual : G.E → ℝ) (ht : 0 < t)
    (htotal : ∀ e, (∑ c, ∑ i, ∑ j, x e c i j) + residual e = 1)
    (e : G.E) :
    (∑ z ∈ (G.cyclicLargeEdgeOptionSystem K t bucket).fiber e,
      G.cyclicLargeEdgeMass K t x residual z) = 1 := by
  rw [G.sum_cyclicLargeEdgeMass_fiber K t bucket x residual ht e,
    htotal e]

theorem cyclicLargeEdgeOptionSystem_pairUnique :
    (G.cyclicLargeEdgeOptionSystem
      (Color := Color) (Class := Class) K t bucket).PairUnique := by
  apply RankThreeOptionSystem.separatedSum_pairUnique
  · exact G.ordinarySlotChoice_pairUnique K
  · exact G.cyclicExtraChoice_pairUnique bucket t

theorem cyclicLargeEdge_quantized_jobSlotCodegree_inl_le
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (residual : G.E → ℝ) (hx : ∀ e c i j, 0 ≤ x e c i j)
    (N : ℕ) (e : G.E) (s : OrdinarySlot G.V Color K) :
    (((G.cyclicLargeEdgeOptionSystem K t bucket).quantized N
      (G.cyclicLargeEdgeMass K t x residual)).jobSlotCodegree e (Sum.inl s) : ℝ)
      ≤ (N : ℝ) * ∑ i, ∑ j, x e s.color i j := by
  unfold cyclicLargeEdgeOptionSystem cyclicLargeEdgeMass
  rw [RankThreeOptionSystem.separatedSum_quantized_jobSlotCodegree_inl]
  exact OrdinarySlotChoice.quantized_jobSlotCodegree_upper_colorTotal
    G.fst G.snd K x hx G.noLoop N e s

theorem cyclicLargeEdge_quantized_jobSlotCodegree_inr_le
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (residual : G.E → ℝ)
    (hr0 : ∀ e, 0 ≤ residual e) (hr1 : ∀ e, residual e ≤ 1)
    (ht : 0 < t) (N : ℕ) (e : G.E)
    (s : CyclicExtraSlot G.V Class t) :
    (((G.cyclicLargeEdgeOptionSystem K t bucket).quantized N
      (G.cyclicLargeEdgeMass K t x residual)).jobSlotCodegree e (Sum.inr s) : ℝ)
      ≤ (N : ℝ) / t := by
  unfold cyclicLargeEdgeOptionSystem cyclicLargeEdgeMass
  rw [RankThreeOptionSystem.separatedSum_quantized_jobSlotCodegree_inr]
  exact CyclicExtraChoice.quantized_jobSlotCodegree_le
    G.fst G.snd bucket t residual hr0 ht hr1 G.noLoop N e s

theorem cyclicLargeEdge_quantized_slotDegree_inl_le
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (residual : G.E → ℝ) (hx : ∀ e c i j, 0 ≤ x e c i j)
    (N : ℕ) (s : OrdinarySlot G.V Color K) :
    ((((G.cyclicLargeEdgeOptionSystem K t bucket).quantized N
      (G.cyclicLargeEdgeMass K t x residual)).slotDegree (Sum.inl s) : ℕ) : ℝ)
      ≤ (N : ℝ) * ∑ e,
        ((if s.vertex = G.fst e then ∑ j, x e s.color s.place j else 0) +
          if s.vertex = G.snd e then ∑ i, x e s.color i s.place else 0) := by
  unfold cyclicLargeEdgeOptionSystem cyclicLargeEdgeMass
  rw [RankThreeOptionSystem.separatedSum_quantized_slotDegree_inl]
  exact OrdinarySlotChoice.quantized_slotDegree_upper
    G.fst G.snd K x hx N s

theorem cyclicLargeEdge_quantized_slotDegree_inr_le
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (residual : G.E → ℝ) (hr0 : ∀ e, 0 ≤ residual e)
    {gamma : ℝ} (ht : 0 < t)
    (hclass : ∀ v h,
      G.classResidual bucket residual v h ≤ (1 - gamma) * t)
    (N : ℕ) (s : CyclicExtraSlot G.V Class t) :
    ((((G.cyclicLargeEdgeOptionSystem K t bucket).quantized N
      (G.cyclicLargeEdgeMass K t x residual)).slotDegree (Sum.inr s) : ℕ) : ℝ)
      ≤ (1 - gamma) * N := by
  unfold cyclicLargeEdgeOptionSystem cyclicLargeEdgeMass
  rw [RankThreeOptionSystem.separatedSum_quantized_slotDegree_inr]
  exact G.quantized_cyclicExtraSlotDegree_le bucket residual hr0 ht hclass N s

/-- If every ordinary atom is at most `1/t`, every pair of distinct slots
has copied codegree at most `N/t`.  Cross pairs have codegree zero by the
separated sum construction. -/
theorem cyclicLargeEdge_quantized_slotPairCodegree_le
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (residual : G.E → ℝ) (hx0 : ∀ e c i j, 0 ≤ x e c i j)
    (hx : ∀ e c i j, x e c i j ≤ 1 / (t : ℝ))
    (hr0 : ∀ e, 0 ≤ residual e) (hr1 : ∀ e, residual e ≤ 1)
    (ht : 0 < t) (N : ℕ)
    {s r : G.CyclicLargeEdgeSlot (Color := Color) (Class := Class) K t}
    (hsr : s ≠ r) :
    ((((G.cyclicLargeEdgeOptionSystem K t bucket).quantized N
      (G.cyclicLargeEdgeMass K t x residual)).slotPairCodegree s r : ℕ) : ℝ)
      ≤ (N : ℝ) / t := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  calc
    _ ≤ (N : ℝ) * (1 / (t : ℝ)) := by
      apply (G.cyclicLargeEdgeOptionSystem K t bucket).quantized_slotPairCodegree_le
        (G.cyclicLargeEdgeOptionSystem_pairUnique K t bucket)
        N (G.cyclicLargeEdgeMass K t x residual) (1 / (t : ℝ))
      · exact le_of_lt (one_div_pos.mpr ht0)
      · exact G.cyclicLargeEdgeMass_nonneg K t x residual hx0 hr0
      · intro z
        cases z with
        | inl q => exact hx q.job q.color q.leftPlace q.rightPlace
        | inr p => exact (div_le_div_iff_of_pos_right ht0).2 (hr1 p.1)
      · exact hsr
    _ = (N : ℝ) / t := by ring

/-- The copied degree of a combined job loses only the ordinary base count
plus `t`, rather than a Cartesian product of endpoint counts. -/
theorem cyclicLargeEdge_quantizedJobDegree_lower
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (residual : G.E → ℝ) (ht : 0 < t) (N : ℕ) (e : G.E) :
    (N : ℝ) * ((∑ c, ∑ i, ∑ j, x e c i j) + residual e) -
        ((Fintype.card Color * K * K : ℕ) + t) ≤
      ((G.cyclicLargeEdgeOptionSystem K t bucket).quantizedJobDegree N
        (G.cyclicLargeEdgeMass K t x residual) e : ℝ) := by
  have hord := OrdinarySlotChoice.quantizedJobDegree_lower
    G.fst G.snd K x N e
  have hextra := CyclicExtraChoice.quantizedJobDegree_lower
    G.fst G.snd bucket t residual ht N e
  unfold cyclicLargeEdgeOptionSystem cyclicLargeEdgeMass
  unfold RankThreeOptionSystem.separatedSum
  rw [RankThreeOptionSystem.sum_quantizedJobDegree]
  have hliftOrd :
      ((OrdinarySlotChoice.system G.fst G.snd K).liftSlotsLeft
        (Slot₂ := CyclicExtraSlot G.V Class t)).quantizedJobDegree
          N (OrdinarySlotChoice.mass K x) e =
        (OrdinarySlotChoice.system G.fst G.snd K).quantizedJobDegree
          N (OrdinarySlotChoice.mass K x) e := rfl
  have hliftExtra :
      ((CyclicExtraChoice.system G.fst G.snd bucket t).liftSlotsRight
        (Slot₁ := OrdinarySlot G.V Color K)).quantizedJobDegree
          N (CyclicExtraChoice.mass t residual) e =
        (CyclicExtraChoice.system G.fst G.snd bucket t).quantizedJobDegree
          N (CyclicExtraChoice.mass t residual) e := rfl
  rw [hliftOrd, hliftExtra]
  push_cast at hord hextra ⊢
  linarith

end WeightedSimpleGraph

end

end WeightedEdgeColoring
