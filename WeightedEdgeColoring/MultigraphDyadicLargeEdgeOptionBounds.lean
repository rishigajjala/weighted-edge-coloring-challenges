import WeightedEdgeColoring.BoundedMultiplicityDyadicOptions
import WeightedEdgeColoring.BoundedMultiplicityDyadicExtraSlotBudget

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u w₁ w₂

namespace WeightedMultigraph

variable (G : WeightedMultigraph.{u})
variable {Color : Type w₁} {Class : Type w₂}
  [Fintype Color] [DecidableEq Color]
  [Fintype Class] [DecidableEq Class]

variable (K : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
  (residual : G.E → ℝ)

abbrev DyadicLargeEdgeSlot :=
  OrdinarySlot G.V Color K ⊕ ExtraSlot G.V Class
    (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)

abbrev DyadicLargeEdgeOption :=
  OrdinarySlotChoice G.E Color K ⊕
    DivisibleLocalExtraChoice G.E G.V Class G.fst G.snd bucket
      (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)

def dyadicLargeEdgeOptionSystem :
    RankThreeOptionSystem G.E
      (G.DyadicLargeEdgeSlot (Color := Color) K bucket gamma reserve residual)
      (G.DyadicLargeEdgeOption (Color := Color) K bucket gamma reserve residual) :=
  (OrdinarySlotChoice.system G.fst G.snd K).separatedSum
    (DivisibleLocalExtraChoice.system G.fst G.snd bucket
      (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
      (G.boundedDyadic_left_dvd_support bucket residual gamma reserve)
      (G.boundedDyadic_right_dvd_support bucket residual gamma reserve))

def dyadicLargeEdgeMass
    (x : G.E → Color → Fin K → Fin K → ℝ) :
    G.DyadicLargeEdgeOption (Color := Color) K bucket gamma reserve residual → ℝ :=
  RankThreeOptionSystem.sumMass (OrdinarySlotChoice.mass K x)
    (DivisibleLocalExtraChoice.mass G.fst G.snd bucket
      (G.boundedDyadicExtraSlotCount bucket residual gamma reserve) residual)

theorem dyadicLargeEdgeMass_nonneg
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (hx : ∀ e c i j, 0 ≤ x e c i j) (hr0 : ∀ e, 0 ≤ residual e) :
    ∀ z, 0 ≤ G.dyadicLargeEdgeMass K bucket gamma reserve residual x z := by
  apply RankThreeOptionSystem.sumMass_nonneg
  · exact OrdinarySlotChoice.mass_nonneg K x hx
  · exact DivisibleLocalExtraChoice.mass_nonneg
      G.fst G.snd bucket _ residual hr0

theorem sum_dyadicLargeEdgeMass_fiber
    (x : G.E → Color → Fin K → Fin K → ℝ) (e : G.E) :
    (∑ z ∈ (G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).fiber e,
      G.dyadicLargeEdgeMass K bucket gamma reserve residual x z) =
      (∑ c, ∑ i, ∑ j, x e c i j) + residual e := by
  change
    (∑ z ∈ (((OrdinarySlotChoice.system G.fst G.snd K).liftSlotsLeft).sum
      ((DivisibleLocalExtraChoice.system G.fst G.snd bucket
        (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
        (G.boundedDyadic_left_dvd_support bucket residual gamma reserve)
        (G.boundedDyadic_right_dvd_support bucket residual gamma reserve)).liftSlotsRight)).fiber e,
      _) = _
  unfold dyadicLargeEdgeMass
  rw [RankThreeOptionSystem.sum_sumMass_fiber]
  change (∑ q ∈ (OrdinarySlotChoice.system G.fst G.snd K).fiber e,
      OrdinarySlotChoice.mass K x q) +
    (∑ p ∈ (DivisibleLocalExtraChoice.system G.fst G.snd bucket
      (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
      (G.boundedDyadic_left_dvd_support bucket residual gamma reserve)
      (G.boundedDyadic_right_dvd_support bucket residual gamma reserve)).fiber e,
      DivisibleLocalExtraChoice.mass G.fst G.snd bucket
        (G.boundedDyadicExtraSlotCount bucket residual gamma reserve) residual p) = _
  rw [OrdinarySlotChoice.sum_mass_fiber G.fst G.snd K x e,
    DivisibleLocalExtraChoice.sum_mass_fiber G.fst G.snd bucket
      (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
      (G.boundedDyadic_left_dvd_support bucket residual gamma reserve)
      (G.boundedDyadic_right_dvd_support bucket residual gamma reserve)
      residual (fun j ↦ G.boundedDyadicExtraSlotCount_pos
        bucket residual gamma reserve _ _) e]

theorem dyadicLargeEdgeOptionSystem_slots_card_eq_two
    (z : G.DyadicLargeEdgeOption (Color := Color) K bucket gamma reserve
      residual) :
    ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).slots z).card = 2 := by
  cases z with
  | inl o =>
      have hne : OrdinarySlotChoice.leftSlot G.fst K o ≠
          OrdinarySlotChoice.rightSlot G.snd K o := by
        intro h
        exact G.noLoop o.job
          (congrArg (fun s : OrdinarySlot G.V Color K ↦ s.vertex) h)
      simp [dyadicLargeEdgeOptionSystem, RankThreeOptionSystem.separatedSum,
        RankThreeOptionSystem.liftSlotsLeft, RankThreeOptionSystem.sum,
        OrdinarySlotChoice.system, hne]
  | inr p =>
      have hne : DivisibleLocalExtraChoice.leftSlot G.fst G.snd bucket
            (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
            (G.boundedDyadic_left_dvd_support bucket residual gamma reserve) p ≠
          DivisibleLocalExtraChoice.rightSlot G.fst G.snd bucket
            (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
            (G.boundedDyadic_right_dvd_support bucket residual gamma reserve) p := by
        intro h
        exact G.noLoop p.1
          (congrArg (fun s : ExtraSlot G.V Class
            (G.boundedDyadicExtraSlotCount bucket residual gamma reserve) ↦
              s.1.1) h)
      simp [dyadicLargeEdgeOptionSystem, RankThreeOptionSystem.separatedSum,
        RankThreeOptionSystem.liftSlotsRight, RankThreeOptionSystem.sum,
        DivisibleLocalExtraChoice.system, hne]

theorem quantized_dyadicLargeEdgeOptionSystem_slots_card_eq_two
    (x : G.E → Color → Fin K → Fin K → ℝ) (N : ℕ)
    (q : QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)) :
    (((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).slots q).card =
        2 := by
  exact G.dyadicLargeEdgeOptionSystem_slots_card_eq_two
    K bucket gamma reserve residual q.1

theorem dyadicLargeEdge_quantized_jobSlotCodegree_inl_le
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (hx : ∀ e c i j, 0 ≤ x e c i j) (N : ℕ) (e : G.E)
    (s : OrdinarySlot G.V Color K) :
    (((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).jobSlotCodegree e
        (Sum.inl s) : ℝ) ≤
      (N : ℝ) * ∑ i, ∑ j, x e s.color i j := by
  unfold dyadicLargeEdgeOptionSystem dyadicLargeEdgeMass
  rw [RankThreeOptionSystem.separatedSum_quantized_jobSlotCodegree_inl]
  exact OrdinarySlotChoice.quantized_jobSlotCodegree_upper_colorTotal
    G.fst G.snd K x hx G.noLoop N e s

theorem dyadicLargeEdge_quantized_jobSlotCodegree_inr_le
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (hr0 : ∀ e, 0 ≤ residual e) (hr1 : ∀ e, residual e ≤ 1)
    (hreserve : 0 < reserve) (N : ℕ) (e : G.E)
    (s : ExtraSlot G.V Class
      (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)) :
    (((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).jobSlotCodegree e
        (Sum.inr s) : ℝ) ≤ (N : ℝ) / reserve := by
  unfold dyadicLargeEdgeOptionSystem dyadicLargeEdgeMass
  rw [RankThreeOptionSystem.separatedSum_quantized_jobSlotCodegree_inr]
  exact DivisibleLocalExtraChoice.quantized_jobSlotCodegree_le_reserve
    G.fst G.snd bucket
    (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
    (G.boundedDyadic_left_dvd_support bucket residual gamma reserve)
    (G.boundedDyadic_right_dvd_support bucket residual gamma reserve)
    residual hr0 hr1
    (fun e ↦ G.boundedDyadicExtraSlotCount_pos bucket residual gamma reserve _ _)
    (fun e ↦ G.boundedDyadicExtraSlotCount_pos bucket residual gamma reserve _ _)
    (G.boundedDyadicExtraSlotCount_ge_reserve bucket residual gamma reserve)
    hreserve G.noLoop N e s

theorem dyadicLargeEdge_quantized_slotDegree_inl_le
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (hx : ∀ e c i j, 0 ≤ x e c i j) (N : ℕ)
    (s : OrdinarySlot G.V Color K) :
    ((((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).slotDegree
        (Sum.inl s) : ℕ) : ℝ) ≤
      (N : ℝ) * ∑ e,
        ((if s.vertex = G.fst e then ∑ j, x e s.color s.place j else 0) +
          if s.vertex = G.snd e then ∑ i, x e s.color i s.place else 0) := by
  unfold dyadicLargeEdgeOptionSystem dyadicLargeEdgeMass
  rw [RankThreeOptionSystem.separatedSum_quantized_slotDegree_inl]
  exact OrdinarySlotChoice.quantized_slotDegree_upper
    G.fst G.snd K x hx N s

theorem dyadicLargeEdge_quantized_slotDegree_inr_le
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (hr0 : ∀ e, 0 ≤ residual e) (hreserve : 0 < reserve)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (N : ℕ)
    (s : ExtraSlot G.V Class
      (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)) :
    ((((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).slotDegree
        (Sum.inr s) : ℕ) : ℝ) ≤ (1 - gamma) * N := by
  unfold dyadicLargeEdgeOptionSystem dyadicLargeEdgeMass
  rw [RankThreeOptionSystem.separatedSum_quantized_slotDegree_inr]
  exact G.quantized_graphDyadicExtraSlotDegree_le
    bucket residual hr0 gamma hreserve hgamma0 hgamma1 N s

theorem dyadicLargeEdge_quantizedJobDegree_lower
    (x : G.E → Color → Fin K → Fin K → ℝ) (N : ℕ) (e : G.E) :
    (N : ℝ) * ((∑ c, ∑ i, ∑ j, x e c i j) + residual e) -
        ((Fintype.card Color * K * K : ℕ) +
          DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
            (G.boundedDyadicExtraSlotCount bucket residual gamma reserve) e) ≤
      ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantizedJobDegree N
          (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) e : ℝ) := by
  have hord := OrdinarySlotChoice.quantizedJobDegree_lower
    G.fst G.snd K x N e
  have hextra := DivisibleLocalExtraChoice.quantizedJobDegree_lower
    G.fst G.snd bucket
    (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
    (G.boundedDyadic_left_dvd_support bucket residual gamma reserve)
    (G.boundedDyadic_right_dvd_support bucket residual gamma reserve)
    residual (fun j ↦ G.boundedDyadicExtraSlotCount_pos
      bucket residual gamma reserve _ _) N e
  unfold dyadicLargeEdgeOptionSystem dyadicLargeEdgeMass
  unfold RankThreeOptionSystem.separatedSum
  rw [RankThreeOptionSystem.sum_quantizedJobDegree]
  have hliftOrd :
      ((OrdinarySlotChoice.system G.fst G.snd K).liftSlotsLeft
        (Slot₂ := ExtraSlot G.V Class
          (G.boundedDyadicExtraSlotCount bucket residual gamma reserve))).quantizedJobDegree N
          (OrdinarySlotChoice.mass K x) e =
        (OrdinarySlotChoice.system G.fst G.snd K).quantizedJobDegree
          N (OrdinarySlotChoice.mass K x) e := rfl
  have hliftExtra :
      ((DivisibleLocalExtraChoice.system G.fst G.snd bucket
        (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
        (G.boundedDyadic_left_dvd_support bucket residual gamma reserve)
        (G.boundedDyadic_right_dvd_support bucket residual gamma reserve)).liftSlotsRight
          (Slot₁ := OrdinarySlot G.V Color K)).quantizedJobDegree
          N (DivisibleLocalExtraChoice.mass G.fst G.snd bucket
            (G.boundedDyadicExtraSlotCount bucket residual gamma reserve) residual) e =
        (DivisibleLocalExtraChoice.system G.fst G.snd bucket
          (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
          (G.boundedDyadic_left_dvd_support bucket residual gamma reserve)
          (G.boundedDyadic_right_dvd_support bucket residual gamma reserve)).quantizedJobDegree N
              (DivisibleLocalExtraChoice.mass G.fst G.snd bucket
                (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
                residual) e := rfl
  rw [hliftOrd, hliftExtra]
  push_cast at hord hextra ⊢
  linarith


/-- Fixed endpoint multiplicity gives the `L`-scaled dyadic pair-codegree
bound for the compatibility option-system interface. -/
theorem dyadicLargeEdge_quantized_slotPairCodegree_le
    {L : ℕ} (hmult : G.PairMultiplicityAtMost L)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (hx0 : ∀ e c i j, 0 ≤ x e c i j)
    (hx : ∀ e c i j, x e c i j ≤ 1 / (reserve : ℝ))
    (hr0 : ∀ e, 0 ≤ residual e) (hr1 : ∀ e, residual e ≤ 1)
    (hreserve : 0 < reserve) (N : ℕ)
    {s t : G.DyadicLargeEdgeSlot (Color := Color) K bucket gamma reserve
      residual} (hst : s ≠ t) :
    ((((G.dyadicLargeEdgeOptionSystem (Color := Color) K bucket gamma reserve
        residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)
      ).slotPairCodegree s t : ℕ) : ℝ) ≤
        (L : ℝ) * (N : ℝ) / reserve := by
  simpa [dyadicLargeEdgeOptionSystem, dyadicLargeEdgeMass,
    boundedDyadicLargeEdgeOptionSystem, boundedDyadicLargeEdgeMass] using
    (G.boundedDyadicLargeEdge_quantized_slotPairCodegree_le
      K bucket gamma reserve residual hmult x hx0 hx hr0 hr1 hreserve N hst)

end WeightedMultigraph

end

end WeightedEdgeColoring
