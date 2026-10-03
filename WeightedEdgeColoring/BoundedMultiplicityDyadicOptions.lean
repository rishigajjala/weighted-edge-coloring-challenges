import WeightedEdgeColoring.BoundedMultiplicityPairCodegree
import WeightedEdgeColoring.DyadicLocalExtraCounts

/-!
# Dyadic option systems for bounded-multiplicity multigraphs

This file gives the coordinated ordinary/extra option system on all indexed
edges of a loopless weighted multigraph.  Parallel edges are not split into
simple layers.  If every unordered endpoint pair contains at most `L` edges,
then every pair of distinct slots supports at most `L` base options, and floor
replication has pair-codegree at most `L * N / reserve`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u w₁ w₂

namespace WeightedMultigraph

variable (G : WeightedMultigraph.{u})
variable {Color : Type w₁} {Class : Type w₂}
  [Fintype Color] [DecidableEq Color]
  [Fintype Class] [DecidableEq Class]

/-- Total residual mass at one vertex and one class.  The two endpoint
orientations are kept explicit; looplessness makes them disjoint. -/
def boundedClassResidual (bucket : G.E → Class) (residual : G.E → ℝ)
    (v : G.V) (h : Class) : ℝ :=
  ∑ e,
    ((if (G.fst e, bucket e) = (v, h) then residual e else 0) +
      (if (G.snd e, bucket e) = (v, h) then residual e else 0))

theorem boundedClassResidual_nonneg
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (hr0 : ∀ e, 0 ≤ residual e) (v : G.V) (h : Class) :
    0 ≤ G.boundedClassResidual bucket residual v h := by
  unfold boundedClassResidual
  exact Finset.sum_nonneg fun e _ ↦ add_nonneg (by split <;> simp [hr0])
    (by split <;> simp [hr0])

/-- Dyadic local extra-slot count for a multigraph residual. -/
def boundedDyadicExtraSlotCount
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) (reserve : ℕ) (v : G.V) (h : Class) : ℕ :=
  dyadicExtraSlotCount (G.boundedClassResidual bucket residual v h)
    gamma reserve

theorem boundedDyadicExtraSlotCount_pos
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) (reserve : ℕ) (v : G.V) (h : Class) :
    0 < G.boundedDyadicExtraSlotCount bucket residual gamma reserve v h :=
  dyadicExtraSlotCount_pos _ _ _

theorem boundedDyadicExtraSlotCount_ge_reserve
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) (reserve : ℕ) (v : G.V) (h : Class) :
    reserve ≤ G.boundedDyadicExtraSlotCount bucket residual gamma reserve v h :=
  reserve_le_dyadicExtraSlotCount _ _ _

theorem boundedDyadic_left_dvd_support
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) (reserve : ℕ) (e : G.E) :
    G.boundedDyadicExtraSlotCount bucket residual gamma reserve
        (G.fst e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
        (G.boundedDyadicExtraSlotCount bucket residual gamma reserve) e := by
  exact dyadicCeil_dvd_max
    (extraSlotCount
      (G.boundedClassResidual bucket residual (G.fst e) (bucket e))
      gamma reserve)
    (extraSlotCount
      (G.boundedClassResidual bucket residual (G.snd e) (bucket e))
      gamma reserve)

theorem boundedDyadic_right_dvd_support
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) (reserve : ℕ) (e : G.E) :
    G.boundedDyadicExtraSlotCount bucket residual gamma reserve
        (G.snd e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
        (G.boundedDyadicExtraSlotCount bucket residual gamma reserve) e := by
  exact (dyadicCeil_both_dvd_max
    (extraSlotCount
      (G.boundedClassResidual bucket residual (G.fst e) (bucket e))
      gamma reserve)
    (extraSlotCount
      (G.boundedClassResidual bucket residual (G.snd e) (bucket e))
      gamma reserve)).2

variable (K : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
  (residual : G.E → ℝ)

abbrev BoundedDyadicLargeEdgeSlot :=
  OrdinarySlot G.V Color K ⊕ ExtraSlot G.V Class
    (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)

abbrev BoundedDyadicLargeEdgeOption :=
  OrdinarySlotChoice G.E Color K ⊕
    DivisibleLocalExtraChoice G.E G.V Class G.fst G.snd bucket
      (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)

/-- One coordinated option system containing every indexed edge, including
parallel edges. -/
def boundedDyadicLargeEdgeOptionSystem :
    RankThreeOptionSystem G.E
      (G.BoundedDyadicLargeEdgeSlot (Color := Color) K bucket gamma reserve
        residual)
      (G.BoundedDyadicLargeEdgeOption (Color := Color) K bucket gamma reserve
        residual) :=
  (OrdinarySlotChoice.system G.fst G.snd K).separatedSum
    (DivisibleLocalExtraChoice.system G.fst G.snd bucket
      (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
      (G.boundedDyadic_left_dvd_support bucket residual gamma reserve)
      (G.boundedDyadic_right_dvd_support bucket residual gamma reserve))

def boundedDyadicLargeEdgeMass
    (x : G.E → Color → Fin K → Fin K → ℝ) :
    G.BoundedDyadicLargeEdgeOption (Color := Color) K bucket gamma reserve
        residual → ℝ :=
  RankThreeOptionSystem.sumMass (OrdinarySlotChoice.mass K x)
    (DivisibleLocalExtraChoice.mass G.fst G.snd bucket
      (G.boundedDyadicExtraSlotCount bucket residual gamma reserve) residual)

theorem boundedDyadicLargeEdgeMass_nonneg
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (hx : ∀ e c i j, 0 ≤ x e c i j) (hr0 : ∀ e, 0 ≤ residual e) :
    ∀ z, 0 ≤ G.boundedDyadicLargeEdgeMass K bucket gamma reserve
      residual x z := by
  apply RankThreeOptionSystem.sumMass_nonneg
  · exact OrdinarySlotChoice.mass_nonneg K x hx
  · exact DivisibleLocalExtraChoice.mass_nonneg G.fst G.snd bucket _
      residual hr0

/-- Every base option still uses exactly its two endpoint slots. -/
theorem boundedDyadicLargeEdgeOptionSystem_slots_card_eq_two
    (z : G.BoundedDyadicLargeEdgeOption (Color := Color) K bucket gamma
      reserve residual) :
    ((G.boundedDyadicLargeEdgeOptionSystem K bucket gamma reserve residual
      ).slots z).card = 2 := by
  cases z with
  | inl o =>
      have hne : OrdinarySlotChoice.leftSlot G.fst K o ≠
          OrdinarySlotChoice.rightSlot G.snd K o := by
        intro h
        exact G.noLoop o.job
          (congrArg (fun s : OrdinarySlot G.V Color K ↦ s.vertex) h)
      simp [boundedDyadicLargeEdgeOptionSystem,
        RankThreeOptionSystem.separatedSum,
        RankThreeOptionSystem.liftSlotsLeft, RankThreeOptionSystem.sum,
        OrdinarySlotChoice.system, hne]
  | inr p =>
      have hne :
          DivisibleLocalExtraChoice.leftSlot G.fst G.snd bucket
              (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
              (G.boundedDyadic_left_dvd_support bucket residual gamma reserve)
              p ≠
            DivisibleLocalExtraChoice.rightSlot G.fst G.snd bucket
              (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
              (G.boundedDyadic_right_dvd_support bucket residual gamma reserve)
              p := by
        intro h
        exact G.noLoop p.1
          (congrArg (fun s : ExtraSlot G.V Class
            (G.boundedDyadicExtraSlotCount bucket residual gamma reserve) ↦
              s.1.1) h)
      simp [boundedDyadicLargeEdgeOptionSystem,
        RankThreeOptionSystem.separatedSum,
        RankThreeOptionSystem.liftSlotsRight, RankThreeOptionSystem.sum,
        DivisibleLocalExtraChoice.system, hne]

theorem quantized_boundedDyadicLargeEdgeOptionSystem_slots_card_eq_two
    (x : G.E → Color → Fin K → Fin K → ℝ) (N : ℕ)
    (q : QuantizedCopy N
      (G.boundedDyadicLargeEdgeMass K bucket gamma reserve residual x)) :
    (((G.boundedDyadicLargeEdgeOptionSystem K bucket gamma reserve residual
      ).quantized N
      (G.boundedDyadicLargeEdgeMass K bucket gamma reserve residual x)
      ).slots q).card = 2 := by
  exact G.boundedDyadicLargeEdgeOptionSystem_slots_card_eq_two
    K bucket gamma reserve residual q.1

/-- The base combined system has pair support bounded by the graph's endpoint
multiplicity. -/
theorem boundedDyadicLargeEdgeOptionSystem_pairSupportBounded
    {L : ℕ} (hmult : G.PairMultiplicityAtMost L) :
    (G.boundedDyadicLargeEdgeOptionSystem (Color := Color) K bucket gamma
      reserve residual).PairSupportBounded L := by
  apply RankThreeOptionSystem.separatedSum_pairSupportBounded
  · exact G.ordinarySlotChoice_pairSupportBounded hmult K
  · exact G.divisibleLocalExtraChoice_pairSupportBounded hmult bucket
      (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
      (G.boundedDyadic_left_dvd_support bucket residual gamma reserve)
      (G.boundedDyadic_right_dvd_support bucket residual gamma reserve)
      (fun e ↦ G.boundedDyadicExtraSlotCount_pos bucket residual gamma
        reserve _ _)
      (fun e ↦ G.boundedDyadicExtraSlotCount_pos bucket residual gamma
        reserve _ _)

/-- Fixed endpoint multiplicity multiplies the simple dyadic pair-codegree by
exactly `L`. -/
theorem boundedDyadicLargeEdge_quantized_slotPairCodegree_le
    {L : ℕ} (hmult : G.PairMultiplicityAtMost L)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (hx0 : ∀ e c i j, 0 ≤ x e c i j)
    (hx : ∀ e c i j, x e c i j ≤ 1 / (reserve : ℝ))
    (hr0 : ∀ e, 0 ≤ residual e) (hr1 : ∀ e, residual e ≤ 1)
    (hreserve : 0 < reserve) (N : ℕ)
    {s t : G.BoundedDyadicLargeEdgeSlot (Color := Color) K bucket gamma
      reserve residual} (hst : s ≠ t) :
    ((((G.boundedDyadicLargeEdgeOptionSystem (Color := Color) K bucket gamma
        reserve residual).quantized N
      (G.boundedDyadicLargeEdgeMass K bucket gamma reserve residual x)
      ).slotPairCodegree s t : ℕ) : ℝ) ≤
        (L : ℝ) * (N : ℝ) / reserve := by
  have hreserveR : (0 : ℝ) < reserve := by exact_mod_cast hreserve
  have hmassBound : ∀ z,
      G.boundedDyadicLargeEdgeMass K bucket gamma reserve residual x z ≤
        1 / (reserve : ℝ) := by
    intro z
    cases z with
    | inl q => exact hx q.job q.color q.leftPlace q.rightPlace
    | inr p =>
        have hcount : reserve ≤
            DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
              (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
              p.1 :=
          (G.boundedDyadicExtraSlotCount_ge_reserve bucket residual gamma
            reserve (G.fst p.1) (bucket p.1)).trans (Nat.le_max_left _ _)
        exact residual_div_count_le_inv_reserve (residual p.1) (hr1 p.1)
          hreserve hcount
  have hbase :=
    (G.boundedDyadicLargeEdgeOptionSystem (Color := Color) K bucket gamma
      reserve residual).quantized_slotPairCodegree_le_of_pairSupportBounded
      (G.boundedDyadicLargeEdgeOptionSystem_pairSupportBounded
        K bucket gamma reserve residual hmult)
      N (G.boundedDyadicLargeEdgeMass K bucket gamma reserve residual x)
      (1 / (reserve : ℝ)) (le_of_lt (one_div_pos.mpr hreserveR))
      (G.boundedDyadicLargeEdgeMass_nonneg K bucket gamma reserve residual x
        hx0 hr0) hmassBound hst
  calc
    _ ≤ (L : ℝ) * (N : ℝ) * (1 / (reserve : ℝ)) := hbase
    _ = (L : ℝ) * (N : ℝ) / reserve := by ring

/-- Endpoint-iteration form of the bound.  Thus the scalar package must use
`L * N / reserve ≤ lambda`, replacing the simple-graph condition
`N / reserve ≤ lambda`. -/
theorem boundedDyadicLargeEdge_quantized_slotPairCodegree_le_lambda
    {L : ℕ} (hmult : G.PairMultiplicityAtMost L)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (hx0 : ∀ e c i j, 0 ≤ x e c i j)
    (hx : ∀ e c i j, x e c i j ≤ 1 / (reserve : ℝ))
    (hr0 : ∀ e, 0 ≤ residual e) (hr1 : ∀ e, residual e ≤ 1)
    (hreserve : 0 < reserve) (N lambda : ℕ)
    (hscalar : (L : ℝ) * (N : ℝ) / reserve ≤ lambda)
    {s t : G.BoundedDyadicLargeEdgeSlot (Color := Color) K bucket gamma
      reserve residual} (hst : s ≠ t) :
    ((G.boundedDyadicLargeEdgeOptionSystem (Color := Color) K bucket gamma
        reserve residual).quantized N
      (G.boundedDyadicLargeEdgeMass K bucket gamma reserve residual x)
      ).slotPairCodegree s t ≤ lambda := by
  have hreal := G.boundedDyadicLargeEdge_quantized_slotPairCodegree_le
    K bucket gamma reserve residual hmult x hx0 hx hr0 hr1 hreserve N hst
  exact_mod_cast hreal.trans hscalar

end WeightedMultigraph

end

end WeightedEdgeColoring
