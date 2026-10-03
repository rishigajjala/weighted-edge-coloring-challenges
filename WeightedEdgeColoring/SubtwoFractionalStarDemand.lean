import WeightedEdgeColoring.SubtwoFractionalTriangle

/-!
# Half-star coloring for real type demands

Here an edge index is a type, and a pattern may contain any natural number
of copies of that type. Demands and pattern masses are nonnegative real
numbers. This is the fractional form used after demand normalization;
it does not require an integer local bin bound or unit demand per edge.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Finite local fractional bin packings for real type demands. The same
finite index type can be padded with zero masses at different vertices. -/
structure SubtwoLocalFractionalBins (demand : G.E → ℝ) where
  P : Type u
  fintypeP : Fintype P
  pattern : G.V → P → G.E → ℕ
  mass : G.V → P → ℝ
  mass_nonneg : ∀ v p, 0 ≤ mass v p
  bin_feasible : ∀ v p, (∑ e, (pattern v p e : ℝ) * G.weight e) ≤ 1
  covers : ∀ v e, (∑ p, mass v p * (pattern v p e : ℝ)) =
    if G.Inc v e then demand e else 0

attribute [instance] SubtwoLocalFractionalBins.fintypeP

/-- A fractional weighted coloring of real type demands. A pattern is
feasible at each vertex, rather than having total weight at most one. -/
structure SubtwoFractionalDemandColoring (demand : G.E → ℝ) where
  P : Type u
  fintypeP : Fintype P
  pattern : P → G.E → ℕ
  mass : P → ℝ
  mass_nonneg : ∀ p, 0 ≤ mass p
  feasible : ∀ p v,
    (∑ e, if G.Inc v e then (pattern p e : ℝ) * G.weight e else 0) ≤ 1
  covers : ∀ e, (∑ p, mass p * (pattern p e : ℝ)) = demand e

attribute [instance] SubtwoFractionalDemandColoring.fintypeP

noncomputable def SubtwoFractionalDemandColoring.cost {demand : G.E → ℝ}
    (C : G.SubtwoFractionalDemandColoring demand) : ℝ := ∑ p, C.mass p

/-- Taking one half of each fractional local packing covers each type
exactly once, since every edge type has exactly two endpoints. -/
theorem exists_subtwoFractionalDemandColoring_of_local
    (demand : G.E → ℝ) (B : G.SubtwoLocalFractionalBins demand) (N : ℝ)
    (hcost : ∀ v, (∑ p, B.mass v p) ≤ N) :
    ∃ C : G.SubtwoFractionalDemandColoring demand,
      C.cost ≤ (Fintype.card G.V : ℝ) * N / 2 := by
  classical
  let C : G.SubtwoFractionalDemandColoring demand :=
    { P := G.V × B.P
      fintypeP := inferInstance
      pattern := fun p ↦ B.pattern p.1 p.2
      mass := fun p ↦ B.mass p.1 p.2 / 2
      mass_nonneg := fun p ↦ div_nonneg (B.mass_nonneg p.1 p.2) (by norm_num)
      feasible := by
        intro p v
        calc
          _ ≤ ∑ e, (B.pattern p.1 p.2 e : ℝ) * G.weight e := by
            apply Finset.sum_le_sum
            intro e _
            split_ifs
            · rfl
            · exact mul_nonneg (Nat.cast_nonneg _) (G.weight_nonneg e)
          _ ≤ 1 := B.bin_feasible p.1 p.2
      covers := by
        intro e
        rw [Fintype.sum_prod_type]
        have hlocal (v : G.V) :
            (∑ p, B.mass v p / 2 * (B.pattern v p e : ℝ)) =
              if G.Inc v e then demand e / 2 else 0 := by
          calc
            _ = (∑ p, B.mass v p * (B.pattern v p e : ℝ)) / 2 := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro p _
              ring
            _ = _ := by rw [B.covers]; split_ifs <;> simp
        simp_rw [hlocal]
        calc
          _ = (∑ v : G.V, if G.Inc v e then (1 / 2 : ℝ) else 0) * demand e := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro v _
            split_ifs <;> ring
          _ = demand e := by rw [G.subtwo_sum_incidence_half]; ring }
  refine ⟨C, ?_⟩
  calc
    C.cost = (∑ v : G.V, ∑ p, B.mass v p) / 2 := by
      simp [SubtwoFractionalDemandColoring.cost, C, Fintype.sum_prod_type,
        Finset.sum_div]
    _ ≤ (∑ _v : G.V, N) / 2 := by
      exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun v _ ↦ hcost v)
        (by norm_num)
    _ = (Fintype.card G.V : ℝ) * N / 2 := by simp

/-- On three vertices, arbitrary real local type demands have a
fractional weighted coloring of mass at most `3N/2`. -/
theorem exists_subtwoFractionalDemandColoring_triangle
    (demand : G.E → ℝ) (B : G.SubtwoLocalFractionalBins demand) (N : ℝ)
    (hV : Fintype.card G.V = 3) (hcost : ∀ v, (∑ p, B.mass v p) ≤ N) :
    ∃ C : G.SubtwoFractionalDemandColoring demand, C.cost ≤ 3 * N / 2 := by
  obtain ⟨C, hC⟩ := G.exists_subtwoFractionalDemandColoring_of_local demand B N hcost
  exact ⟨C, by simpa [hV] using hC⟩

end WeightedEdgeColoring.WeightedMultigraph
