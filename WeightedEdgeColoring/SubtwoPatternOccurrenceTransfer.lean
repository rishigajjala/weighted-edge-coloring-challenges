import WeightedEdgeColoring.SubtwoPaletteProjection
import WeightedEdgeColoring.SubtwoGraphPalette

/-!
# Sending a palette through linear grouping

Each retained occurrence is paid for by a different original edge with the
same endpoints and at least its rounded weight. The resulting pattern on
retained types preserves capacity and endpoint reservations. This applies
to linear grouping after the block palette has already been proved.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 160000

open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u v
variable (G H : WeightedMultigraph.{u}) (vertex : G.V → H.V)
variable (O : H.E → Type v) [∀ j, Fintype (O j)]
variable (source : (Σ j, O j) → G.E)

/-- A feasible color on the rounded types, paid for by distinct old edges. -/
def subtwoOccurrencePattern
    (hvertex : Function.Surjective vertex) (hinj : Function.Injective source)
    (hinc : ∀ v o, G.Inc v (source o) ↔ H.Inc (vertex v) o.1)
    (hweight : ∀ o, H.weight o.1 ≤ G.weight (source o))
    (p : G.SubtwoWeightedPattern) : H.SubtwoWeightedPattern := by
  classical
  refine ⟨fun j => ∑ o : O j, p.val (source ⟨j,o⟩), ?_⟩
  intro w
  obtain ⟨v, rfl⟩ := hvertex w
  calc
    (∑ j : H.E, if H.Inc (vertex v) j then
        ((∑ o : O j, p.val (source ⟨j,o⟩) : ℕ) : ℝ) * H.weight j else 0) =
        ∑ j : H.E, ∑ o : O j,
          if H.Inc (vertex v) j then (p.val (source ⟨j,o⟩) : ℝ) * H.weight j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hi : H.Inc (vertex v) j
      · simp only [hi, if_true, Nat.cast_sum, Finset.sum_mul]
      · simp [hi]
    _ = ∑ o : (Σ j, O j),
        if H.Inc (vertex v) o.1 then (p.val (source o) : ℝ) * H.weight o.1 else 0 :=
      (Fintype.sum_sigma (fun o : (Σ j, O j) =>
        if H.Inc (vertex v) o.1 then (p.val (source o) : ℝ) * H.weight o.1 else 0)).symm
    _ ≤ ∑ o : (Σ j, O j),
        if G.Inc v (source o) then (p.val (source o) : ℝ) * G.weight (source o) else 0 := by
      apply Finset.sum_le_sum
      intro o _
      by_cases hi : G.Inc v (source o)
      · simp only [hi, if_true, (hinc v o).mp hi]
        exact mul_le_mul_of_nonneg_left (hweight o) (Nat.cast_nonneg _)
      · have hh : ¬ H.Inc (vertex v) o.1 := fun h => hi ((hinc v o).mpr h)
        simp [hi, hh]
    _ ≤ ∑ e : G.E, if G.Inc v e then (p.val e : ℝ) * G.weight e else 0 := by
      let image := (Finset.univ : Finset (Σ j, O j)).image source
      calc
        _ = ∑ e ∈ image, if G.Inc v e then (p.val e : ℝ) * G.weight e else 0 := by
          rw [Finset.sum_image hinj.injOn]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ image) (by
          intro e _ _
          by_cases hi : G.Inc v e
          · simp only [hi, if_true]
            exact mul_nonneg (Nat.cast_nonneg _) (G.weight_nonneg e)
          · simp [hi])
    _ ≤ 1 := p.property v

/-- The pattern map also preserves every reserved endpoint. -/
theorem subtwoOccurrencePattern_reserved
    (hvertex : Function.Surjective vertex) (hinj : Function.Injective source)
    (hinc : ∀ v o, G.Inc v (source o) ↔ H.Inc (vertex v) o.1)
    (hweight : ∀ o, H.weight o.1 ≤ G.weight (source o))
    (l : Option G.V) (p : G.SubtwoWeightedPattern) (j : H.E) :
    H.subtwoReservedColorPattern (l.map vertex)
      (G.subtwoOccurrencePattern H vertex O source hvertex hinj hinc hweight p) j =
    ∑ o : O j, G.subtwoReservedColorPattern l p (source ⟨j,o⟩) := by
  classical
  cases l with
  | none =>
    change ((∑ o : O j, p.val (source ⟨j,o⟩) : ℕ) : ℝ) = _
    simp only [Nat.cast_sum]
    rfl
  | some v =>
    change (((G.subtwoOccurrencePattern H vertex O source hvertex hinj hinc hweight p).avoidVertex
      H (vertex v)).val j : ℝ) = ∑ o : O j, ((p.avoidVertex G v).val (source ⟨j,o⟩) : ℝ)
    by_cases hi : H.Inc (vertex v) j
    · rw [SubtwoWeightedPattern.avoidVertex_zero _ _ _ _ hi]
      simp only [Nat.cast_zero]
      apply Eq.symm
      apply Finset.sum_eq_zero
      intro o _
      rw [SubtwoWeightedPattern.avoidVertex_zero _ _ _ _ ((hinc v ⟨j,o⟩).mpr hi)]
      simp
    · rw [SubtwoWeightedPattern.avoidVertex_keeps _ _ _ _ hi]
      change ((∑ o : O j, p.val (source ⟨j,o⟩) : ℕ) : ℝ) = _
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro o _
      have hh : ¬G.Inc v (source ⟨j,o⟩) := fun h => hi ((hinc v ⟨j,o⟩).mp h)
      rw [SubtwoWeightedPattern.avoidVertex_keeps _ _ _ _ hh]

/-- Fractional coverage transfers to the actual retained occurrences. -/
theorem subtwoOccurrence_paletteAttainable
    (hvertex : Function.Surjective vertex) (hinj : Function.Injective source)
    (hinc : ∀ v o, G.Inc v (source o) ↔ H.Inc (vertex v) o.1)
    (hweight : ∀ o, H.weight o.1 ≤ G.weight (source o))
    (budget : Option G.V → ℝ) (demand : G.E → ℝ)
    (hd : demand ∈ Subtwo.PaletteAttainable budget G.subtwoReservedColorPattern) :
    (fun j : H.E => ∑ o : O j, demand (source ⟨j,o⟩)) ∈
      Subtwo.PaletteAttainable budget
        (fun l p j => H.subtwoReservedColorPattern (l.map vertex) p j) := by
  classical
  have h := Subtwo.paletteAttainable_project budget
    G.subtwoReservedColorPattern
    (fun l p j => H.subtwoReservedColorPattern (l.map vertex) p j)
    (fun _ p => G.subtwoOccurrencePattern H vertex O source hvertex hinj hinc hweight p)
    (fun j e => ∑ o : O j, if source ⟨j,o⟩ = e then (1 : ℝ) else 0)
    (by intro j e; exact Finset.sum_nonneg (by intro o _; split_ifs <;> norm_num))
    (by
      intro l p j
      dsimp only
      rw [G.subtwoOccurrencePattern_reserved H vertex O source hvertex hinj hinc hweight]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro o _
      simp)
    hd
  convert h using 2
  dsimp only
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

end
end WeightedEdgeColoring.WeightedMultigraph
