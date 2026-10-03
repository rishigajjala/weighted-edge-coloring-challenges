import WeightedEdgeColoring.SubtwoPaletteAllocation

/-!
# Removing coordinates and combining identical pattern types

A nonnegative linear map on demand coordinates transports a fractional
reserved palette when every old pattern has a corresponding new pattern.
Allocation masses are summed when several old patterns have the same
image. This permits deleting tiny internal objects before integer rounding
and combining repeated physical copies into a bounded menu of types.
-/

open scoped BigOperators
namespace WeightedEdgeColoring.Subtwo
noncomputable section

variable {I J L P Q : Type*}
  [Fintype I] [Fintype J] [Fintype L] [DecidableEq L]
  [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- Aggregate the allocation on all old patterns with the same new image. -/
def projectedPaletteAllocation (map : L → P → Q) (a : L × P → ℝ) : L × Q → ℝ :=
  fun lq => ∑ p, if map lq.1 p = lq.2 then a (lq.1,p) else 0

theorem projectedPaletteAllocation_feasible
    (budget : L → ℝ) (map : L → P → Q) (a : L × P → ℝ)
    (ha : PaletteFeasible budget a) :
    PaletteFeasible budget (projectedPaletteAllocation map a) := by
  constructor
  · intro lq
    apply Finset.sum_nonneg
    intro p _
    split_ifs
    · exact ha.1 _
    · rfl
  · intro l
    unfold projectedPaletteAllocation
    rw [Finset.sum_comm]
    simpa using ha.2 l

theorem projectedPaletteCoverage
    (old : L → P → I → ℝ) (new : L → Q → J → ℝ)
    (map : L → P → Q) (A : J → I → ℝ)
    (hmap : ∀ l p j, new l (map l p) j = ∑ i, A j i * old l p i)
    (a : L × P → ℝ) (j : J) :
    paletteCoverage new (projectedPaletteAllocation map a) j =
      ∑ i, A j i * paletteCoverage old a i := by
  unfold paletteCoverage projectedPaletteAllocation
  calc
    (∑ l, ∑ q, (∑ p, if map l p = q then a (l,p) else 0) * new l q j) =
        ∑ l, ∑ p, a (l,p) * new l (map l p) j := by
      apply Finset.sum_congr rfl
      intro l _
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      simp only [ite_mul, zero_mul, Fintype.sum_ite_eq]
    _ = ∑ l, ∑ p, ∑ i, A j i * (a (l,p) * old l p i) := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro p _
      rw [hmap, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i, A j i * ∑ l, ∑ p, a (l,p) * old l p i := by
      calc
        _ = ∑ l, ∑ i, ∑ p, A j i * (a (l,p) * old l p i) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.sum_comm]
        _ = ∑ i, ∑ l, ∑ p, A j i * (a (l,p) * old l p i) := by
          rw [Finset.sum_comm]
        _ = _ := by simp_rw [Finset.mul_sum]

/-- Projecting the actual patterns preserves palette attainability. -/
theorem paletteAttainable_project
    (budget : L → ℝ)
    (old : L → P → I → ℝ) (new : L → Q → J → ℝ)
    (map : L → P → Q) (A : J → I → ℝ) (hA : ∀ j i, 0 ≤ A j i)
    (hmap : ∀ l p j, new l (map l p) j = ∑ i, A j i * old l p i)
    {d : I → ℝ} (hd : d ∈ PaletteAttainable budget old) :
    (fun j => ∑ i, A j i * d i) ∈ PaletteAttainable budget new := by
  obtain ⟨a, ha, hcover⟩ := hd.2
  refine ⟨?_, projectedPaletteAllocation map a,
    projectedPaletteAllocation_feasible budget map a ha, ?_⟩
  · intro j
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hA j i) (hd.1 i))
  · intro j
    rw [projectedPaletteCoverage old new map A hmap a j]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hcover i) (hA j i))

end
end WeightedEdgeColoring.Subtwo
