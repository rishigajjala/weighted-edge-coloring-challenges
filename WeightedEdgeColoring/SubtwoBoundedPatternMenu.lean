import WeightedEdgeColoring.SubtwoWeightedPatterns
import WeightedEdgeColoring.SubtwoLabelRounding

/-!
# Uniform finite errors for bounded type menus

After finite-type preprocessing, every retained type has weight at least
1/S and each block has at most m types. Then the entire pattern menu, and
therefore the error from flooring its masses, has a bound depending only
on S and m, not on the number of physical copies or graph vertices.
-/

open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G : WeightedMultigraph.{u})

theorem subtwoPattern_multiplicity_le_of_weight_lower
    (S : ℕ) (hS : 0 < S)
    (hweight : ∀ e, (1 : ℝ) / S ≤ G.weight e)
    (p : G.SubtwoWeightedPattern) (e : G.E) : p.val e ≤ S := by
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have hw : 1 ≤ G.weight e * S := (div_le_iff₀ hs).mp (hweight e)
  have hp := p.coordinate_load_le G e
  have hm : (0 : ℝ) ≤ p.val e := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hp hs.le
  have hmul2 := mul_le_mul_of_nonneg_left hw hm
  have hreal : (p.val e : ℝ) ≤ S := by nlinarith
  exact_mod_cast hreal

/-- A pattern is encoded by one of S+1 multiplicities at each type. -/
theorem card_subtwoWeightedPattern_le_uniform
    (S : ℕ) (hS : 0 < S)
    (hweight : ∀ e, (1 : ℝ) / S ≤ G.weight e) :
    Fintype.card G.SubtwoWeightedPattern ≤ (S + 1) ^ Fintype.card G.E := by
  let code : G.SubtwoWeightedPattern → (G.E → Fin (S + 1)) :=
    fun p e => ⟨p.val e, Nat.lt_succ_of_le
      (G.subtwoPattern_multiplicity_le_of_weight_lower S hS hweight p e)⟩
  have hi : Function.Injective code := by
    intro p q h
    apply Subtype.ext
    funext e
    exact congrArg Fin.val (congrFun h e)
  have hh := Fintype.card_le_of_injective code hi
  simpa using hh

end
end WeightedEdgeColoring.WeightedMultigraph

namespace WeightedEdgeColoring.Subtwo

variable {I L P : Type*} [Fintype I] [Fintype L] [Fintype P]

/-- A uniform bound on the number of omitted physical copies of one type. -/
theorem roundedPaletteErrorCount_le_uniform
    (pattern : L → P → I → ℕ) (S : ℕ)
    (hpattern : ∀ l p i, pattern l p i ≤ S) (i : I) :
    roundedPaletteErrorCount pattern i ≤ Fintype.card L * Fintype.card P * S := by
  unfold roundedPaletteErrorCount
  calc
    (∑ l, ∑ p, pattern l p i) ≤ ∑ _l : L, ∑ _p : P, S := by
      exact Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun p _ => hpattern l p i))
    _ = _ := by simp; ring

/-- The weighted rounding error at a vertex is bounded by the finite menu
size. It does not count the physical edges or the number of blocks. -/
theorem roundedPaletteVertexError_le_uniform
    (pattern : L → P → I → ℕ) (S : ℕ)
    (hpattern : ∀ l p i, pattern l p i ≤ S)
    (inc : I → Prop) [DecidablePred inc]
    (weight : I → ℝ) (hw0 : ∀ i, 0 ≤ weight i) (hw1 : ∀ i, weight i ≤ 1) :
    (∑ i, if inc i then (roundedPaletteErrorCount pattern i : ℝ) * weight i else 0) ≤
      (Fintype.card I : ℝ) * Fintype.card L * Fintype.card P * S := by
  classical
  calc
    (∑ i, if inc i then (roundedPaletteErrorCount pattern i : ℝ) * weight i else 0) ≤
        ∑ _i : I, ((Fintype.card L * Fintype.card P * S : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have he : (roundedPaletteErrorCount pattern i : ℝ) ≤
          ((Fintype.card L * Fintype.card P * S : ℕ) : ℝ) := by
        exact_mod_cast roundedPaletteErrorCount_le_uniform pattern S hpattern i
      by_cases hi : inc i
      · rw [if_pos hi]
        calc
          (roundedPaletteErrorCount pattern i : ℝ) * weight i ≤
              (roundedPaletteErrorCount pattern i : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left (hw1 i) (Nat.cast_nonneg _)
          _ ≤ _ := by simpa using he
      · rw [if_neg hi]
        exact Nat.cast_nonneg _
    _ = _ := by simp; ring

end WeightedEdgeColoring.Subtwo
