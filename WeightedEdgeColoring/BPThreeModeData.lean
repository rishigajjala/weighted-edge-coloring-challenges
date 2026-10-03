import WeightedEdgeColoring.BPCompatibleModeSelection
import WeightedEdgeColoring.BPCompatibleColoring
import WeightedEdgeColoring.BPGeneralReduction

/-!
# The three compatible modes

This file gives names to the three rows used by the sharp bipartite
bin-packing argument.  Keeping the data separate makes the subsequent
selection and coloring proof a direct application of the generic lemmas.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

abbrev ThreeMode := Fin 3

noncomputable def threeModeHeavyCap : ThreeMode → ℝ :=
  ![5 / 8, 7 / 12, 17 / 24]

noncomputable def threeModeLightCap : ThreeMode → ℝ :=
  ![3 / 8, 5 / 12, 7 / 24]

noncomputable def threeModeHeavyProbability : ThreeMode → ℝ :=
  ![1 / 20, 1 / 10, 1 / 12]

noncomputable def threeModeLightProbability : ThreeMode → ℝ :=
  ![1 / 20, 1 / 10, 1 / 18]

def threeModeClassK : ThreeMode → ℕ := ![2, 2, 3]

def threeModeCopies : ThreeMode → ℕ := ![2, 2, 2]

variable (G : WeightedMultigraph)

noncomputable def threeModeHeavyEdges (m : ThreeMode) : Finset G.E :=
  Finset.univ.filter fun e ↦
    1 / 2 < G.weight e ∧ G.weight e ≤ threeModeHeavyCap m

noncomputable def threeModeLightEdges (m : ThreeMode) : Finset G.E :=
  Finset.univ.filter fun e ↦
    1 / (threeModeClassK m + 1 : ℕ) < G.weight e ∧
      G.weight e ≤ threeModeLightCap m

theorem threeModeCopies_eq_two (m : ThreeMode) :
    threeModeCopies m = 2 := by
  fin_cases m <;> rfl

theorem threeModeClassK_pos (m : ThreeMode) :
    0 < threeModeClassK m := by
  fin_cases m <;> norm_num [threeModeClassK]

theorem threeModeHeavyProbability_nonneg (m : ThreeMode) :
    0 ≤ threeModeHeavyProbability m := by
  fin_cases m <;> norm_num [threeModeHeavyProbability]

theorem threeModeLightProbability_nonneg (m : ThreeMode) :
    0 ≤ threeModeLightProbability m := by
  fin_cases m <;> norm_num [threeModeLightProbability]

theorem threeModeLightProbability_le_heavy (m : ThreeMode) :
    threeModeLightProbability m ≤ threeModeHeavyProbability m := by
  fin_cases m <;> norm_num [threeModeLightProbability,
    threeModeHeavyProbability]

theorem threeModeHeavyProbability_sum :
    (∑ m : ThreeMode, threeModeHeavyProbability m) = 7 / 30 := by
  norm_num [Fin.sum_univ_succ, threeModeHeavyProbability]

theorem threeMode_probability_sum_le_one (e : G.E) :
    (∑ m : ThreeMode,
      G.compatibleModeProbability G.threeModeHeavyEdges
        G.threeModeLightEdges threeModeHeavyProbability
        threeModeLightProbability e m) ≤ 1 := by
  have hterm : ∀ m : ThreeMode,
      G.compatibleModeProbability G.threeModeHeavyEdges
          G.threeModeLightEdges threeModeHeavyProbability
          threeModeLightProbability e m ≤ threeModeHeavyProbability m := by
    intro m
    unfold compatibleModeProbability
    split_ifs
    · exact le_rfl
    · exact threeModeLightProbability_le_heavy m
    · exact threeModeHeavyProbability_nonneg m
  calc
    (∑ m : ThreeMode,
      G.compatibleModeProbability G.threeModeHeavyEdges
        G.threeModeLightEdges threeModeHeavyProbability
        threeModeLightProbability e m) ≤
        ∑ m : ThreeMode, threeModeHeavyProbability m :=
      Finset.sum_le_sum fun m _hm ↦ hterm m
    _ = 7 / 30 := threeModeHeavyProbability_sum
    _ ≤ 1 := by norm_num

theorem threeModeHeavy_light_disjoint (m : ThreeMode) :
    Disjoint (G.threeModeHeavyEdges m) (G.threeModeLightEdges m) := by
  rw [Finset.disjoint_left]
  intro e heH heS
  have hH := (Finset.mem_filter.mp heH).2.1
  have hS := (Finset.mem_filter.mp heS).2.2
  fin_cases m <;>
    norm_num [threeModeLightEdges, threeModeHeavyEdges,
      threeModeLightCap, threeModeClassK] at hS ⊢ <;> linarith

theorem threeModeHeavy_weight_le (m : ThreeMode) {e : G.E}
    (he : e ∈ G.threeModeHeavyEdges m) :
    G.weight e ≤ threeModeHeavyCap m :=
  (Finset.mem_filter.mp he).2.2

theorem threeModeLight_weight_le (m : ThreeMode) {e : G.E}
    (he : e ∈ G.threeModeLightEdges m) :
    G.weight e ≤ threeModeLightCap m :=
  (Finset.mem_filter.mp he).2.2

theorem threeModeLightCap_nonneg (m : ThreeMode) :
    0 ≤ threeModeLightCap m := by
  fin_cases m <;> norm_num [threeModeLightCap]

theorem threeMode_small_capacity (m : ThreeMode) :
    (threeModeCopies m : ℝ) * threeModeLightCap m ≤ 1 := by
  fin_cases m <;> norm_num [threeModeCopies, threeModeLightCap]

theorem threeMode_mixed_capacity (m : ThreeMode) :
    threeModeHeavyCap m +
        ((threeModeCopies m - 1 : ℕ) : ℝ) * threeModeLightCap m ≤ 1 := by
  fin_cases m <;>
    norm_num [threeModeCopies, threeModeHeavyCap, threeModeLightCap]

end WeightedMultigraph
end WeightedEdgeColoring
