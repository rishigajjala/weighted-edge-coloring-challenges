import WeightedEdgeColoring.SubtwoK6CycleDirection
import WeightedEdgeColoring.SubtwoK6SupportBridge

namespace WeightedEdgeColoring.Subtwo.K6CycleWitness
open K6MatchingDeficits K6SupportFinite K6SupportBridge K6CycleDirection

theorem cycleMask_bit : ∀ j : Fin 105, ∀ e : Edge,
    (evenCycleMasks[j]).testBit e.val = true ↔ intDirection j e ≠ 0 := by
  decide +kernel

theorem cycleMask_lt : ∀ j : Fin 105, evenCycleMasks[j] < 32768 := by
  decide +kernel

theorem hasEvenCycle_witness (b : Edge → Bool)
    (h : hasEvenCycle (supportMask b).val = true) :
    ∃ j : Fin 105, ∀ e : Edge, direction j e ≠ 0 → b e = true := by
  obtain ⟨i, hi, hc⟩ := Array.any_eq_true.mp h
  have hisize : i < 105 := by simpa [evenCycleMasks] using hi
  let j : Fin 105 := ⟨i, hisize⟩
  refine ⟨j, ?_⟩
  intro e hde
  have hmb : (evenCycleMasks[j]).testBit e.val = true := by
    apply (cycleMask_bit j e).2
    intro hz
    apply hde
    simp only [direction]
    exact_mod_cast hz
  have hcm : contains (supportMask b).val (evenCycleMasks[j]) = true := by
    simpa [hasEvenCycle, evenCycleMasks, j] using hc
  have hm : (evenCycleMasks[j]) < 32768 := cycleMask_lt j
  exact (contains_supportMask_iff b _ hm).1 hcm e hmb

end WeightedEdgeColoring.Subtwo.K6CycleWitness
