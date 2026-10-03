import WeightedEdgeColoring.GreedySkeleton

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph)

/-- A certificate for the weighted insertion argument: a descending greedy
skeleton together with an ordinary proper Shannon coloring. -/
def HasColoredHeavySkeleton (n : ℕ) : Prop :=
  ∃ F : Finset G.E, ∃ base : G.E → Fin (3 * n),
    G.HasHeavySkeletonWitnesses F n ∧ G.IsProperOn F base

/-- A colored heavy skeleton gives the exact weighted `3n` bound. -/
theorem hasWeightedColoring_three_of_coloredHeavySkeleton
    (n : ℕ) (hn : 1 ≤ n) (hdelta : G.deltaW ≤ n)
    (hskel : G.HasColoredHeavySkeleton n) :
    G.HasWeightedColoring (3 * n) := by
  rcases hskel with ⟨F, base, hwitness, hproper⟩
  exact G.hasWeightedColoring_three_of_heavySkeleton n hn F base hproper
    (G.isFeasibleOn_of_isProperOn F base hproper) hdelta hwitness

/-- Positive edge weights imply that weighted degree zero is possible only
when there are no edges. -/
theorem hasWeightedColoring_zero_of_deltaW_eq_zero
    (hzero : G.deltaW = 0) : G.HasWeightedColoring 0 := by
  have hedge : ∀ e : G.E, False := by
    intro e
    have hpos : 0 < G.starWeight (G.fst e) :=
      (G.weight_pos e).trans_le (G.weight_le_starWeight_fst e)
    have hle : G.starWeight (G.fst e) ≤ 0 := by
      simpa [hzero] using G.starWeight_le_deltaW (G.fst e)
    linarith
  let color : G.E → Fin 0 := fun e => (hedge e).elim
  refine ⟨color, ?_⟩
  intro _v i
  exact Fin.elim0 i

/-- A construction of colored heavy skeletons at every positive integral
load proves the exact `3 * ceil Δw` theorem. -/
theorem generalMultigraphThreeCeil_of_coloredHeavySkeletons
    (hskel : ∀ (H : WeightedMultigraph.{u}) (n : ℕ),
      1 ≤ n → H.deltaW ≤ n → H.HasColoredHeavySkeleton n) :
    GeneralMultigraphThreeCeil.{u} := by
  intro H
  let n := Nat.ceil H.deltaW
  have hdelta : H.deltaW ≤ n := Nat.le_ceil H.deltaW
  by_cases hn0 : n = 0
  · have hzero : H.deltaW = 0 := by
      apply le_antisymm
      · simpa [n, hn0] using hdelta
      · exact H.deltaW_nonneg
    have hz := H.hasWeightedColoring_zero_of_deltaW_eq_zero hzero
    have hchi : H.chiW ≤ 0 := H.chiW_le_of_hasWeightedColoring hz
    simpa [n, hn0] using hchi
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hc := H.hasWeightedColoring_three_of_coloredHeavySkeleton n hn hdelta
      (hskel H n hn hdelta)
    exact H.chiW_le_of_hasWeightedColoring hc

/-- Shannon's ordinary `3n` coloring statement in precisely the form used by
the weighted proof. -/
def ShannonThreeAt (G : WeightedMultigraph) (n : ℕ) : Prop :=
  0 < n → ∀ F : Finset G.E,
    (∀ v, G.degreeOn F v ≤ 2 * n) →
    ∃ base : G.E → Fin (3 * n), G.IsProperOn F base

theorem hasColoredHeavySkeleton_of_shannon
    (n : ℕ) (hn : 0 < n) (hshannon : G.ShannonThreeAt n) :
    G.HasColoredHeavySkeleton n := by
  let F := G.greedySkeleton n
  rcases hshannon hn F (G.degreeOn_greedySkeleton_le n) with ⟨base, hproper⟩
  exact ⟨F, base, G.greedySkeleton_hasHeavyWitnesses n, hproper⟩

/-- The axiom-free weighted development reduces the exact theorem to the
ordinary finite Shannon coloring theorem, with no analytic or asymptotic
claim left in the bridge. -/
theorem generalMultigraphThreeCeil_of_shannon
    (hshannon : ∀ H : WeightedMultigraph.{u}, ∀ n, H.ShannonThreeAt n) :
    GeneralMultigraphThreeCeil.{u} := by
  apply generalMultigraphThreeCeil_of_coloredHeavySkeletons
  intro H n hn _hdelta
  exact H.hasColoredHeavySkeleton_of_shannon n hn (hshannon H n)

theorem generalMultigraphDeltaAsymptotic_of_shannon
    (hshannon : ∀ H : WeightedMultigraph.{u}, ∀ n, H.ShannonThreeAt n) :
    GeneralMultigraphDeltaAsymptotic.{u} :=
  generalMultigraphDeltaAsymptotic_of_threeCeil
    (generalMultigraphThreeCeil_of_shannon hshannon)

end WeightedMultigraph
end WeightedEdgeColoring
