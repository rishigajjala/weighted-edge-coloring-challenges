import WeightedEdgeColoring.KempeGraphMomentBlockSequence
import WeightedEdgeColoring.FiniteColorPairingScheduleRobust

/-!
# Realizing a schedule of perfect color pairings

Each schedule stage is realized by processing its canonical color-pair roots
sequentially.  Properness preserves the size of every missing palette, so the
same selector hypotheses can be reused at every stage.  The resulting graph
statistics form the approximate orbits consumed by the robust operator
schedule lemmas.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open WeightedEdgeColoring.FiniteColorPairing
open WeightedEdgeColoring.FiniteColorPairingScheduleRobust

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

theorem exists_realizing_pairingSchedule
    {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color)
    (schedule : List (Pairing (Fin q)))
    (alpha L : ℝ) (halpha : 0 < alpha) (hL : 0 < L) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hrestricted : ∀ w, G.restrictedCharge R charge w ≤ n)
    (hpair : ∀ v w, G.pairCharge R charge v w ≤ L) :
    ∃ final : G.E → Fin q,
      G.IsProperOn F final ∧
      (∀ v, SingleApproxOrbit (G.momentBlockError alpha L n q) schedule
        (G.graphFirstMoment R charge F color v)
        (G.graphFirstMoment R charge F final v)) ∧
      (∀ v, SingleApproxOrbit (G.momentBlockError alpha L n q / n) schedule
        (G.graphDiagonalMoment R charge F color v)
        (G.graphDiagonalMoment R charge F final v)) ∧
      ∀ v, PairApproxOrbit (2 * (G.momentBlockError alpha L n q / n)) schedule
        (G.graphPairMoment R charge F color v)
        (G.graphPairMoment R charge F final v) := by
  induction schedule generalizing color with
  | nil =>
      refine ⟨color, hproper, ?_, ?_, ?_⟩
      · intro v
        exact SingleApproxOrbit.nil _
      · intro v
        exact SingleApproxOrbit.nil _
      · intro v
        exact PairApproxOrbit.nil _
  | cons p schedule ih =>
      rcases G.exists_realizing_pairingStage R charge F color hproper p
          alpha L halpha hL hn hcharge hmissing hrestricted hpair with
        ⟨next, hproperNext, hfirstStep, hdiagStep, hpairStep⟩
      have hmissingNext : ∀ w,
          alpha * n ≤ G.momentMissingSize F next w := by
        intro w
        have hcard := G.card_missingColorsAt_eq_of_isProperOn
          F color next hproper hproperNext w
        unfold momentMissingSize
        rw [← hcard]
        exact hmissing w
      rcases ih next hproperNext hmissingNext with
        ⟨final, hproperFinal, hfirstTail, hdiagTail, hpairTail⟩
      refine ⟨final, hproperFinal, ?_, ?_, ?_⟩
      · intro v
        exact SingleApproxOrbit.cons p schedule
          (G.graphFirstMoment R charge F color v)
          (G.graphFirstMoment R charge F next v)
          (G.graphFirstMoment R charge F final v)
          (hfirstStep v) (hfirstTail v)
      · intro v
        exact SingleApproxOrbit.cons p schedule
          (G.graphDiagonalMoment R charge F color v)
          (G.graphDiagonalMoment R charge F next v)
          (G.graphDiagonalMoment R charge F final v)
          (hdiagStep v) (hdiagTail v)
      · intro v
        exact PairApproxOrbit.cons p schedule
          (G.graphPairMoment R charge F color v)
          (G.graphPairMoment R charge F next v)
          (G.graphPairMoment R charge F final v)
          (hpairStep v) (hpairTail v)

end

end WeightedMultigraph
end WeightedEdgeColoring
