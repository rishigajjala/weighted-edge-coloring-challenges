import WeightedEdgeColoring.KempeGraphMomentBlockConcrete

/-!
# One concrete block, uniformly over all moment coordinates

The concrete selector states its nontrivial estimates only on the two block
colors and on cross-block pair coordinates.  The exact outside and paired
invariance lemmas fill in all remaining coordinates here.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open WeightedEdgeColoring.FiniteColorPairBlockOperators

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- The single-coordinate support of the block swapping `a` and `b`. -/
def singleBlockTouches {q : ℕ} (a b c : Fin q) : Prop := c = a ∨ c = b

instance instDecidableSingleBlockTouches {q : ℕ} (a b c : Fin q) :
    Decidable (singleBlockTouches a b c) := by
  unfold singleBlockTouches
  infer_instance

/-- The pair-coordinate support of the block swapping `a` and `b`. -/
def pairBlockTouches {q : ℕ} (a b c d : Fin q) : Prop :=
  singleBlockTouches a b c ∨ singleBlockTouches a b d

instance instDecidablePairBlockTouches {q : ℕ} (a b c d : Fin q) :
    Decidable (pairBlockTouches a b c d) := by
  unfold pairBlockTouches
  infer_instance

theorem momentBlockError_nonneg {n q : ℕ}
    {alpha L : ℝ} (halpha : 0 < alpha) (hL : 0 < L) (hn : 0 < n) :
    0 ≤ G.momentBlockError alpha L n q := by
  unfold momentBlockError momentBlockB
  apply mul_nonneg
  · positivity
  · unfold WeightedEdgeColoring.FinitePartialResamplingNumerics.packingDeviation
    have hD0 : 0 ≤ G.momentBlockD alpha L n q := by
      unfold momentBlockD momentBlockB
      positivity
    have hBpos : 0 < 2 * (L / alpha + L / alpha ^ 2) / (n : ℝ) := by
      positivity
    have hlog0 :=
      WeightedEdgeColoring.FinitePartialResamplingNumerics.packingLog_nonneg
        (div_nonneg hD0 hBpos.le)
    positivity

theorem exists_kempeBoolSwitch_realizing_momentBlock_allCoordinates
    {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q) (hab : a ≠ b)
    (alpha L : ℝ) (halpha : 0 < alpha) (hL : 0 < L) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hrestricted : ∀ w, G.restrictedCharge R charge w ≤ n)
    (hpair : ∀ v w, G.pairCharge R charge v w ≤ L) :
    ∃ next : G.E → Fin q,
      G.IsProperOn F next ∧
      (∀ v c,
        |G.graphFirstMoment R charge F next v c -
          singleBlockAverage a b
            (G.graphFirstMoment R charge F color v) c| ≤
          if singleBlockTouches a b c then
            G.momentBlockError alpha L n q else 0) ∧
      (∀ v c,
        |G.graphDiagonalMoment R charge F next v c -
          singleBlockAverage a b
            (G.graphDiagonalMoment R charge F color v) c| ≤
          if singleBlockTouches a b c then
            G.momentBlockError alpha L n q / n else 0) ∧
      ∀ v c d,
        |G.graphPairMoment R charge F next v c d -
          pairBlockAverage a b
            (G.graphPairMoment R charge F color v) c d| ≤
          if pairBlockTouches a b c d then
            G.momentBlockError alpha L n q / n else 0 := by
  rcases G.exists_kempeBoolSwitch_realizing_momentBlock_concrete
      R charge F color hproper a b alpha L halpha hL hn hcharge
      hmissing hrestricted hpair with
    ⟨coin, hproperNext, hfirst, hdiag, hpairCross⟩
  let next := G.kempeBoolSwitch F color a b coin
  have herror0 : 0 ≤ G.momentBlockError alpha L n q :=
    G.momentBlockError_nonneg halpha hL hn
  have herrorSecond0 : 0 ≤ G.momentBlockError alpha L n q / n :=
    div_nonneg herror0 (Nat.cast_nonneg n)
  refine ⟨next, hproperNext, ?_, ?_, ?_⟩
  · intro v c
    by_cases hca : c = a
    · subst c
      simpa [next, blockSideColor, singleBlockTouches] using
        (hfirst v false).le
    · by_cases hcb : c = b
      · subst c
        simpa [next, blockSideColor, singleBlockTouches] using
          (hfirst v true).le
      · rw [G.graphFirstMoment_kempeBoolSwitch_outside
          R charge F color hproper a b c hca hcb coin v]
        rw [singleBlockAverage_apply_of_ne hca hcb]
        simp [singleBlockTouches, hca, hcb]
  · intro v c
    by_cases hca : c = a
    · subst c
      simpa [next, blockSideColor, singleBlockTouches] using
        (hdiag v false).le
    · by_cases hcb : c = b
      · subst c
        simpa [next, blockSideColor, singleBlockTouches] using
          (hdiag v true).le
      · rw [G.graphDiagonalMoment_kempeBoolSwitch_outside
          R charge F color hproper a b c hca hcb coin v]
        rw [singleBlockAverage_apply_of_ne hca hcb]
        simp [singleBlockTouches, hca, hcb]
  · intro v c d
    have hpairAverageSymm (i j : Fin q) :
        pairBlockAverage a b
            (G.graphPairMoment R charge F color v) i j =
          pairBlockAverage a b
            (G.graphPairMoment R charge F color v) j i := by
      unfold pairBlockAverage
      rw [G.graphPairMoment_symmetric R charge F color v i j]
      rw [G.graphPairMoment_symmetric R charge F color v
        (Equiv.swap a b i) (Equiv.swap a b j)]
    by_cases hcd : c = d
    · subst d
      simp [graphPairMoment, WeightedMomentStatistics.pairMoment,
        pairBlockAverage, pairBlockTouches, singleBlockTouches]
      split
      · exact herrorSecond0
      · exact le_rfl
    by_cases hca : c = a
    · subst c
      by_cases hda : d = a
      · exact False.elim (hcd hda.symm)
      by_cases hdb : d = b
      · subst d
        rw [G.graphPairMoment_kempeBoolSwitch_paired
          R charge F color hproper a b coin v,
          pairBlockAverage_apply_paired a b
            (G.graphPairMoment R charge F color v)
            (G.graphPairMoment_symmetric R charge F color v)]
        simpa [pairBlockTouches, singleBlockTouches] using herrorSecond0
      · simpa [next, blockSideColor, pairBlockTouches,
          singleBlockTouches] using
          (hpairCross v false d hda hdb).le
    · by_cases hcb : c = b
      · subst c
        by_cases hda : d = a
        · subst d
          rw [G.graphPairMoment_symmetric R charge F next v b a,
            hpairAverageSymm b a]
          have hpaired := G.graphPairMoment_kempeBoolSwitch_paired
            R charge F color hproper a b coin v
          rw [hpaired,
            pairBlockAverage_apply_paired a b
              (G.graphPairMoment R charge F color v)
              (G.graphPairMoment_symmetric R charge F color v)]
          simpa [pairBlockTouches, singleBlockTouches] using herrorSecond0
        · by_cases hdb : d = b
          · exact False.elim (hcd hdb.symm)
          · simpa [next, blockSideColor, pairBlockTouches,
              singleBlockTouches] using
              (hpairCross v true d hda hdb).le
      · by_cases hda : d = a
        · subst d
          rw [G.graphPairMoment_symmetric R charge F next v c a,
            hpairAverageSymm c a]
          have h := hpairCross v false c hca hcb
          simpa [next, blockSideColor, pairBlockTouches,
            singleBlockTouches,
            pairBlockAverage,
            Equiv.swap_apply_of_ne_of_ne hca hcb,
            G.graphPairMoment_symmetric R charge F color v] using h.le
        · by_cases hdb : d = b
          · subst d
            rw [G.graphPairMoment_symmetric R charge F next v c b,
              hpairAverageSymm c b]
            have h := hpairCross v true c hca hcb
            simpa [next, blockSideColor, pairBlockTouches,
              singleBlockTouches,
              pairBlockAverage,
              Equiv.swap_apply_of_ne_of_ne hca hcb,
              G.graphPairMoment_symmetric R charge F color v] using h.le
          · rw [G.graphPairMoment_kempeBoolSwitch_outside
              R charge F color hproper a b c d hca hcb hda hdb coin v]
            rw [pairBlockAverage_apply_of_ne hca hcb hda hdb]
            simp [pairBlockTouches, singleBlockTouches, hca, hcb,
              hda, hdb]

end

end WeightedMultigraph
end WeightedEdgeColoring
