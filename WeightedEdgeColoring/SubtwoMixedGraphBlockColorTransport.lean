import WeightedEdgeColoring.SubtwoMixedGraphBlockUniformEventualDecoder

/-! The decoder's canonical finite palette and the factory's flattened
block palette have the same colors, through a specified equivalence. -/

namespace WeightedEdgeColoring

noncomputable section

/-- Decoder color `Fin (card (Fin B × Fin k))` as an actual flattened block
color in `Fin (B*k)`. -/
def mixedBlockPaletteEquiv (B k : ℕ) :
    Fin (Fintype.card (Fin B × Fin k)) ≃ Fin (B * k) :=
  (Fintype.equivFin (Fin B × Fin k)).symm.trans finProdFinEquiv

theorem mixedBlockPaletteEquiv_apply (B k : ℕ)
    (d : Fin (Fintype.card (Fin B × Fin k))) :
    mixedBlockPaletteEquiv B k d =
      finProdFinEquiv ((Fintype.equivFin (Fin B × Fin k)).symm d) := rfl

theorem mixedBlockPaletteEquiv_symm_apply (B k : ℕ)
    (c : Fin (B * k)) :
    (mixedBlockPaletteEquiv B k).symm c =
      (Fintype.equivFin (Fin B × Fin k))
        (finProdFinEquiv.symm c) := by
  simp [mixedBlockPaletteEquiv]

namespace WeightedMultigraph

variable (G : WeightedMultigraph)

theorem isFeasibleOn_colorEquiv {q q' : ℕ}
    (P : Finset G.E) (color : G.E → Fin q)
    (phi : Fin q ≃ Fin q')
    (hcolor : G.IsFeasibleOn P color) :
    G.IsFeasibleOn P (fun e ↦ phi (color e)) := by
  classical
  intro v i
  have h := hcolor v (phi.symm i)
  unfold colorLoadOn at h ⊢
  convert h using 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases hinc : G.Inc v e
  · simp [hinc, phi.apply_eq_iff_eq_symm_apply]
  · simp [hinc]

theorem isFeasibleOn_flattenMixedBlockColor
    {B k : ℕ} (P : Finset G.E)
    (color : G.E → Fin (Fintype.card (Fin B × Fin k)))
    (hcolor : G.IsFeasibleOn P color) :
    G.IsFeasibleOn P
      (fun e ↦ mixedBlockPaletteEquiv B k (color e)) :=
  G.isFeasibleOn_colorEquiv P color (mixedBlockPaletteEquiv B k) hcolor

theorem positiveFlatProposal_of_positiveBlockProposal
    {B k : ℕ} (x : G.E → Fin (B * k) → ℝ)
    (color : G.E → Fin (Fintype.card (Fin B × Fin k)))
    (e : G.E)
    (hpos : 0 < x e (finProdFinEquiv
      ((Fintype.equivFin (Fin B × Fin k)).symm (color e)))) :
    0 < x e (mixedBlockPaletteEquiv B k (color e)) := by
  simpa only [mixedBlockPaletteEquiv_apply] using hpos

end WeightedMultigraph

end
end WeightedEdgeColoring
