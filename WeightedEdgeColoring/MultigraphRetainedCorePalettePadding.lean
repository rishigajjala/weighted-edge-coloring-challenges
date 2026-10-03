import WeightedEdgeColoring.MultigraphColorDependentRetainedCoreRoundingFinal

/-!
# Padding an arbitrary palette to the retained-core block width

The retained-core selector chooses a fixed block width.  This file pads an
arbitrary nonempty palette by fewer than one block, runs the exact-product
theorem, and removes the zero-probability padding colors.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

/-- Split a larger finite palette into the original colors and padding colors. -/
def palettePadEquiv {q Q : ℕ} (h : q ≤ Q) :
    Fin q ⊕ Fin (Q - q) ≃ Fin Q :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

/-- Extend a proposal by zero on the padding colors. -/
def padProposal (G : WeightedMultigraph.{u}) {q Q : ℕ} (h : q ≤ Q)
    (x : G.E → Fin q → ℝ) : G.E → Fin Q → ℝ :=
  fun e c ↦ Sum.elim (x e) (fun _ ↦ 0) ((palettePadEquiv h).symm c)

@[simp] theorem padProposal_inl (G : WeightedMultigraph.{u})
    {q Q : ℕ} (h : q ≤ Q) (x : G.E → Fin q → ℝ) (e : G.E) (c : Fin q) :
    G.padProposal h x e (palettePadEquiv h (Sum.inl c)) = x e c := by
  simp [padProposal, palettePadEquiv]

@[simp] theorem padProposal_inr (G : WeightedMultigraph.{u})
    {q Q : ℕ} (h : q ≤ Q) (x : G.E → Fin q → ℝ) (e : G.E)
    (c : Fin (Q - q)) :
    G.padProposal h x e (palettePadEquiv h (Sum.inr c)) = 0 := by
  simp [padProposal, palettePadEquiv]

@[simp] theorem sum_padProposal (G : WeightedMultigraph.{u})
    {q Q : ℕ} (h : q ≤ Q) (x : G.E → Fin q → ℝ) (e : G.E) :
    ∑ c, G.padProposal h x e c = ∑ c, x e c := by
  rw [← (palettePadEquiv h).sum_comp]
  rw [Fintype.sum_sum_type]
  simp

/-- Zero padding preserves a local packing-polytope proposal. -/
theorem padProposal_isAverageOfStarFeasibleSets (G : WeightedMultigraph.{u})
    {q Q : ℕ} (h : q ≤ Q) (x : G.E → Fin q → ℝ)
    (hlocal : ∀ v c, G.IsAverageOfStarFeasibleSets v
      (fun se ↦ x se.1 c)) :
    ∀ v c, G.IsAverageOfStarFeasibleSets v
      (fun se ↦ G.padProposal h x se.1 c) := by
  intro v c
  cases hc : (palettePadEquiv h).symm c with
  | inl d =>
      simpa [padProposal, hc] using hlocal v d
  | inr d =>
      refine ⟨1, (fun _ ↦ 1), (fun _ ↦ ∅), ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro i
        simp [StarFeasible]
      · intro e
        simp [padProposal, hc]

/-- Removing the zero padding colors preserves support and feasibility. -/
theorem exists_unpad_partialColoring
    (G : WeightedMultigraph.{u}) {q Q : ℕ} (hq : 0 < q) (h : q ≤ Q)
    (x : G.E → Fin q → ℝ)
    {P : Finset G.E} {paddedColor : G.E → Fin Q}
    (hfeasible : G.IsFeasibleOn P paddedColor)
    (hsupport : ∀ e ∈ P, 0 < G.padProposal h x e (paddedColor e)) :
    ∃ color : G.E → Fin q,
      G.IsFeasibleOn P color ∧ ∀ e ∈ P, 0 < x e (color e) := by
  classical
  let fallback : Fin q := ⟨0, hq⟩
  let color : G.E → Fin q := fun e ↦
    match (palettePadEquiv h).symm (paddedColor e) with
    | Sum.inl c => c
    | Sum.inr _ => fallback
  have hside : ∀ e ∈ P, ∃ c : Fin q,
      (palettePadEquiv h).symm (paddedColor e) = Sum.inl c := by
    intro e he
    cases hc : (palettePadEquiv h).symm (paddedColor e) with
    | inl c => exact ⟨c, rfl⟩
    | inr d =>
        have hp := hsupport e he
        simp [padProposal, hc] at hp
  have hcolor : ∀ e ∈ P,
      palettePadEquiv h (Sum.inl (color e)) = paddedColor e := by
    intro e he
    rcases hside e he with ⟨c, hc⟩
    calc
      palettePadEquiv h (Sum.inl (color e)) =
          palettePadEquiv h (Sum.inl c) := by simp [color, hc]
      _ = paddedColor e := by
        rw [← hc]
        exact (palettePadEquiv h).apply_symm_apply (paddedColor e)
  refine ⟨color, ?_, ?_⟩
  · intro v c
    have hp := hfeasible v (palettePadEquiv h (Sum.inl c))
    unfold colorLoadOn at hp ⊢
    convert hp using 1
    apply Finset.sum_congr rfl
    intro e he
    rw [← hcolor e he]
    simp [color]
  · intro e he
    rcases hside e he with ⟨c, hc⟩
    have hp := hsupport e he
    simpa [padProposal, color, hc] using hp

end WeightedMultigraph

end

end WeightedEdgeColoring
