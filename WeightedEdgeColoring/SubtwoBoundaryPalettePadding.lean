import WeightedEdgeColoring.SubtwoFinitePartialBijection

/-!
# Padding actual boundary color classes

A color already used on the boundary keeps its endpoint label. Unused
colors may be assigned extra labels until prescribed integral class sizes
are reached. This gives room for every rounded reserved pattern without
changing any existing physical edge color.
-/

open scoped BigOperators
namespace WeightedEdgeColoring.Subtwo
noncomputable section

variable {C L : Type*} [Fintype C] [Fintype L] [DecidableEq L]

/-- The free class consists of all colors left after padding the labeled
classes to their prescribed sizes. -/
def paddedBoundaryBudget (K : ℕ) (m : L → ℕ) : Option L → ℕ
  | none => K - ∑ l, m l
  | some l => m l

/-- Identify the actual palette with the padded label classes, fixing the
label of every color that is already used. -/
theorem exists_boundaryPaletteEquiv
    (label : C → Option L) (m : L → ℕ)
    (hcount : ∀ l, Fintype.card {c : C // label c = some l} ≤ m l)
    (htotal : (∑ l, m l) ≤ Fintype.card C) :
    ∃ e : C ≃ (Σ l : Option L, Fin (paddedBoundaryBudget (Fintype.card C) m l)),
      ∀ c, label c ≠ none → (e c).1 = label c := by
  classical
  let Budget := paddedBoundaryBudget (Fintype.card C) m
  let Target := Σ l : Option L, Fin (Budget l)
  let Used := {c : C // label c ≠ none}
  let Fiber := fun l : L => {c : C // label c = some l}
  have hem : ∀ l, Nonempty (Fiber l ↪ Fin (m l)) := by
    intro l
    exact Function.Embedding.nonempty_of_card_le (by simpa [Fiber] using hcount l)
  let emb : ∀ l, Fiber l ↪ Fin (m l) := fun l => Classical.choice (hem l)
  have hget : ∀ c : Used, ∃ l : L, label c.val = some l :=
    fun c => Option.ne_none_iff_exists'.mp c.property
  choose get hget using hget
  let g : Used → (Σ l : L, Fiber l) := fun c => ⟨get c, ⟨c.val, hget c⟩⟩
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : (Σ l : L, Fiber l) => z.2.val) hab
  let em : (Σ l : L, Fiber l) ↪ Target :=
    Function.Embedding.sigmaMap ⟨some, Option.some_injective L⟩ emb
  let f : Used → Target := fun c => em (g c)
  have hf : Function.Injective f := em.injective.comp hg
  have hcard : Fintype.card C = Fintype.card Target := by
    simp only [Target, Fintype.card_sigma, Fintype.card_fin,
      Fintype.sum_option, Budget, paddedBoundaryBudget]
    omega
  obtain ⟨e, he⟩ := exists_equiv_extending_subtype
    (fun c : C => label c ≠ none) f hf hcard
  refine ⟨e, ?_⟩
  intro c hc
  have hh := congrArg Sigma.fst (he ⟨c, hc⟩)
  change (e c).1 = some (get ⟨c, hc⟩) at hh
  exact hh.trans (hget ⟨c, hc⟩).symm

/-- Place any family of local reserved pattern colors in the actual
boundary palette. A placed pattern with label `none` meets no used boundary
color; a pattern with label `some v` can meet only the same endpoint `v`.
Unused boundary colors can host any label. -/
theorem exists_reservedPalettePlacement
    (label : C → Option L) (m : L → ℕ)
    (hcount : ∀ l, Fintype.card {c : C // label c = some l} ≤ m l)
    (htotal : (∑ l, m l) ≤ Fintype.card C)
    (P : Option L → Type*) [∀ l, Fintype (P l)]
    (hP : ∀ l, Fintype.card (P l) ≤ paddedBoundaryBudget (Fintype.card C) m l) :
    ∃ place : (Σ l, P l) ↪ C,
      ∀ p, label (place p) = none ∨ label (place p) = p.1 := by
  classical
  obtain ⟨e, he⟩ := exists_boundaryPaletteEquiv label m hcount htotal
  have hem : ∀ l, Nonempty (P l ↪ Fin (paddedBoundaryBudget (Fintype.card C) m l)) := by
    intro l
    exact Function.Embedding.nonempty_of_card_le (by simpa using hP l)
  let emb : ∀ l, P l ↪ Fin (paddedBoundaryBudget (Fintype.card C) m l) :=
    fun l => Classical.choice (hem l)
  let target : (Σ l, P l) ↪ (Σ l, Fin (paddedBoundaryBudget (Fintype.card C) m l)) :=
    Function.Embedding.sigmaMap (Function.Embedding.refl _) emb
  let place : (Σ l, P l) ↪ C := target.trans e.symm.toEmbedding
  refine ⟨place, ?_⟩
  intro p
  by_cases hn : label (place p) = none
  · exact Or.inl hn
  · right
    have hh := he (place p) hn
    have hcoord : (e (place p)).1 = p.1 := by
      change (e (e.symm (target p))).1 = p.1
      rw [Equiv.apply_symm_apply]
      cases p
      rfl
    exact hh.symm.trans hcoord

end
end WeightedEdgeColoring.Subtwo
