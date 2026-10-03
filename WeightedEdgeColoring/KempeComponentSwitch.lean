import WeightedEdgeColoring.BipartitePackets
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Two-colour component switches

Fix a proper colouring on an edge set `F` and two colours `a,b`.  The
`a,b`-edges define a simple graph on the original vertices.  A Kempe switch
chooses any collection of connected components of this graph and exchanges
`a` and `b` on every selected component.

This file proves the two structural facts used by the mixing argument:

* every selected-component switch is still proper on `F`;
* at a vertex, the new missing-colour set is obtained from the old one by
  either the transposition `(a b)` or the identity, according to the bit of
  that vertex's component.

No probability is used here.  Later files may put independent fair bits on
the connected components.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- The oriented relation carried by the `a,b`-coloured edges in `F`.
`SimpleGraph.fromRel` below adds the reverse direction and removes loops. -/
def twoColorRel {q : ℕ} (F : Finset G.E) (color : G.E → Fin q)
    (a b : Fin q) (u v : G.V) : Prop :=
  ∃ e, e ∈ F ∧ G.fst e = u ∧ G.snd e = v ∧
    (color e = a ∨ color e = b)

/-- The simple graph formed by the edges of `F` carrying either `a` or `b`. -/
def twoColorGraph {q : ℕ} (F : Finset G.E) (color : G.E → Fin q)
    (a b : Fin q) : SimpleGraph G.V :=
  SimpleGraph.fromRel (G.twoColorRel F color a b)

/-- Connected components of the two-colour graph are the independent Kempe
switch variables. -/
abbrev TwoColorComponent {q : ℕ} (F : Finset G.E)
    (color : G.E → Fin q) (a b : Fin q) :=
  (G.twoColorGraph F color a b).ConnectedComponent

theorem twoColorGraph_adj_fst_snd {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    {e : G.E} (heF : e ∈ F) (heColor : color e = a ∨ color e = b) :
    (G.twoColorGraph F color a b).Adj (G.fst e) (G.snd e) := by
  refine ⟨G.noLoop e, Or.inl ?_⟩
  exact ⟨e, heF, rfl, rfl, heColor⟩

theorem twoColorComponent_fst_eq_snd {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    {e : G.E} (heF : e ∈ F) (heColor : color e = a ∨ color e = b) :
    (G.twoColorGraph F color a b).connectedComponentMk (G.fst e) =
      (G.twoColorGraph F color a b).connectedComponentMk (G.snd e) := by
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (G.twoColorGraph_adj_fst_snd F color a b heF heColor)

/-- Every two-colour edge incident with `v` lies in the component of `v`. -/
theorem twoColorComponent_fst_eq_of_inc {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    {v : G.V} {e : G.E} (heF : e ∈ F)
    (heColor : color e = a ∨ color e = b) (hev : G.Inc v e) :
    (G.twoColorGraph F color a b).connectedComponentMk (G.fst e) =
      (G.twoColorGraph F color a b).connectedComponentMk v := by
  rcases hev with hfst | hsnd
  · simpa [hfst]
  · exact (G.twoColorComponent_fst_eq_snd F color a b heF heColor).trans
      (by simpa [hsnd])

/-- The colour permutation used locally at one vertex by a component
selection. -/
noncomputable def kempeLocalPerm {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (flip : G.TwoColorComponent F color a b → Prop)
    [DecidablePred flip] (v : G.V) : Fin q ≃ Fin q :=
  if flip ((G.twoColorGraph F color a b).connectedComponentMk v) then
    Equiv.swap a b
  else Equiv.refl (Fin q)

/-- Exchange `a` and `b` on every `F`-edge in a selected connected
component.  Edges outside `F` are left unchanged. -/
noncomputable def kempeComponentSwitch {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (flip : G.TwoColorComponent F color a b → Prop)
    [DecidablePred flip] : G.E → Fin q :=
  fun e ↦
    if he : e ∈ F ∧ (color e = a ∨ color e = b) then
      if flip ((G.twoColorGraph F color a b).connectedComponentMk
          (G.fst e)) then
        Equiv.swap a b (color e)
      else color e
    else color e

/-- At all selected edges incident with one vertex, the component switch is
one common permutation of the old colours. -/
theorem kempeComponentSwitch_eq_localPerm {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (flip : G.TwoColorComponent F color a b → Prop)
    [DecidablePred flip] {v : G.V} {e : G.E}
    (heF : e ∈ F) (hev : G.Inc v e) :
    G.kempeComponentSwitch F color a b flip e =
      G.kempeLocalPerm F color a b flip v (color e) := by
  classical
  by_cases heColor : color e = a ∨ color e = b
  · have hcomponent :=
      G.twoColorComponent_fst_eq_of_inc F color a b heF heColor hev
    simp only [kempeComponentSwitch, kempeLocalPerm, heF, heColor,
      and_self, dite_true]
    rw [hcomponent]
    split <;> rfl
  · have hneA : color e ≠ a := fun h ↦ heColor (Or.inl h)
    have hneB : color e ≠ b := fun h ↦ heColor (Or.inr h)
    simp only [kempeComponentSwitch, kempeLocalPerm, heF, heColor,
      and_false, dite_false]
    split
    · exact (Equiv.swap_apply_of_ne_of_ne hneA hneB).symm
    · rfl

/-- A Kempe component switch preserves ordinary properness. -/
theorem isProperOn_kempeComponentSwitch {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q)
    (flip : G.TwoColorComponent F color a b → Prop)
    [DecidablePred flip] :
    G.IsProperOn F (G.kempeComponentSwitch F color a b flip) := by
  classical
  intro v e he f hf hsame
  let pi := G.kempeLocalPerm F color a b flip v
  have heData := Finset.mem_filter.mp (Finset.mem_coe.mp he)
  have hfData := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
  have heLocal : G.kempeComponentSwitch F color a b flip e =
      pi (color e) := by
    exact G.kempeComponentSwitch_eq_localPerm F color a b flip
      heData.1 heData.2
  have hfLocal : G.kempeComponentSwitch F color a b flip f =
      pi (color f) := by
    exact G.kempeComponentSwitch_eq_localPerm F color a b flip
      hfData.1 hfData.2
  apply hproper v he hf
  apply pi.injective
  rw [← heLocal, ← hfLocal]
  exact hsame

/-- Membership in the missing palette is transported by the same local
permutation. -/
theorem mem_missingColorsAt_kempeComponentSwitch_localPerm_iff {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (flip : G.TwoColorComponent F color a b → Prop)
    [DecidablePred flip] (v : G.V) (c : Fin q) :
    G.kempeLocalPerm F color a b flip v c ∈
        G.missingColorsAt F (G.kempeComponentSwitch F color a b flip) v ↔
      c ∈ G.missingColorsAt F color v := by
  classical
  let pi := G.kempeLocalPerm F color a b flip v
  have himage :
      pi c ∈ (F.filter (G.Inc v)).image
          (G.kempeComponentSwitch F color a b flip) ↔
        c ∈ (F.filter (G.Inc v)).image color := by
    constructor
    · intro h
      rcases Finset.mem_image.mp h with ⟨e, he, heq⟩
      have heData := Finset.mem_filter.mp he
      have hlocal : G.kempeComponentSwitch F color a b flip e =
          pi (color e) := by
        exact G.kempeComponentSwitch_eq_localPerm F color a b flip
          heData.1 heData.2
      apply Finset.mem_image.mpr
      refine ⟨e, he, ?_⟩
      apply pi.injective
      exact hlocal.symm.trans heq
    · intro h
      rcases Finset.mem_image.mp h with ⟨e, he, heq⟩
      have heData := Finset.mem_filter.mp he
      have hlocal : G.kempeComponentSwitch F color a b flip e =
          pi (color e) := by
        exact G.kempeComponentSwitch_eq_localPerm F color a b flip
          heData.1 heData.2
      apply Finset.mem_image.mpr
      refine ⟨e, he, ?_⟩
      rw [hlocal, heq]
  simp only [missingColorsAt, Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact not_congr himage

/-- When the component of `v` is selected, the two missing indicators at
`v` are exchanged. -/
theorem mem_missingColorsAt_kempeComponentSwitch_of_flip {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (flip : G.TwoColorComponent F color a b → Prop)
    [DecidablePred flip] (v : G.V)
    (hv : flip ((G.twoColorGraph F color a b).connectedComponentMk v)) :
    (b ∈ G.missingColorsAt F
          (G.kempeComponentSwitch F color a b flip) v ↔
        a ∈ G.missingColorsAt F color v) ∧
      (a ∈ G.missingColorsAt F
          (G.kempeComponentSwitch F color a b flip) v ↔
        b ∈ G.missingColorsAt F color v) := by
  have ha := G.mem_missingColorsAt_kempeComponentSwitch_localPerm_iff
    F color a b flip v a
  have hb := G.mem_missingColorsAt_kempeComponentSwitch_localPerm_iff
    F color a b flip v b
  simp [kempeLocalPerm, hv] at ha hb
  exact ⟨ha, hb⟩

/-- When the component of `v` is not selected, its missing palette is
unchanged pointwise. -/
theorem mem_missingColorsAt_kempeComponentSwitch_of_not_flip_iff {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (flip : G.TwoColorComponent F color a b → Prop)
    [DecidablePred flip] (v : G.V)
    (hv : ¬ flip ((G.twoColorGraph F color a b).connectedComponentMk v))
    (c : Fin q) :
    c ∈ G.missingColorsAt F
        (G.kempeComponentSwitch F color a b flip) v ↔
      c ∈ G.missingColorsAt F color v := by
  have h := G.mem_missingColorsAt_kempeComponentSwitch_localPerm_iff
    F color a b flip v c
  simpa [kempeLocalPerm, hv] using h

end WeightedMultigraph
end WeightedEdgeColoring
