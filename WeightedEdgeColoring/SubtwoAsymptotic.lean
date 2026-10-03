import WeightedEdgeColoring.ShannonBridge

/-!
# A strict sub-two target for unrestricted weighted multigraphs

The propositions below use the concrete `bp` and `chiW` optima from
`WeightedMultigraph`.  They quantify uniformly over graph order, edge
multiplicity, and positive edge weights.  This file proves equivalences and
epsilon bookkeeping; it does not assert the strict sub-two graph theorem.
-/

namespace WeightedEdgeColoring

universe u

/-- The uniform epsilon--threshold meaning of
`χ'_w(G) ≤ c bp(G) + o(bp(G))` for finite loopless weighted multigraphs. -/
def GeneralBPAsymptoticAt (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ G : WeightedMultigraph.{u},
    N ≤ G.bp → (G.chiW : ℝ) ≤ (c + ε) * (G.bp : ℝ)

/-- The graph-independent additive version.  Its constant can depend on
`ε`, but not on the graph, edge multiplicities, or weights. -/
def GeneralBPAdditiveAt (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ G : WeightedMultigraph.{u},
    (G.chiW : ℝ) ≤ (c + ε) * (G.bp : ℝ) + C

/-- The unrestricted coefficient-`1.999` proposition. Its proof is
`subtwoBPAsymptotic_unrestricted` in `SubtwoUnrestrictedProof.lean`. -/
def SubtwoBPAsymptotic : Prop :=
  GeneralBPAsymptoticAt.{u} (1999 / 1000 : ℝ)

/-- Additive formulation of the coefficient-`1.999` proposition, proved by
`subtwoBPAdditive_unrestricted` in `SubtwoUnrestrictedProof.lean`. -/
def SubtwoBPAdditive : Prop :=
  GeneralBPAdditiveAt.{u} (1999 / 1000 : ℝ)

/-- A graph-independent additive error is absorbed after a uniform threshold. -/
theorem generalBPAsymptoticAt_of_additive (c : ℝ)
    (h : GeneralBPAdditiveAt.{u} c) : GeneralBPAsymptoticAt.{u} c := by
  intro ε hε
  obtain ⟨C, hC⟩ := h (ε / 2) (half_pos hε)
  let N : ℕ := Nat.ceil (2 * max C 0 / ε)
  refine ⟨N, ?_⟩
  intro G hN
  have hratio : 2 * max C 0 / ε ≤ (G.bp : ℝ) := by
    calc
      2 * max C 0 / ε ≤ (N : ℝ) := Nat.le_ceil _
      _ ≤ (G.bp : ℝ) := by exact_mod_cast hN
  have hsmall : C ≤ (ε / 2) * (G.bp : ℝ) := by
    have hm : 2 * max C 0 ≤ (G.bp : ℝ) * ε :=
      (div_le_iff₀ hε).mp hratio
    have hc : C ≤ max C 0 := le_max_left _ _
    nlinarith
  calc
    (G.chiW : ℝ) ≤ (c + ε / 2) * (G.bp : ℝ) + C := hC G
    _ ≤ (c + ε) * (G.bp : ℝ) := by nlinarith

/-- Shannon's proved bound controls the finitely many small `bp` values,
uniformly even when the number of edges or their multiplicities is unbounded. -/
theorem generalBPAdditiveAt_of_asymptotic (c : ℝ)
    (h : GeneralBPAsymptoticAt.{u} c) : GeneralBPAdditiveAt.{u} c := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨(3 : ℝ) * N + 3 + max (-c - ε) 0 * N, ?_⟩
  intro G
  by_cases hlarge : N ≤ G.bp
  · have hb := hN G hlarge
    have hm : 0 ≤ max (-c - ε) 0 := le_max_right _ _
    have hC : 0 ≤ (3 : ℝ) * N + 3 + max (-c - ε) 0 * N := by positivity
    linarith
  · have hbp : (G.bp : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (le_of_lt (lt_of_not_ge hlarge))
    have hchi : (G.chiW : ℝ) ≤ 3 * (G.bp : ℝ) + 3 := by
      have hs := G.chiW_lt_three_deltaW_add_three
      have hd := G.deltaW_le_bp
      linarith
    have hmax : -(c + ε) ≤ max (-c - ε) 0 := by
      calc
        -(c + ε) = -c - ε := by ring
        _ ≤ max (-c - ε) 0 := le_max_left _ _
    have hprod : -(c + ε) * (G.bp : ℝ) ≤
        max (-c - ε) 0 * (N : ℝ) := by
      calc
        -(c + ε) * (G.bp : ℝ) ≤
            max (-c - ε) 0 * (G.bp : ℝ) :=
          mul_le_mul_of_nonneg_right hmax (Nat.cast_nonneg _)
        _ ≤ max (-c - ε) 0 * (N : ℝ) :=
          mul_le_mul_of_nonneg_left hbp (le_max_right _ _)
    nlinarith

/-- Exact equivalence of the two uniform formulations. -/
theorem generalBPAsymptoticAt_iff_additive (c : ℝ) :
    GeneralBPAsymptoticAt.{u} c ↔ GeneralBPAdditiveAt.{u} c :=
  ⟨generalBPAdditiveAt_of_asymptotic c,
    generalBPAsymptoticAt_of_additive c⟩

theorem subtwoBPAsymptotic_iff_additive :
    SubtwoBPAsymptotic.{u} ↔ SubtwoBPAdditive.{u} :=
  generalBPAsymptoticAt_iff_additive (1999 / 1000 : ℝ)

/-- A fixed additive bound at `1.999` would suffice for the target. -/
theorem subtwoBPAsymptotic_of_fixed_additive
    (h : ∃ C : ℝ, ∀ G : WeightedMultigraph.{u},
      (G.chiW : ℝ) ≤ (1999 / 1000 : ℝ) * (G.bp : ℝ) + C) :
    SubtwoBPAsymptotic.{u} := by
  apply generalBPAsymptoticAt_of_additive
  intro ε hε
  obtain ⟨C, hC⟩ := h
  refine ⟨C, ?_⟩
  intro G
  have hbp : (0 : ℝ) ≤ G.bp := Nat.cast_nonneg _
  have hδ : (1999 / 1000 : ℝ) * (G.bp : ℝ) ≤
      ((1999 / 1000 : ℝ) + ε) * (G.bp : ℝ) := by nlinarith
  exact (hC G).trans (by linarith)

/-- A uniform palette construction with a sub-two slope and additive loss
reduces the target to a concrete coloring theorem. -/
theorem subtwoBPAsymptotic_of_colorings
    (h : ∃ C : ℝ, ∀ G : WeightedMultigraph.{u},
      ∃ q : ℕ, G.HasWeightedColoring q ∧
        (q : ℝ) ≤ (1999 / 1000 : ℝ) * (G.bp : ℝ) + C) :
    SubtwoBPAsymptotic.{u} := by
  apply subtwoBPAsymptotic_of_fixed_additive
  obtain ⟨C, hC⟩ := h
  refine ⟨C, ?_⟩
  intro G
  obtain ⟨q, hcolor, hq⟩ := hC G
  have hchi : (G.chiW : ℝ) ≤ q := by
    exact_mod_cast G.chiW_le_of_hasWeightedColoring hcolor
  exact hchi.trans hq

end WeightedEdgeColoring
