import WeightedEdgeColoring.MultigraphMixedLocalPolytope

/-!
# A proposal budget for finite harmonic classes plus tiny edges

This packages the exact local-polytope hypothesis consumed by coordinated
whole-edge rounding.  Finite-class edges pay their reciprocal-class charge
and one diffuse atom per class.  Tiny edges pay their physical fractional
load divided by `1 - tau` and one further diffuse atom.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u v

variable (G : WeightedMultigraph.{u})

theorem finiteClassesTinyProposal_isAverageOfStarFeasibleSets
    {vertex : G.V} (isFiniteClass : G.StarEdge vertex → Prop)
    [DecidablePred isFiniteClass]
    {K : Type v} [Fintype K] [DecidableEq K] [Nonempty K]
    (capacity : K → ℕ) (hcapacity : ∀ a, 0 < capacity a)
    (classOf : {e : G.StarEdge vertex // isFiniteClass e} → K)
    (x : G.StarEdge vertex → ℝ) (M tau : ℝ)
    (hM : 0 < M) (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (hfiniteWeight : ∀ e : {e : G.StarEdge vertex // isFiniteClass e},
      G.weight e.1.1 ≤ (1 : ℝ) / capacity (classOf e))
    (htinyWeight : ∀ e : {e : G.StarEdge vertex // ¬isFiniteClass e},
      G.weight e.1.1 ≤ tau)
    (hx0 : ∀ e, 0 ≤ x e) (hxM : ∀ e, x e ≤ M)
    (hbudget :
      (∑ e : {e : G.StarEdge vertex // isFiniteClass e},
          x e.1 / (capacity (classOf e) : ℝ)) +
        (Fintype.card K : ℝ) * M +
        (∑ e : {e : G.StarEdge vertex // ¬isFiniteClass e},
          G.weight e.1.1 * x e.1) / (1 - tau) + M ≤ 1) :
    G.IsAverageOfStarFeasibleSets vertex x := by
  let finiteLoad : K → ℝ := fun a ↦
    ∑ e : {e : G.StarEdge vertex // isFiniteClass e},
      if classOf e = a then x e.1 else 0
  let classMass : K → ℝ := fun a ↦
    finiteLoad a / (capacity a : ℝ) + M
  let tinyLoad : ℝ :=
    ∑ e : {e : G.StarEdge vertex // ¬isFiniteClass e},
      G.weight e.1.1 * x e.1
  let tinyMass : ℝ := tinyLoad / (1 - tau) + M
  have honeTau : 0 < 1 - tau := sub_pos.mpr htau1
  have hfiniteLoad0 : ∀ a, 0 ≤ finiteLoad a := by
    intro a
    apply Finset.sum_nonneg
    intro e _he
    split
    · exact hx0 e.1
    · exact le_rfl
  have hclassMass0 : ∀ a, 0 ≤ classMass a := by
    intro a
    exact add_nonneg
      (div_nonneg (hfiniteLoad0 a) (Nat.cast_nonneg _)) hM.le
  have hclassMassPos : 0 < ∑ a, classMass a := by
    let a : K := Classical.choice inferInstance
    have ha : 0 < classMass a := by
      dsimp [classMass]
      exact add_pos_of_nonneg_of_pos
        (div_nonneg (hfiniteLoad0 a) (Nat.cast_nonneg _)) hM
    exact lt_of_lt_of_le ha
      (Finset.single_le_sum (fun b _hb ↦ hclassMass0 b)
        (Finset.mem_univ a))
  have htinyLoad0 : 0 ≤ tinyLoad := by
    dsimp [tinyLoad]
    apply Finset.sum_nonneg
    intro e _he
    exact mul_nonneg (G.weight_nonneg e.1.1) (hx0 e.1)
  have htinyMass : 0 < tinyMass := by
    dsimp [tinyMass]
    exact add_pos_of_nonneg_of_pos
      (div_nonneg htinyLoad0 honeTau.le) hM
  have hsumFinite :
      (∑ a, finiteLoad a / (capacity a : ℝ)) =
        ∑ e : {e : G.StarEdge vertex // isFiniteClass e},
          x e.1 / (capacity (classOf e) : ℝ) := by
    calc
      _ = ∑ a, ∑ e : {e : G.StarEdge vertex // isFiniteClass e},
          if classOf e = a then x e.1 / (capacity a : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro e _he
        by_cases h : classOf e = a <;> simp [finiteLoad, h]
      _ = ∑ e : {e : G.StarEdge vertex // isFiniteClass e}, ∑ a,
          if classOf e = a then x e.1 / (capacity a : ℝ) else 0 := by
        rw [Finset.sum_comm]
      _ = _ := by simp
  have hsumClassMass :
      (∑ a, classMass a) =
        (∑ e : {e : G.StarEdge vertex // isFiniteClass e},
          x e.1 / (capacity (classOf e) : ℝ)) +
            (Fintype.card K : ℝ) * M := by
    calc
      _ = (∑ a, finiteLoad a / (capacity a : ℝ)) +
          (Fintype.card K : ℝ) * M := by
        simp [classMass, Finset.sum_add_distrib]
      _ = _ := by rw [hsumFinite]
  apply G.finiteClassesAndTiny_isAverageOfStarFeasibleSets
    isFiniteClass capacity hcapacity classOf x classMass tinyMass tau
  · exact hclassMass0
  · exact hclassMassPos
  · exact htinyMass
  · rw [hsumClassMass]
    dsimp [tinyMass, tinyLoad]
    linarith [hbudget]
  · exact hfiniteWeight
  · exact htinyWeight
  · exact htau0
  · exact hx0
  · intro e
    calc
      x e.1 ≤ M := hxM e.1
      _ ≤ finiteLoad (classOf e) / (capacity (classOf e) : ℝ) + M :=
        le_add_of_nonneg_left
          (div_nonneg (hfiniteLoad0 (classOf e)) (Nat.cast_nonneg _))
  · intro a
    dsimp [classMass, finiteLoad]
    have hcap : (0 : ℝ) < capacity a := by
      exact_mod_cast hcapacity a
    calc
      _ = (capacity a : ℝ) *
          ((∑ e : {e : G.StarEdge vertex // isFiniteClass e},
            if classOf e = a then x e.1 else 0) /
              (capacity a : ℝ)) := by field_simp
      _ ≤ (capacity a : ℝ) *
          ((∑ e : {e : G.StarEdge vertex // isFiniteClass e},
            if classOf e = a then x e.1 else 0) /
              (capacity a : ℝ) + M) := by
        nlinarith [hM, hcap]
  · intro e
    dsimp [tinyMass]
    exact (hxM e.1).trans (le_add_of_nonneg_left
      (div_nonneg htinyLoad0 honeTau.le))
  · dsimp [tinyMass, tinyLoad]
    calc
      tinyLoad = (tinyLoad / (1 - tau)) * (1 - tau) := by
        rw [div_mul_cancel₀ _ honeTau.ne']
      _ ≤ (tinyLoad / (1 - tau) + M) * (1 - tau) := by
        nlinarith [hM, honeTau]

end

end WeightedMultigraph
end WeightedEdgeColoring
