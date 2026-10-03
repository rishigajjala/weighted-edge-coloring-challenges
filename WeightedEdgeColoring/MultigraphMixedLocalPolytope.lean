import WeightedEdgeColoring.CardinalityLocalPolytope
import WeightedEdgeColoring.MultigraphPartitionLocalPolytope
import WeightedEdgeColoring.WeightedSlackLocalPolytope

/-!
# A finite-class plus tiny local star polytope

The finite harmonic classes and the tiny remainder use disjoint portions of
one unit of selection probability.  Conditional on a harmonic class we pick
at most its capacity; conditional on the tiny part we use weighted dependent
rounding with one tiny-edge weight of slack.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u v

variable (G : WeightedMultigraph.{u})

/-- A directly usable local distribution for the union of finitely many
reciprocal size classes and one arbitrary tiny class. -/
theorem finiteClassesAndTiny_isAverageOfStarFeasibleSets
    {vertex : G.V} (isFiniteClass : G.StarEdge vertex → Prop)
    [DecidablePred isFiniteClass]
    {K : Type v} [Fintype K] [DecidableEq K]
    (capacity : K → ℕ) (hcapacity : ∀ a, 0 < capacity a)
    (classOf : {e : G.StarEdge vertex // isFiniteClass e} → K)
    (x : G.StarEdge vertex → ℝ) (classMass : K → ℝ)
    (tinyMass tau : ℝ)
    (hclassMass0 : ∀ a, 0 ≤ classMass a)
    (hclassMassPos : 0 < ∑ a, classMass a)
    (htinyMass : 0 < tinyMass)
    (htotal : (∑ a, classMass a) + tinyMass ≤ 1)
    (hfiniteWeight : ∀ e : {e : G.StarEdge vertex // isFiniteClass e},
      G.weight e.1.1 ≤ (1 : ℝ) / capacity (classOf e))
    (htinyWeight : ∀ e : {e : G.StarEdge vertex // ¬isFiniteClass e},
      G.weight e.1.1 ≤ tau)
    (htau : 0 ≤ tau)
    (hx0 : ∀ e, 0 ≤ x e)
    (hfinitePoint : ∀ e : {e : G.StarEdge vertex // isFiniteClass e},
      x e.1 ≤ classMass (classOf e))
    (hfiniteClass : ∀ a,
      (∑ e : {e : G.StarEdge vertex // isFiniteClass e},
        if classOf e = a then x e.1 else 0) ≤
          (capacity a : ℝ) * classMass a)
    (htinyPoint : ∀ e : {e : G.StarEdge vertex // ¬isFiniteClass e},
      x e.1 ≤ tinyMass)
    (htinyLoad :
      (∑ e : {e : G.StarEdge vertex // ¬isFiniteClass e},
        G.weight e.1.1 * x e.1) ≤ tinyMass * (1 - tau)) :
    G.IsAverageOfStarFeasibleSets vertex x := by
  let totalClassMass : ℝ := ∑ a, classMass a
  let normalizedClassMass : K → ℝ := fun a => classMass a / totalClassMass
  have htotalClassMass : 0 < totalClassMass := by
    simpa [totalClassMass] using hclassMassPos
  have hnormalized0 : ∀ a, 0 ≤ normalizedClassMass a := by
    intro a
    exact div_nonneg (hclassMass0 a) htotalClassMass.le
  have hnormalizedSum : ∑ a, normalizedClassMass a ≤ 1 := by
    dsimp [normalizedClassMass]
    rw [← Finset.sum_div]
    simp [totalClassMass, htotalClassMass.ne']
  have hleft : IsAverageOfFeasibleSubsets
      (fun e : {e : G.StarEdge vertex // isFiniteClass e} => G.weight e.1.1)
      1 (fun e => x e.1 / totalClassMass) := by
    apply sizeClasses_isAverageOfFeasibleSubsets capacity hcapacity classOf
      (fun e : {e : G.StarEdge vertex // isFiniteClass e} => G.weight e.1.1)
      (fun e => x e.1 / totalClassMass) normalizedClassMass
    · exact hnormalized0
    · exact hnormalizedSum
    · intro e
      exact (G.weight_pos e.1.1).le
    · exact hfiniteWeight
    · intro e
      exact div_nonneg (hx0 e.1) htotalClassMass.le
    · intro e
      dsimp [normalizedClassMass]
      exact div_le_div_of_nonneg_right (hfinitePoint e) htotalClassMass.le
    · intro a
      have heq :
          (∑ e : {e : G.StarEdge vertex // isFiniteClass e},
            if classOf e = a then x e.1 / totalClassMass else 0) =
          (∑ e : {e : G.StarEdge vertex // isFiniteClass e},
            if classOf e = a then x e.1 else 0) / totalClassMass := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro e _he
        by_cases h : classOf e = a <;> simp [h]
      rw [heq]
      dsimp [normalizedClassMass]
      rw [← mul_div_assoc]
      exact (div_le_div_iff_of_pos_right htotalClassMass).2 (hfiniteClass a)
  have hright : IsAverageOfFeasibleSubsets
      (fun e : {e : G.StarEdge vertex // ¬isFiniteClass e} => G.weight e.1.1)
      1 (fun e => x e.1 / tinyMass) := by
    apply weightedSlack_isAverageOfFeasibleSubsets
      (fun e : {e : G.StarEdge vertex // ¬isFiniteClass e} => G.weight e.1.1)
      (fun e => x e.1 / tinyMass) 1 tau
    · intro e
      exact G.weight_pos e.1.1
    · exact htinyWeight
    · exact htau
    · intro e
      exact div_nonneg (hx0 e.1) htinyMass.le
    · intro e
      exact (div_le_one htinyMass).2 (htinyPoint e)
    · have heq :
          (∑ e : {e : G.StarEdge vertex // ¬isFiniteClass e},
            G.weight e.1.1 * (x e.1 / tinyMass)) =
          (∑ e : {e : G.StarEdge vertex // ¬isFiniteClass e},
            G.weight e.1.1 * x e.1) / tinyMass := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro e _he
        ring
      rw [heq]
      exact (div_le_iff₀ htinyMass).2 (by simpa [mul_comm] using htinyLoad)
  apply G.isAverageOfStarFeasibleSets_of_partition isFiniteClass x
    totalClassMass tinyMass htotalClassMass htinyMass
  · simpa [totalClassMass] using htotal
  · exact hleft
  · exact hright

end

end WeightedMultigraph
end WeightedEdgeColoring
