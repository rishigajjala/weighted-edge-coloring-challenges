import WeightedEdgeColoring.SubtwoFiniteSampleSubsetLaw
import WeightedEdgeColoring.SubtwoLabelConditionalLaw
import WeightedEdgeColoring.FiniteClassesTinyProposalLocalPolytope

/-! Separate finite-class and tiny charges by original endpoint label. -/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open scoped BigOperators
noncomputable section

variable (G : WeightedMultigraph)

theorem finiteTiny_singleLabelDistribution
    {v : G.V} {Label K : Type*}
    [Fintype Label] [DecidableEq Label]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (edgeLabel : G.StarEdge v → Label)
    (isFiniteClass : G.StarEdge v → Prop) [DecidablePred isFiniteClass]
    (capacity : K → ℕ) (hcapacity : ∀ a, 0 < capacity a)
    (classOf : {e : G.StarEdge v // isFiniteClass e} → K)
    (x : G.StarEdge v → ℝ) (M tau : ℝ)
    (hM : 0 < M) (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (hfiniteWeight : ∀ e : {e : G.StarEdge v // isFiniteClass e},
      G.weight e.1.1 ≤ (1 : ℝ) / capacity (classOf e))
    (htinyWeight : ∀ e : {e : G.StarEdge v // ¬isFiniteClass e},
      G.weight e.1.1 ≤ tau)
    (hx0 : ∀ e, 0 ≤ x e) (hxM : ∀ e, x e ≤ M)
    (mass : Label → ℝ) (hmass : ∀ l, 0 < mass l)
    (hmassSum : ∑ l, mass l ≤ 1)
    (hbudget : ∀ l : Label,
      (∑ e : {e : G.StarEdge v // isFiniteClass e},
        (if edgeLabel e.1 = l then x e.1 / mass l else 0) /
          (capacity (classOf e) : ℝ)) +
        (Fintype.card K : ℝ) * (M / mass l) +
        (∑ e : {e : G.StarEdge v // ¬isFiniteClass e},
          G.weight e.1.1 *
            (if edgeLabel e.1 = l then x e.1 / mass l else 0)) /
          (1 - tau) + M / mass l ≤ 1) :
    ∃ q : Finset (G.StarEdge v) → ℝ,
      (∀ S, 0 ≤ q S) ∧ (∑ S, q S = 1) ∧
      (∀ S, q S ≠ 0 → G.StarFeasible v S) ∧
      (∀ e, (∑ S, if e ∈ S then q S else 0) = x e) ∧
      (∀ S, q S ≠ 0 → S ≠ ∅ →
        ∃ l, ∀ e ∈ S, edgeLabel e = l) ∧
      (∀ l, subsetLabelMass edgeLabel q l ≤ mass l) := by
  classical
  let y : Label → G.StarEdge v → ℝ := fun l e =>
    if edgeLabel e = l then x e / mass l else 0
  have hy0 : ∀ l e, 0 ≤ y l e := by
    intro l e
    by_cases he : edgeLabel e = l
    · simpa [y, he] using div_nonneg (hx0 e) (hmass l).le
    · simp [y, he]
  have hyM : ∀ l e, y l e ≤ M / mass l := by
    intro l e
    by_cases he : edgeLabel e = l
    · simpa [y, he] using
        div_le_div_of_nonneg_right (hxM e) (hmass l).le
    · simp [y, he, div_nonneg hM.le (hmass l).le]
  have havg : ∀ l, G.IsAverageOfStarFeasibleSets v (y l) := by
    intro l
    exact G.finiteClassesTinyProposal_isAverageOfStarFeasibleSets
      isFiniteClass capacity hcapacity classOf (y l) (M / mass l) tau
      (div_pos hM (hmass l)) htau0 htau1 hfiniteWeight htinyWeight
      (hy0 l) (hyM l) (hbudget l)
  have hq : ∀ l : Label, ∃ q : Finset (G.StarEdge v) → ℝ,
      (∀ S, 0 ≤ q S) ∧ (∑ S, q S = 1) ∧
      (∀ S, q S ≠ 0 → G.StarFeasible v S) ∧
      (∀ e, (∑ S, if e ∈ S then q S else 0) = y l e) ∧
      (∀ S, q S ≠ 0 → S ≠ ∅ →
        ∀ e ∈ S, edgeLabel e = l) := by
    intro l
    exact G.singleLabelSubsetLaw_of_average edgeLabel l (y l) (havg l)
      (by intro e he; simp [y, he])
  let qLabel : Label → Finset (G.StarEdge v) → ℝ :=
    fun l => Classical.choose (hq l)
  apply G.mix_singleLabelSubsetLaws edgeLabel x mass hmass hmassSum qLabel
  · intro l S; exact (Classical.choose_spec (hq l)).1 S
  · intro l; exact (Classical.choose_spec (hq l)).2.1
  · intro l S hS; exact (Classical.choose_spec (hq l)).2.2.1 S hS
  · intro l e
    simpa only [y] using (Classical.choose_spec (hq l)).2.2.2.1 e
  · intro l S hS hSne e he
    exact (Classical.choose_spec (hq l)).2.2.2.2 S hS hSne e he

/-- A single aggregate charge budget, with one diffuse atom for every
label/finite-class pair and every label's tiny class, suffices. -/
theorem finiteTiny_singleLabelDistribution_of_charge
    {v : G.V} {Label K : Type*}
    [Fintype Label] [DecidableEq Label]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (edgeLabel : G.StarEdge v → Label)
    (isFiniteClass : G.StarEdge v → Prop) [DecidablePred isFiniteClass]
    (capacity : K → ℕ) (hcapacity : ∀ a, 0 < capacity a)
    (classOf : {e : G.StarEdge v // isFiniteClass e} → K)
    (x : G.StarEdge v → ℝ) (M tau : ℝ)
    (hM : 0 < M) (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (hfiniteWeight : ∀ e : {e : G.StarEdge v // isFiniteClass e},
      G.weight e.1.1 ≤ (1 : ℝ) / capacity (classOf e))
    (htinyWeight : ∀ e : {e : G.StarEdge v // ¬isFiniteClass e},
      G.weight e.1.1 ≤ tau)
    (hx0 : ∀ e, 0 ≤ x e) (hxM : ∀ e, x e ≤ M)
    (hcharge :
      (∑ e : {e : G.StarEdge v // isFiniteClass e},
        x e.1 / (capacity (classOf e) : ℝ)) +
      (∑ e : {e : G.StarEdge v // ¬isFiniteClass e},
        G.weight e.1.1 * x e.1) / (1 - tau) +
      (Fintype.card Label : ℝ) * ((Fintype.card K : ℝ) + 1) * M ≤ 1) :
    ∃ q : Finset (G.StarEdge v) → ℝ,
      (∀ S, 0 ≤ q S) ∧ (∑ S, q S = 1) ∧
      (∀ S, q S ≠ 0 → G.StarFeasible v S) ∧
      (∀ e, (∑ S, if e ∈ S then q S else 0) = x e) ∧
      (∀ S, q S ≠ 0 → S ≠ ∅ →
        ∃ l, ∀ e ∈ S, edgeLabel e = l) ∧
      (∀ l, subsetLabelMass edgeLabel q l ≤
        (∑ e : {e : G.StarEdge v // isFiniteClass e},
          if edgeLabel e.1 = l then
            x e.1 / (capacity (classOf e) : ℝ) else 0) +
        (∑ e : {e : G.StarEdge v // ¬isFiniteClass e},
          if edgeLabel e.1 = l then G.weight e.1.1 * x e.1 else 0) /
            (1 - tau) + ((Fintype.card K : ℝ) + 1) * M) := by
  classical
  let finiteCharge : Label → ℝ := fun l =>
    ∑ e : {e : G.StarEdge v // isFiniteClass e},
      if edgeLabel e.1 = l then x e.1 / (capacity (classOf e) : ℝ) else 0
  let tinyCharge : Label → ℝ := fun l =>
    ∑ e : {e : G.StarEdge v // ¬isFiniteClass e},
      if edgeLabel e.1 = l then G.weight e.1.1 * x e.1 else 0
  let mass : Label → ℝ := fun l =>
    finiteCharge l + tinyCharge l / (1 - tau) +
      ((Fintype.card K : ℝ) + 1) * M
  have hf0 : ∀ l, 0 ≤ finiteCharge l := by
    intro l
    apply Finset.sum_nonneg
    intro e _
    split
    · exact div_nonneg (hx0 e.1) (Nat.cast_nonneg _)
    · exact le_rfl
  have ht0 : ∀ l, 0 ≤ tinyCharge l := by
    intro l
    apply Finset.sum_nonneg
    intro e _
    split
    · exact mul_nonneg (G.weight_nonneg e.1.1) (hx0 e.1)
    · exact le_rfl
  have hmpos : ∀ l, 0 < mass l := by
    intro l
    dsimp [mass]
    have hcard : (0 : ℝ) ≤ Fintype.card K := Nat.cast_nonneg _
    have hs : 0 < ((Fintype.card K : ℝ) + 1) * M :=
      mul_pos (by linarith) hM
    exact add_pos_of_nonneg_of_pos
      (add_nonneg (hf0 l) (div_nonneg (ht0 l) (sub_pos.mpr htau1).le)) hs
  have hfinSum : (∑ l, finiteCharge l) =
      ∑ e : {e : G.StarEdge v // isFiniteClass e},
        x e.1 / (capacity (classOf e) : ℝ) := by
    rw [Finset.sum_comm]
    simp [finiteCharge]
  have htinySum : (∑ l, tinyCharge l) =
      ∑ e : {e : G.StarEdge v // ¬isFiniteClass e},
        G.weight e.1.1 * x e.1 := by
    rw [Finset.sum_comm]
    simp [tinyCharge]
  have hmSum : ∑ l, mass l ≤ 1 := by
    have heq : (∑ l, mass l) =
        (∑ l, finiteCharge l) + (∑ l, tinyCharge l) / (1 - tau) +
          (Fintype.card Label : ℝ) * ((Fintype.card K : ℝ) + 1) * M := by
      simp [mass, Finset.sum_add_distrib, Finset.sum_div]
      ring
    rw [heq, hfinSum, htinySum]
    exact hcharge
  simpa only [finiteCharge, tinyCharge, mass] using
    (G.finiteTiny_singleLabelDistribution edgeLabel isFiniteClass
    capacity hcapacity classOf x M tau hM htau0 htau1
    hfiniteWeight htinyWeight hx0 hxM mass hmpos hmSum (by
  intro l
  have hmass : mass l ≠ 0 := ne_of_gt (hmpos l)
  have hnormFinite :
      (∑ e : {e : G.StarEdge v // isFiniteClass e},
        (if edgeLabel e.1 = l then x e.1 / mass l else 0) /
          (capacity (classOf e) : ℝ)) = finiteCharge l / mass l := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : edgeLabel e.1 = l <;> simp [finiteCharge, he] <;> ring
  have hnormTiny :
      (∑ e : {e : G.StarEdge v // ¬isFiniteClass e},
        G.weight e.1.1 *
          (if edgeLabel e.1 = l then x e.1 / mass l else 0)) /
          (1 - tau) = tinyCharge l / ((1 - tau) * mass l) := by
    have hτ : 1 - tau ≠ 0 := ne_of_gt (sub_pos.mpr htau1)
    calc
      _ = (tinyCharge l / mass l) / (1 - tau) := by
        apply congrArg (fun z : ℝ => z / (1 - tau))
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : edgeLabel e.1 = l <;> simp [he] <;> ring
      _ = _ := by field_simp [hmass, hτ]
  rw [hnormFinite, hnormTiny]
  have hτ : 1 - tau ≠ 0 := ne_of_gt (sub_pos.mpr htau1)
  have heq : finiteCharge l / mass l +
      (Fintype.card K : ℝ) * (M / mass l) +
      tinyCharge l / ((1 - tau) * mass l) + M / mass l = 1 := by
    calc
    finiteCharge l / mass l + (Fintype.card K : ℝ) * (M / mass l) +
        tinyCharge l / ((1 - tau) * mass l) + M / mass l =
      (finiteCharge l + tinyCharge l / (1 - tau) +
        ((Fintype.card K : ℝ) + 1) * M) / mass l := by
        field_simp [hmass, hτ]
        ring
    _ = mass l / mass l := by rfl
    _ = 1 := div_self hmass
  exact heq.le))

end
end WeightedMultigraph
end WeightedEdgeColoring
