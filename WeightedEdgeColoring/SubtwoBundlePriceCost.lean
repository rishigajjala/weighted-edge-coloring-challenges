import WeightedEdgeColoring.SubtwoGraphPatternCopies
import WeightedEdgeColoring.SubtwoBundleCharge

/-!
# Physical edge prices are paid by minimum bundle costs

Edges of equal weight need not have equal prices. For each weight we choose
an edge of largest price. A type pattern can then be realized by repeating
these representatives. This gives the price-cost inequality without any
assumption that the original price vector is constant on weight classes.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G : WeightedMultigraph.{u})

theorem subtwo_exists_weight_price_representative (F : Finset G.E)
    (price : G.E → ℝ) (x : G.EdgeSetWeightType F) :
    ∃ e ∈ F, G.weight e = x.val ∧
      ∀ f ∈ F, G.weight f = x.val → price f ≤ price e := by
  classical
  have hn : (F.filter fun e => G.weight e = x.val).Nonempty := by
    rcases Finset.mem_image.mp x.property with ⟨e, he, hx⟩
    exact ⟨e, Finset.mem_filter.mpr ⟨he, hx⟩⟩
  rcases Finset.exists_max_image (F.filter fun e => G.weight e = x.val) price hn with
    ⟨e, he, hmax⟩
  exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2,
    fun f hf hx => hmax f (Finset.mem_filter.mpr ⟨hf, hx⟩)⟩

def subtwoWeightPriceRepresentative (F : Finset G.E) (price : G.E → ℝ)
    (x : G.EdgeSetWeightType F) : G.E :=
  Classical.choose (G.subtwo_exists_weight_price_representative F price x)

theorem subtwoWeightPriceRepresentative_spec (F : Finset G.E) (price : G.E → ℝ)
    (x : G.EdgeSetWeightType F) :
    G.subtwoWeightPriceRepresentative F price x ∈ F ∧
    G.weight (G.subtwoWeightPriceRepresentative F price x) = x.val ∧
    ∀ e ∈ F, G.weight e = x.val →
      price e ≤ price (G.subtwoWeightPriceRepresentative F price x) :=
  Classical.choose_spec (G.subtwo_exists_weight_price_representative F price x)

def subtwoTypePatternMultiplicity (F : Finset G.E)
    (rep : G.EdgeSetWeightType F → G.E)
    (p : (G.edgeSetWeightBinPackingInstance F).Pattern) (e : G.E) : ℕ :=
  ∑ x : G.EdgeSetWeightType F, if rep x = e then p.multiplicity x else 0

theorem sum_subtwoTypePatternMultiplicity (F : Finset G.E)
    (rep : G.EdgeSetWeightType F → G.E)
    (p : (G.edgeSetWeightBinPackingInstance F).Pattern) (f : G.E → ℝ) :
    (∑ e : G.E, f e * (G.subtwoTypePatternMultiplicity F rep p e : ℝ)) =
      ∑ x : G.EdgeSetWeightType F, f (rep x) * (p.multiplicity x : ℝ) := by
  classical
  simp only [subtwoTypePatternMultiplicity, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp [mul_ite]

def subtwoLiftWeightPattern (F : Finset G.E)
    (rep : G.EdgeSetWeightType F → G.E)
    (hw : ∀ x, G.weight (rep x) = x.val)
    (p : (G.edgeSetWeightBinPackingInstance F).Pattern) : G.SubtwoWeightedPattern :=
  SubtwoWeightedPattern.ofTotalLoad G (G.subtwoTypePatternMultiplicity F rep p) (by
    have heq := G.sum_subtwoTypePatternMultiplicity F rep p G.weight
    simp_rw [hw] at heq
    have hc : (∑ x : G.EdgeSetWeightType F, x.val * (p.multiplicity x : ℝ)) ≤ 1 := by
      simpa only [edgeSetWeightBinPackingInstance_weight, mul_comm] using p.capacity
    simpa only [mul_comm] using heq.trans_le hc)

theorem subtwoLiftWeightPattern_support (F : Finset G.E) (S : Finset G.V)
    (hF : ∀ e ∈ F, G.fst e ∈ S ∧ G.snd e ∈ S)
    (rep : G.EdgeSetWeightType F → G.E) (hr : ∀ x, rep x ∈ F)
    (hw : ∀ x, G.weight (rep x) = x.val)
    (p : (G.edgeSetWeightBinPackingInstance F).Pattern) :
    (G.subtwoLiftWeightPattern F rep hw p).restrictTo G S =
      G.subtwoLiftWeightPattern F rep hw p := by
  classical
  apply SubtwoWeightedPattern.restrictTo_fixed
  intro e he
  by_contra hs
  apply he
  change G.subtwoTypePatternMultiplicity F rep p e = 0
  apply Finset.sum_eq_zero
  intro x hx
  have hne : rep x ≠ e := by
    intro h
    exact hs (h ▸ hF (rep x) (hr x))
  simp [hne]

theorem subtwo_type_pattern_price_le (F : Finset G.E) (S : Finset G.V)
    (hF : ∀ e ∈ F, G.fst e ∈ S ∧ G.snd e ∈ S)
    (price : G.E → ℝ)
    (p : (G.edgeSetWeightBinPackingInstance F).Pattern) :
    (∑ x : G.EdgeSetWeightType F,
      price (G.subtwoWeightPriceRepresentative F price x) * (p.multiplicity x : ℝ)) ≤
      G.subtwoSupportedPriceMax S price := by
  let rep := G.subtwoWeightPriceRepresentative F price
  have hw : ∀ x, G.weight (rep x) = x.val :=
    fun x => (G.subtwoWeightPriceRepresentative_spec F price x).2.1
  let q := G.subtwoLiftWeightPattern F rep hw p
  have h := Subtwo.patternPrice_le_paletteMaxScore (G.subtwoSupportedColorPattern S) price () q
  change (∑ e, price e * ((q.restrictTo G S).val e : ℝ)) ≤ _ at h
  rw [G.subtwoLiftWeightPattern_support F S hF rep
    (fun x => (G.subtwoWeightPriceRepresentative_spec F price x).1) hw p] at h
  exact (G.sum_subtwoTypePatternMultiplicity F rep p price).symm.trans_le h

theorem subtwo_sum_price_le_type_representatives (F : Finset G.E) (price : G.E → ℝ) :
    (∑ e ∈ F, price e) ≤
      ∑ x : G.EdgeSetWeightType F,
        (G.edgeSetWeightDemand F x : ℝ) * price (G.subtwoWeightPriceRepresentative F price x) := by
  classical
  calc
    _ = ∑ x : G.EdgeSetWeightType F, ∑ e ∈ F,
        if G.weight e = x.val then price e else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      let x : G.EdgeSetWeightType F := ⟨G.weight e, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
      rw [Finset.sum_eq_single x]
      · simp [x]
      · intro y hy hne
        have h : G.weight e ≠ y.val := fun h => hne (Subtype.ext h.symm)
        simp [h]
      · simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      rw [← Finset.sum_filter]
      calc
        _ ≤ ∑ e ∈ F.filter (fun e => G.weight e = x.val),
            price (G.subtwoWeightPriceRepresentative F price x) := by
          apply Finset.sum_le_sum
          intro e he
          exact (G.subtwoWeightPriceRepresentative_spec F price x).2.2 e
            (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
        _ = _ := by simp [edgeSetWeightDemand]

/-- The actual physical price sum is bounded by any exact type cover's
cost times the maximum price of a feasible color supported on the block. -/
theorem subtwo_edgeSet_price_le_cover_cost_mul
    (F : Finset G.E) (S : Finset G.V)
    (hF : ∀ e ∈ F, G.fst e ∈ S ∧ G.snd e ∈ S)
    (price : G.E → ℝ) (C : G.EdgeSetExactDemandCover F) :
    (∑ e ∈ F, price e) ≤ C.cost * G.subtwoSupportedPriceMax S price := by
  classical
  let r := fun x => price (G.subtwoWeightPriceRepresentative F price x)
  calc
    _ ≤ ∑ x : G.EdgeSetWeightType F, (G.edgeSetWeightDemand F x : ℝ) * r x :=
      G.subtwo_sum_price_le_type_representatives F price
    _ = ∑ x : G.EdgeSetWeightType F,
        (∑ p : (G.edgeSetWeightBinPackingInstance F).Pattern,
          C.coeff p * (p.multiplicity x : ℝ)) * r x := by
      simp_rw [C.sum_coeff_mul_multiplicity_eq]
    _ = ∑ p : (G.edgeSetWeightBinPackingInstance F).Pattern,
        C.coeff p * (∑ x : G.EdgeSetWeightType F, r x * (p.multiplicity x : ℝ)) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ ∑ p : (G.edgeSetWeightBinPackingInstance F).Pattern,
        C.coeff p * G.subtwoSupportedPriceMax S price := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (G.subtwo_type_pattern_price_le F S hF price p)
        (C.coeff_nonneg p)
    _ = _ := by rw [← Finset.sum_mul, C.sum_coeff_eq_cost]

theorem subtwo_floorBundle_price_le_cost_mul
    (a b : G.V) (hab : a ≠ b) (price : G.E → ℝ) :
    (∑ e ∈ G.floorBundle (G.floorPairKey a b), price e) ≤
      (G.floorBundleCover (G.floorPairKey a b)).cost * G.subtwoSupportedPriceMax {a, b} price := by
  apply G.subtwo_edgeSet_price_le_cover_cost_mul
  intro e he
  rw [G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween a b hab] at he
  rcases (Finset.mem_filter.mp he).2 with h | h
  · simp [h.1, h.2]
  · simp [h.1, h.2]

end
end WeightedEdgeColoring.WeightedMultigraph
