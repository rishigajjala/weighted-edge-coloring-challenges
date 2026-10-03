import WeightedEdgeColoring.SubtwoLinearGroupedRestoration
import WeightedEdgeColoring.SubtwoInjectiveColorLifting

/-!
# Restoring original edges with graph-independent local errors

Linear grouping loses at most 2|E|/M plus |V|²M original edges. Filling the
rounded palette adds only the fixed pattern-menu error. The coloring is
on the original edge indices and avoids each occupied boundary label.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 160000
open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
namespace SubtwoLinearGrouping
variable (G : WeightedMultigraph.{u})

/-- Restore the original retained block edges in the actual boundary palette. -/
theorem exists_physical_reserved_restoration
    (M S : ℕ) (hM : 0 < M) (hS : 0 < S)
    (hlower : ∀ e, (1 : ℝ)/S ≤ G.weight e)
    (n D K : ℕ) (hn : 0 < n) (hK : 0 < K)
    (κ : ℝ) (q : G.V → ℝ) (hq : ∀ v, 0 ≤ q v) (hsum : (∑ v,q v) ≤ κ)
    (hd : (fun _e : G.E => (1 : ℝ)/n) ∈
      Subtwo.PaletteAttainable (Subtwo.reservedPaletteBudget κ q) G.subtwoReservedColorPattern)
    (boundaryLabel : Fin K → Option G.V)
    (hlabel : ∀ v,
      (Fintype.card {c : Fin K // boundaryLabel c = some v} : ℝ) ≤ n*q v+D)
    (hpalette : (n : ℝ)*κ+(Fintype.card G.V : ℝ)*(D+1) ≤ K) :
    ∃ R : Finset G.E, ∃ color : G.E → Fin K,
      G.IsFeasibleOn R color ∧
      (∀ e ∈ R, ∀ v, G.Inc v e → boundaryLabel (color e) ≠ some v) ∧
      ∀ v, (∑ e ∈ Finset.univ \ R, if G.Inc v e then G.weight e else 0) ≤
        2*(Fintype.card G.E : ℝ)/M + ((Fintype.card G.V)^2 : ℕ)*M +
        ((Fintype.card G.V)^2*M : ℕ)*((Fintype.card G.V : ℝ)+1)*
          ((S+1)^((Fintype.card G.V)^2*M) : ℕ)*S := by
  classical
  obtain ⟨R,color,hfeasible,havoid,herror⟩ := exists_grouped_reserved_restoration G
    M S hM hS hlower n D K hn hK κ q hq hsum hd boundaryLabel hlabel hpalette
  have htinj := BinPackingInstance.KeyedLinearRoundedCover.targetItem_injective (key G) M
  obtain ⟨lifted,hlift,hsame,hresidual⟩ :=
    G.exists_lift_injective_partialColor (targetGraph G M) (fun v : G.V => v)
      (target G M) htinj (fun _ _ => Iff.rfl) (fun _ => rfl) R K hK color hfeasible
  let T : Finset G.E := (Finset.univ : Finset (Occurrence G M)).image (target G M)
  let A : Finset G.E := R.image (target G M)
  have hAT : A ⊆ T := Finset.image_subset_image (Finset.subset_univ R)
  have hdisj : Disjoint (Finset.univ \ T) (T \ A) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (Finset.mem_sdiff.mp he).2 (Finset.mem_sdiff.mp hf).1
  have hsplit : Finset.univ \ A = (Finset.univ \ T) ∪ (T \ A) := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro ha
      by_cases ht : e ∈ T
      · exact Or.inr ⟨ht,ha⟩
      · exact Or.inl ht
    · intro h
      rcases h with ht | ⟨_,ha⟩
      · exact fun ha => ht (hAT ha)
      · exact ha
  refine ⟨A,lifted,hlift,?_,?_⟩
  · intro e he v hi
    obtain ⟨o,ho,rfl⟩ := Finset.mem_image.mp he
    rw [hsame o ho]
    exact havoid o ho v hi
  · intro v
    have hfirst : (∑ e ∈ Finset.univ \ T, if G.Inc v e then G.weight e else 0) ≤
        ((Finset.univ \ T).card : ℝ) := by
      calc
        _ ≤ ∑ _e ∈ Finset.univ \ T, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro e _
          split_ifs
          · exact G.weight_le_one e
          · norm_num
        _ = _ := by simp
    have hgroup : ((Finset.univ \ T).card : ℝ) ≤
        2*(Fintype.card G.E : ℝ)/M + ((Fintype.card G.V)^2 : ℕ)*M := by
      have hg := BinPackingInstance.KeyedLinearRoundedCover.card_nonTargetItems_le_two_mul_div_add_key_mul
        (key G) M hM
      simpa only [BinPackingInstance.KeyedLinearRoundedCover.nonTargetItems,
        BinPackingInstance.KeyedLinearRoundedCover.targetItems, T,
        Fintype.card_prod, Nat.cast_mul, pow_two] using hg
    rw [hsplit, Finset.sum_union hdisj]
    exact add_le_add (hfirst.trans hgroup) ((le_of_eq (hresidual v)).trans (herror v))

end SubtwoLinearGrouping
end
end WeightedEdgeColoring.WeightedMultigraph
