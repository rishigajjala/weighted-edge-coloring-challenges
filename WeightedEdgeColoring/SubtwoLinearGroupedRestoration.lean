import WeightedEdgeColoring.SubtwoLinearGroupedGraph
import WeightedEdgeColoring.SubtwoGraphPalettePhysicalRestoration

/-!
# A finite, uniform restoration theorem after linear grouping

The only extra color budget is the padding for original endpoint labels.
The omitted weight from flooring the pattern menu is bounded by a constant
depending on the cutoff and grouping width, independently of multiplicity.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 160000
open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u v

/-- An actual sigma fiber has exactly the number of its occurrence indices. -/
theorem subtwo_card_sigmaFiber {I : Type u} [Fintype I] [DecidableEq I]
    (O : I → Type v) [∀ j, Fintype (O j)] (j : I) :
    ((Finset.univ : Finset (Σ i, O i)).filter fun o => o.1 = j).card =
      Fintype.card (O j) := by
  classical
  have heq : ((Finset.univ : Finset (Σ i, O i)).filter fun o => o.1 = j) =
      (Finset.univ : Finset (O j)).image (fun o => Sigma.mk j o) := by
    ext o
    rcases o with ⟨i,o⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      subst i
      exact ⟨o,rfl⟩
    · rintro ⟨p,h⟩
      exact (congrArg Sigma.fst h).symm
  rw [heq, Finset.card_image_of_injective]
  · exact Finset.card_univ
  · intro a b h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

namespace SubtwoLinearGrouping
variable (G : WeightedMultigraph.{u})

/-- The actual rounded occurrence graph admits a partial coloring in the
reserved palette, with a fixed weighted error at each original vertex. -/
theorem exists_grouped_reserved_restoration
    (M S : ℕ) (hM : 0 < M) (hS : 0 < S)
    (hlower : ∀ e, (1 : ℝ) / S ≤ G.weight e)
    (n D K : ℕ) (hn : 0 < n) (hK : 0 < K)
    (κ : ℝ) (q : G.V → ℝ) (hq : ∀ v, 0 ≤ q v) (hsum : (∑ v,q v) ≤ κ)
    (hd : (fun _e : G.E => (1 : ℝ) / n) ∈
      Subtwo.PaletteAttainable (Subtwo.reservedPaletteBudget κ q) G.subtwoReservedColorPattern)
    (boundaryLabel : Fin K → Option G.V)
    (hlabel : ∀ v,
      (Fintype.card {c : Fin K // boundaryLabel c = some v} : ℝ) ≤ n*q v+D)
    (hpalette : (n : ℝ)*κ+(Fintype.card G.V : ℝ)*(D+1) ≤ K) :
    ∃ R : Finset (targetGraph G M).E, ∃ color : (targetGraph G M).E → Fin K,
      (targetGraph G M).IsFeasibleOn R color ∧
      (∀ e ∈ R, ∀ v, (targetGraph G M).Inc v e → boundaryLabel (color e) ≠ some v) ∧
      ∀ v, (∑ e ∈ Finset.univ \ R,
        if (targetGraph G M).Inc v e then (targetGraph G M).weight e else 0) ≤
        ((Fintype.card G.V)^2*M : ℕ) * ((Fintype.card G.V : ℝ)+1) *
          ((S+1)^((Fintype.card G.V)^2*M) : ℕ) * S := by
  classical
  let demand : (typeGraph G M).E → ℝ := fun j => (Fintype.card (OccurrenceAt G M j) : ℝ)/n
  have ha := paletteAttainable G M hM (Subtwo.reservedPaletteBudget κ q)
    (fun _ => (1 : ℝ)/n) hd
  have hdtype : demand ∈ Subtwo.PaletteAttainable (Subtwo.reservedPaletteBudget κ q)
      (typeGraph G M).subtwoReservedColorPattern := by
    convert ha using 2
    dsimp only [demand]
    simp [div_eq_mul_inv]
  have hdmap : demand ∈ Subtwo.PaletteAttainable (Subtwo.reservedPaletteBudget κ q)
      (fun l p i => (typeGraph G M).subtwoReservedColorPattern (l.map (fun v : G.V => v)) p i) := by
    obtain ⟨hd0,a,ha,hcover⟩ := hdtype
    refine ⟨hd0,a,ha,?_⟩
    intro j
    convert hcover j using 1
    unfold Subtwo.paletteCoverage
    apply Finset.sum_congr rfl
    intro l _
    cases l <;> rfl
  have hcount : ∀ j : (typeGraph G M).E,
      (((Finset.univ : Finset (targetGraph G M).E).filter fun e => e.1=j).card : ℝ) ≤
        (n : ℝ)*demand j := by
    intro j
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    calc
      _ = (Fintype.card (OccurrenceAt G M j) : ℝ) := by
        exact_mod_cast subtwo_card_sigmaFiber (OccurrenceAt G M) j
      _ ≤ (n : ℝ)*demand j := by
        dsimp only [demand]
        exact le_of_eq (by field_simp)
  obtain ⟨R,_hR,color,hfeasible,havoid,herror⟩ :=
    (typeGraph G M).exists_physical_restoration_of_graphPalette (targetGraph G M)
      Finset.univ (fun v : G.V => v) (fun e => e.1)
      (fun e _ v hi => (target_inc G M v e).mp hi)
      (fun e _ => target_weight_le G M e)
      S hS (type_weight_ge G M S hlower) n D K hK κ q hq hsum
      demand hdmap hcount boundaryLabel hlabel hpalette
  refine ⟨R,color,hfeasible,havoid,fun v => (herror v).trans ?_⟩
  have ht : (Fintype.card (typeGraph G M).E : ℝ) ≤
      ((Fintype.card G.V)^2*M : ℕ) := by exact_mod_cast card_types_le G M
  have hp : (Fintype.card (typeGraph G M).SubtwoWeightedPattern : ℝ) ≤
      ((S+1)^((Fintype.card G.V)^2*M) : ℕ) := by
    exact_mod_cast card_patterns_le G M S hS hlower
  change (Fintype.card (typeGraph G M).E : ℝ) * ((Fintype.card G.V : ℝ)+1) *
      Fintype.card (typeGraph G M).SubtwoWeightedPattern * S ≤ _
  gcongr

end SubtwoLinearGrouping
end
end WeightedEdgeColoring.WeightedMultigraph
