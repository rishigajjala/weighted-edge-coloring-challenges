import WeightedEdgeColoring.SubtwoVertexRestrictionPatterns
import WeightedEdgeColoring.SubtwoPaletteProjection

/-!
# Restricting a reserved palette to its actual block

Reservations outside the block have zero budget. Removing those labels
and projecting each pattern to the internal edges gives an allocation on
the induced graph, with exactly the block's three or five vertex labels.
-/

open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G : WeightedMultigraph.{u}) (S : Finset G.V)

noncomputable def vertexRestriction_patternRestrict (p : G.SubtwoWeightedPattern) :
    (G.vertexRestriction S).SubtwoWeightedPattern := by
  classical
  refine ⟨fun e => p.val e.1, ?_⟩
  intro v
  let f : G.E → ℝ := fun e => if G.Inc v.val e then (p.val e : ℝ)*G.weight e else 0
  have heq : (∑ e : (G.vertexRestriction S).E,
      if (G.vertexRestriction S).Inc v e then
        (p.val e.1 : ℝ)*(G.vertexRestriction S).weight e else 0) =
      ∑ e : (G.vertexRestriction S).E, f e.1 := by
    apply Finset.sum_congr rfl
    intro e _
    simp only [G.vertexRestriction_inc S v e, f]
    rfl
  rw [heq, G.vertexRestriction_sum S f]
  calc
    G.subtwoInternalCost f S ≤ ∑ e : G.E, f e := by
      unfold subtwoInternalCost
      apply Finset.sum_le_sum
      intro e _
      split_ifs
      · rfl
      · dsimp [f]
        split_ifs
        · exact mul_nonneg (Nat.cast_nonneg _) (G.weight_nonneg _)
        · rfl
    _ ≤ 1 := p.property v.val

/-- Pattern restriction commutes with reserving a color at a block vertex. -/
theorem vertexRestriction_reservedPattern
    (l : Option (G.vertexRestriction S).V) (p : G.SubtwoWeightedPattern)
    (e : (G.vertexRestriction S).E) :
    (G.vertexRestriction S).subtwoReservedColorPattern l
      (G.vertexRestriction_patternRestrict S p) e =
      G.subtwoReservedColorPattern (l.map Subtype.val) p e.1 := by
  classical
  cases l with
  | none => rfl
  | some v =>
    change (((G.vertexRestriction_patternRestrict S p).avoidVertex
      (G.vertexRestriction S) v).val e : ℝ) =
      ((p.avoidVertex G v.val).val e.val : ℝ)
    simp only [SubtwoWeightedPattern.avoidVertex, SubtwoWeightedPattern.ofLE,
      G.vertexRestriction_inc S v e]
    rfl

/-- A reserved allocation with zero outside budgets gives an allocation
on the induced graph, using only the vertices in the block as labels. -/
theorem vertexRestriction_paletteAttainable
    (κ : ℝ) (q : G.V → ℝ)
    (houtside : ∀ v, v ∉ S → q v = 0)
    (demand : G.E → ℝ)
    (hd : demand ∈ Subtwo.PaletteAttainable (Subtwo.reservedPaletteBudget κ q)
      G.subtwoReservedColorPattern) :
    (fun e : (G.vertexRestriction S).E => demand e.val) ∈
      Subtwo.PaletteAttainable
        (Subtwo.reservedPaletteBudget κ (fun v : (G.vertexRestriction S).V => q v.val))
        (G.vertexRestriction S).subtwoReservedColorPattern := by
  classical
  obtain ⟨a, ha, hcover⟩ := hd.2
  have hzero : ∀ v, v ∉ S → ∀ p : G.SubtwoWeightedPattern, a (some v,p) = 0 := by
    intro v hv p
    have hs := ha.2 (some v)
    change (∑ p, a (some v,p)) ≤ q v at hs
    rw [houtside v hv] at hs
    have hp : a (some v,p) ≤ ∑ r, a (some v,r) :=
      Finset.single_le_sum (fun r _ => ha.1 (some v,r)) (Finset.mem_univ p)
    exact le_antisymm (hp.trans hs) (ha.1 _)
  have hsumq : (∑ v : (G.vertexRestriction S).V, q v.val) = ∑ v : G.V, q v := by
    calc
      _ = ∑ v ∈ S, q v := (Finset.sum_subtype S (fun v => Iff.rfl) q).symm
      _ = ∑ v : G.V, q v := Finset.sum_subset (Finset.subset_univ S)
        (fun v _ hv => houtside v hv)
  let b : Option (G.vertexRestriction S).V × G.SubtwoWeightedPattern → ℝ :=
    fun lp => a (lp.1.map Subtype.val,lp.2)
  let old : Option (G.vertexRestriction S).V → G.SubtwoWeightedPattern →
      (G.vertexRestriction S).E → ℝ :=
    fun l p e => G.subtwoReservedColorPattern (l.map Subtype.val) p e.val
  have hb : Subtwo.PaletteFeasible
      (Subtwo.reservedPaletteBudget κ (fun v : (G.vertexRestriction S).V => q v.val)) b := by
    constructor
    · intro lp
      exact ha.1 _
    · intro l
      cases l with
      | none =>
        simpa only [b, Option.map_none, Subtwo.reservedPaletteBudget, hsumq] using ha.2 none
      | some v => exact ha.2 (some v.val)
  have hcoverage : ∀ e : (G.vertexRestriction S).E,
      Subtwo.paletteCoverage old b e =
        Subtwo.paletteCoverage G.subtwoReservedColorPattern a e.val := by
    intro e
    have hs :
        (∑ v : (G.vertexRestriction S).V, ∑ p : G.SubtwoWeightedPattern,
          a (some v.val,p)*G.subtwoReservedColorPattern (some v.val) p e.val) =
        ∑ v : G.V, ∑ p : G.SubtwoWeightedPattern,
          a (some v,p)*G.subtwoReservedColorPattern (some v) p e.val := by
      let f : G.V → ℝ := fun v => ∑ p : G.SubtwoWeightedPattern,
        a (some v,p)*G.subtwoReservedColorPattern (some v) p e.val
      calc
        _ = ∑ v ∈ S, f v := (Finset.sum_subtype S (fun v => Iff.rfl) f).symm
        _ = ∑ v : G.V, f v := Finset.sum_subset (Finset.subset_univ S) (by
          intro v _ hv
          simp [f, hzero v hv])
    unfold Subtwo.paletteCoverage
    rw [Fintype.sum_option, Fintype.sum_option]
    simpa only [b, old, Option.map_none, Option.map_some] using
      congrArg (fun x : ℝ =>
        (∑ p : G.SubtwoWeightedPattern, a (none,p)*G.subtwoReservedColorPattern none p e.val)+x) hs
  have hbAttain : (fun e : (G.vertexRestriction S).E => demand e.val) ∈
      Subtwo.PaletteAttainable
        (Subtwo.reservedPaletteBudget κ (fun v : (G.vertexRestriction S).V => q v.val)) old := by
    refine ⟨fun e => hd.1 e.val, b, hb, ?_⟩
    intro e
    rw [hcoverage]
    exact hcover e.val
  have hproject := Subtwo.paletteAttainable_project
    (Subtwo.reservedPaletteBudget κ (fun v : (G.vertexRestriction S).V => q v.val))
    old (G.vertexRestriction S).subtwoReservedColorPattern
    (fun _ p => G.vertexRestriction_patternRestrict S p)
    (fun j i : (G.vertexRestriction S).E => if i = j then (1 : ℝ) else 0)
    (by intro j i; dsimp only; split_ifs <;> norm_num)
    (by
      intro l p e
      simpa only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq'] using
        G.vertexRestriction_reservedPattern S l p e)
    hbAttain
  simpa only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq'] using hproject

end
end WeightedEdgeColoring.WeightedMultigraph
