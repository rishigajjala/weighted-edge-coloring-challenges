import WeightedEdgeColoring.SubtwoGraphPalette
import WeightedEdgeColoring.SubtwoAttainablePhysicalRestoration
import WeightedEdgeColoring.SubtwoBoundedPatternMenu

/-! A graph palette fills physical type slots with a uniform local error. -/

set_option maxHeartbeats 4000000
open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (H : WeightedMultigraph.{u})

noncomputable def subtwoReservedNatPattern :
    Option H.V → H.SubtwoWeightedPattern → H.E → ℕ
  | none, p, e => p.val e
  | some v, p, e => (p.avoidVertex H v).val e

theorem subtwoReservedNatPattern_cast (l : Option H.V)
    (p : H.SubtwoWeightedPattern) (e : H.E) :
    (H.subtwoReservedNatPattern l p e : ℝ) = H.subtwoReservedColorPattern l p e := by
  cases l <;> rfl

theorem subtwoReservedNatPattern_capacity (l : Option H.V)
    (p : H.SubtwoWeightedPattern) (v : H.V) :
    (∑ e : H.E, if H.Inc v e then
      (H.subtwoReservedNatPattern l p e : ℝ) * H.weight e else 0) ≤ 1 := by
  simp_rw [H.subtwoReservedNatPattern_cast]
  exact H.subtwoReservedColorPattern_capacity l p v

theorem subtwoReservedNatPattern_avoids (v : H.V)
    (p : H.SubtwoWeightedPattern) (e : H.E) (hi : H.Inc v e) :
    H.subtwoReservedNatPattern (some v) p e = 0 :=
  p.avoidVertex_zero H v e hi

theorem subtwoReservedNatPattern_le (S : ℕ) (hS : 0 < S)
    (hweight : ∀ e, (1 : ℝ) / S ≤ H.weight e)
    (l : Option H.V) (p : H.SubtwoWeightedPattern) (e : H.E) :
    H.subtwoReservedNatPattern l p e ≤ S := by
  cases l with
  | none => exact H.subtwoPattern_multiplicity_le_of_weight_lower S hS hweight p e
  | some v =>
    exact H.subtwoPattern_multiplicity_le_of_weight_lower S hS hweight
      (p.avoidVertex H v) e

/-- A palette on a bounded type graph colors actual edges, omitting only a
fixed menu error at each vertex. Reservations use the original vertices. -/
theorem exists_physical_restoration_of_graphPalette
    (G : WeightedMultigraph.{u}) (F : Finset G.E)
    (vertex : G.V → H.V) (typeOf : G.E → H.E)
    (hinc : ∀ e ∈ F, ∀ v, G.Inc v e → H.Inc (vertex v) (typeOf e))
    (hweight : ∀ e ∈ F, G.weight e ≤ H.weight (typeOf e))
    (S : ℕ) (hS : 0 < S) (hlower : ∀ i, (1 : ℝ) / S ≤ H.weight i)
    (n D K : ℕ) (hK : 0 < K) (κ : ℝ) (q : G.V → ℝ)
    (hq : ∀ l, 0 ≤ q l) (hsum : (∑ l, q l) ≤ κ)
    (demand : H.E → ℝ)
    (hd : demand ∈ Subtwo.PaletteAttainable (Subtwo.reservedPaletteBudget κ q)
      (fun l p i => H.subtwoReservedColorPattern (l.map vertex) p i))
    (hdemand : ∀ i, ((F.filter fun e => typeOf e = i).card : ℝ) ≤
      (n : ℝ) * demand i)
    (boundaryLabel : Fin K → Option G.V)
    (hlabel : ∀ l,
      (Fintype.card {c : Fin K // boundaryLabel c = some l} : ℝ) ≤ (n : ℝ) * q l + D)
    (hpalette : (n : ℝ) * κ + (Fintype.card G.V : ℝ) * (D + 1) ≤ K) :
    ∃ R ⊆ F, ∃ color : G.E → Fin K,
      G.IsFeasibleOn R color ∧
      (∀ e ∈ R, ∀ v, G.Inc v e → boundaryLabel (color e) ≠ some v) ∧
      ∀ v, (∑ e ∈ F \ R, if G.Inc v e then G.weight e else 0) ≤
        (Fintype.card H.E : ℝ) * (Fintype.card G.V + 1) *
          Fintype.card H.SubtwoWeightedPattern * S := by
  classical
  let pattern : Option G.V → H.SubtwoWeightedPattern → H.E → ℕ :=
    fun l p i => H.subtwoReservedNatPattern (l.map vertex) p i
  have hp : ∀ l p i, (pattern l p i : ℝ) =
      H.subtwoReservedColorPattern (l.map vertex) p i := by
    intro l p i
    exact H.subtwoReservedNatPattern_cast _ _ _
  obtain ⟨R, hRF, color, hfeasible, havoid, _hcount, herror⟩ :=
    Subtwo.exists_physical_restoration_of_attainable F typeOf (fun v => v)
      (fun v i => H.Inc (vertex v) i) H.weight H.weight_nonneg hinc hweight pattern
      (fun l p v => H.subtwoReservedNatPattern_capacity _ p (vertex v))
      (fun v p i hi => H.subtwoReservedNatPattern_avoids (vertex v) p i hi)
      n D K hK κ q hq hsum demand (by simpa only [hp] using hd)
      hdemand boundaryLabel hlabel hpalette
  refine ⟨R, hRF, color, hfeasible, havoid, fun v => (herror v).trans ?_⟩
  have hb := Subtwo.roundedPaletteVertexError_le_uniform pattern S
    (fun l p i => H.subtwoReservedNatPattern_le S hS hlower (l.map vertex) p i)
    (fun i => H.Inc (vertex v) i) H.weight H.weight_nonneg H.weight_le_one
  simpa only [Fintype.card_option, Nat.cast_add, Nat.cast_one] using hb

end
end WeightedEdgeColoring.WeightedMultigraph
