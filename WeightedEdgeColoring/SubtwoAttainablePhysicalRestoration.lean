import WeightedEdgeColoring.SubtwoPlacedPatternSlots

/-!
# From fractional reserved palettes to physical partial colorings

This theorem performs all finite restoration steps: round the fractional
allocation, place its label classes in the real palette, fill the integer
slots with distinct physical edges, and bound the leftover weight. Only
the fractional palette inequality and the boundary label counts enter as
inputs. A selected internal color avoids its actual boundary endpoint.
-/

open scoped BigOperators
namespace WeightedEdgeColoring.Subtwo
noncomputable section
universe u

variable {G : WeightedEdgeColoring.WeightedMultigraph.{u}}
  {I L P : Type*} [Fintype I] [DecidableEq I]
  [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]

/-- Complete finite restoration for an attainable reserved palette.
The only losses are the explicit pattern-menu errors, with no dependence
on the number of other blocks in the graph. -/
theorem exists_physical_restoration_of_attainable
    (F : Finset G.E) (typeOf : G.E → I)
    (vertexLabel : G.V → L) (typeInc : G.V → I → Prop) [DecidableRel typeInc]
    (typeWeight : I → ℝ) (hweight0 : ∀ i, 0 ≤ typeWeight i)
    (hinc : ∀ e ∈ F, ∀ v, G.Inc v e → typeInc v (typeOf e))
    (hweight : ∀ e ∈ F, G.weight e ≤ typeWeight (typeOf e))
    (pattern : Option L → P → I → ℕ)
    (hcapacity : ∀ l p v,
      (∑ i, if typeInc v i then (pattern l p i : ℝ) * typeWeight i else 0) ≤ 1)
    (havoid : ∀ v p i, typeInc v i → pattern (some (vertexLabel v)) p i = 0)
    (n D K : ℕ) (hK : 0 < K) (κ : ℝ) (q : L → ℝ)
    (hq : ∀ l, 0 ≤ q l) (hsum : (∑ l, q l) ≤ κ)
    (demand : I → ℝ)
    (hd : demand ∈ PaletteAttainable (reservedPaletteBudget κ q)
      (fun l p i => (pattern l p i : ℝ)))
    (hdemand : ∀ i, ((F.filter fun e => typeOf e = i).card : ℝ) ≤
      (n : ℝ) * demand i)
    (boundaryLabel : Fin K → Option L)
    (hlabel : ∀ l,
      (Fintype.card {c : Fin K // boundaryLabel c = some l} : ℝ) ≤
        (n : ℝ) * q l + D)
    (hpalette : (n : ℝ) * κ + (Fintype.card L : ℝ) * (D + 1) ≤ K) :
    ∃ R ⊆ F, ∃ color : G.E → Fin K,
      G.IsFeasibleOn R color ∧
      (∀ e ∈ R, ∀ v, G.Inc v e →
        boundaryLabel (color e) ≠ some (vertexLabel v)) ∧
      (∀ i, ((F \ R).filter fun e => typeOf e = i).card ≤
        roundedPaletteErrorCount pattern i) ∧
      ∀ v, (∑ e ∈ F \ R, if G.Inc v e then G.weight e else 0) ≤
        ∑ i, if typeInc v i then
          (roundedPaletteErrorCount pattern i : ℝ) * typeWeight i else 0 := by
  classical
  obtain ⟨a, ha, _hlabels, hslots⟩ :=
    exists_roundedPaletteSlots_of_attainable n (reservedPaletteBudget κ q)
      pattern hd (fun i => (F.filter fun e => typeOf e = i).card) hdemand
  obtain ⟨place, hplace⟩ := exists_roundedReservedPalettePlacement
    n D κ q hq hsum a ha boundaryLabel hlabel (by simpa using hpalette)
  let slots : Fin K → I → ℕ := placedRoundedPatternSlots n a place pattern
  have hslotTotal : ∀ i, (F.filter fun e => typeOf e = i).card ≤
      (∑ c, slots c i) + roundedPaletteErrorCount pattern i := by
    intro i
    simpa only [slots, sum_placedRoundedPatternSlots] using hslots i
  have hslotCapacity : ∀ v c,
      (∑ i, if typeInc v i then (slots c i : ℝ) * typeWeight i else 0) ≤ 1 :=
    placedRoundedPatternSlots_capacity n a place pattern typeInc typeWeight hcapacity
  obtain ⟨R, hRF, color, hfeasible, hcount, herror⟩ :=
    exists_partialColoring_of_type_slots F typeOf K hK typeInc typeWeight hweight0
      slots (roundedPaletteErrorCount pattern) hinc hweight hslotTotal hslotCapacity
  refine ⟨R, hRF, color, hfeasible, ?_, herror,
    residualStarWeight_le_type_error F R typeOf typeInc typeWeight hweight0
      (roundedPaletteErrorCount pattern) hinc hweight herror⟩
  intro e he v hev hc
  have hpositive : 0 < slots (color e) (typeOf e) :=
    positive_slot_of_colored R typeOf color slots hcount he
  let labelInc : L → I → Prop := fun l i => ∃ v, vertexLabel v = l ∧ typeInc v i
  have hlabelAvoid : ∀ l p i, labelInc l i → pattern (some l) p i = 0 := by
    intro l p i hi
    obtain ⟨v, hl, hv⟩ := hi
    simpa [hl] using havoid v p i hv
  have hz := placedRoundedPatternSlots_avoids n a place pattern boundaryLabel
    hplace labelInc hlabelAvoid (vertexLabel v) (color e) (typeOf e)
    ⟨v, rfl, hinc e (hRF he) v hev⟩ hc
  change slots (color e) (typeOf e) = 0 at hz
  omega

end
end WeightedEdgeColoring.Subtwo
