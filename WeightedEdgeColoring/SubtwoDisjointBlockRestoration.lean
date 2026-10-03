import WeightedEdgeColoring.SubtwoPhysicalPaletteMerge

/-!
# Reusing restored colors in every disjoint block

Each internal edge belongs to the block of each of its endpoints. Local
partial colorings can therefore use the same palette simultaneously. The
leftover bound is the bound in the vertex's own block; it is never summed
over all blocks.
-/

open scoped BigOperators
namespace WeightedEdgeColoring.Subtwo
noncomputable section
universe u

/-- Assemble local physical restorations, retaining endpoint avoidance
and the local weighted leftover bound. -/
theorem exists_blockwise_physical_restoration
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {B L : Type*} [DecidableEq B]
    {K : ℕ} (F : Finset G.E) (block : G.V → B) (owner : G.E → B)
    (hinc : ∀ e ∈ F, ∀ v, G.Inc v e → owner e = block v)
    (boundaryLabel : B → Fin K → Option L) (vertexLabel : B → G.V → L)
    (loss : ℝ)
    (hlocal : ∀ b, ∃ P ⊆ F.filter (fun e => owner e = b),
      ∃ color : G.E → Fin K,
        G.IsFeasibleOn P color ∧
        (∀ e ∈ P, ∀ v, G.Inc v e →
          boundaryLabel b (color e) ≠ some (vertexLabel b v)) ∧
        ∀ v, block v = b →
          (∑ e ∈ (F.filter fun e => owner e = b) \ P,
            if G.Inc v e then G.weight e else 0) ≤ loss) :
    ∃ R ⊆ F, ∃ color : G.E → Fin K,
      G.IsFeasibleOn R color ∧
      (∀ e ∈ R, ∀ v, G.Inc v e →
        boundaryLabel (block v) (color e) ≠ some (vertexLabel (block v) v)) ∧
      ∀ v, (∑ e ∈ F \ R, if G.Inc v e then G.weight e else 0) ≤ loss := by
  classical
  choose P hsub color hfeasible havoid hloss using hlocal
  let R : Finset G.E := F.filter fun e => e ∈ P (owner e)
  have hRF : R ⊆ F := Finset.filter_subset _ _
  have hRfilter : ∀ b, R.filter (fun e => owner e = b) = P b := by
    intro b
    ext e
    constructor
    · intro he
      obtain ⟨heR, heb⟩ := Finset.mem_filter.mp he
      have heP := (Finset.mem_filter.mp heR).2
      simpa [heb] using heP
    · intro he
      obtain ⟨heF, heb⟩ := Finset.mem_filter.mp (hsub b he)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨heF, by simpa [heb] using he⟩, heb⟩
  let globalColor : G.E → Fin K := fun e => color (owner e) e
  refine ⟨R, hRF, globalColor, ?_, ?_, ?_⟩
  · apply feasibleOn_of_blockwise_feasible R block owner
      (fun e he => hinc e (hRF he)) color
    intro b
    rw [hRfilter]
    exact hfeasible b
  · intro e he v hev
    have heP := (Finset.mem_filter.mp he).2
    have ho := hinc e (hRF he) v hev
    simpa [globalColor, ho] using havoid (owner e) e heP v hev
  · intro v
    have hset : (F \ R).filter (fun e => G.Inc v e) =
        ((F.filter fun e => owner e = block v) \ P (block v)).filter
          (fun e => G.Inc v e) := by
      ext e
      by_cases heF : e ∈ F
      · by_cases hev : G.Inc v e
        · have ho := hinc e heF v hev
          simp [R, heF, hev, ho]
        · simp [hev]
      · simp [heF]
    have hsum := congrArg (fun A : Finset G.E => ∑ e ∈ A, G.weight e) hset
    simp only [Finset.sum_filter] at hsum
    rw [hsum]
    exact hloss (block v) v rfl

/-- Add all local restorations to a fixed feasible boundary coloring.
Existing boundary colors remain exactly unchanged. -/
theorem exists_boundary_and_blockwise_restoration
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {B L : Type*} [DecidableEq B]
    {K : ℕ} (Fbase F : Finset G.E) (hdisj : Disjoint Fbase F)
    (base : G.E → Fin K) (hbase : G.IsFeasibleOn Fbase base)
    (block : G.V → B) (owner : G.E → B)
    (hinc : ∀ e ∈ F, ∀ v, G.Inc v e → owner e = block v)
    (boundaryLabel : B → Fin K → Option L) (vertexLabel : B → G.V → L)
    (hboundary : ∀ e ∈ Fbase, ∀ v, G.Inc v e →
      boundaryLabel (block v) (base e) = some (vertexLabel (block v) v))
    (loss : ℝ)
    (hlocal : ∀ b, ∃ P ⊆ F.filter (fun e => owner e = b),
      ∃ color : G.E → Fin K,
        G.IsFeasibleOn P color ∧
        (∀ e ∈ P, ∀ v, G.Inc v e →
          boundaryLabel b (color e) ≠ some (vertexLabel b v)) ∧
        ∀ v, block v = b →
          (∑ e ∈ (F.filter fun e => owner e = b) \ P,
            if G.Inc v e then G.weight e else 0) ≤ loss) :
    ∃ R ⊆ F, ∃ color : G.E → Fin K,
      G.IsFeasibleOn (Fbase ∪ R) color ∧
      (∀ e ∈ Fbase, color e = base e) ∧
      ∀ v, (∑ e ∈ F \ R, if G.Inc v e then G.weight e else 0) ≤ loss := by
  classical
  obtain ⟨R, hRF, internal, hfeasible, havoid, hleft⟩ :=
    exists_blockwise_physical_restoration F block owner hinc boundaryLabel vertexLabel
      loss hlocal
  refine ⟨R, hRF, (fun e => if e ∈ Fbase then base e else internal e), ?_,
    (fun e he => by simp [he]), hleft⟩
  apply feasibleOn_merge_of_vertex_color_separation Fbase R (hdisj.mono_right hRF)
    base internal hbase hfeasible
  intro e he f hf v hev hfv hc
  apply havoid f hf v hfv
  rw [← hc]
  exact hboundary e he v hev

end
end WeightedEdgeColoring.Subtwo
