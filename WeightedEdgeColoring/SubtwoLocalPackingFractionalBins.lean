import WeightedEdgeColoring.SubtwoFractionalStarDemand

/-! An ordinary integral packing of every star supplies the uniform
fractional-bin demand used by the five-vertex local theorem. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable def localPackingFractionalBins {n : ℕ} (hn : 0 < n)
    (hlocal : G.LocallyPacksInto n) :
    G.SubtwoLocalFractionalBins (fun _ => 1 / (n : ℝ)) := by
  classical
  let bin (v : G.V) : G.StarEdge v → Fin n := Classical.choose (hlocal v)
  have hbin (v : G.V) (j : Fin n) : G.starBinLoad (bin v) j ≤ 1 :=
    Classical.choose_spec (hlocal v) j
  refine {
    P := G.V × Fin n
    fintypeP := inferInstance
    pattern := fun v p e => if h : G.Inc v e then
      if bin v ⟨e, h⟩ = p.2 then 1 else 0 else 0
    mass := fun v p => if p.1 = v then 1 / (n : ℝ) else 0
    mass_nonneg := by intro v p; split_ifs <;> positivity
    bin_feasible := ?_
    covers := ?_ }
  · intro v p
    let f : G.E → ℝ := fun e =>
      if h : G.Inc v e then
        if bin v ⟨e, h⟩ = p.2 then G.weight e else 0 else 0
    have heq :
        (∑ e : G.E,
          ((if h : G.Inc v e then if bin v ⟨e, h⟩ = p.2 then (1:ℕ) else 0 else 0 : ℕ) : ℝ) *
            G.weight e) = G.starBinLoad (bin v) p.2 := by
      calc
        _ = ∑ e : G.E, f e := by
          apply Finset.sum_congr rfl
          intro e _
          by_cases h : G.Inc v e
          · by_cases hb : bin v ⟨e, h⟩ = p.2 <;> simp [f, h, hb]
          · simp [f, h]
        _ = ∑ e : G.StarEdge v, f e.1 := by
          calc
            (∑ e : G.E, f e) =
                ∑ e ∈ (Finset.univ : Finset G.E).filter (G.Inc v), f e := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro e _
              by_cases h : G.Inc v e <;> simp [f, h]
            _ = _ := (Finset.sum_subtype (p := G.Inc v)
              ((Finset.univ : Finset G.E).filter (G.Inc v))
              (by intro e; simp) f)
        _ = G.starBinLoad (bin v) p.2 := by
          unfold starBinLoad
          apply Finset.sum_congr rfl
          intro e _
          simp [f, e.2]
    exact heq ▸ hbin v p.2
  · intro v e
    by_cases hv : G.Inc v e
    · simp [hv, Fintype.sum_prod_type]
    · simp [hv]

theorem localPackingFractionalBins_total {n : ℕ} (hn : 0 < n)
    (hlocal : G.LocallyPacksInto n) (v : G.V) :
    (∑ j, (G.localPackingFractionalBins hn hlocal).mass v j) ≤ 1 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [localPackingFractionalBins, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp [hnR]

end WeightedEdgeColoring.WeightedMultigraph
