import WeightedEdgeColoring.SubtwoPhysicalPackets
import WeightedEdgeColoring.SubtwoOrdinaryQuotientProved

/-! The actual crossing full packets have an unconditional uniform
`1.999 + eta` coloring. Expanding packets preserves weighted feasibility
and the single original endpoint label at every contracted block. -/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u

theorem exists_subtwoFloorBaseColor_uniform (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (n : ℕ),
      N ≤ n → G.LocallyPacksInto n →
      ∃ k : ℕ, ∃ hk : 0 < k, (k : ℝ) ≤ (subtwoKappa + eta) * n ∧
        ∃ color : (G.subtwoFloorQuotient n).E → Fin k,
          (G.subtwoFloorQuotient n).IsProperOn (G.subtwoFloorQuotientEdges n) color ∧
          G.IsFeasibleOn (G.subtwoFloorBaseEdges n) (G.subtwoFloorBaseColor hk n color) ∧
          ∀ e ∈ G.subtwoFloorBaseEdges n, ∀ f ∈ G.subtwoFloorBaseEdges n,
            ∀ v w, G.Inc v e → G.Inc w f →
              G.subtwoFloorBlock n v = G.subtwoFloorBlock n w →
              G.subtwoFloorBaseColor hk n color e = G.subtwoFloorBaseColor hk n color f →
              v = w := by
  obtain ⟨N, hN⟩ := Subtwo.quotientOrdinaryColoring_proved.{u} eta heta
  refine ⟨max N 1, ?_⟩
  intro G n hn hlocal
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N 1).trans hn)
  obtain ⟨k, hk, hbound, color, hproper⟩ :=
    hN (G.subtwoFloorQuotient n) (G.subtwoFloorQuotientEdges n) n hnN
      (G.subtwoFloorQuotient_degree_le hn0 hlocal)
      (G.subtwoFloorQuotient_oddSetDensityAtMost hn0 hlocal)
  refine ⟨k, hk, hbound, color, hproper,
    G.subtwoFloorBaseColor_isFeasibleOn hk color hproper, ?_⟩
  intro e he f hf v w hev hfw hb hc
  exact G.subtwoFloorBaseColor_endpoint_unique hk color hproper he hf hev hfw hb hc

end WeightedEdgeColoring.WeightedMultigraph
