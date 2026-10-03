import WeightedEdgeColoring.SubtwoPriceRelabel
import Mathlib.Tactic

/-! Order the three prices in an arbitrary high-price triangle. -/

namespace WeightedEdgeColoring.Subtwo.TrianglePriceSort

open EndpointPotential TwoModelGeometry PriceRelabel

theorem edge_subset_three :
    ∀ u v w : Vertex, u ≠ v → u ≠ w → v ≠ w →
      ∀ e : Bundle, edge e ⊆ {u, v, w} →
        edge e = {u, v} ∨ edge e = {u, w} ∨ edge e = {v, w} := by
  decide

theorem exists_triangle_sorted (p : Bundle → ℝ)
    (u v w : Vertex) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ∃ π : Equiv.Perm Vertex,
      ({π 0, π 1, π 2} : Finset Vertex) = {u, v, w} ∧
      let p' := permutePrices π.symm p
      p' 4 ≤ p' 1 ∧ p' 1 ≤ p' 0 := by
  let P := p (pairIndex u v huv)
  let Q := p (pairIndex u w huw)
  let R := p (pairIndex v w hvw)
  have hvu : p (pairIndex v u huv.symm) = P := by
    exact congrArg p (pairIndex_symm u v huv).symm
  have hwu : p (pairIndex w u huw.symm) = Q := by
    exact congrArg p (pairIndex_symm u w huw).symm
  have hwv : p (pairIndex w v hvw.symm) = R := by
    exact congrArg p (pairIndex_symm v w hvw).symm
  by_cases hPQ : P ≤ Q
  · by_cases hQR : Q ≤ R
    · -- P ≤ Q ≤ R: canonical edges are vw, wu, vu.
      obtain ⟨π, h0, h1, h2, hs⟩ :=
        exists_triangle_ordered_tuple p w v u hvw.symm huw.symm huv.symm
          (by rw [hwv, hwu]; exact hQR)
          (by rw [hvu, hwu]; exact hPQ)
      refine ⟨π, ?_, hs⟩
      rw [h0, h1, h2]
      ext t
      simp [or_comm, or_left_comm, or_assoc]
    · have hRQ : R ≤ Q := le_of_not_ge hQR
      by_cases hPR : P ≤ R
      · -- P ≤ R ≤ Q: canonical edges are uw, wv, uv.
        obtain ⟨π, h0, h1, h2, hs⟩ :=
          exists_triangle_ordered_tuple p w u v huw.symm hvw.symm huv
            (by rw [hwu, hwv]; exact hRQ)
            (by rw [hwv]; exact hPR)
        refine ⟨π, ?_, hs⟩
        rw [h0, h1, h2]

        ext t
        simp [or_comm, or_left_comm, or_assoc]
      · have hRP : R ≤ P := le_of_not_ge hPR
        -- R ≤ P ≤ Q: canonical edges are uw, uv, wv.
        obtain ⟨π, h0, h1, h2, hs⟩ :=
          exists_triangle_ordered_tuple p u w v huw huv hvw.symm
            (by exact hPQ)
            (by rw [hwv]; exact hRP)
        refine ⟨π, ?_, hs⟩
        rw [h0, h1, h2]
        ext t
        simp [or_comm, or_left_comm, or_assoc]
  · have hQP : Q ≤ P := le_of_not_ge hPQ
    by_cases hPR : P ≤ R
    · -- Q ≤ P ≤ R: canonical edges are vw, vu, wu.
      obtain ⟨π, h0, h1, h2, hs⟩ :=
        exists_triangle_ordered_tuple p v w u hvw huv.symm huw.symm
          (by rw [hvu]; exact hPR)
          (by rw [hvu, hwu]; exact hQP)
      refine ⟨π, ?_, hs⟩
      rw [h0, h1, h2]
      ext t
      simp [or_comm, or_left_comm, or_assoc]
    · have hRP : R ≤ P := le_of_not_ge hPR
      by_cases hQR : Q ≤ R
      · -- Q ≤ R ≤ P: canonical edges are uv, vw, uw.
        obtain ⟨π, h0, h1, h2, hs⟩ :=
          exists_triangle_ordered_tuple p v u w huv.symm hvw huw
            (by rw [hvu]; exact hRP)
            (by exact hQR)
        refine ⟨π, ?_, hs⟩
        rw [h0, h1, h2]
        ext t
        simp [or_comm, or_left_comm, or_assoc]
      · have hRQ : R ≤ Q := le_of_not_ge hQR
        -- R ≤ Q ≤ P: canonical edges are uv, uw, vw.
        obtain ⟨π, h0, h1, h2, hs⟩ :=
          exists_triangle_ordered_tuple p u v w huv huw hvw hQP hRQ
        refine ⟨π, ?_, hs⟩
        rw [h0, h1, h2]

theorem high_on_triangle_subset (p : Bundle → ℝ)
    (u v w : Vertex) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hUV : (1 / 2 : ℝ) < p (pairIndex u v huv))
    (hUW : (1 / 2 : ℝ) < p (pairIndex u w huw))
    (hVW : (1 / 2 : ℝ) < p (pairIndex v w hvw)) :
    ∀ e : Bundle, edge e ⊆ {u, v, w} → (1 / 2 : ℝ) < p e := by
  intro e he
  rcases edge_subset_three u v w huv huw hvw e he with h | h | h
  · have : e = pairIndex u v huv := edge_injective (h.trans (edge_pairIndex u v huv).symm)
    simpa [this] using hUV
  · have : e = pairIndex u w huw := edge_injective (h.trans (edge_pairIndex u w huw).symm)
    simpa [this] using hUW
  · have : e = pairIndex v w hvw := edge_injective (h.trans (edge_pairIndex v w hvw).symm)
    simpa [this] using hVW

theorem exists_triangle_model_cover (p : Bundle → ℝ)
    (hdisjoint : ∀ e f : Bundle,
      Disjoint (edge e) (edge f) → p e + p f ≤ 1)
    (u v w : Vertex) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hUV : (1 / 2 : ℝ) < p (pairIndex u v huv))
    (hUW : (1 / 2 : ℝ) < p (pairIndex u w huw))
    (hVW : (1 / 2 : ℝ) < p (pairIndex v w hvw)) :
    ∃ π : Equiv.Perm Vertex, ∃ a x y : ℝ,
      1 / 2 < a ∧ 1 - a ≤ y ∧ y ≤ x ∧ x ≤ a ∧
      ∀ e : Bundle, permutePrices π.symm p e ≤ M a x y e := by
  obtain ⟨π, hset, hsort⟩ := exists_triangle_sorted p u v w huv huw hvw
  let p' := permutePrices π.symm p
  let a := p' 0
  let b := p' 1
  let c := p' 4
  have hdis' := permute_disjoint_price π p hdisjoint
  have hhigh := high_on_triangle_subset p u v w huv huw hvw hUV hUW hVW
  have hcan : ∀ e : Bundle, e = 0 ∨ e = 1 ∨ e = 4 →
      edge e ⊆ ({0, 1, 2} : Finset Vertex) := by decide
  have hmap : (({0, 1, 2} : Finset Vertex).map π.toEmbedding) = {u, v, w} := by
    simpa using hset
  have htri : ∀ e : Bundle, e = 0 ∨ e = 1 ∨ e = 4 →
      (1 / 2 : ℝ) < p' e := by
    intro e he
    have hsub : edge (edgePerm π e) ⊆ {u, v, w} := by
      rw [edge_edgePerm, ← hmap]
      exact (Finset.map_subset_map).2 (hcan e he)
    exact hhigh _ hsub
  have ha : (1 / 2 : ℝ) < a := htri 0 (Or.inl rfl)
  have hb : (1 / 2 : ℝ) < b := htri 1 (Or.inr (Or.inl rfl))
  have hc : (1 / 2 : ℝ) < c := htri 4 (Or.inr (Or.inr rfl))
  have hdom := triangle_domain a b c (by linarith [hsort.1, hsort.2])
    hb.le hc.le hsort.2
  refine ⟨π, a, b, 1 - c, ha, hdom.1, hdom.2.1, hdom.2.2, ?_⟩
  simpa [a, b, c, p'] using triangle_prices_le_M p' a b c rfl rfl rfl hdis'
end WeightedEdgeColoring.Subtwo.TrianglePriceSort
