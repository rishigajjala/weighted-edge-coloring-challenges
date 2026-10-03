import WeightedEdgeColoring.SubtwoThreePhysicalCostRows

/-! Incident budgets and triangle cost bounds for actual three-block data. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph.SubtwoThreePhysicalData

universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ} (D : G.SubtwoThreePhysicalData n)

private def incidentBundleIndex : Fin 3 → Fin 2 → Fin 3 :=
  ![![1,2],![0,2],![0,1]]

private theorem incidentBundleIndex_ne (v : Fin 3) :
    incidentBundleIndex v 0 ≠ incidentBundleIndex v 1 := by
  fin_cases v <;> decide

theorem incident_bundle_cost_identity (v : Fin 3) :
    (∑ i : Fin 3, D.bundleCost i) - D.bundleCost v =
      ∑ a : Fin 2, D.bundleCost (incidentBundleIndex v a) := by
  fin_cases v <;>
    simp [incidentBundleIndex, Fin.sum_univ_succ] <;> ring

private theorem incident_key_injective (v : Fin 3) :
    Function.Injective (fun a : Fin 2 => D.bundleKey (incidentBundleIndex v a)) := by
  intro a b h
  have hab := D.bundleKey_injective h
  fin_cases v <;> fin_cases a <;> fin_cases b <;>
    simp_all [incidentBundleIndex]

private theorem incident_key_internal (v : Fin 3) (a : Fin 2) :
    ((D.bundleKey (incidentBundleIndex v a)).1 ∈ D.vertexSet ∧
      (D.bundleKey (incidentBundleIndex v a)).2 ∈ D.vertexSet) ∧
      ((D.bundleKey (incidentBundleIndex v a)).1 = D.vertex v ∨
       (D.bundleKey (incidentBundleIndex v a)).2 = D.vertex v) := by
  have hi := D.bundleKey_internal (incidentBundleIndex v a)
  refine ⟨hi, ?_⟩
  fin_cases v <;> fin_cases a <;>
    simp [incidentBundleIndex, bundleKey, first, second, oppositePair,
      floorPairKey] <;>
    split_ifs <;> simp

theorem incident_bundleCost_le_fractional (v : Fin 3) :
    (∑ a : Fin 2, D.bundleCost (incidentBundleIndex v a)) ≤
      G.subtwoFractionalIncidentBundleCost D.vertexSet (D.vertex v) / n := by
  classical
  let key : Fin 2 → G.V × G.V := fun a => D.bundleKey (incidentBundleIndex v a)
  let keep : G.V × G.V → Prop := fun k =>
    (k.1 ∈ D.vertexSet ∧ k.2 ∈ D.vertexSet) ∧
      (k.1 = D.vertex v ∨ k.2 = D.vertex v)
  have hi : Finset.univ.image key ⊆ Finset.univ.filter keep := by
    intro k hk
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, D.incident_key_internal v a⟩
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hi
    (fun k _ _ => (G.floorBundleCover k).cost_nonneg)
  rw [Finset.sum_image (fun a _ b _ h => D.incident_key_injective v h),
    Finset.sum_filter] at hs
  change (∑ a : Fin 2, (G.floorBundleCover (key a)).cost) ≤
    G.subtwoFractionalIncidentBundleCost D.vertexSet (D.vertex v) at hs
  simp only [bundleCost, subtwoPhysicalBundleCost, ← Finset.sum_div]
  exact div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)

theorem incident_budget (hlocal : G.LocallyPacksInto n) (v : Fin 3) :
    (∑ i : Fin 3, D.bundleCost i) - D.bundleCost v +
      D.exteriorCharge v ≤ subtwoM := by
  rw [D.incident_bundle_cost_identity]
  have hs := D.incident_bundleCost_le_fractional v
  have hm := G.subtwo_exterior_add_fractionalIncident_le hlocal D.vertexSet (D.vertex v)
  have hn : (0:ℝ) < n := by exact_mod_cast D.n_pos
  have hx : D.exteriorCharge v * n =
      G.subtwoExteriorHarmonicCharge D.vertexSet (D.vertex v) := by
    unfold exteriorCharge
    exact div_mul_cancel₀ _ hn.ne'
  have hmul := (le_div_iff₀ hn).mp hs
  nlinarith

theorem bundleCost_le_one (hlocal : G.LocallyPacksInto n) (i : Fin 3) :
    D.bundleCost i ≤ 1 := by
  have h := G.subtwoPhysicalBundleCost_bounds D.n_pos
    (D.first i) (D.second i) (D.first_ne_second i)
    (hlocal (D.first i))
  exact h.2

theorem bundleCost_sum_le_two (hlocal : G.LocallyPacksInto n) :
    (∑ i : Fin 3, D.bundleCost i) ≤ 2 := by
  have h := G.subtwo_three_floorBundleCosts_le_two_mul
    (D.vertex 0) (D.vertex 1) (D.vertex 2) n
    (D.vertex_injective.ne (by decide))
    (D.vertex_injective.ne (by decide))
    (D.vertex_injective.ne (by decide))
    (hlocal (D.vertex 0)) (hlocal (D.vertex 1)) (hlocal (D.vertex 2))
  have hn : (0:ℝ) < n := by exact_mod_cast D.n_pos
  have hdiv :
      ((G.floorBundleCover (G.floorPairKey (D.vertex 0) (D.vertex 1))).cost +
        (G.floorBundleCover (G.floorPairKey (D.vertex 0) (D.vertex 2))).cost +
        (G.floorBundleCover (G.floorPairKey (D.vertex 1) (D.vertex 2))).cost) / n ≤
        (2:ℝ) := (div_le_iff₀ hn).mpr (by nlinarith [h])
  simp [bundleCost, subtwoPhysicalBundleCost, first, second, oppositePair,
    Fin.sum_univ_succ] at *
  convert hdiv using 1 <;> ring

end WeightedEdgeColoring.WeightedMultigraph.SubtwoThreePhysicalData
