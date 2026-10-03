import WeightedEdgeColoring.SubtwoThreePhysicalData
import WeightedEdgeColoring.SubtwoPhysicalFiveCostKeys

/-! Exact triangle bundle costs and the original fractional-cost density. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph.SubtwoThreePhysicalData

universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ} (D : G.SubtwoThreePhysicalData n)

noncomputable def bundleKey (i : Fin 3) : G.V × G.V :=
  G.floorPairKey (D.first i) (D.second i)

theorem bundleKey_injective : Function.Injective D.bundleKey := by
  intro i j h
  have he := G.subtwo_floorPairKey_eq_endpoints
    (D.first i) (D.second i) (D.first j) (D.second j) h
  have hveq (a b : Fin 3) : D.vertex a = D.vertex b ↔ a = b :=
    D.vertex_injective.eq_iff
  fin_cases i <;> fin_cases j <;>
    simp_all [bundleKey, first, second, oppositePair, hveq]

theorem bundleKey_internal (i : Fin 3) :
    (D.bundleKey i).1 ∈ D.vertexSet ∧ (D.bundleKey i).2 ∈ D.vertexSet := by
  unfold bundleKey floorPairKey
  split_ifs <;> exact ⟨D.vertex_mem _, D.vertex_mem _⟩

theorem pairKey_in_bundleKeys (i j : Fin 3) (hij : i ≠ j) :
    G.floorPairKey (D.vertex i) (D.vertex j) ∈
      Finset.univ.image D.bundleKey := by
  fin_cases i <;> fin_cases j
  all_goals
    first
    | exact False.elim (hij rfl)
    | exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    | exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
    | exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
    | exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _,
        G.subtwo_floorPairKey_comm _ _⟩
    | exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _,
        G.subtwo_floorPairKey_comm _ _⟩
    | exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _,
        G.subtwo_floorPairKey_comm _ _⟩

theorem internal_nonempty_bundle_in_image (k : G.V × G.V)
    (hk : k.1 ∈ D.vertexSet ∧ k.2 ∈ D.vertexSet)
    (hne : G.floorBundle k ≠ ∅) :
    k ∈ Finset.univ.image D.bundleKey := by
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have heq := G.floorKey_eq_of_mem_floorBundle he
  have hint : G.fst e ∈ D.vertexSet ∧ G.snd e ∈ D.vertexSet := by
    apply (G.subtwo_floorKey_internal D.vertexSet e).mp
    simpa only [heq] using hk
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hint.1
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hint.2
  have hij : i ≠ j := by
    intro h
    exact G.noLoop e (by rw [← hi, ← hj, h])
  have hp := D.pairKey_in_bundleKeys i j hij
  rwa [hi, hj, ← G.floorKey_eq_floorPairKey, heq] at hp

theorem bundleCost_sum_eq_fractional_internal :
    (∑ i : Fin 3, D.bundleCost i) =
      G.subtwoFractionalInternalBundleCost D.vertexSet / n := by
  classical
  have hi : (Finset.univ.image D.bundleKey) ⊆
      Finset.univ.filter (fun k : G.V × G.V =>
        k.1 ∈ D.vertexSet ∧ k.2 ∈ D.vertexSet) := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, D.bundleKey_internal i⟩
  have hs := Finset.sum_subset hi (f := fun k => (G.floorBundleCover k).cost) (by
    intro k hk hn
    apply G.subtwo_floorBundleCover_cost_zero_of_empty k
    by_contra he
    exact hn (D.internal_nonempty_bundle_in_image k (Finset.mem_filter.mp hk).2 he))
  rw [Finset.sum_image (fun a _ b _ h => D.bundleKey_injective h)] at hs
  rw [Finset.sum_filter] at hs
  change (∑ i : Fin 3, (G.floorBundleCover (D.bundleKey i)).cost) =
    G.subtwoFractionalInternalBundleCost D.vertexSet at hs
  simp only [bundleCost, subtwoPhysicalBundleCost, ← Finset.sum_div]
  exact congrArg (fun x : ℝ => x / n) hs

theorem bundleCost_sum_ge_kappa
    (hlocal : G.LocallyPacksInto n)
    (b : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank
      (G.subtwoFloorCost n) b = 1)
    (hset : D.vertexSet =
      G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b) :
    (1999/1000:ℝ) ≤ ∑ i : Fin 3, D.bundleCost i := by
  have h := G.subtwoFloorBlock_fractional_paid D.n_pos hlocal b
  rw [hrank] at h
  rw [D.bundleCost_sum_eq_fractional_internal, hset]
  exact (le_div_iff₀ (by exact_mod_cast D.n_pos : (0:ℝ)<n)).mpr
    (by simpa [subtwoKappa] using h)

end WeightedEdgeColoring.WeightedMultigraph.SubtwoThreePhysicalData
