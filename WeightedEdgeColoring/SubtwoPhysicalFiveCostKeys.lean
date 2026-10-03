import WeightedEdgeColoring.SubtwoPhysicalFiveLocalRows
import WeightedEdgeColoring.SubtwoBundleTriangle

/-!
# The ten physical bundle keys of a five-vertex block

Each nonempty internal bundle occurs exactly once among the ten pairs.
The equalities below connect the indexed costs to the previously proved
physical incident and internal cost bounds.
-/

open scoped BigOperators
set_option autoImplicit false

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G : WeightedMultigraph.{u})

theorem subtwo_floorPairKey_eq_endpoints (a b c d : G.V)
    (h : G.floorPairKey a b = G.floorPairKey c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  unfold floorPairKey at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩

theorem subtwo_floorBundleCover_cost_zero_of_empty (k : G.V × G.V)
    (h : G.floorBundle k = ∅) : (G.floorBundleCover k).cost = 0 := by
  have hu := G.subtwo_floorBundleCover_cost_le_harmonic k
  have hz : (∑ e ∈ G.floorBundle k, harmonicCharge (G.weight e)) = 0 := by
    rw [h, Finset.sum_empty]
  rw [hz] at hu
  exact le_antisymm hu (G.floorBundleCover k).cost_nonneg

theorem subtwoFivePair_eq_of_endpoints (e f : Fin 10)
    (h : ((subtwoFivePair e).1 = (subtwoFivePair f).1 ∧
      (subtwoFivePair e).2 = (subtwoFivePair f).2) ∨
      ((subtwoFivePair e).1 = (subtwoFivePair f).2 ∧
      (subtwoFivePair e).2 = (subtwoFivePair f).1)) : e = f := by
  have ht : ∀ e f : Fin 10,
      (((subtwoFivePair e).1 = (subtwoFivePair f).1 ∧
        (subtwoFivePair e).2 = (subtwoFivePair f).2) ∨
        ((subtwoFivePair e).1 = (subtwoFivePair f).2 ∧
        (subtwoFivePair e).2 = (subtwoFivePair f).1)) → e = f := by decide
  exact ht e f h

namespace SubtwoFivePhysicalData
variable {G} {n : ℕ} (D : G.SubtwoFivePhysicalData n)

def bundleKey (e : Fin 10) : G.V × G.V :=
  G.floorPairKey (D.vertex (subtwoFivePair e).1) (D.vertex (subtwoFivePair e).2)

theorem bundleKey_injective : Function.Injective D.bundleKey := by
  intro e f h
  obtain h | h := G.subtwo_floorPairKey_eq_endpoints _ _ _ _ h
  · exact subtwoFivePair_eq_of_endpoints e f (Or.inl
      ⟨D.vertex_injective h.1, D.vertex_injective h.2⟩)
  · exact subtwoFivePair_eq_of_endpoints e f (Or.inr
      ⟨D.vertex_injective h.1, D.vertex_injective h.2⟩)

theorem bundleKey_internal (e : Fin 10) :
    (D.bundleKey e).1 ∈ D.vertexSet ∧ (D.bundleKey e).2 ∈ D.vertexSet := by
  have hm (v : Fin 5) : D.vertex v ∈ D.vertexSet :=
    Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  unfold bundleKey floorPairKey
  split_ifs <;> exact ⟨hm _, hm _⟩

theorem internal_nonempty_bundle_in_image (k : G.V × G.V)
    (hk : k.1 ∈ D.vertexSet ∧ k.2 ∈ D.vertexSet)
    (hne : G.floorBundle k ≠ ∅) : k ∈ Finset.univ.image D.bundleKey := by
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have heq := G.floorKey_eq_of_mem_floorBundle he
  have hi : G.fst e ∈ D.vertexSet ∧ G.snd e ∈ D.vertexSet := by
    apply (G.subtwo_floorKey_internal D.vertexSet e).mp
    simpa only [heq] using hk
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hi.1
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hi.2
  have hab : a ≠ b := by
    intro h
    exact G.noLoop e (by rw [← ha, ← hb, h])
  refine Finset.mem_image.mpr ⟨subtwoFivePairIndex a b, Finset.mem_univ _, ?_⟩
  unfold bundleKey
  obtain hp | hp := subtwoFivePairIndex_endpoints a b hab
  · rw [hp.1, hp.2, ha, hb, ← G.floorKey_eq_floorPairKey, heq]
  · rw [hp.1, hp.2, hb, ha, subtwo_floorPairKey_comm,
      ← G.floorKey_eq_floorPairKey, heq]

theorem bundleCost_sum_eq_fractional_internal :
    (∑ e : Fin 10, D.bundleCost e) = G.subtwoFractionalInternalBundleCost D.vertexSet / n := by
  classical
  have hi : (Finset.univ.image D.bundleKey) ⊆
      Finset.univ.filter (fun k : G.V × G.V => k.1 ∈ D.vertexSet ∧ k.2 ∈ D.vertexSet) := by
    intro k hk
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, D.bundleKey_internal e⟩
  have hs := Finset.sum_subset hi (f := fun k => (G.floorBundleCover k).cost) (by
    intro k hk hn
    apply G.subtwo_floorBundleCover_cost_zero_of_empty k
    by_contra he
    exact hn (D.internal_nonempty_bundle_in_image k (Finset.mem_filter.mp hk).2 he))
  rw [Finset.sum_image (fun a _ b _ h => D.bundleKey_injective h)] at hs
  rw [Finset.sum_filter] at hs
  change (∑ e : Fin 10, (G.floorBundleCover (D.bundleKey e)).cost) =
    G.subtwoFractionalInternalBundleCost D.vertexSet at hs
  simp only [bundleCost, subtwoPhysicalBundleCost, ← Finset.sum_div]
  exact congrArg (fun x : ℝ => x / n) hs

theorem incident_bundleKey_injective (v : Fin 5) :
    Function.Injective (fun a : Fin 4 => G.floorPairKey (D.vertex v) (D.neighbor v a)) := by
  intro a b h
  obtain h | h := G.subtwo_floorPairKey_eq_endpoints _ _ _ _ h
  · exact D.neighbor_injective v h.2
  · exact False.elim (D.neighbor_ne v b h.1)

theorem incident_bundleCost_sum_le_fractional_incident (v : Fin 5) :
    (∑ a : Fin 4, D.bundleCost (subtwoFivePairIndex v (v.succAbove a))) ≤
      G.subtwoFractionalIncidentBundleCost D.vertexSet (D.vertex v) / n := by
  classical
  let key := fun a : Fin 4 => G.floorPairKey (D.vertex v) (D.neighbor v a)
  let keep := fun k : G.V × G.V =>
    (k.1 ∈ D.vertexSet ∧ k.2 ∈ D.vertexSet) ∧ (k.1 = D.vertex v ∨ k.2 = D.vertex v)
  have hv (a : Fin 5) : D.vertex a ∈ D.vertexSet :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hkeep (a : Fin 4) : keep (key a) := by
    dsimp only [keep, key, neighbor]
    unfold floorPairKey
    split_ifs <;> simp only [hv, and_true, eq_self, true_or, or_true]
  have hi : Finset.univ.image key ⊆ Finset.univ.filter keep := by
    intro k hk
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkeep a⟩
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hi
    (fun k _ _ => (G.floorBundleCover k).cost_nonneg)
  rw [Finset.sum_image (fun a _ b _ h => D.incident_bundleKey_injective v h),
    Finset.sum_filter] at hs
  change (∑ a : Fin 4, (G.floorBundleCover (key a)).cost) ≤
    G.subtwoFractionalIncidentBundleCost D.vertexSet (D.vertex v) at hs
  simp only [D.bundleCost_incident, subtwoPhysicalBundleCost, ← Finset.sum_div]
  exact div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)

end SubtwoFivePhysicalData
end
end WeightedEdgeColoring.WeightedMultigraph
