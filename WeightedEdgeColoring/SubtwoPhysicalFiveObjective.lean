import WeightedEdgeColoring.SubtwoPhysicalFiveCoordinates
import WeightedEdgeColoring.SubtwoSparseRowBridge

/-!
# The certificate objective is the physical palette-dual expression

Physical edge prices may differ even on edges of equal weight. The ten
bundle demand prices recover their actual internal sum exactly.
-/

open scoped BigOperators
set_option autoImplicit false

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ}
open SubtwoRationalCertificate

def subtwoFiveObjectiveRow : List (Fin 970 × ℚ) :=
  (List.ofFn fun e : Fin 10 => (⟨85 + e.val, by omega⟩, 1)) ++
    (List.ofFn fun v : Fin 5 => (⟨95 + v.val, by omega⟩, 1))

def subtwoFiveObjectiveCoefficients : Fin 970 → ℚ := sparseRowCoefficients subtwoFiveObjectiveRow

namespace SubtwoFivePhysicalData
variable (D : G.SubtwoFivePhysicalData n)

theorem vector_objective_eq :
    (∑ k : Fin 970, (subtwoFiveObjectiveCoefficients k : ℝ) * D.vector k) =
      (∑ e : Fin 10, D.demandPrice e) + ∑ v : Fin 5, D.avoidingLoss v := by
  unfold subtwoFiveObjectiveCoefficients
  rw [← realSparseRowEval_eq_dot]
  simp only [subtwoFiveObjectiveRow, realSparseRowEval_append, realSparseRowEval_ofFn,
    Rat.cast_one, one_mul, D.vector_demandPrice, D.vector_avoidingLoss]

theorem sum_over_bundleKeys_eq_internal (f : G.V × G.V → ℝ)
    (hzero : ∀ k, G.floorBundle k = ∅ → f k = 0) :
    (∑ e : Fin 10, f (D.bundleKey e)) =
      ∑ k : G.V × G.V, if k.1 ∈ D.vertexSet ∧ k.2 ∈ D.vertexSet then f k else 0 := by
  classical
  have hi : (Finset.univ.image D.bundleKey) ⊆
      Finset.univ.filter (fun k : G.V × G.V => k.1 ∈ D.vertexSet ∧ k.2 ∈ D.vertexSet) := by
    intro k hk
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, D.bundleKey_internal e⟩
  have hs := Finset.sum_subset hi (f := f) (by
    intro k hk hn
    apply hzero k
    by_contra he
    exact hn (D.internal_nonempty_bundle_in_image k (Finset.mem_filter.mp hk).2 he))
  rw [Finset.sum_image (fun a _ b _ h => D.bundleKey_injective h), Finset.sum_filter] at hs
  exact hs

theorem demandPrice_sum_eq_internal_price :
    (∑ e : Fin 10, D.demandPrice e) =
      G.subtwoInternalCost D.price D.vertexSet / ((n : ℝ) * G.subtwoColorPriceMax D.price) := by
  classical
  have hs := D.sum_over_bundleKeys_eq_internal
    (fun k => ∑ e ∈ G.floorBundle k, D.price e) (by
      intro k hk
      dsimp only
      rw [hk, Finset.sum_empty])
  have ht : (∑ k : G.V × G.V,
      if k.1 ∈ D.vertexSet ∧ k.2 ∈ D.vertexSet then
        ∑ e ∈ G.floorBundle k, D.price e else 0) = G.subtwoInternalCost D.price D.vertexSet := by
    calc
      _ = ∑ k : G.V × G.V, ∑ e ∈ G.floorBundle k,
          if k.1 ∈ D.vertexSet ∧ k.2 ∈ D.vertexSet then D.price e else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> simp
      _ = ∑ e : G.E, if (G.floorKey e).1 ∈ D.vertexSet ∧ (G.floorKey e).2 ∈ D.vertexSet
          then D.price e else 0 := G.subtwo_sum_floorBundles _
      _ = _ := by
        unfold subtwoInternalCost
        simp only [G.subtwo_floorKey_internal]
  simp only [demandPrice, subtwoPhysicalBundlePrice, ← Finset.sum_div]
  exact congrArg (fun x : ℝ => x / ((n : ℝ) * G.subtwoColorPriceMax D.price)) (hs.trans ht)

theorem palette_dual_objective_identity :
    ((n : ℝ) * G.subtwoColorPriceMax D.price) *
      ((∑ e : Fin 10, D.demandPrice e) + ∑ v : Fin 5, D.avoidingLoss v) =
      G.subtwoInternalCost D.price D.vertexSet +
        ∑ v : Fin 5, G.subtwoExteriorHarmonicCharge D.vertexSet (D.vertex v) *
          (G.subtwoColorPriceMax D.price - G.subtwoAvoidingPriceMax D.price (D.vertex v)) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt D.n_pos)
  have hR : G.subtwoColorPriceMax D.price ≠ 0 := D.price_max_pos.ne'
  have hv (v : Fin 5) : ((n : ℝ) * G.subtwoColorPriceMax D.price) * D.avoidingLoss v =
      G.subtwoExteriorHarmonicCharge D.vertexSet (D.vertex v) *
        (G.subtwoColorPriceMax D.price - G.subtwoAvoidingPriceMax D.price (D.vertex v)) := by
    unfold avoidingLoss subtwoAvoidingPriceLoss exteriorCharge subtwoNormalizedAvoidingPrice
    field_simp
  rw [mul_add, D.demandPrice_sum_eq_internal_price, mul_div_cancel₀ _ (mul_ne_zero hn hR),
    Finset.mul_sum]
  simp only [hv]

/-- This bridge uses the exact encoded objective only after the actual
physical vector has been proved feasible for the selected frozen matrix. -/
theorem physical_objective_lt_of_certificate {m : ℕ}
    (P : Problem m 970)
    (hc : ∀ k, P.c k = subtwoFiveObjectiveCoefficients k)
    (hcertificate : ∀ x : Fin 970 → ℝ, P.RealFeasible x → P.realObjective x < (1999 / 1000 : ℝ))
    (hfeasible : P.RealFeasible D.vector) :
    (∑ e : Fin 10, D.demandPrice e) + ∑ v : Fin 5, D.avoidingLoss v < 1999 / 1000 := by
  have h := hcertificate D.vector hfeasible
  unfold Problem.realObjective at h
  simpa only [hc, D.vector_objective_eq] using h

end SubtwoFivePhysicalData
end
end WeightedEdgeColoring.WeightedMultigraph
