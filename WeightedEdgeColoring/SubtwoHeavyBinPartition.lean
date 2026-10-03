import WeightedEdgeColoring.SubtwoFractionalStarDemand
import WeightedEdgeColoring.SubtwoSharedHeavyPattern

/-!
# Partitioning actual local bins by their heavy type

A bin of load at most one contains at most one item of weight greater
than one half. Its type occurs once. Consequently the mass of bins with
a fixed heavy type is its demand at either endpoint, even when the two
local packings have different distributions.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

namespace SubtwoLocalFractionalBins

/-- Delete counts outside the star. This preserves every required demand. -/
noncomputable def starRestrict {demand : G.E → ℝ}
    (B : G.SubtwoLocalFractionalBins demand) : G.SubtwoLocalFractionalBins demand where
  P := B.P
  fintypeP := B.fintypeP
  pattern := fun v p e ↦ if G.Inc v e then B.pattern v p e else 0
  mass := B.mass
  mass_nonneg := B.mass_nonneg
  bin_feasible := by
    intro v p
    refine le_trans (Finset.sum_le_sum ?_) (B.bin_feasible v p)
    intro e _
    split_ifs
    · rfl
    · simpa using mul_nonneg (Nat.cast_nonneg (B.pattern v p e)) (G.weight_nonneg e)
  covers := by
    intro v e
    by_cases he : G.Inc v e
    · simpa [he] using B.covers v e
    · simp [he]

theorem starRestrict_support {demand : G.E → ℝ}
    (B : G.SubtwoLocalFractionalBins demand) (v : G.V) (p : B.P) (e : G.E)
    (he : ¬G.Inc v e) : (B.starRestrict G).pattern v p e = 0 := by
  simp [starRestrict, he]

end SubtwoLocalFractionalBins

/-- Two heavy types cannot both occur in a unit bin. -/
theorem subtwo_heavy_type_unique (n : G.E → ℕ)
    (hload : (∑ e, (n e : ℝ) * G.weight e) ≤ 1)
    (e f : G.E) (he : (1 / 2 : ℝ) < G.weight e)
    (hf : (1 / 2 : ℝ) < G.weight f) (hne : n e ≠ 0) (hnf : n f ≠ 0) : e = f := by
  classical
  by_contra hef
  have hc_e : (1 : ℝ) ≤ n e := by exact_mod_cast (show 1 ≤ n e by omega)
  have hc_f : (1 : ℝ) ≤ n f := by exact_mod_cast (show 1 ≤ n f by omega)
  have htwo : (n e : ℝ) * G.weight e + (n f : ℝ) * G.weight f ≤ 1 := by
    calc
      _ = ∑ g ∈ ({e, f} : Finset G.E), (n g : ℝ) * G.weight g := by simp [hef]
      _ ≤ ∑ g, (n g : ℝ) * G.weight g := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun g _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (G.weight_nonneg g))
      _ ≤ 1 := hload
  nlinarith [mul_le_mul_of_nonneg_right hc_e (G.weight_nonneg e),
    mul_le_mul_of_nonneg_right hc_f (G.weight_nonneg f)]

/-- `none` means that every item is light. -/
noncomputable def subtwoHeavyTag (n : G.E → ℕ) : Option G.E :=
  if H : ∃ e, (1 / 2 : ℝ) < G.weight e ∧ n e ≠ 0 then some H.choose else none

theorem subtwoHeavyTag_some_iff (n : G.E → ℕ)
    (hload : (∑ e, (n e : ℝ) * G.weight e) ≤ 1) (e : G.E) :
    G.subtwoHeavyTag n = some e ↔ (1 / 2 : ℝ) < G.weight e ∧ n e ≠ 0 := by
  classical
  unfold subtwoHeavyTag
  split_ifs with H
  · constructor
    · intro h
      have hc : H.choose = e := Option.some.inj h
      simpa only [hc] using H.choose_spec
    · rintro ⟨he, hn⟩
      have hc := G.subtwo_heavy_type_unique n hload H.choose e
        H.choose_spec.1 he H.choose_spec.2 hn
      exact congrArg some hc
  · simp only [false_iff]
    exact fun he ↦ H ⟨e, he⟩

theorem subtwoHeavyTag_none_iff (n : G.E → ℕ) :
    G.subtwoHeavyTag n = none ↔ ∀ e, n e ≠ 0 → G.weight e ≤ 1 / 2 := by
  classical
  unfold subtwoHeavyTag
  split_ifs with H
  · constructor
    · simp
    · intro h
      exact False.elim (not_lt_of_ge (h H.choose H.choose_spec.2) H.choose_spec.1)
  · simp only [true_iff]
    intro e hn
    exact le_of_not_gt fun he ↦ H ⟨e, he, hn⟩

theorem subtwoHeavyTag_count (n : G.E → ℕ)
    (hload : (∑ e, (n e : ℝ) * G.weight e) ≤ 1) (e : G.E)
    (he : (1 / 2 : ℝ) < G.weight e) :
    n e = if G.subtwoHeavyTag n = some e then 1 else 0 := by
  classical
  by_cases hn : n e = 0
  · have ht : G.subtwoHeavyTag n ≠ some e := by
      intro ht
      exact ((G.subtwoHeavyTag_some_iff n hload e).mp ht).2 hn
    simp [hn, ht]
  · have ht := (G.subtwoHeavyTag_some_iff n hload e).mpr ⟨he, hn⟩
    simp [ht, G.subtwo_heavy_count_eq_one e n he hn hload]

theorem subtwoHeavyTag_incident (v : G.V) (n : G.E → ℕ)
    (hload : (∑ e, (n e : ℝ) * G.weight e) ≤ 1)
    (hsupport : ∀ e, ¬G.Inc v e → n e = 0) (e : G.E)
    (htag : G.subtwoHeavyTag n = some e) : G.Inc v e := by
  by_contra hi
  exact ((G.subtwoHeavyTag_some_iff n hload e).mp htag).2 (hsupport e hi)

namespace SubtwoLocalFractionalBins

/-- The heavy-type mass is exactly its demand at each endpoint. -/
theorem heavyTag_mass {demand : G.E → ℝ}
    (B : G.SubtwoLocalFractionalBins demand) (v : G.V) (e : G.E)
    (he : (1 / 2 : ℝ) < G.weight e) :
    (∑ p, if G.subtwoHeavyTag (B.pattern v p) = some e then B.mass v p else 0) =
      if G.Inc v e then demand e else 0 := by
  classical
  rw [← B.covers v e]
  apply Finset.sum_congr rfl
  intro p _
  rw [G.subtwoHeavyTag_count (B.pattern v p) (B.bin_feasible v p) e he]
  split_ifs <;> simp

/-- A light type is never the label of a heavy bin. -/
theorem lightTag_mass {demand : G.E → ℝ}
    (B : G.SubtwoLocalFractionalBins demand) (v : G.V) (e : G.E)
    (he : G.weight e ≤ 1 / 2) :
    (∑ p, if G.subtwoHeavyTag (B.pattern v p) = some e then B.mass v p else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro p _
  have ht : G.subtwoHeavyTag (B.pattern v p) ≠ some e := by
    intro ht
    exact not_lt_of_ge he
      ((G.subtwoHeavyTag_some_iff (B.pattern v p) (B.bin_feasible v p) e).mp ht).1
  simp [ht]

end SubtwoLocalFractionalBins

end WeightedEdgeColoring.WeightedMultigraph
