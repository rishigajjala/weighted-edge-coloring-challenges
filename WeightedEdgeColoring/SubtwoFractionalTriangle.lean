import WeightedEdgeColoring.WeightedMultigraph
import Mathlib.Tactic

/-!
# Fractional triangle coloring directly from local bin packings

Half of every local star packing covers every edge exactly once. Every
individual local bin is a feasible global weighted color. On three
vertices the resulting total mass is `3n/2`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- A finite fractional weighted coloring with exact unit edge coverage. -/
structure SubtwoFractionalColoring where
  P : Type u
  fintypeP : Fintype P
  pattern : P → Finset G.E
  mass : P → ℝ
  mass_nonneg : ∀ p, 0 ≤ mass p
  feasible : ∀ p v, (∑ e ∈ pattern p, if G.Inc v e then G.weight e else 0) ≤ 1
  covers : ∀ e, (∑ p, if e ∈ pattern p then mass p else 0) = 1

attribute [instance] SubtwoFractionalColoring.fintypeP

noncomputable def SubtwoFractionalColoring.cost (C : G.SubtwoFractionalColoring) : ℝ :=
  ∑ p, C.mass p

/-- The physical edge set in one bin of one vertex star. -/
noncomputable def subtwoStarBin {n : ℕ} {v : G.V}
    (bin : G.StarEdge v → Fin n) (i : Fin n) : Finset G.E := by
  classical
  exact (Finset.univ.filter fun e : G.StarEdge v ↦ bin e = i).image Subtype.val

theorem mem_subtwoStarBin {n : ℕ} {v : G.V}
    (bin : G.StarEdge v → Fin n) (i : Fin n) (e : G.E) :
    e ∈ G.subtwoStarBin bin i ↔ ∃ h : G.Inc v e, bin ⟨e, h⟩ = i := by
  classical
  simp only [subtwoStarBin, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨⟨f, hf⟩, hb, rfl⟩
    exact ⟨hf, hb⟩
  · rintro ⟨h, hb⟩
    exact ⟨⟨e, h⟩, hb, rfl⟩

theorem sum_weight_subtwoStarBin {n : ℕ} {v : G.V}
    (bin : G.StarEdge v → Fin n) (i : Fin n) :
    (∑ e ∈ G.subtwoStarBin bin i, G.weight e) = G.starBinLoad bin i := by
  classical
  unfold subtwoStarBin starBinLoad
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
  · intro a _ b _ h
    exact Subtype.ext h

/-- A bin feasible at its central vertex is a feasible weighted color at
every vertex, because every other load is a sub-sum of its total weight. -/
theorem subtwoStarBin_feasible {n : ℕ} {v : G.V}
    (bin : G.StarEdge v → Fin n) (hbin : ∀ i, G.starBinLoad bin i ≤ 1)
    (i : Fin n) (w : G.V) :
    (∑ e ∈ G.subtwoStarBin bin i, if G.Inc w e then G.weight e else 0) ≤ 1 := by
  calc
    _ ≤ ∑ e ∈ G.subtwoStarBin bin i, G.weight e := by
      apply Finset.sum_le_sum
      intro e _
      split_ifs
      · rfl
      · exact G.weight_nonneg e
    _ = G.starBinLoad bin i := G.sum_weight_subtwoStarBin bin i
    _ ≤ 1 := hbin i

/-- Every indexed edge has exactly two distinct incident vertices. -/
theorem subtwo_sum_incidence_half (e : G.E) :
    (∑ v : G.V, if G.Inc v e then (1 / 2 : ℝ) else 0) = 1 := by
  classical
  have he (v : G.V) :
      (if G.Inc v e then (1 / 2 : ℝ) else 0) =
        (if G.fst e = v then (1 / 2 : ℝ) else 0) +
        (if G.snd e = v then (1 / 2 : ℝ) else 0) := by
    by_cases hf : G.fst e = v <;> by_cases hs : G.snd e = v
    · exact (G.noLoop e (hf.trans hs.symm)).elim
    all_goals simp [Inc, hf, hs]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  norm_num

/-- The half-star construction is a genuine fractional coloring; no
rounding or asymptotic coloring theorem is used. -/
theorem exists_subtwoFractionalColoring_of_local {n : ℕ}
    (hlocal : G.LocallyPacksInto n) :
    ∃ C : G.SubtwoFractionalColoring,
      C.cost = (Fintype.card G.V : ℝ) * n / 2 := by
  classical
  choose bin hbin using hlocal
  let C : G.SubtwoFractionalColoring :=
    { P := G.V × Fin n
      fintypeP := inferInstance
      pattern := fun p ↦ G.subtwoStarBin (bin p.1) p.2
      mass := fun _ ↦ 1 / 2
      mass_nonneg := fun _ ↦ by norm_num
      feasible := fun p v ↦ G.subtwoStarBin_feasible (bin p.1) (hbin p.1) p.2 v
      covers := by
        intro e
        rw [Fintype.sum_prod_type]
        have hh (v : G.V) :
            (∑ i : Fin n, if e ∈ G.subtwoStarBin (bin v) i then (1 / 2 : ℝ) else 0) =
              if G.Inc v e then (1 / 2 : ℝ) else 0 := by
          by_cases hv : G.Inc v e
          · simp [G.mem_subtwoStarBin, hv]
          · simp [G.mem_subtwoStarBin, hv]
        simp_rw [hh]
        exact G.subtwo_sum_incidence_half e }
  refine ⟨C, ?_⟩
  simp [SubtwoFractionalColoring.cost, C]
  ring

/-- On three vertices, half of the three local star packings has mass
`3n/2`, including arbitrary positive weights and parallel edges. -/
theorem exists_subtwoFractionalColoring_triangle {n : ℕ}
    (hV : Fintype.card G.V = 3) (hlocal : G.LocallyPacksInto n) :
    ∃ C : G.SubtwoFractionalColoring, C.cost = (3 / 2 : ℝ) * n := by
  obtain ⟨C, hC⟩ := G.exists_subtwoFractionalColoring_of_local hlocal
  refine ⟨C, ?_⟩
  rw [hC, hV]
  push_cast
  ring

end WeightedEdgeColoring.WeightedMultigraph

namespace WeightedEdgeColoring.Subtwo

/-- The reserved fraction leaves a common fraction `s` of each bundle.
This is the exact use of the upper bound of one on a bundle cost. -/
theorem triangle_reserved_fraction_le {t q s : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hs : 0 ≤ s)
    (hq : q ≤ t - s) : q / t ≤ 1 - s := by
  apply (div_le_iff₀ ht).2
  nlinarith

/-- Separate residual bundle packing plus half of each local star packing
has the palette cost used in the triangle restoration. -/
theorem triangle_palette_cost_identity (t q : Fin 3 → ℝ) (s : ℝ)
    (ht : ∀ i, t i ≠ 0) :
    (∑ i, q i) + (∑ i, (1 - s - q i / t i) * t i) + 3 * s / 2 =
      (∑ i, t i) - s * (∑ i, t i) + 3 * s / 2 := by
  have hi (i : Fin 3) : (1 - s - q i / t i) * t i =
      t i - s * t i - q i := by field_simp [ht i]
  simp_rw [hi]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The total restoration cost is at most `1 + M/2` on the required
interval. This proves the quadratic estimate without calculus. -/
theorem triangle_palette_cost_le {M T : ℝ}
    (hM : (3 / 2 : ℝ) ≤ M) (hT : T ≤ 2) :
    T - (T - M) * (T - 3 / 2) ≤ 1 + M / 2 := by
  have hprod : 0 ≤ (2 - T) * (M + 1 / 2 - T) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- The chosen rational constants leave a strict margin for rounding. -/
theorem triangle_palette_cost_lt_kappa {T : ℝ} (hT : T ≤ 2) :
    T - (T - (1691031 / 1000000 : ℝ)) * (T - 3 / 2) < 1999 / 1000 := by
  have h := triangle_palette_cost_le
    (M := (1691031 / 1000000 : ℝ)) (T := T) (by norm_num) hT
  linarith

end WeightedEdgeColoring.Subtwo
