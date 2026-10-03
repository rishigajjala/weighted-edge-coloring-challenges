import WeightedEdgeColoring.FiniteHarmonicPacketColoring

/-!
# Encoding non-tiny harmonic classes

If every edge has weight at least `1 / T`, then its harmonic index
`floor (1 / w)` lies in `{1, ..., T}`.  This file records the corresponding
zero-based element of `Fin T`, proves that its represented class size is the
harmonic index, and feeds those facts into the finite harmonic-packet
coloring certificate.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable {G : WeightedMultigraph.{u}}

/-- The zero-based finite harmonic class of an edge whose weight is at least
`1 / T`.  Its value is `floor (1 / weight e) - 1`. -/
def finiteHarmonicClassOf (T : ℕ) (hT : 0 < T)
    (hlower : ∀ e, (1 : ℝ) / T ≤ G.weight e) (e : G.E) : Fin T := by
  let r : ℕ := ⌊(1 : ℝ) / G.weight e⌋₊
  have hw : 0 < G.weight e := G.weight_pos e
  have hinv_nonneg : 0 ≤ (1 : ℝ) / G.weight e :=
    div_nonneg zero_le_one hw.le
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hinv_le_T : (1 : ℝ) / G.weight e ≤ T := by
    apply (div_le_iff₀ hw).2
    have h := (div_le_iff₀ hTR).1 (hlower e)
    nlinarith
  have hr_le : r ≤ T := by
    have hr_cast : (r : ℝ) ≤ (1 : ℝ) / G.weight e := by
      simpa [r] using Nat.floor_le hinv_nonneg
    exact_mod_cast hr_cast.trans hinv_le_T
  exact ⟨r - 1, by omega⟩

@[simp] theorem finiteHarmonicClassOf_val (T : ℕ) (hT : 0 < T)
    (hlower : ∀ e, (1 : ℝ) / T ≤ G.weight e) (e : G.E) :
    (G.finiteHarmonicClassOf T hT hlower e).1 =
      ⌊(1 : ℝ) / G.weight e⌋₊ - 1 := by
  rfl

/-- The represented one-based class size is exactly `floor (1 / weight e)`. -/
theorem finiteClassSize_finiteHarmonicClassOf (T : ℕ) (hT : 0 < T)
    (hlower : ∀ e, (1 : ℝ) / T ≤ G.weight e) (e : G.E) :
    finiteClassSize (G.finiteHarmonicClassOf T hT hlower e) =
      ⌊(1 : ℝ) / G.weight e⌋₊ := by
  let r : ℕ := ⌊(1 : ℝ) / G.weight e⌋₊
  have hw : 0 < G.weight e := G.weight_pos e
  have hinv_nonneg : 0 ≤ (1 : ℝ) / G.weight e :=
    div_nonneg zero_le_one hw.le
  have hone_le_inv : (1 : ℝ) ≤ (1 : ℝ) / G.weight e := by
    rw [le_div_iff₀ hw]
    simpa using G.weight_le_one e
  have hr_pos : 0 < r := by
    have : 1 ≤ r := by
      apply (Nat.le_floor_iff hinv_nonneg).2
      simpa [r] using hone_le_inv
    omega
  change (r - 1) + 1 = r
  omega

/-- A non-tiny edge in harmonic class `r` has weight at most `1 / r`. -/
theorem weight_le_inv_finiteClassSize_finiteHarmonicClassOf
    (T : ℕ) (hT : 0 < T)
    (hlower : ∀ e, (1 : ℝ) / T ≤ G.weight e) (e : G.E) :
    G.weight e ≤
      (1 : ℝ) / finiteClassSize (G.finiteHarmonicClassOf T hT hlower e) := by
  let r : ℕ := ⌊(1 : ℝ) / G.weight e⌋₊
  have hw : 0 < G.weight e := G.weight_pos e
  have hinv_nonneg : 0 ≤ (1 : ℝ) / G.weight e :=
    div_nonneg zero_le_one hw.le
  have hone_le_inv : (1 : ℝ) ≤ (1 : ℝ) / G.weight e := by
    rw [le_div_iff₀ hw]
    simpa using G.weight_le_one e
  have hr_pos : 0 < r := by
    have : 1 ≤ r := by
      apply (Nat.le_floor_iff hinv_nonneg).2
      simpa [r] using hone_le_inv
    omega
  have hr_cast : (r : ℝ) ≤ (1 : ℝ) / G.weight e := by
    simpa [r] using Nat.floor_le hinv_nonneg
  rw [G.finiteClassSize_finiteHarmonicClassOf T hT hlower e]
  apply (le_div_iff₀ (by exact_mod_cast hr_pos : (0 : ℝ) < r)).2
  simpa [mul_comm] using (le_div_iff₀ hw).1 hr_cast

/-- The preceding bound with the harmonic index displayed explicitly. -/
theorem weight_le_inv_floor_of_weight_ge_inv
    (T : ℕ) (hT : 0 < T)
    (hlower : ∀ e, (1 : ℝ) / T ≤ G.weight e) (e : G.E) :
    G.weight e ≤ (1 : ℝ) / ⌊(1 : ℝ) / G.weight e⌋₊ := by
  rw [← G.finiteClassSize_finiteHarmonicClassOf T hT hlower e]
  exact G.weight_le_inv_finiteClassSize_finiteHarmonicClassOf T hT hlower e

/-- Harmonic charge is exactly the reciprocal of the represented finite
class size. -/
theorem harmonicCharge_eq_inv_finiteClassSize_finiteHarmonicClassOf
    (T : ℕ) (hT : 0 < T)
    (hlower : ∀ e, (1 : ℝ) / T ≤ G.weight e) (e : G.E) :
    harmonicCharge (G.weight e) =
      (1 : ℝ) / finiteClassSize (G.finiteHarmonicClassOf T hT hlower e) := by
  unfold harmonicCharge
  rw [G.finiteClassSize_finiteHarmonicClassOf T hT hlower e]

/-- Harmonic charge is `1 / r` for the explicit index
`r = floor (1 / weight e)`. -/
theorem harmonicCharge_eq_inv_floor_of_weight_ge_inv
    (T : ℕ) (hT : 0 < T)
    (hlower : ∀ e, (1 : ℝ) / T ≤ G.weight e) (e : G.E) :
    harmonicCharge (G.weight e) =
      (1 : ℝ) / ⌊(1 : ℝ) / G.weight e⌋₊ := by
  rw [← G.finiteClassSize_finiteHarmonicClassOf T hT hlower e]
  exact G.harmonicCharge_eq_inv_finiteClassSize_finiteHarmonicClassOf
    T hT hlower e

/-- The colored finite harmonic-packet certificate for a graph whose edge
weights are all at least `1 / T`, using the canonical floor classes. -/
theorem exists_finiteHarmonicPacketColoringCertificate_of_weight_ge_inv
    (T : ℕ) (hT : 0 < T)
    (hlower : ∀ e, (1 : ℝ) / T ≤ G.weight e)
    (b : G.Bipartition)
    (K : ℕ) (hK : 0 < K) (A margin : ℝ) (hmargin : 0 ≤ margin)
    (hpalette : A + margin ≤ (K : ℝ))
    (horiginal : ∀ v,
      (∑ e : G.E,
        if G.Inc v e then harmonicCharge (G.weight e) else 0) ≤ A) :
    Nonempty (G.FiniteHarmonicPacketColoringCertificate b
      (G.finiteHarmonicClassOf T hT hlower) K) := by
  apply G.exists_finiteHarmonicPacketColoringCertificate
    b (G.finiteHarmonicClassOf T hT hlower)
    (fun e ↦ G.weight_le_inv_finiteClassSize_finiteHarmonicClassOf
      T hT hlower e)
    (fun e ↦ G.harmonicCharge_eq_inv_finiteClassSize_finiteHarmonicClassOf
      T hT hlower e)
    K hK A margin hmargin hpalette horiginal

end

end WeightedMultigraph
end WeightedEdgeColoring
