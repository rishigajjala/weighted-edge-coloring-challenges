import WeightedEdgeColoring.HarmonicBinCharge
import Mathlib.Tactic

/-!
# Bin geometry and averaged dense-five profile rows

This module proves necessary inequalities from finite weighted local bins.
Its averaged rows take the relevant one-bin rank bounds as explicit
hypotheses. The heavy-bin load inequalities and their harmonic charge caps
follow here from unit load and the definition of `harmonicCharge`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.SubtwoBinProfileRows

/-- In an `H(i,j)` bin the heavy projection has load above one half and
`j` is at least as large as either remaining projection. The two smaller
loads are together below one third, and each is below one fourth. -/
theorem heavy_bin_smaller_loads (heavy second small₁ small₂ : ℝ)
    (hheavy : 1 / 2 < heavy)
    (hsmall₁ : 0 ≤ small₁) (hsmall₂ : 0 ≤ small₂)
    (hsecond₁ : small₁ ≤ second) (hsecond₂ : small₂ ≤ second)
    (hload : heavy + second + small₁ + small₂ ≤ 1) :
    small₁ + small₂ < 1 / 3 ∧
      small₁ < 1 / 4 ∧ small₂ < 1 / 4 := by
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The two smaller projections can be repeated three times within unit
capacity; this is the load fact used by the small-price row. -/
theorem three_smaller_pairs_fit (heavy second small₁ small₂ : ℝ)
    (hheavy : 1 / 2 < heavy)
    (hsmall₁ : 0 ≤ small₁) (hsmall₂ : 0 ≤ small₂)
    (hsecond₁ : small₁ ≤ second) (hsecond₂ : small₂ ≤ second)
    (hload : heavy + second + small₁ + small₂ ≤ 1) :
    3 * (small₁ + small₂) < 1 := by
  have h := (heavy_bin_smaller_loads heavy second small₁ small₂
    hheavy hsmall₁ hsmall₂ hsecond₁ hsecond₂ hload).1
  linarith

/-- Harmonic charge of a positive projection is at most `1/r` whenever
its load is at most `1/r`. -/
theorem harmonicCharge_le_inv_of_le {w : ℝ} {r : ℕ}
    (hr : 0 < r) (hw : 0 < w) (hwr : w ≤ (1 : ℝ) / r) :
    harmonicCharge w ≤ (1 : ℝ) / r := by
  let k : ℕ := ⌊(1 : ℝ) / w⌋₊
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hwr' : w * (r : ℝ) ≤ 1 := (le_div_iff₀ hrR).1 hwr
  have hrk : r ≤ k := by
    apply (Nat.le_floor_iff (div_nonneg zero_le_one hw.le)).2
    rw [le_div_iff₀ hw]
    nlinarith
  have hrkR : (r : ℝ) ≤ k := by exact_mod_cast hrk
  unfold harmonicCharge
  change (1 : ℝ) / k ≤ 1 / r
  exact one_div_le_one_div_of_le hrR hrkR

/-- An `N`-class projection has harmonic charge at most one half. -/
theorem normal_projection_charge_le_half {w : ℝ}
    (hw : 0 < w) (hhalf : w ≤ 1 / 2) :
    harmonicCharge w ≤ 1 / 2 := by
  exact harmonicCharge_le_inv_of_le (r := 2) (by decide) hw hhalf

/-- Either smaller projection in an `H(i,j)` bin has harmonic charge at
most one fourth. -/
theorem heavy_bin_smaller_charge_le_quarter
    (heavy second small₁ small₂ : ℝ)
    (hheavy : 1 / 2 < heavy)
    (hsecond₁ : small₁ ≤ second) (hsecond₂ : small₂ ≤ second)
    (hload : heavy + second + small₁ + small₂ ≤ 1)
    (hsmall₁ : 0 < small₁) (hsmall₂ : 0 < small₂) :
    harmonicCharge small₁ ≤ 1 / 4 ∧
      harmonicCharge small₂ ≤ 1 / 4 := by
  obtain ⟨_, h₁, h₂⟩ := heavy_bin_smaller_loads heavy second small₁ small₂
    hheavy hsmall₁.le hsmall₂.le hsecond₁ hsecond₂ hload
  exact ⟨harmonicCharge_le_inv_of_le (r := 4) (by decide) hsmall₁ h₁.le,
    harmonicCharge_le_inv_of_le (r := 4) (by decide) hsmall₂ h₂.le⟩

/-- The singleton harmonic ranks in an `H(i,j)` bin: heavy, second, and
both remaining projections have caps `1, 1/2, 1/4, 1/4`. -/
theorem heavy_bin_singleton_charge_ranks
    (heavy second small₁ small₂ : ℝ)
    (hheavy : 1 / 2 < heavy)
    (hsecond : 0 < second)
    (hsmall₁ : 0 < small₁) (hsmall₂ : 0 < small₂)
    (hsecond₁ : small₁ ≤ second) (hsecond₂ : small₂ ≤ second)
    (hload : heavy + second + small₁ + small₂ ≤ 1) :
    harmonicCharge heavy = 1 ∧
    harmonicCharge second ≤ 1 / 2 ∧
    harmonicCharge small₁ ≤ 1 / 4 ∧
    harmonicCharge small₂ ≤ 1 / 4 := by
  have hheavy_le : heavy ≤ 1 := by linarith
  have hsecond_le : second ≤ 1 / 2 := by linarith
  have hhead : harmonicCharge heavy = 1 := by
    have h := harmonicCharge_eq_of_band (r := 1) (by decide)
      (by linarith : 0 < heavy) (by simpa using hheavy_le)
      (by norm_num; linarith)
    simpa using h
  have htail := heavy_bin_smaller_charge_le_quarter heavy second small₁ small₂
    hheavy hsecond₁ hsecond₂ hload hsmall₁ hsmall₂
  exact ⟨hhead, normal_projection_charge_le_half hsecond hsecond_le,
    htail.1, htail.2⟩

/-- The mass of any selected class of bins is at most one when the whole
fractional packing has mass at most one. -/
theorem selected_bin_mass_le_one {B : Type*} [Fintype B]
    (selected : Finset B) (mass : B → ℝ)
    (hmass : ∀ b, 0 ≤ mass b)
    (htotal : (∑ b, mass b) ≤ 1) :
    (∑ b ∈ selected, mass b) ≤ 1 := by
  have hsubset : selected ⊆ Finset.univ := Finset.subset_univ _
  have hsum : (∑ b ∈ selected, mass b) ≤ ∑ b, mass b := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro b hb hnot
    exact hmass b
  exact hsum.trans htotal

/-- If the two price contributions in each selected `H(i,j)` bin sum to
at most its mass, their aggregate satisfies `Bᵢⱼ+Sᵢⱼ≤μᵢⱼ`. -/
theorem big_add_small_le_class_mass {B : Type*}
    (selected : Finset B) (mass big small : B → ℝ)
    (hmass : ∀ b ∈ selected, 0 ≤ mass b)
    (hprice : ∀ b ∈ selected, big b + small b ≤ 1) :
    (∑ b ∈ selected, mass b * big b) +
      (∑ b ∈ selected, mass b * small b) ≤
        ∑ b ∈ selected, mass b := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b hb
  rw [← mul_add]
  simpa using mul_le_mul_of_nonneg_left (hprice b hb) (hmass b hb)

/-- A finite weighted average of the one-bin harmonic resource bound
gives the LP row `∑ tᵤ + q ≤ M`. Here `internal` and `external` are the
actual per-bin charge contributions, and the cost domination premises are
the separate bundle-packing projection step. -/
theorem harmonic_resource_row {B : Type*} [Fintype B]
    (mass : B → ℝ) (internal : B → Fin 4 → ℝ)
    (external : B → ℝ) (t : Fin 4 → ℝ) (q M : ℝ)
    (hmass : ∀ b, 0 ≤ mass b) (htotal : (∑ b, mass b) ≤ 1)
    (hM : 0 ≤ M)
    (hbin : ∀ b, (∑ u, internal b u) + external b ≤ M)
    (ht : ∀ u, t u ≤ ∑ b, mass b * internal b u)
    (hq : q ≤ ∑ b, mass b * external b) :
    (∑ u, t u) + q ≤ M := by
  have hcost : (∑ u, t u) + q ≤
      (∑ u, ∑ b, mass b * internal b u) +
        ∑ b, mass b * external b :=
    add_le_add (Finset.sum_le_sum fun u _ => ht u) hq
  have hswap :
      (∑ u, ∑ b, mass b * internal b u) +
        ∑ b, mass b * external b =
      ∑ b, mass b * ((∑ u, internal b u) + external b) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  calc
    (∑ u, t u) + q ≤
        (∑ u, ∑ b, mass b * internal b u) +
          ∑ b, mass b * external b := hcost
    _ = ∑ b, mass b * ((∑ u, internal b u) + external b) := hswap
    _ ≤ ∑ b, mass b * M := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hbin b) (hmass b)
    _ = M * ∑ b, mass b := by rw [Finset.mul_sum]; simp [mul_comm]
    _ ≤ M := by nlinarith [htotal]

/-- Averaging the `N`- and `H`-bin full-star rank caps gives exactly
`∑ tᵤ ≤ 17/12 + (23/84) λ`, the frozen generator's star row. The
one-bin rank caps are exposed as premises. -/
theorem full_star_rank_row {B : Type*} [Fintype B]
    (mass : B → ℝ) (heavy : B → Prop) [DecidablePred heavy]
    (charge : B → Fin 4 → ℝ) (t : Fin 4 → ℝ)
    (hmass : ∀ b, 0 ≤ mass b) (htotal : (∑ b, mass b) ≤ 1)
    (hrank : ∀ b, (∑ u, charge b u) ≤
      if heavy b then (71 / 42 : ℝ) else 17 / 12)
    (ht : ∀ u, t u ≤ ∑ b, mass b * charge b u) :
    (∑ u, t u) ≤ (17 / 12 : ℝ) +
      (23 / 84 : ℝ) * ∑ b, if heavy b then mass b else 0 := by
  have hcost : (∑ u, t u) ≤
      ∑ b, mass b * (∑ u, charge b u) := by
    calc
      (∑ u, t u) ≤ ∑ u, ∑ b, mass b * charge b u :=
        Finset.sum_le_sum fun u _ => ht u
      _ = ∑ b, mass b * (∑ u, charge b u) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
  have hranks :
      (∑ b, mass b * (∑ u, charge b u)) ≤
        ∑ b, mass b * (if heavy b then (71 / 42 : ℝ) else 17 / 12) := by
    apply Finset.sum_le_sum
    intro b hb
    exact mul_le_mul_of_nonneg_left (hrank b) (hmass b)
  have hrewrite :
      (∑ b, mass b * (if heavy b then (71 / 42 : ℝ) else 17 / 12)) =
        (17 / 12 : ℝ) * (∑ b, mass b) +
          (23 / 84 : ℝ) * ∑ b, if heavy b then mass b else 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h : heavy b <;> simp [h] <;> ring
  rw [hrewrite] at hranks
  have hbase : (17 / 12 : ℝ) * (∑ b, mass b) ≤ 17 / 12 := by
    nlinarith [htotal]
  linarith

/-- Averaging the one-, two-, and three-copy price inequalities gives the
frozen shared-pair row. The `outside` bins permit two copies of the pair;
the `both` sub-class permits three. The subset relation records the class
geometry, while the three price inequalities record feasible patterns. -/
theorem shared_pair_price_row {B : Type*} [Fintype B]
    (mass pairPrice : B → ℝ) (outside both : B → Prop)
    [DecidablePred outside] [DecidablePred both] (m : ℝ)
    (hmass : ∀ b, 0 ≤ mass b) (htotal : (∑ b, mass b) ≤ 1)
    (hm : m ≤ 1)
    (hboth : ∀ b, both b → outside b)
    (hone : ∀ b, pairPrice b + m ≤ 1)
    (htwo : ∀ b, outside b → 2 * pairPrice b + m ≤ 1)
    (hthree : ∀ b, both b → 3 * pairPrice b + m ≤ 1) :
    (∑ b, mass b * pairPrice b) ≤
      (1 - m) *
        (1 - (∑ b, if outside b then mass b else 0) / 2 -
          (∑ b, if both b then mass b else 0) / 6) := by
  let factor : B → ℝ := fun b =>
    1 - (if outside b then 1 / 2 else 0) -
      (if both b then 1 / 6 else 0)
  have hpoint (b : B) : pairPrice b ≤ (1 - m) * factor b := by
    by_cases hb : both b
    · have ho := hboth b hb
      simp [factor, hb, ho]
      nlinarith [hthree b hb]
    · by_cases ho : outside b
      · simp [factor, hb, ho]
        nlinarith [htwo b ho]
      · simp [factor, hb, ho]
        nlinarith [hone b]
  have hweighted : (∑ b, mass b * pairPrice b) ≤
      ∑ b, mass b * ((1 - m) * factor b) := by
    apply Finset.sum_le_sum
    intro b hb
    exact mul_le_mul_of_nonneg_left (hpoint b) (hmass b)
  have hidentity :
      (∑ b, mass b * ((1 - m) * factor b)) =
        (1 - m) *
          ((∑ b, mass b) -
            (∑ b, if outside b then mass b else 0) / 2 -
            (∑ b, if both b then mass b else 0) / 6) := by
    have hterm (b : B) :
        mass b * ((1 - m) * factor b) =
          (1 - m) * (mass b -
            (if outside b then mass b else 0) / 2 -
            (if both b then mass b else 0) / 6) := by
      by_cases ho : outside b <;> by_cases hb : both b <;>
        simp [factor, ho, hb] <;> ring
    calc
      (∑ b, mass b * ((1 - m) * factor b)) =
          ∑ b, (1 - m) *
            (mass b - (if outside b then mass b else 0) / 2 -
              (if both b then mass b else 0) / 6) := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hterm b
      _ = (1 - m) * ∑ b,
            (mass b - (if outside b then mass b else 0) / 2 -
              (if both b then mass b else 0) / 6) := by
        rw [Finset.mul_sum]
      _ = _ := by
        congr 1
        simp only [Finset.sum_sub_distrib, Finset.sum_div]
  rw [hidentity] at hweighted
  have htop :
      (1 - m) *
          ((∑ b, mass b) -
            (∑ b, if outside b then mass b else 0) / 2 -
            (∑ b, if both b then mass b else 0) / 6) ≤
        (1 - m) *
          (1 - (∑ b, if outside b then mass b else 0) / 2 -
            (∑ b, if both b then mass b else 0) / 6) := by
    exact mul_le_mul_of_nonneg_left (by linarith [htotal]) (sub_nonneg.mpr hm)
  exact hweighted.trans htop

/-- A fractional bundle packing with total mass `t` and every packet
price at most `m` has demand price at most `m*t`. This is the source of
the frozen row `cₑ≤mₑtₑ` before replacing the product by a lift. -/
theorem bundle_price_le_max_mul_cost {P : Type*}
    (patterns : Finset P) (mass price : P → ℝ) (m : ℝ)
    (hmass : ∀ p ∈ patterns, 0 ≤ mass p)
    (hprice : ∀ p ∈ patterns, price p ≤ m) :
    (∑ p ∈ patterns, mass p * price p) ≤
      m * ∑ p ∈ patterns, mass p := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left (hprice p hp) (hmass p hp)

/-- The avoiding-vertex profit row follows when an avoiding pattern can
contain two vertex-disjoint packets of prices `m₁,m₂`. -/
theorem exterior_profit_le_matching_cap (q r m₁ m₂ z : ℝ)
    (hq : 0 ≤ q) (hr : m₁ + m₂ ≤ r)
    (hz : z = q * (1 - r)) :
    z ≤ q * (1 - m₁ - m₂) := by
  rw [hz]
  nlinarith [mul_le_mul_of_nonneg_left
    (show 1 - r ≤ 1 - m₁ - m₂ by linarith) hq]

/-- Summing the five per-vertex resource rows and using the edge-incidence
double count gives `qᵥ≤5M-4K`. The handshake identity is stated explicitly
because the edge indexing is supplied by the graph bridge. -/
theorem five_boundary_charge_cap
    (degreeCharge boundaryCharge : Fin 5 → ℝ) (T M K : ℝ)
    (hresource : ∀ v, degreeCharge v + boundaryCharge v ≤ M)
    (hhandshake : (∑ v, degreeCharge v) = 2 * T)
    (hdensity : 2 * K ≤ T)
    (hboundary : ∀ v, 0 ≤ boundaryCharge v) :
    ∀ v, boundaryCharge v ≤ 5 * M - 4 * K := by
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hresource v)
  have hMsum : (∑ _v : Fin 5, M) = 5 * M := by norm_num
  rw [Finset.sum_add_distrib, hhandshake, hMsum] at hsum
  intro v
  have hsingle : boundaryCharge v ≤ ∑ u, boundaryCharge u :=
    Finset.single_le_sum (fun u _ => hboundary u) (Finset.mem_univ v)
  linarith

end WeightedEdgeColoring.SubtwoBinProfileRows
