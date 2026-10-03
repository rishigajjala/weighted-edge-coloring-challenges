import WeightedEdgeColoring.SubtwoHighPriceSupports
import Mathlib.Tactic

/-!
# The two-model geometry of five-vertex packet prices

The ten coordinates use the repository's standard edge order
`01, 02, 03, 04, 12, 13, 14, 23, 24, 34`.
At a fixed largest price `a`, every labelled star or triangle majorant
lies in the triangular region spanned by two labelled stars and one triangle.
-/

namespace WeightedEdgeColoring.Subtwo.TwoModelGeometry

abbrev PriceVec := Fin 10 → ℝ

/-- The same ten-coordinate order as the price vectors, now as actual
two-vertex subsets of `Fin 5`. This connects the geometry to the
generic high-price support theorem. -/
def edge : Fin 10 → Finset (Fin 5) :=
  ![{0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2},
    {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}]

theorem edge_injective : Function.Injective edge := by decide

theorem edge_card_two (i : Fin 10) : (edge i).card = 2 := by
  fin_cases i <;> decide

/-- The generic pair-support theorem, specialized to our ten-edge
coordinate convention. This identifies the only two possible shapes
of the edges whose *actual* packet prices exceed one half. -/
theorem high_price_support_star_or_triangle_fin10 (p : PriceVec)
    (hdisjoint : ∀ i j : Fin 10,
      Disjoint (edge i) (edge j) → p i + p j ≤ 1)
    (hne : ∃ i : Fin 10, (1 / 2 : ℝ) < p i) :
    (∃ v : Fin 5, ∀ i : Fin 10, (1 / 2 : ℝ) < p i → v ∈ edge i) ∨
      ∃ u v w : Fin 5, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
        ∀ i : Fin 10, (1 / 2 : ℝ) < p i →
          edge i = {u, v} ∨ edge i = {u, w} ∨ edge i = {v, w} := by
  classical
  let H : Finset (Finset (Fin 5)) :=
    (Finset.univ.filter fun i : Fin 10 => (1 / 2 : ℝ) < p i).image edge
  have hmem (i : Fin 10) (hi : (1 / 2 : ℝ) < p i) : edge i ∈ H := by
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
  have hH : H.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨edge i, hmem i hi⟩
  have hc : ∀ e ∈ H, e.card = 2 := by
    intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact edge_card_two i
  have hint : ∀ e ∈ H, ∀ f ∈ H, (e ∩ f).Nonempty := by
    intro e he f hf
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hf
    have hpi : (1 / 2 : ℝ) < p i := (Finset.mem_filter.mp hi).2
    have hpj : (1 / 2 : ℝ) < p j := (Finset.mem_filter.mp hj).2
    by_contra h
    have hempty : edge i ∩ edge j = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hd : Disjoint (edge i) (edge j) :=
      Finset.disjoint_iff_inter_eq_empty.mpr hempty
    linarith [hdisjoint i j hd]
  rcases WeightedEdgeColoring.Subtwo.intersecting_pairs_star_or_triangle H hH hc hint with
    ⟨v, hv⟩ | ⟨u, v, w, huv, huw, hvw, ht⟩
  · exact Or.inl ⟨v, fun i hi => hv (edge i) (hmem i hi)⟩
  · exact Or.inr ⟨u, v, w, huv, huw, hvw,
      fun i hi => ht (edge i) (hmem i hi)⟩

def S0 (a : ℝ) : PriceVec :=
  ![a, a, a, a, 1 - a, 1 - a, 1 - a, 1 - a, 1 - a, 1 - a]

def S1 (a : ℝ) : PriceVec :=
  ![a, 1 - a, 1 - a, 1 - a, a, a, a, 1 - a, 1 - a, 1 - a]

def T (a : ℝ) : PriceVec :=
  ![a, a, 1 - a, 1 - a, a, 1 - a, 1 - a, 1 - a, 1 - a, 1 - a]

def M (a x y : ℝ) : PriceVec :=
  ![a, x, y, y, 1 - y, 1 - x, 1 - x, 1 - a, 1 - a, 1 - a]

noncomputable def lambda0 (a y : ℝ) : ℝ := (y - (1 - a)) / (2 * a - 1)
noncomputable def lambda1 (a x : ℝ) : ℝ := (a - x) / (2 * a - 1)
noncomputable def lambdaT (a x y : ℝ) : ℝ := (x - y) / (2 * a - 1)

theorem lambda0_nonneg (a y : ℝ) (ha : 1 / 2 < a)
    (hy : 1 - a ≤ y) : 0 ≤ lambda0 a y := by
  unfold lambda0
  apply div_nonneg
  · linarith
  · linarith

theorem lambda1_nonneg (a x : ℝ) (ha : 1 / 2 < a)
    (hx : x ≤ a) : 0 ≤ lambda1 a x := by
  unfold lambda1
  apply div_nonneg
  · linarith
  · linarith

theorem lambdaT_nonneg (a x y : ℝ) (ha : 1 / 2 < a)
    (hxy : y ≤ x) : 0 ≤ lambdaT a x y := by
  unfold lambdaT
  apply div_nonneg
  · linarith
  · linarith

theorem lambda_sum (a x y : ℝ) (ha : 1 / 2 < a) :
    lambda0 a y + lambda1 a x + lambdaT a x y = 1 := by
  have hne : 2 * a - 1 ≠ 0 := by linarith
  unfold lambda0 lambda1 lambdaT
  rw [← add_div, ← add_div]
  have hnum : (y - (1 - a)) + (a - x) + (x - y) = 2 * a - 1 := by ring
  rw [hnum, div_self hne]

theorem M_eq_convex_models (a x y : ℝ) (ha : 1 / 2 < a) :
    ∀ e : Fin 10,
      M a x y e = lambda0 a y * S0 a e +
        lambda1 a x * S1 a e + lambdaT a x y * T a e := by
  have hne : 2 * a - 1 ≠ 0 := by linarith
  intro e
  have hpoly :
      (2 * a - 1) * M a x y e =
        (y - (1 - a)) * S0 a e + (a - x) * S1 a e + (x - y) * T a e := by
    fin_cases e <;> simp [M, S0, S1, T] <;> ring
  have hdiv :
      M a x y e =
        ((y - (1 - a)) * S0 a e + (a - x) * S1 a e +
          (x - y) * T a e) / (2 * a - 1) := by
    apply (eq_div_iff hne).2
    simpa [mul_comm] using hpoly
  rw [hdiv]
  simp only [lambda0, lambda1, lambdaT]
  ring

theorem M_in_convex_hull (a x y : ℝ) (ha : 1 / 2 < a)
    (hsy : 1 - a ≤ y) (hyx : y ≤ x) (hxa : x ≤ a) :
    0 ≤ lambda0 a y ∧ 0 ≤ lambda1 a x ∧ 0 ≤ lambdaT a x y ∧
      lambda0 a y + lambda1 a x + lambdaT a x y = 1 ∧
      (∀ e : Fin 10,
        M a x y e = lambda0 a y * S0 a e +
          lambda1 a x * S1 a e + lambdaT a x y * T a e) := by
  exact ⟨lambda0_nonneg a y ha hsy, lambda1_nonneg a x ha hxa,
    lambdaT_nonneg a x y ha hyx, lambda_sum a x y ha,
    M_eq_convex_models a x y ha⟩

def starMajorant (a b c d : ℝ) : PriceVec :=
  ![a, b, c, d, 1 - c, 1 - b, 1 - b, 1 - a, 1 - a, 1 - a]

def triangleMajorant (a b c : ℝ) : PriceVec :=
  ![a, b, 1 - c, 1 - c, c, 1 - b, 1 - b, 1 - a, 1 - a, 1 - a]

theorem starMajorant_le_M (a b c d : ℝ) (hdc : d ≤ c) :
    ∀ e : Fin 10, starMajorant a b c d e ≤ M a b c e := by
  intro e
  fin_cases e <;> simp [starMajorant, M, hdc]

theorem triangleMajorant_eq_M (a b c : ℝ) :
    triangleMajorant a b c = M a b (1 - c) := by
  funext e
  fin_cases e <;> simp [triangleMajorant, M]

theorem star_domain (a b c : ℝ) (ha : 1 / 2 ≤ a)
    (hcb : c ≤ b) (hba : b ≤ a) (hc : 1 / 2 ≤ c) :
    1 - a ≤ c ∧ c ≤ b ∧ b ≤ a := by
  constructor
  · linarith
  · exact ⟨hcb, hba⟩

theorem triangle_domain (a b c : ℝ) (hca : c ≤ a)
    (hb : 1 / 2 ≤ b) (hc : 1 / 2 ≤ c) (hba : b ≤ a) :
    1 - a ≤ 1 - c ∧ 1 - c ≤ b ∧ b ≤ a := by
  constructor
  · linarith
  constructor
  · linarith
  · exact hba

/-- A sorted labelled high-star price vector is dominated by `M`.
Only the fourth spoke may be raised, from its price to the third
spoke's padded price. The disjoint-packet inequality supplies each
core bound. -/
theorem star_prices_le_M (p : PriceVec) (a : ℝ)
    (h01 : p 0 = a) (h32 : p 3 ≤ p 2)
    (hcore : ∀ i : Fin 10, 4 ≤ i.val → p i ≤ 1 / 2)
    (hdisjoint : ∀ i j : Fin 10, Disjoint (edge i) (edge j) → p i + p j ≤ 1) :
    ∀ i : Fin 10,
      p i ≤ M a (max (1 / 2) (p 1)) (max (1 / 2) (p 2)) i := by
  have h42 : p 4 + p 2 ≤ 1 := hdisjoint 4 2 (by decide)
  have h51 : p 5 + p 1 ≤ 1 := hdisjoint 5 1 (by decide)
  have h61 : p 6 + p 1 ≤ 1 := hdisjoint 6 1 (by decide)
  have h70 : p 7 + p 0 ≤ 1 := hdisjoint 7 0 (by decide)
  have h80 : p 8 + p 0 ≤ 1 := hdisjoint 8 0 (by decide)
  have h90 : p 9 + p 0 ≤ 1 := hdisjoint 9 0 (by decide)
  have hc4 : p 4 ≤ 1 / 2 := hcore 4 (by decide)
  have hc5 : p 5 ≤ 1 / 2 := hcore 5 (by decide)
  have hc6 : p 6 ≤ 1 / 2 := hcore 6 (by decide)
  have hb1 : p 1 ≤ max (1 / 2 : ℝ) (p 1) := le_max_right _ _
  have hc2 : p 2 ≤ max (1 / 2 : ℝ) (p 2) := le_max_right _ _
  have hc3 : p 3 ≤ max (1 / 2 : ℝ) (p 2) := le_trans h32 hc2
  have hcore4 : max (1 / 2 : ℝ) (p 2) ≤ 1 - p 4 :=
    (max_le_iff).2 ⟨by linarith, by linarith⟩
  have hcore5 : max (1 / 2 : ℝ) (p 1) ≤ 1 - p 5 :=
    (max_le_iff).2 ⟨by linarith, by linarith⟩
  have hcore6 : max (1 / 2 : ℝ) (p 1) ≤ 1 - p 6 :=
    (max_le_iff).2 ⟨by linarith, by linarith⟩
  intro i
  fin_cases i <;> simp [M] <;> try linarith
  exact Or.inr h32

theorem star_padded_domain (p : PriceVec) (a : ℝ)
    (ha : 1 / 2 ≤ a) (h10 : p 1 ≤ a) (h21 : p 2 ≤ p 1) :
    1 - a ≤ max (1 / 2) (p 2) ∧
      max (1 / 2) (p 2) ≤ max (1 / 2) (p 1) ∧
      max (1 / 2) (p 1) ≤ a := by
  have hc_half : (1 / 2 : ℝ) ≤ max (1 / 2) (p 2) := le_max_left _ _
  have hb_half : (1 / 2 : ℝ) ≤ a := ha
  constructor
  · linarith
  constructor
  · apply max_le
    · exact le_max_left _ _
    · exact h21.trans (le_max_right _ _)
  · exact max_le ha h10

/-- A sorted labelled high-triangle vector has exactly the indicated
majorant. The seven nontriangle coordinates are bounded by disjoint
packets. -/
theorem triangle_prices_le_M (p : PriceVec) (a b c : ℝ)
    (h01 : p 0 = a) (h02 : p 1 = b) (h12 : p 4 = c)
    (hdisjoint : ∀ i j : Fin 10, Disjoint (edge i) (edge j) → p i + p j ≤ 1) :
    ∀ i : Fin 10, p i ≤ M a b (1 - c) i := by
  have h24 : p 2 + p 4 ≤ 1 := hdisjoint 2 4 (by decide)
  have h34 : p 3 + p 4 ≤ 1 := hdisjoint 3 4 (by decide)
  have h51 : p 5 + p 1 ≤ 1 := hdisjoint 5 1 (by decide)
  have h61 : p 6 + p 1 ≤ 1 := hdisjoint 6 1 (by decide)
  have h70 : p 7 + p 0 ≤ 1 := hdisjoint 7 0 (by decide)
  have h80 : p 8 + p 0 ≤ 1 := hdisjoint 8 0 (by decide)
  have h90 : p 9 + p 0 ≤ 1 := hdisjoint 9 0 (by decide)
  intro i
  fin_cases i <;> simp [M] <;> linarith

end WeightedEdgeColoring.Subtwo.TwoModelGeometry
