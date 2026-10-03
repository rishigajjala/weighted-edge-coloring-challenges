import WeightedEdgeColoring.WeightedMomentGraphLinks
import WeightedEdgeColoring.KempeComponentMomentSelection
import WeightedEdgeColoring.FiniteColorPairBlockOperators

/-!
# Concrete graph statistics for selecting one Kempe color block

Second moments are multiplied by `n` before partial resampling.  Thus first
and second moment summands have the same `O(1/n)` pointwise scale; after the
selection theorem the second-moment error is divided by `n` again and is
`o(1/n)`.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open scoped BigOperators
open WeightedEdgeColoring.WeightedMomentStatistics

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

theorem inc_otherEndpoint_eq_iff_endpoint_pair
    {v w : G.V} {e : G.E} :
    (G.Inc v e ∧ G.kempeOtherEndpoint v e = w) ↔
      (G.fst e = v ∧ G.snd e = w) ∨
        (G.fst e = w ∧ G.snd e = v) := by
  constructor
  · rintro ⟨hinc, hother⟩
    rcases hinc with hfst | hsnd
    · left
      exact ⟨hfst, by simpa [kempeOtherEndpoint, hfst] using hother⟩
    · right
      have hne : G.fst e ≠ v := by
        intro h
        exact G.noLoop e (h.trans hsnd.symm)
      exact ⟨by simpa [kempeOtherEndpoint, hne] using hother, hsnd⟩
  · intro hpair
    rcases hpair with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
    · refine ⟨Or.inl hfst, ?_⟩
      unfold kempeOtherEndpoint
      rw [if_pos hfst]
      exact hsnd
    · refine ⟨Or.inr hsnd, ?_⟩
      have hne : G.fst e ≠ v := by
        intro h
        exact G.noLoop e (h.trans hsnd.symm)
      unfold kempeOtherEndpoint
      rw [if_neg hne]
      exact hfst

theorem firstLinkCharge_eq_pairCharge_div {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (v w : G.V) :
    G.firstLinkCharge R charge F color v w =
      G.pairCharge R charge v w /
        G.momentMissingSize F color w := by
  unfold firstLinkCharge pairCharge
  rw [Finset.sum_div]
  conv_rhs => rw [← Finset.sum_attach, Finset.attach_eq_univ]
  apply Finset.sum_congr rfl
  intro e _he
  simp only [G.inc_otherEndpoint_eq_iff_endpoint_pair]
  split <;> ring

theorem secondLinkCharge_eq_pairCharge_div_sq {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (v w : G.V) :
    G.secondLinkCharge R charge F color v w =
      G.pairCharge R charge v w /
        (G.momentMissingSize F color w) ^ 2 := by
  unfold secondLinkCharge pairCharge
  rw [Finset.sum_div]
  conv_rhs => rw [← Finset.sum_attach, Finset.attach_eq_univ]
  apply Finset.sum_congr rfl
  intro e _he
  simp only [G.inc_otherEndpoint_eq_iff_endpoint_pair]
  split <;> ring

theorem sum_pairCharge (R : Finset G.E) (charge : G.E → ℝ) (v : G.V) :
    (∑ w : G.V, G.pairCharge R charge v w) =
      G.restrictedCharge R charge v := by
  unfold pairCharge restrictedCharge
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hinc : G.Inc v e
  · let w := G.kempeOtherEndpoint v e
    rw [if_pos hinc]
    rw [show
        (∑ x : G.V,
          if (G.fst e = v ∧ G.snd e = x) ∨
              (G.fst e = x ∧ G.snd e = v) then charge e else 0) =
          charge e by
      rw [show
          (∑ x : G.V,
            if (G.fst e = v ∧ G.snd e = x) ∨
                (G.fst e = x ∧ G.snd e = v) then charge e else 0) =
          ∑ x : G.V, if x = w then charge e else 0 by
        apply Finset.sum_congr rfl
        intro x _hx
        have hiff :
            ((G.fst e = v ∧ G.snd e = x) ∨
              (G.fst e = x ∧ G.snd e = v)) ↔ x = w := by
          rw [← G.inc_otherEndpoint_eq_iff_endpoint_pair]
          constructor
          · intro hx
            simpa [w] using hx.2.symm
          · intro hx
            refine ⟨hinc, ?_⟩
            simpa [w] using hx.symm
        simp only [hiff]]
      simp]
  · have hnone : ∀ w,
        ¬((G.fst e = v ∧ G.snd e = w) ∨
          (G.fst e = w ∧ G.snd e = v)) := by
      intro w hw
      exact hinc ((G.inc_otherEndpoint_eq_iff_endpoint_pair).2 hw).1
    simp [hinc, hnone]

theorem pairCharge_nonneg
    (R : Finset G.E) (charge : G.E → ℝ)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e) (v w : G.V) :
    0 ≤ G.pairCharge R charge v w := by
  unfold pairCharge
  apply Finset.sum_nonneg
  intro e _he
  split
  · exact hcharge e _he
  · exact le_rfl

theorem firstLinkCharge_le_inv_linear {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (alpha L : ℝ) (halpha : 0 < alpha) (hL : 0 ≤ L) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hpair : ∀ v w, G.pairCharge R charge v w ≤ L)
    (v w : G.V) :
    G.firstLinkCharge R charge F color v w ≤ (L / alpha) / n := by
  rw [G.firstLinkCharge_eq_pairCharge_div R charge F color v w]
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hfpos : 0 < G.momentMissingSize F color w :=
    (mul_pos halpha hnreal).trans_le (hmissing w)
  rw [div_le_iff₀ hfpos]
  have hratio :
      L ≤ (L / alpha / n) * G.momentMissingSize F color w := by
    calc
      L = (L / alpha / n) * (alpha * n) := by
        field_simp [halpha.ne', hnreal.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmissing w)
        (div_nonneg (div_nonneg hL halpha.le) hnreal.le)
  exact (hpair v w).trans hratio

theorem n_mul_secondLinkCharge_le_inv_linear {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (alpha L : ℝ) (halpha : 0 < alpha) (hL : 0 ≤ L) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hpair : ∀ v w, G.pairCharge R charge v w ≤ L)
    (v w : G.V) :
    (n : ℝ) * G.secondLinkCharge R charge F color v w ≤
      (L / alpha ^ 2) / n := by
  rw [G.secondLinkCharge_eq_pairCharge_div_sq R charge F color v w]
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hfpos : 0 < G.momentMissingSize F color w :=
    (mul_pos halpha hnreal).trans_le (hmissing w)
  have hfsq : (alpha * n) ^ 2 ≤
      (G.momentMissingSize F color w) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg halpha.le hnreal.le)
      ((mul_nonneg halpha.le hnreal.le).trans (hmissing w))).2 (hmissing w)
  rw [show
      (n : ℝ) * (G.pairCharge R charge v w /
        (G.momentMissingSize F color w) ^ 2) =
      ((n : ℝ) * G.pairCharge R charge v w) /
        (G.momentMissingSize F color w) ^ 2 by ring]
  rw [div_le_iff₀ (sq_pos_of_pos hfpos)]
  calc
    (n : ℝ) * G.pairCharge R charge v w ≤ (n : ℝ) * L :=
      mul_le_mul_of_nonneg_left (hpair v w) hnreal.le
    _ = ((L / alpha ^ 2) / n) * (alpha * n) ^ 2 := by
      field_simp [halpha.ne', hnreal.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hfsq
      (div_nonneg (div_nonneg hL (sq_nonneg alpha)) hnreal.le)

/-- Rows tracked while one paired block `{a,b}` is selected.  `diagonal`
and `pair` rows are stored after multiplication by `n`. -/
inductive MomentBlockRow (V : Type*) (q : ℕ)
  | first (v : V) (side : Bool)
  | diagonal (v : V) (side : Bool)
  | pair (v : V) (side : Bool) (d : Fin q)
  deriving Fintype, DecidableEq

def momentBlockRowEquiv (V : Type*) (q : ℕ) :
    MomentBlockRow V q ≃
      (V × Bool) ⊕ ((V × Bool) ⊕ (V × Bool × Fin q)) where
  toFun
    | .first v side => Sum.inl (v, side)
    | .diagonal v side => Sum.inr (Sum.inl (v, side))
    | .pair v side d => Sum.inr (Sum.inr (v, side, d))
  invFun
    | Sum.inl (v, side) => .first v side
    | Sum.inr (Sum.inl (v, side)) => .diagonal v side
    | Sum.inr (Sum.inr (v, side, d)) => .pair v side d
  left_inv row := by cases row <;> rfl
  right_inv row := by
    rcases row with ⟨v, side⟩ | row
    · rfl
    · rcases row with ⟨v, side⟩ | ⟨v, side, d⟩ <;> rfl

theorem sum_momentBlockRow
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (f : MomentBlockRow V q → ℝ) :
    (∑ row, f row) =
      (∑ v : V, ∑ side : Bool, f (.first v side)) +
      (∑ v : V, ∑ side : Bool, f (.diagonal v side)) +
      ∑ v : V, ∑ side : Bool, ∑ d : Fin q, f (.pair v side d) := by
  have hreindex := Equiv.sum_comp (momentBlockRowEquiv V q) (fun row ↦
    match row with
    | Sum.inl (v, side) => f (.first v side)
    | Sum.inr (Sum.inl (v, side)) => f (.diagonal v side)
    | Sum.inr (Sum.inr (v, side, d)) => f (.pair v side d))
  calc
    (∑ row, f row) =
        ∑ row, match momentBlockRowEquiv V q row with
          | Sum.inl (v, side) => f (.first v side)
          | Sum.inr (Sum.inl (v, side)) => f (.diagonal v side)
          | Sum.inr (Sum.inr (v, side, d)) => f (.pair v side d) := by
      apply Finset.sum_congr rfl
      intro row _hrow
      cases row <;> rfl
    _ = ∑ row : (V × Bool) ⊕ ((V × Bool) ⊕ (V × Bool × Fin q)),
          match row with
          | Sum.inl (v, side) => f (.first v side)
          | Sum.inr (Sum.inl (v, side)) => f (.diagonal v side)
          | Sum.inr (Sum.inr (v, side, d)) => f (.pair v side d) := hreindex
    _ =
        (∑ v : V, ∑ side : Bool, f (.first v side)) +
        (∑ v : V, ∑ side : Bool, f (.diagonal v side)) +
        ∑ v : V, ∑ side : Bool, ∑ d : Fin q, f (.pair v side d) := by
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
      rw [add_assoc]

def blockSideColor {q : ℕ} (a b : Fin q) : Bool → Fin q
  | false => a
  | true => b

/-- The old endpoint indicator read after applying the indicated block coin. -/
def blockIndicator {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (bit side : Bool) (w : G.V) : ℝ :=
  if bit then
    paletteIndicator (G.missingColorsAt F color w)
      (blockSideColor a b (!side))
  else
    paletteIndicator (G.missingColorsAt F color w)
      (blockSideColor a b side)

theorem blockIndicator_nonneg {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (bit side : Bool) (w : G.V) :
    0 ≤ G.blockIndicator F color a b bit side w := by
  unfold blockIndicator
  split <;> exact paletteIndicator_nonneg _ _

theorem blockIndicator_le_one {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (bit side : Bool) (w : G.V) :
    G.blockIndicator F color a b bit side w ≤ 1 := by
  unfold blockIndicator
  split <;> exact paletteIndicator_le_one _ _

/-- Contribution of one active endpoint to one normalized statistic row. -/
def momentBlockVertexUse {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (w : G.V) (bit : Bool) : MomentBlockRow G.V q → ℝ
  | .first v side =>
      G.firstLinkCharge R charge F color v w *
        G.blockIndicator F color a b bit side w
  | .diagonal v side =>
      n * G.secondLinkCharge R charge F color v w *
        G.blockIndicator F color a b bit side w
  | .pair v side d =>
      if d = a ∨ d = b then 0 else
        n * G.secondLinkCharge R charge F color v w *
          G.blockIndicator F color a b bit side w *
          paletteIndicator (G.missingColorsAt F color w) d

/-- Sparse pointwise cap for the preceding contribution. -/
def momentBlockVertexCap {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (w : G.V) : MomentBlockRow G.V q → ℝ
  | .first v _side => G.firstLinkCharge R charge F color v w
  | .diagonal v _side => n * G.secondLinkCharge R charge F color v w
  | .pair v _side d =>
      if d = a ∨ d = b then 0 else
        n * G.secondLinkCharge R charge F color v w *
          paletteIndicator (G.missingColorsAt F color w) d

/-- Sum the endpoint contributions belonging to one two-color component. -/
def momentBlockUse {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (component : G.TwoColorComponent F color a b) (bit : Bool)
    (row : MomentBlockRow G.V q) : ℝ :=
  ∑ w ∈ G.activeVerticesInComponent F color a b component,
    G.momentBlockVertexUse (n := n) R charge F color a b w.1 bit row

theorem momentBlockVertexUse_nonneg {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (w : G.V) (bit : Bool) (row : MomentBlockRow G.V q) :
    0 ≤ G.momentBlockVertexUse (n := n)
      R charge F color a b w bit row := by
  cases row with
  | first v side =>
      change 0 ≤ G.firstLinkCharge R charge F color v w *
        G.blockIndicator F color a b bit side w
      exact mul_nonneg
        (G.firstLinkCharge_nonneg R charge F color hcharge v w)
        (G.blockIndicator_nonneg F color a b bit side w)
  | diagonal v side =>
      change 0 ≤ (n : ℝ) * G.secondLinkCharge R charge F color v w *
        G.blockIndicator F color a b bit side w
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n)
        (G.secondLinkCharge_nonneg R charge F color hcharge v w))
        (G.blockIndicator_nonneg F color a b bit side w)
  | pair v side d =>
      change 0 ≤ if d = a ∨ d = b then 0 else
        (n : ℝ) * G.secondLinkCharge R charge F color v w *
          G.blockIndicator F color a b bit side w *
          paletteIndicator (G.missingColorsAt F color w) d
      split
      · exact le_rfl
      · exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (Nat.cast_nonneg n)
              (G.secondLinkCharge_nonneg R charge F color hcharge v w))
            (G.blockIndicator_nonneg F color a b bit side w))
          (paletteIndicator_nonneg _ _)

theorem momentBlockVertexUse_le_cap {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (w : G.V) (bit : Bool) (row : MomentBlockRow G.V q) :
    G.momentBlockVertexUse (n := n) R charge F color a b w bit row ≤
      G.momentBlockVertexCap (n := n) R charge F color a b w row := by
  cases row with
  | first v side =>
      change G.firstLinkCharge R charge F color v w *
          G.blockIndicator F color a b bit side w ≤
        G.firstLinkCharge R charge F color v w
      exact mul_le_of_le_one_right
        (G.firstLinkCharge_nonneg R charge F color hcharge v w)
        (G.blockIndicator_le_one F color a b bit side w)
  | diagonal v side =>
      change (n : ℝ) * G.secondLinkCharge R charge F color v w *
          G.blockIndicator F color a b bit side w ≤
        (n : ℝ) * G.secondLinkCharge R charge F color v w
      exact mul_le_of_le_one_right
        (mul_nonneg (Nat.cast_nonneg n)
          (G.secondLinkCharge_nonneg R charge F color hcharge v w))
        (G.blockIndicator_le_one F color a b bit side w)
  | pair v side d =>
      change (if d = a ∨ d = b then 0 else
          (n : ℝ) * G.secondLinkCharge R charge F color v w *
            G.blockIndicator F color a b bit side w *
            paletteIndicator (G.missingColorsAt F color w) d) ≤
        if d = a ∨ d = b then 0 else
          (n : ℝ) * G.secondLinkCharge R charge F color v w *
            paletteIndicator (G.missingColorsAt F color w) d
      split
      · exact le_rfl
      · have hbase : 0 ≤
            (n : ℝ) * G.secondLinkCharge R charge F color v w *
              paletteIndicator (G.missingColorsAt F color w) d :=
          mul_nonneg
            (mul_nonneg (Nat.cast_nonneg n)
              (G.secondLinkCharge_nonneg R charge F color hcharge v w))
            (paletteIndicator_nonneg _ _)
        calc
          (n : ℝ) * G.secondLinkCharge R charge F color v w *
                G.blockIndicator F color a b bit side w *
                paletteIndicator (G.missingColorsAt F color w) d =
              ((n : ℝ) * G.secondLinkCharge R charge F color v w *
                paletteIndicator (G.missingColorsAt F color w) d) *
                G.blockIndicator F color a b bit side w := by ring
          _ ≤ _ := mul_le_of_le_one_right hbase
            (G.blockIndicator_le_one F color a b bit side w)

theorem momentBlockUse_nonneg {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (component : G.TwoColorComponent F color a b) (bit : Bool)
    (row : MomentBlockRow G.V q) :
    0 ≤ G.momentBlockUse (n := n)
      R charge F color a b component bit row := by
  unfold momentBlockUse
  apply Finset.sum_nonneg
  intro w _hw
  exact G.momentBlockVertexUse_nonneg (n := n)
    R charge F color a b hcharge
    w.1 bit row

theorem momentBlockUse_le_componentInfluenceCap {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (component : G.TwoColorComponent F color a b) (bit : Bool)
    (row : MomentBlockRow G.V q) :
    G.momentBlockUse (n := n) R charge F color a b component bit row ≤
      G.componentInfluenceCap F color a b
        (G.momentBlockVertexCap (n := n) R charge F color a b) component row := by
  unfold momentBlockUse componentInfluenceCap
  apply Finset.sum_le_sum
  intro w _hw
  exact G.momentBlockVertexUse_le_cap (n := n)
    R charge F color a b hcharge
    w.1 bit row

/-- Every normalized endpoint-row cap has the common first-moment scale
`O(1/n)`. -/
theorem momentBlockVertexCap_le_inv_linear {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (alpha L : ℝ) (halpha : 0 < alpha) (hL : 0 ≤ L) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hpair : ∀ v w, G.pairCharge R charge v w ≤ L)
    (w : G.V) (row : MomentBlockRow G.V q) :
    G.momentBlockVertexCap (n := n) R charge F color a b w row ≤
      (L / alpha + L / alpha ^ 2) / n := by
  have hfirst := G.firstLinkCharge_le_inv_linear R charge F color
    alpha L halpha hL hn hcharge hmissing hpair
  have hsecond := G.n_mul_secondLinkCharge_le_inv_linear R charge F color
    alpha L halpha hL hn hcharge hmissing hpair
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hLa : 0 ≤ L / alpha := div_nonneg hL halpha.le
  have hLa2 : 0 ≤ L / alpha ^ 2 := div_nonneg hL (sq_nonneg alpha)
  have hcommon0 : 0 ≤ (L / alpha + L / alpha ^ 2) / n :=
    div_nonneg (add_nonneg hLa hLa2) hnreal.le
  cases row with
  | first v side =>
      change G.firstLinkCharge R charge F color v w ≤
        (L / alpha + L / alpha ^ 2) / n
      calc
        G.firstLinkCharge R charge F color v w ≤ (L / alpha) / n :=
          hfirst v w
        _ ≤ (L / alpha + L / alpha ^ 2) / n := by
          exact div_le_div_of_nonneg_right
            (le_add_of_nonneg_right hLa2) hnreal.le
  | diagonal v side =>
      change (n : ℝ) * G.secondLinkCharge R charge F color v w ≤
        (L / alpha + L / alpha ^ 2) / n
      calc
        (n : ℝ) * G.secondLinkCharge R charge F color v w ≤
            (L / alpha ^ 2) / n := hsecond v w
        _ ≤ (L / alpha + L / alpha ^ 2) / n := by
          exact div_le_div_of_nonneg_right
            (le_add_of_nonneg_left hLa) hnreal.le
  | pair v side d =>
      change (if d = a ∨ d = b then 0 else
          (n : ℝ) * G.secondLinkCharge R charge F color v w *
            paletteIndicator (G.missingColorsAt F color w) d) ≤
        (L / alpha + L / alpha ^ 2) / n
      split
      · exact hcommon0
      · calc
          (n : ℝ) * G.secondLinkCharge R charge F color v w *
              paletteIndicator (G.missingColorsAt F color w) d ≤
              (n : ℝ) * G.secondLinkCharge R charge F color v w :=
            mul_le_of_le_one_right
              (mul_nonneg (Nat.cast_nonneg n)
                (G.secondLinkCharge_nonneg R charge F color hcharge v w))
              (paletteIndicator_le_one _ _)
          _ ≤ (L / alpha ^ 2) / n := hsecond v w
          _ ≤ (L / alpha + L / alpha ^ 2) / n := by
            exact div_le_div_of_nonneg_right
              (le_add_of_nonneg_left hLa) hnreal.le

end

end WeightedMultigraph
end WeightedEdgeColoring
