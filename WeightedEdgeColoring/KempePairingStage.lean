import WeightedEdgeColoring.KempeComponentSwitchAverage
import WeightedEdgeColoring.FiniteColorPairingOperators
import Mathlib.Data.Fintype.Sigma

/-!
# One simultaneous Kempe stage for a perfect pairing of the colors

Fix a perfect pairing `p` of the colors.  For every paired-color component
we choose one Boolean coin.  The stage swaps the two colors on exactly the
components whose coin is true.  All pairs are processed simultaneously.

The direct definition below is useful for two reasons.  First, it avoids an
arbitrary order on the color pairs.  Second, at each vertex the new colors
are obtained from the old colors by one involutive permutation.  Properness
therefore follows in the same way as for one ordinary Kempe switch.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open scoped BigOperators
open WeightedEdgeColoring.FiniteColorPairing
open WeightedEdgeColoring.FiniteColorPairingOperators

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- The smaller color in the pair containing `c`.  It is used only to make
the component coin for a pair independent of which of its two colors is
named first. -/
def pairingRoot {q : ℕ} (p : Pairing (Fin q)) (c : Fin q) : Fin q :=
  min c (partner (Fin q) p c)

@[simp] theorem pairingRoot_partner {q : ℕ}
    (p : Pairing (Fin q)) (c : Fin q) :
    pairingRoot p (partner (Fin q) p c) = pairingRoot p c := by
  simp [pairingRoot, partner_partner, min_comm]

theorem self_eq_pairingRoot_or_partner_pairingRoot {q : ℕ}
    (p : Pairing (Fin q)) (c : Fin q) :
    c = pairingRoot p c ∨
      c = partner (Fin q) p (pairingRoot p c) := by
  by_cases hle : c ≤ partner (Fin q) p c
  · exact Or.inl (by simp [pairingRoot, min_eq_left hle])
  · have hrev : partner (Fin q) p c ≤ c := le_of_not_ge hle
    exact Or.inr (by
      simp [pairingRoot, min_eq_right hrev, partner_partner])

/-- All paired-color components that carry independent stage coins.  The
upper color of each pair also contributes unused coordinates; this harmless
duplication keeps the dependent type simple. -/
abbrev PairingStageSource {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q)) :=
  Σ a : Fin q,
    G.TwoColorComponent F color a (partner (Fin q) p a)

abbrev PairingStageCoin {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q)) :=
  G.PairingStageSource F color p → Bool

/-- The coin coordinate read by color `c` at vertex `v`. -/
def pairingStageSourceAt {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (v : G.V) (c : Fin q) : G.PairingStageSource F color p :=
  ⟨pairingRoot p c,
    (G.twoColorGraph F color (pairingRoot p c)
      (partner (Fin q) p (pairingRoot p c))).connectedComponentMk v⟩

@[simp] theorem pairingStageSourceAt_partner {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (v : G.V) (c : Fin q) :
    G.pairingStageSourceAt F color p v (partner (Fin q) p c) =
      G.pairingStageSourceAt F color p v c := by
  unfold pairingStageSourceAt
  rw [pairingRoot_partner]

/-- The Boolean used at one vertex-color coordinate. -/
def pairingStageBit {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (coin : G.PairingStageCoin F color p) (v : G.V) (c : Fin q) : Bool :=
  coin (G.pairingStageSourceAt F color p v c)

@[simp] theorem pairingStageBit_partner {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (coin : G.PairingStageCoin F color p) (v : G.V) (c : Fin q) :
    G.pairingStageBit F color p coin v (partner (Fin q) p c) =
      G.pairingStageBit F color p coin v c := by
  simp [pairingStageBit]

/-- Pointwise color map used at one vertex by the simultaneous stage. -/
def pairingLocalMap {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (coin : G.PairingStageCoin F color p) (v : G.V) (c : Fin q) : Fin q :=
  if G.pairingStageBit F color p coin v c then
    partner (Fin q) p c
  else c

theorem pairingLocalMap_involutive {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (coin : G.PairingStageCoin F color p) (v : G.V) :
    Function.Involutive (G.pairingLocalMap F color p coin v) := by
  intro c
  by_cases hbit : G.pairingStageBit F color p coin v c = true
  · have hpartner :
        G.pairingStageBit F color p coin v
            (partner (Fin q) p c) = true := by
      simpa using hbit
    simp [pairingLocalMap, hbit, hpartner, partner_partner]
  · have hfalse : G.pairingStageBit F color p coin v c = false :=
      Bool.eq_false_of_not_eq_true hbit
    simp [pairingLocalMap, hfalse]

/-- The local map packaged as a permutation. -/
def pairingLocalPerm {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (coin : G.PairingStageCoin F color p) (v : G.V) : Fin q ≃ Fin q where
  toFun := G.pairingLocalMap F color p coin v
  invFun := G.pairingLocalMap F color p coin v
  left_inv := G.pairingLocalMap_involutive F color p coin v
  right_inv := G.pairingLocalMap_involutive F color p coin v

@[simp] theorem pairingLocalPerm_apply {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (coin : G.PairingStageCoin F color p) (v : G.V) (c : Fin q) :
    G.pairingLocalPerm F color p coin v c =
      G.pairingLocalMap F color p coin v c := rfl

/-- The coin read at the first endpoint of an edge is the coin read at any
incident vertex. -/
theorem pairingStageBit_fst_eq_of_inc {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (coin : G.PairingStageCoin F color p)
    {v : G.V} {e : G.E} (heF : e ∈ F) (hev : G.Inc v e) :
    G.pairingStageBit F color p coin (G.fst e) (color e) =
      G.pairingStageBit F color p coin v (color e) := by
  let r := pairingRoot p (color e)
  have heColor : color e = r ∨
      color e = partner (Fin q) p r := by
    simpa [r] using self_eq_pairingRoot_or_partner_pairingRoot p (color e)
  have hcomponent := G.twoColorComponent_fst_eq_of_inc
    F color r (partner (Fin q) p r) heF heColor hev
  apply congrArg coin
  exact Sigma.ext rfl (heq_of_eq hcomponent)

/-- Apply all paired-color component switches at once.  Edges outside `F`
are left unchanged. -/
def kempePairingStage {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (coin : G.PairingStageCoin F color p) : G.E → Fin q :=
  fun e ↦ if e ∈ F then
    G.pairingLocalMap F color p coin (G.fst e) (color e)
  else color e

/-- At all selected edges incident with one vertex, the whole stage is one
common color permutation. -/
theorem kempePairingStage_eq_localPerm {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (coin : G.PairingStageCoin F color p)
    {v : G.V} {e : G.E} (heF : e ∈ F) (hev : G.Inc v e) :
    G.kempePairingStage F color p coin e =
      G.pairingLocalPerm F color p coin v (color e) := by
  simp only [kempePairingStage, heF, if_true, pairingLocalPerm_apply,
    pairingLocalMap]
  rw [G.pairingStageBit_fst_eq_of_inc F color p coin heF hev]

/-- A simultaneous stage preserves properness on the selected edge set. -/
theorem isProperOn_kempePairingStage {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (p : Pairing (Fin q))
    (coin : G.PairingStageCoin F color p) :
    G.IsProperOn F (G.kempePairingStage F color p coin) := by
  intro v e he f hf hsame
  let pi := G.pairingLocalPerm F color p coin v
  have heData := Finset.mem_filter.mp (Finset.mem_coe.mp he)
  have hfData := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
  have heLocal : G.kempePairingStage F color p coin e = pi (color e) :=
    G.kempePairingStage_eq_localPerm F color p coin heData.1 heData.2
  have hfLocal : G.kempePairingStage F color p coin f = pi (color f) :=
    G.kempePairingStage_eq_localPerm F color p coin hfData.1 hfData.2
  apply hproper v he hf
  apply pi.injective
  rw [← heLocal, ← hfLocal]
  exact hsame

/-- Missing-palette membership is transported by the local pairing
permutation. -/
theorem mem_missingColorsAt_kempePairingStage_localPerm_iff {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (coin : G.PairingStageCoin F color p) (v : G.V) (c : Fin q) :
    G.pairingLocalPerm F color p coin v c ∈
        G.missingColorsAt F (G.kempePairingStage F color p coin) v ↔
      c ∈ G.missingColorsAt F color v := by
  let pi := G.pairingLocalPerm F color p coin v
  have himage :
      pi c ∈ (F.filter (G.Inc v)).image
          (G.kempePairingStage F color p coin) ↔
        c ∈ (F.filter (G.Inc v)).image color := by
    constructor
    · intro h
      rcases Finset.mem_image.mp h with ⟨e, he, heq⟩
      have heData := Finset.mem_filter.mp he
      have hlocal : G.kempePairingStage F color p coin e =
          pi (color e) :=
        G.kempePairingStage_eq_localPerm
          F color p coin heData.1 heData.2
      apply Finset.mem_image.mpr
      refine ⟨e, he, ?_⟩
      apply pi.injective
      exact hlocal.symm.trans heq
    · intro h
      rcases Finset.mem_image.mp h with ⟨e, he, heq⟩
      have heData := Finset.mem_filter.mp he
      have hlocal : G.kempePairingStage F color p coin e =
          pi (color e) :=
        G.kempePairingStage_eq_localPerm
          F color p coin heData.1 heData.2
      apply Finset.mem_image.mpr
      refine ⟨e, he, ?_⟩
      rw [hlocal, heq]
  simp only [missingColorsAt, Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact not_congr himage

/-- Endpoint form: a true component coin exchanges the two missing-color
indicators, and a false coin leaves them in place. -/
theorem mem_missingColorsAt_kempePairingStage_iff {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (coin : G.PairingStageCoin F color p) (v : G.V) (c : Fin q) :
    c ∈ G.missingColorsAt F (G.kempePairingStage F color p coin) v ↔
      if G.pairingStageBit F color p coin v c then
        partner (Fin q) p c ∈ G.missingColorsAt F color v
      else c ∈ G.missingColorsAt F color v := by
  have h := G.mem_missingColorsAt_kempePairingStage_localPerm_iff
    F color p coin v (G.pairingLocalMap F color p coin v c)
  have hinv := G.pairingLocalMap_involutive F color p coin v c
  rw [show G.pairingLocalPerm F color p coin v
      (G.pairingLocalMap F color p coin v c) = c by exact hinv] at h
  by_cases hbit : G.pairingStageBit F color p coin v c = true
  · simpa [pairingLocalMap, hbit] using h
  · have hfalse : G.pairingStageBit F color p coin v c = false :=
      Bool.eq_false_of_not_eq_true hbit
    simpa [pairingLocalMap, hfalse] using h

/-- A stage never moves a color outside its prescribed pair. -/
theorem kempePairingStage_eq_self_or_partner {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (coin : G.PairingStageCoin F color p) (e : G.E) :
    G.kempePairingStage F color p coin e = color e ∨
      G.kempePairingStage F color p coin e =
        partner (Fin q) p (color e) := by
  unfold kempePairingStage pairingLocalMap
  split
  · split <;> simp_all
  · simp_all

/-! ## Exact finite coin averages -/

/-- A single coordinate of a uniformly enumerated Boolean word is a fair
bit. -/
theorem average_boolWords_apply
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (component : Component) (f : Bool → ℝ) :
    (∑ coin : Component → Bool, f (coin component)) /
        (Fintype.card (Component → Bool) : ℝ) =
      (∑ bit : Bool, f bit) / 2 := by
  rw [sum_boolWords_apply component f]
  have hcard :
      Fintype.card (Component → Bool) =
        2 * Fintype.card ({c : Component // c ≠ component} → Bool) := by
    calc
      Fintype.card (Component → Bool) =
          Fintype.card
            (Bool × ({c : Component // c ≠ component} → Bool)) :=
        Fintype.card_congr (Equiv.funSplitAt component Bool)
      _ = _ := by simp
  have hrest :
      (Fintype.card ({c : Component // c ≠ component} → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [hcard]
  push_cast
  field_simp

/-- Two distinct coordinates of a uniformly enumerated Boolean word are
independent fair bits. -/
theorem average_boolWords_apply_mul_of_ne
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (x y : Component) (hxy : x ≠ y) (f g : Bool → ℝ) :
    (∑ coin : Component → Bool,
      f (coin x) * g (coin y)) /
        (Fintype.card (Component → Bool) : ℝ) =
      ((∑ bit : Bool, f bit) / 2) *
        ((∑ bit : Bool, g bit) / 2) := by
  let RestX := {z : Component // z ≠ x}
  let yRest : RestX := ⟨y, hxy.symm⟩
  let RestXY := {z : RestX // z ≠ yRest}
  let splitX := Equiv.funSplitAt x Bool
  have hsum :
      (∑ coin : Component → Bool, f (coin x) * g (coin y)) =
        (Fintype.card (RestXY → Bool) : ℝ) *
          (∑ bit : Bool, f bit) * (∑ bit : Bool, g bit) := by
    have hreindex := Equiv.sum_comp splitX
      (fun value : Bool × (RestX → Bool) ↦
        f value.1 * g (value.2 yRest))
    calc
      (∑ coin : Component → Bool, f (coin x) * g (coin y)) =
          ∑ value : Bool × (RestX → Bool),
            f value.1 * g (value.2 yRest) := by
        simpa [splitX, RestX, yRest] using hreindex
      _ = ∑ leftBit : Bool, ∑ rest : RestX → Bool,
            f leftBit * g (rest yRest) := by
        rw [Fintype.sum_prod_type]
      _ = ∑ leftBit : Bool,
            f leftBit *
              ((Fintype.card (RestXY → Bool) : ℝ) *
                ∑ rightBit : Bool, g rightBit) := by
        apply Finset.sum_congr rfl
        intro leftBit _hleft
        rw [← Finset.mul_sum,
          sum_boolWords_apply yRest g]
      _ = (Fintype.card (RestXY → Bool) : ℝ) *
          (∑ bit : Bool, f bit) * (∑ bit : Bool, g bit) := by
        rw [← Finset.sum_mul]
        ring
  have hcardRest :
      Fintype.card (RestX → Bool) =
        2 * Fintype.card (RestXY → Bool) := by
    calc
      Fintype.card (RestX → Bool) =
          Fintype.card (Bool × (RestXY → Bool)) :=
        Fintype.card_congr (Equiv.funSplitAt yRest Bool)
      _ = _ := by simp
  have hcard :
      Fintype.card (Component → Bool) =
        4 * Fintype.card (RestXY → Bool) := by
    calc
      Fintype.card (Component → Bool) =
          Fintype.card (Bool × (RestX → Bool)) :=
        Fintype.card_congr splitX
      _ = 2 * Fintype.card (RestX → Bool) := by simp
      _ = 4 * Fintype.card (RestXY → Bool) := by
        rw [hcardRest]
        ring
  have hrest : (Fintype.card (RestXY → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [hsum, hcard]
  push_cast
  field_simp
  ring

/-- Indicator form of the endpoint transport formula. -/
theorem paletteIndicator_kempePairingStage {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (coin : G.PairingStageCoin F color p) (v : G.V) (c : Fin q) :
    paletteIndicator
        (G.missingColorsAt F (G.kempePairingStage F color p coin) v) c =
      if G.pairingStageBit F color p coin v c then
        paletteIndicator (G.missingColorsAt F color v)
          (partner (Fin q) p c)
      else paletteIndicator (G.missingColorsAt F color v) c := by
  unfold paletteIndicator
  by_cases hbit : G.pairingStageBit F color p coin v c = true <;>
    simp [hbit,
      G.mem_missingColorsAt_kempePairingStage_iff F color p coin v c]

/-- If two colors have the same root, they are equal or are paired with one
another. -/
theorem eq_or_partner_eq_of_pairingRoot_eq {q : ℕ}
    (p : Pairing (Fin q)) {c d : Fin q}
    (hroot : pairingRoot p c = pairingRoot p d) :
    c = d ∨ partner (Fin q) p c = d := by
  rcases self_eq_pairingRoot_or_partner_pairingRoot p c with hc | hc <;>
    rcases self_eq_pairingRoot_or_partner_pairingRoot p d with hd | hd
  · exact Or.inl (hc.trans (hroot.trans hd.symm))
  · right
    rw [hc, hroot]
    exact hd.symm
  · right
    rw [hc, hroot, partner_partner]
    exact hd.symm
  · have hp := congrArg (partner (Fin q) p) hroot
    exact Or.inl (hc.trans (hp.trans hd.symm))

/-- Different colors from different pairs read different coin coordinates
at a fixed vertex. -/
theorem pairingStageSourceAt_ne_of_ne_of_partner_ne {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (p : Pairing (Fin q))
    (v : G.V) {c d : Fin q} (hcd : c ≠ d)
    (hpartner : partner (Fin q) p c ≠ d) :
    G.pairingStageSourceAt F color p v c ≠
      G.pairingStageSourceAt F color p v d := by
  intro hsource
  have hroot : pairingRoot p c = pairingRoot p d :=
    congrArg Sigma.fst hsource
  rcases eq_or_partner_eq_of_pairingRoot_eq p hroot with h | h
  · exact hcd h
  · exact hpartner h

/-- Conditional on a fixed perfect pairing, averaging all component coins
applies `singleAverage` to every missing-color indicator. -/
theorem average_paletteIndicator_kempePairingStage {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (p : Pairing (Fin q)) (v : G.V) (c : Fin q) :
    (∑ coin : G.PairingStageCoin F color p,
      paletteIndicator
        (G.missingColorsAt F (G.kempePairingStage F color p coin) v) c) /
        (Fintype.card (G.PairingStageCoin F color p) : ℝ) =
      singleAverage p
        (fun d ↦ paletteIndicator (G.missingColorsAt F color v) d) c := by
  let source := G.pairingStageSourceAt F color p v c
  let f : Bool → ℝ := fun bit ↦
    if bit then
      paletteIndicator (G.missingColorsAt F color v)
        (partner (Fin q) p c)
    else paletteIndicator (G.missingColorsAt F color v) c
  rw [show (∑ coin : G.PairingStageCoin F color p,
      paletteIndicator
        (G.missingColorsAt F (G.kempePairingStage F color p coin) v) c) =
      ∑ coin : G.PairingStageCoin F color p, f (coin source) by
    apply Finset.sum_congr rfl
    intro coin _hcoin
    rw [G.paletteIndicator_kempePairingStage F color p coin v c]
    rfl]
  rw [average_boolWords_apply source f]
  simp [f, singleAverage, add_comm]

theorem sum_paletteIndicator_kempePairingStage {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (p : Pairing (Fin q)) (v : G.V) (c : Fin q) :
    (∑ coin : G.PairingStageCoin F color p,
      paletteIndicator
        (G.missingColorsAt F (G.kempePairingStage F color p coin) v) c) =
      (Fintype.card (G.PairingStageCoin F color p) : ℝ) *
        singleAverage p
          (fun d ↦ paletteIndicator (G.missingColorsAt F color v) d) c := by
  have hcard :
      (Fintype.card (G.PairingStageCoin F color p) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simpa [mul_comm] using (div_eq_iff hcard).mp
    (G.average_paletteIndicator_kempePairingStage F color p v c)

/-- Conditional on a fixed pairing, two distinct missing-color indicators
have expectation `pairAverage`.  Indicators in one paired block move
together; indicators in different blocks use independent component coins. -/
theorem average_paletteIndicator_mul_kempePairingStage {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (p : Pairing (Fin q)) (v : G.V) {c d : Fin q} (hcd : c ≠ d) :
    (∑ coin : G.PairingStageCoin F color p,
      paletteIndicator
          (G.missingColorsAt F (G.kempePairingStage F color p coin) v) c *
        paletteIndicator
          (G.missingColorsAt F (G.kempePairingStage F color p coin) v) d) /
        (Fintype.card (G.PairingStageCoin F color p) : ℝ) =
      pairAverage p
        (fun a b ↦ paletteIndicator (G.missingColorsAt F color v) a *
          paletteIndicator (G.missingColorsAt F color v) b) c d := by
  by_cases hpair : partner (Fin q) p c = d
  · have hbit (coin : G.PairingStageCoin F color p) :
        G.pairingStageBit F color p coin v d =
          G.pairingStageBit F color p coin v c := by
      simpa [hpair] using G.pairingStageBit_partner F color p coin v c
    have hpartnerD : partner (Fin q) p d = c := by
      rw [← hpair, partner_partner]
    simp_rw [G.paletteIndicator_kempePairingStage F color p]
    rw [show (∑ coin : G.PairingStageCoin F color p,
        (if G.pairingStageBit F color p coin v c then
            paletteIndicator (G.missingColorsAt F color v)
              (partner (Fin q) p c)
          else paletteIndicator (G.missingColorsAt F color v) c) *
        (if G.pairingStageBit F color p coin v d then
            paletteIndicator (G.missingColorsAt F color v)
              (partner (Fin q) p d)
          else paletteIndicator (G.missingColorsAt F color v) d)) =
        ∑ _coin : G.PairingStageCoin F color p,
          paletteIndicator (G.missingColorsAt F color v) c *
            paletteIndicator (G.missingColorsAt F color v) d by
      apply Finset.sum_congr rfl
      intro coin _hcoin
      rw [hbit coin, hpartnerD, hpair]
      by_cases hb : G.pairingStageBit F color p coin v c <;>
        simp [hb, mul_comm]]
    unfold pairAverage
    simp [hcd, hpair]
  · let sourceC := G.pairingStageSourceAt F color p v c
    let sourceD := G.pairingStageSourceAt F color p v d
    have hsources : sourceC ≠ sourceD :=
      G.pairingStageSourceAt_ne_of_ne_of_partner_ne
        F color p v hcd hpair
    let f : Bool → ℝ := fun bit ↦
      if bit then
        paletteIndicator (G.missingColorsAt F color v)
          (partner (Fin q) p c)
      else paletteIndicator (G.missingColorsAt F color v) c
    let g : Bool → ℝ := fun bit ↦
      if bit then
        paletteIndicator (G.missingColorsAt F color v)
          (partner (Fin q) p d)
      else paletteIndicator (G.missingColorsAt F color v) d
    rw [show (∑ coin : G.PairingStageCoin F color p,
        paletteIndicator
            (G.missingColorsAt F (G.kempePairingStage F color p coin) v) c *
          paletteIndicator
            (G.missingColorsAt F (G.kempePairingStage F color p coin) v) d) =
        ∑ coin : G.PairingStageCoin F color p,
          f (coin sourceC) * g (coin sourceD) by
      apply Finset.sum_congr rfl
      intro coin _hcoin
      rw [G.paletteIndicator_kempePairingStage F color p coin v c,
        G.paletteIndicator_kempePairingStage F color p coin v d]
      rfl]
    rw [average_boolWords_apply_mul_of_ne sourceC sourceD hsources f g]
    unfold pairAverage
    simp [hcd, hpair, f, g]
    ring

theorem sum_paletteIndicator_mul_kempePairingStage {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (p : Pairing (Fin q)) (v : G.V) {c d : Fin q} (hcd : c ≠ d) :
    (∑ coin : G.PairingStageCoin F color p,
      paletteIndicator
          (G.missingColorsAt F (G.kempePairingStage F color p coin) v) c *
        paletteIndicator
          (G.missingColorsAt F (G.kempePairingStage F color p coin) v) d) =
      (Fintype.card (G.PairingStageCoin F color p) : ℝ) *
        pairAverage p
          (fun a b ↦ paletteIndicator (G.missingColorsAt F color v) a *
            paletteIndicator (G.missingColorsAt F color v) b) c d := by
  have hcard :
      (Fintype.card (G.PairingStageCoin F color p) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simpa [mul_comm] using (div_eq_iff hcard).mp
    (G.average_paletteIndicator_mul_kempePairingStage
      F color p v hcd)

end

end WeightedMultigraph
end WeightedEdgeColoring
