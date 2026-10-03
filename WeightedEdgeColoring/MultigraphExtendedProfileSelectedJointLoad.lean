import WeightedEdgeColoring.MultigraphExtendedProfileSelectedStateSafety
import WeightedEdgeColoring.MultigraphExtendedProfileNormalizedTinyResidualRounding
import WeightedEdgeColoring.MultigraphOrdinaryMatchingExtraction

/-!
# Joint load of selected large and tiny options

The ordinary matching extraction theorem usually ends with the coarse bound
`load <= 1`.  Here we retain the sharper intermediate bound: its load is at
most the sum of the concrete selected large-slot sizes.  This can then be
added to the tiny-edge load in the same palette and compared with the exact
large-slot-plus-reservoir safety inequality of the selected state.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})

/-- Integral load of the ordinary edges selected by an ordinary rank-three
matching, before extending the partial colour map outside the selected set. -/
def selectedOrdinaryIntegralColorLoad {q K : ℕ}
    (M : Finset (OrdinarySlotChoice G.E (Fin q) K))
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (v : G.V) (c : Fin q) : ℝ :=
  ∑ e : {e // e ∈ G.ordinarySelectedEdges M},
    if G.Inc v e.1 ∧ G.selectedOrdinaryColor M hM e = c then
      G.weight e.1
    else 0

/-- The exact intermediate packing bound: selected ordinary load is bounded
by the sizes of the distinct concrete places it uses. -/
theorem selectedOrdinaryIntegralColorLoad_le_slotSum
    {q K : ℕ} {M : Finset (OrdinarySlotChoice G.E (Fin q) K)}
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (slotSize : G.V → Fin q → Fin K → ℝ)
    (hslot0 : ∀ v c i, 0 ≤ slotSize v c i)
    (hleft : ∀ o ∈ M,
      G.weight o.job ≤ slotSize (G.fst o.job) o.color o.leftPlace)
    (hright : ∀ o ∈ M,
      G.weight o.job ≤ slotSize (G.snd o.job) o.color o.rightPlace)
    (v : G.V) (c : Fin q) :
    G.selectedOrdinaryIntegralColorLoad M hM v c ≤
      ∑ i, slotSize v c i := by
  classical
  let T : Finset {e // e ∈ G.ordinarySelectedEdges M} :=
    Finset.univ.filter fun e ↦
      G.Inc v e.1 ∧ G.selectedOrdinaryColor M hM e = c
  have hfit : ∀ e ∈ T,
      G.weight e.1 ≤
        slotSize v c (G.selectedOrdinaryPlaceAt M hM v e) := by
    intro e heT
    have heData : G.Inc v e.1 ∧
        G.selectedOrdinaryColor M hM e = c := by
      simpa [T] using (Finset.mem_filter.mp heT).2
    let oe := G.selectedOrdinaryOption M hM e.1 e.2
    have hoeM : oe ∈ M := G.selectedOrdinaryOption_mem M hM e.1 e.2
    have hcolor : oe.color = c := by
      simpa [oe, selectedOrdinaryColor] using heData.2
    rcases heData.1 with hev | hev
    · simpa [oe, selectedOrdinaryPlaceAt, hev, hcolor] using
        hleft oe hoeM
    · have hne : G.fst e.1 ≠ v := by
        intro h
        exact G.noLoop e.1 (h.trans hev.symm)
      simpa [oe, selectedOrdinaryPlaceAt, hne, hev, hcolor] using
        hright oe hoeM
  have hinj : Set.InjOn (G.selectedOrdinaryPlaceAt M hM v) (T : Set _) := by
    intro e he f hf
    apply G.selectedOrdinaryPlaceAt_injective_on hM v c
    · simpa [T] using (Finset.mem_filter.mp he).2
    · simpa [T] using (Finset.mem_filter.mp hf).2
  calc
    G.selectedOrdinaryIntegralColorLoad M hM v c =
        ∑ e ∈ T, G.weight e.1 := by
      unfold selectedOrdinaryIntegralColorLoad
      rw [Finset.sum_filter]
    _ ≤ ∑ e ∈ T,
        slotSize v c (G.selectedOrdinaryPlaceAt M hM v e) :=
      Finset.sum_le_sum hfit
    _ = ∑ i ∈ T.image (G.selectedOrdinaryPlaceAt M hM v),
        slotSize v c i := by
      symm
      exact Finset.sum_image hinj
    _ ≤ ∑ i : Fin K, slotSize v c i :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun i _hi _hall ↦ hslot0 v c i)

/-- Evaluate a subtype-indexed tiny decision on the original edge type. -/
def tinyDecisionAt {q : ℕ} (R : Finset G.E)
    (decision : {e : G.E // e ∈ R} → Option (Fin q))
    (e : G.E) : Option (Fin q) :=
  if he : e ∈ R then decision ⟨e, he⟩ else none

@[simp] theorem tinyDecisionAt_of_mem {q : ℕ} (R : Finset G.E)
    (decision : {e : G.E // e ∈ R} → Option (Fin q))
    {e : G.E} (he : e ∈ R) :
    G.tinyDecisionAt R decision e = decision ⟨e, he⟩ := by
  simp [tinyDecisionAt, he]

/-- Tiny edges which the integral decision actually colours. -/
def tinyDecisionColoredEdges {q : ℕ} (R : Finset G.E)
    (decision : {e : G.E // e ∈ R} → Option (Fin q)) : Finset G.E :=
  R.filter fun e ↦ G.tinyDecisionAt R decision e ≠ none

/-- Put an ordinary matching and a tiny decision into one common palette.
The disjointness needed for this definition's later use is proved
separately. -/
def ordinaryTinyJointColor {q K : ℕ} (hq : 0 < q)
    (M : Finset (OrdinarySlotChoice G.E (Fin q) K))
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (R : Finset G.E)
    (decision : {e : G.E // e ∈ R} → Option (Fin q))
    (e : G.E) : Fin q :=
  if he : e ∈ G.ordinarySelectedEdges M then
    G.selectedOrdinaryColor M hM ⟨e, he⟩
  else
    (G.tinyDecisionAt R decision e).getD ⟨0, hq⟩

/-- Exact load identity for the common-palette union of an ordinary matching
and a tiny colour decision. -/
theorem colorLoadOn_ordinaryTinyJoint_eq
    {q K : ℕ} (hq : 0 < q)
    (M : Finset (OrdinarySlotChoice G.E (Fin q) K))
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (R : Finset G.E)
    (decision : {e : G.E // e ∈ R} → Option (Fin q))
    (hdisj : Disjoint (G.ordinarySelectedEdges M) R)
    (v : G.V) (c : Fin q) :
    G.colorLoadOn
        (G.ordinarySelectedEdges M ∪ G.tinyDecisionColoredEdges R decision)
        (G.ordinaryTinyJointColor hq M hM R decision) v c =
      G.selectedOrdinaryIntegralColorLoad M hM v c +
        G.tinyResidualIntegralColorLoad decision v c := by
  classical
  have hdisjColored : Disjoint (G.ordinarySelectedEdges M)
      (G.tinyDecisionColoredEdges R decision) := by
    rw [Finset.disjoint_left]
    intro e heOrd heTiny
    exact Finset.disjoint_left.mp hdisj heOrd
      (Finset.mem_filter.mp heTiny).1
  have hordinary :
      (∑ e ∈ G.ordinarySelectedEdges M,
        if G.Inc v e ∧
            G.ordinaryTinyJointColor hq M hM R decision e = c then
          G.weight e else 0) =
        G.selectedOrdinaryIntegralColorLoad M hM v c := by
    calc
      (∑ e ∈ G.ordinarySelectedEdges M,
          if G.Inc v e ∧
              G.ordinaryTinyJointColor hq M hM R decision e = c then
            G.weight e else 0) =
          ∑ e ∈ G.ordinarySelectedEdges M,
            if G.Inc v e ∧
                G.extendSelectedOrdinaryColor hq M hM e = c then
              G.weight e else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        simp [ordinaryTinyJointColor, he,
          G.extendSelectedOrdinaryColor_of_mem hq M hM he]
      _ = G.selectedOrdinaryIntegralColorLoad M hM v c := by
        unfold selectedOrdinaryIntegralColorLoad
        calc
          (∑ e ∈ G.ordinarySelectedEdges M,
              if G.Inc v e ∧
                  G.extendSelectedOrdinaryColor hq M hM e = c then
                G.weight e else 0) =
              ∑ e : {e : G.E // e ∈ G.ordinarySelectedEdges M},
                if G.Inc v e.1 ∧
                    G.extendSelectedOrdinaryColor hq M hM e.1 = c then
                  G.weight e.1 else 0 := by
            exact Finset.sum_subtype
              (p := fun e : G.E ↦ e ∈ G.ordinarySelectedEdges M)
              (G.ordinarySelectedEdges M) (by intro e; simp) _
          _ = ∑ e : {e : G.E // e ∈ G.ordinarySelectedEdges M},
                if G.Inc v e.1 ∧ G.selectedOrdinaryColor M hM e = c then
                  G.weight e.1 else 0 := by
            apply Finset.sum_congr rfl
            intro e _he
            simp [G.extendSelectedOrdinaryColor_of_mem hq M hM e.2]
  have htiny :
      (∑ e ∈ G.tinyDecisionColoredEdges R decision,
        if G.Inc v e ∧
            G.ordinaryTinyJointColor hq M hM R decision e = c then
          G.weight e else 0) =
        G.tinyResidualIntegralColorLoad decision v c := by
    calc
      (∑ e ∈ G.tinyDecisionColoredEdges R decision,
          if G.Inc v e ∧
              G.ordinaryTinyJointColor hq M hM R decision e = c then
            G.weight e else 0) =
          ∑ e ∈ R,
            if G.Inc v e ∧ G.tinyDecisionAt R decision e = some c then
              G.weight e else 0 := by
        unfold tinyDecisionColoredEdges
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e heR
        have heOrd : e ∉ G.ordinarySelectedEdges M := by
          intro he
          exact Finset.disjoint_left.mp hdisj he heR
        cases hdecision : G.tinyDecisionAt R decision e with
        | none => simp [ordinaryTinyJointColor, heOrd, hdecision]
        | some d =>
            by_cases hdc : d = c
            · simp [ordinaryTinyJointColor, heOrd, hdecision, hdc]
            · simp [ordinaryTinyJointColor, heOrd, hdecision, hdc]
      _ = G.tinyResidualIntegralColorLoad decision v c := by
        unfold tinyResidualIntegralColorLoad
        calc
          (∑ e ∈ R,
              if G.Inc v e ∧ G.tinyDecisionAt R decision e = some c then
                G.weight e else 0) =
              ∑ e : {e : G.E // e ∈ R},
                if G.Inc v e.1 ∧
                    G.tinyDecisionAt R decision e.1 = some c then
                  G.weight e.1 else 0 := by
            exact Finset.sum_subtype
              (p := fun e : G.E ↦ e ∈ R) R (by intro e; simp) _
          _ = ∑ e : {e : G.E // e ∈ R},
                if G.Inc v e.1 ∧ decision e = some c then
                  G.weight e.1 else 0 := by
            apply Finset.sum_congr rfl
            intro e _he
            simp [tinyDecisionAt, e.2]
  unfold WeightedMultigraph.colorLoadOn
  change
    (∑ e ∈ G.ordinarySelectedEdges M ∪
        G.tinyDecisionColoredEdges R decision,
      if G.Inc v e ∧
          G.ordinaryTinyJointColor hq M hM R decision e = c then
        G.weight e else 0) = _
  rw [Finset.sum_union hdisjColored, hordinary, htiny]

/-- A rowwise bound for the two summands in the exact load identity is an
actual feasible coloring of their common-palette union. -/
theorem ordinaryTinyJoint_isFeasibleOn_of_load_le_one
    {q K : ℕ} (hq : 0 < q)
    (M : Finset (OrdinarySlotChoice G.E (Fin q) K))
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (R : Finset G.E)
    (decision : {e : G.E // e ∈ R} → Option (Fin q))
    (hdisj : Disjoint (G.ordinarySelectedEdges M) R)
    (hload : ∀ v c,
      G.selectedOrdinaryIntegralColorLoad M hM v c +
        G.tinyResidualIntegralColorLoad decision v c ≤ 1) :
    G.IsFeasibleOn
      (G.ordinarySelectedEdges M ∪ G.tinyDecisionColoredEdges R decision)
      (G.ordinaryTinyJointColor hq M hM R decision) := by
  intro v c
  rw [G.colorLoadOn_ordinaryTinyJoint_eq hq M hM R decision hdisj v c]
  exact hload v c

variable {Class : Type w} [Fintype Class] [DecidableEq Class]
variable {B k N : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- Every positive physical reservoir of a selected extended state has size
at least the rounding unit `r`.  The repair reservoir has size one, which is
why that case needs `r <= 1`. -/
theorem extendedProfileReservoirSize_ge_r_of_pos
    (hr1 : r ≤ 1) (v : G.V) (z : G.ExtendedProfileState R0 v)
    (hpos : 0 < G.extendedProfileReservoirSize R0 v z) :
    r ≤ G.extendedProfileReservoirSize R0 v z := by
  rcases z with P | t
  · have hn0 : P.1.2.val ≠ 0 := by
      intro hn
      simp [extendedProfileReservoirSize, hn] at hpos
    have hn : 1 ≤ P.1.2.val := Nat.one_le_iff_ne_zero.mpr hn0
    have hnReal : (1 : ℝ) ≤ (P.1.2.val : ℕ) := by
      exact_mod_cast hn
    simp only [extendedProfileReservoirSize]
    nlinarith
  · by_cases h1 : t.1 = 1
    · simpa [extendedProfileReservoirSize, h1] using hr1
    · simp [extendedProfileReservoirSize, h1] at hpos

/-- A selected capacity row bounds the normalized tiny reservoir load. -/
theorem selectedBlockNormalizedTinyReservoirLoad_lt_of_capacityRow
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleftParam : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (a delta : ℝ) (v : G.V) (c : Fin (B * k))
    (hcapacity :
      G.selectedBlockCapacityLoad R0 rho omega choice (Sum.inr (v, c)) /
          ((B * k : ℕ) : ℝ) <
        a * G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c) + delta) :
    G.selectedBlockNormalizedTinyReservoirLoad R0 rho omega choice (v, c) <
      a * G.extendedProfileReservoirSize R0 v
        (G.decodedExtendedProfileBlockSelection R0 choice v c) + delta := by
  have hnReal : (0 : ℝ) < ((B * k : ℕ) : ℝ) := by
    exact_mod_cast hn
  have hrawEq :
      G.selectedBlockCapacityLoad R0 rho omega choice (Sum.inr (v, c)) /
          ((B * k : ℕ) : ℝ) =
        G.selectedBlockTinyReservoirLoad R0 rho omega choice (v, c) := by
    rw [G.selectedBlockCapacityLoad_tiny_eq R0 rho omega choice (v, c)]
    field_simp [hnReal.ne'] <;> ring
  have hraw : G.selectedBlockTinyReservoirLoad
      R0 rho omega choice (v, c) <
        a * G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c) + delta := by
    rw [← hrawEq]
    exact hcapacity
  exact lt_of_le_of_lt
    (G.selectedBlockNormalizedTinyReservoirLoad_le R0
      hn hs hq hr0 hleftParam homega0 homega1 hrho choice (v, c))
    hraw

end WeightedMultigraph

end

end WeightedEdgeColoring
