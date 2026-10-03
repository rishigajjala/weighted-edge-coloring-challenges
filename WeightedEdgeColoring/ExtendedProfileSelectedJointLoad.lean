import WeightedEdgeColoring.ExtendedProfileSelectedStateSafety
import WeightedEdgeColoring.ExtendedProfileNormalizedTinyResidualRounding
import WeightedEdgeColoring.LargeEdgeMatchingExtraction

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

namespace WeightedSimpleGraph

universe u w

variable (G : WeightedSimpleGraph.{u})

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
    G.asMultigraph.colorLoadOn
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
    G.asMultigraph.IsFeasibleOn
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

/-- The ordinary part of a combined selected-profile matching is bounded by
the sum of the concrete large places in the selected state. -/
theorem selectedNormalizedLargeMatching_load_le_concreteSlotSum
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleftParam : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ)
    (M : Finset (QuantizedCopy N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice))))
    (hM : ((G.largeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
      bucket extraCount).quantized N
        (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
          (G.selectedBlockResidualOptionMass R0 rho omega choice))).IsPartialMatching M)
    (v : G.V) (c : Fin (B * k)) :
    let O := G.selectedOrdinaryBaseOptions
      (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
      (G.selectedBlockResidualOptionMass R0 rho omega choice) M
    let hO := G.selectedOrdinaryBaseOptions_isPartialMatching
      (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
      (G.selectedBlockResidualOptionMass R0 rho omega choice) M hM
    G.selectedOrdinaryIntegralColorLoad O hO v c ≤
      ∑ i, G.selectedBlockConcreteSlotSize R0 choice v c i := by
  dsimp only
  apply G.selectedOrdinaryIntegralColorLoad_le_slotSum
    (G.selectedOrdinaryBaseOptions_isPartialMatching
      (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
      (G.selectedBlockResidualOptionMass R0 rho omega choice) M hM)
    (G.selectedBlockConcreteSlotSize R0 choice)
    (G.selectedBlockConcreteSlotSize_nonneg R0 choice)
  · intro o ho
    apply G.weight_le_selectedBlockConcreteSlotSize_fst_of_large_pos R0
      hn hs hq hr0 hleftParam rho omega homega0 homega1 hrho choice
    exact G.selectedOrdinaryBaseOptions_mass_pos
      (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
      (G.selectedBlockResidualOptionMass R0 rho omega choice) M ho
  · intro o ho
    apply G.weight_le_selectedBlockConcreteSlotSize_snd_of_large_pos R0
      hn hs hq hr0 hleftParam rho omega homega0 homega1 hrho choice
    exact G.selectedOrdinaryBaseOptions_mass_pos
      (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
      (G.selectedBlockResidualOptionMass R0 rho omega choice) M ho

/-- Positive normalized large mass cannot occur on an edge below the tiny
threshold.  Hence the ordinary matching and every tiny decision use disjoint
edge sets. -/
theorem selectedNormalizedLargeMatching_disjoint_tinyEdges
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ)
    (M : Finset (QuantizedCopy N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice)))) :
    let O := G.selectedOrdinaryBaseOptions
      (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
      (G.selectedBlockResidualOptionMass R0 rho omega choice) M
    Disjoint (G.ordinarySelectedEdges O) (G.selectedBlockTinyEdges β) := by
  dsimp only
  rw [Finset.disjoint_left]
  intro e heOrd heTiny
  rcases (G.mem_ordinarySelectedEdges_iff _ e).mp heOrd with
    ⟨o, ho, rfl⟩
  have hpos := G.selectedOrdinaryBaseOptions_mass_pos
    (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
    (G.selectedBlockResidualOptionMass R0 rho omega choice) M ho
  have hzero := G.selectedBlockNormalizedLargeOptionMass_eq_zero_of_tiny
    R0 rho omega choice o.job o.color o.leftPlace o.rightPlace
      (G.mem_selectedBlockTinyEdges.mp heTiny)
  exact (ne_of_gt hpos) hzero

/-- Convert the reservoir-sensitive candidate-row output into the normalized
tiny fractional-load bound used by the joint coloring theorem. -/
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

/-- Joint same-palette load bound.  If normalized tiny fractional load is at
most `a` times the selected physical reservoir plus `delta`, the current
two-constraint rounding loses another `2*beta`.  Thus the large and tiny
integral loads together are bounded by `1 + delta + 2*beta` whenever
`0 <= a <= 1`.

The positive additive term is intentional: the selected-state safety lemma
alone has no uniform slack with which to absorb it. -/
theorem selectedNormalizedLarge_add_tinyIntegral_load_le_one_add_error
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleftParam : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ)
    (M : Finset (QuantizedCopy N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice))))
    (hM : ((G.largeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
      bucket extraCount).quantized N
        (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
          (G.selectedBlockResidualOptionMass R0 rho omega choice))).IsPartialMatching M)
    (decision : {e : G.E // e ∈ G.selectedBlockTinyEdges β} →
      Option (Fin (B * k)))
    (a delta : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (htinyFractional : ∀ v c,
      G.selectedBlockNormalizedTinyReservoirLoad R0 rho omega choice (v, c) ≤
        a * G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c) + delta)
    (htinyIntegral : ∀ v c,
      G.tinyResidualIntegralColorLoad decision v c ≤
        G.selectedBlockNormalizedTinyReservoirLoad
          R0 rho omega choice (v, c) + 2 * β)
    (v : G.V) (c : Fin (B * k)) :
    let O := G.selectedOrdinaryBaseOptions
      (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
      (G.selectedBlockResidualOptionMass R0 rho omega choice) M
    let hO := G.selectedOrdinaryBaseOptions_isPartialMatching
      (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
      (G.selectedBlockResidualOptionMass R0 rho omega choice) M hM
    G.selectedOrdinaryIntegralColorLoad O hO v c +
        G.tinyResidualIntegralColorLoad decision v c ≤
      1 + delta + 2 * β := by
  dsimp only
  let reservoir := G.extendedProfileReservoirSize R0 v
    (G.decodedExtendedProfileBlockSelection R0 choice v c)
  have hlarge := G.selectedNormalizedLargeMatching_load_le_concreteSlotSum
    R0 hn hs hq hr0 hleftParam rho omega homega0 homega1 hrho choice
    bucket extraCount M hM v c
  have htiny := (htinyIntegral v c).trans
    (add_le_add_left (htinyFractional v c) (2 * β))
  have hsafe := G.sum_selectedBlockConcreteSlotSize_add_reservoir_le_one
    R0 choice v c
  have hreservoir0 : 0 ≤ reservoir :=
    G.extendedProfileReservoirSize_nonneg R0 v _
  have hareservoir : a * reservoir ≤ reservoir := by
    nlinarith
  calc
    G.selectedOrdinaryIntegralColorLoad
          (G.selectedOrdinaryBaseOptions
            (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
            (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
            (G.selectedBlockResidualOptionMass R0 rho omega choice) M)
          (G.selectedOrdinaryBaseOptions_isPartialMatching
            (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
            (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
            (G.selectedBlockResidualOptionMass R0 rho omega choice) M hM)
          v c + G.tinyResidualIntegralColorLoad decision v c ≤
        (∑ i, G.selectedBlockConcreteSlotSize R0 choice v c i) +
          (a * reservoir + delta + 2 * β) := by
      exact add_le_add hlarge htiny
    _ ≤ ((∑ i, G.selectedBlockConcreteSlotSize R0 choice v c i) +
          reservoir) + delta + 2 * β := by
      linarith
    _ ≤ 1 + delta + 2 * β := by
      linarith

/-- Exact feasibility follows if the additive tiny-rounding error fits in
the unused fraction `(1-a)` of the selected reservoir.  This pointwise
condition is the scalar slack still missing from the current profile
pipeline. -/
theorem selectedNormalizedLarge_add_tinyIntegral_load_le_one_of_slack
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleftParam : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ)
    (M : Finset (QuantizedCopy N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice))))
    (hM : ((G.largeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
      bucket extraCount).quantized N
        (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
          (G.selectedBlockResidualOptionMass R0 rho omega choice))).IsPartialMatching M)
    (decision : {e : G.E // e ∈ G.selectedBlockTinyEdges β} →
      Option (Fin (B * k)))
    (a delta : ℝ)
    (htinyFractional : ∀ v c,
      G.selectedBlockNormalizedTinyReservoirLoad R0 rho omega choice (v, c) ≤
        a * G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c) + delta)
    (htinyIntegral : ∀ v c,
      G.tinyResidualIntegralColorLoad decision v c ≤
        G.selectedBlockNormalizedTinyReservoirLoad
          R0 rho omega choice (v, c) + 2 * β)
    (v : G.V) (c : Fin (B * k))
    (hslack :
      delta + 2 * β ≤
        (1 - a) * G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c))
    :
    let O := G.selectedOrdinaryBaseOptions
      (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
      (G.selectedBlockResidualOptionMass R0 rho omega choice) M
    let hO := G.selectedOrdinaryBaseOptions_isPartialMatching
      (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
      (G.selectedBlockResidualOptionMass R0 rho omega choice) M hM
    G.selectedOrdinaryIntegralColorLoad O hO v c +
        G.tinyResidualIntegralColorLoad decision v c ≤ 1 := by
  dsimp only
  let reservoir := G.extendedProfileReservoirSize R0 v
    (G.decodedExtendedProfileBlockSelection R0 choice v c)
  have hlarge := G.selectedNormalizedLargeMatching_load_le_concreteSlotSum
    R0 hn hs hq hr0 hleftParam rho omega homega0 homega1 hrho choice
    bucket extraCount M hM v c
  have htiny := (htinyIntegral v c).trans
    (add_le_add_left (htinyFractional v c) (2 * β))
  have hsafe := G.sum_selectedBlockConcreteSlotSize_add_reservoir_le_one
    R0 choice v c
  have hslack' : delta + 2 * β ≤ (1 - a) * reservoir :=
    hslack
  calc
    G.selectedOrdinaryIntegralColorLoad
          (G.selectedOrdinaryBaseOptions
            (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
            (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
            (G.selectedBlockResidualOptionMass R0 rho omega choice) M)
          (G.selectedOrdinaryBaseOptions_isPartialMatching
            (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
            (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
            (G.selectedBlockResidualOptionMass R0 rho omega choice) M hM)
          v c + G.tinyResidualIntegralColorLoad decision v c ≤
        (∑ i, G.selectedBlockConcreteSlotSize R0 choice v c i) +
          (a * reservoir + delta + 2 * β) := by
      exact add_le_add hlarge htiny
    _ ≤ (∑ i, G.selectedBlockConcreteSlotSize R0 choice v c i) +
          reservoir := by
      nlinarith
    _ ≤ 1 := hsafe

/-- Rowwise support closes the scalar slack gap.  A row with no selected tiny
edge has zero tiny load.  Otherwise support preservation supplies a positive
physical reservoir, hence a reservoir of size at least `r`.  The single
uniform inequality `delta + 2*beta <= (1-a)*r` then absorbs both selector and
tiny-rounding errors. -/
theorem selectedNormalizedLarge_add_tinyIntegral_load_le_one_of_support
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1)
    (hleftParam : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ)
    (M : Finset (QuantizedCopy N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice))))
    (hM : ((G.largeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
      bucket extraCount).quantized N
        (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
          (G.selectedBlockResidualOptionMass R0 rho omega choice))).IsPartialMatching M)
    (decision : {e : G.E // e ∈ G.selectedBlockTinyEdges β} →
      Option (Fin (B * k)))
    (htinySupport : ∀ e c, decision e = some c →
      0 < G.extendedProfileReservoirSize R0 (G.fst e.1)
          (G.decodedExtendedProfileBlockSelection
            R0 choice (G.fst e.1) c) ∧
        0 < G.extendedProfileReservoirSize R0 (G.snd e.1)
          (G.decodedExtendedProfileBlockSelection
            R0 choice (G.snd e.1) c))
    (a delta : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (htinyFractional : ∀ v c,
      G.selectedBlockNormalizedTinyReservoirLoad R0 rho omega choice (v, c) ≤
        a * G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c) + delta)
    (htinyIntegral : ∀ v c,
      G.tinyResidualIntegralColorLoad decision v c ≤
        G.selectedBlockNormalizedTinyReservoirLoad
          R0 rho omega choice (v, c) + 2 * β)
    (herror : delta + 2 * β ≤ (1 - a) * r)
    (v : G.V) (c : Fin (B * k)) :
    let O := G.selectedOrdinaryBaseOptions
      (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
      (G.selectedBlockResidualOptionMass R0 rho omega choice) M
    let hO := G.selectedOrdinaryBaseOptions_isPartialMatching
      (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
      (G.selectedBlockResidualOptionMass R0 rho omega choice) M hM
    G.selectedOrdinaryIntegralColorLoad O hO v c +
        G.tinyResidualIntegralColorLoad decision v c ≤ 1 := by
  dsimp only
  by_cases hex : ∃ e,
      G.Inc v e.1 ∧ decision e = some c
  · rcases hex with ⟨e, hinc, hdecision⟩
    have hsupport := htinySupport e c hdecision
    have hreservoirPos :
        0 < G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c) := by
      rcases hinc with hfst | hsnd
      · rw [← hfst]
        exact hsupport.1
      · rw [← hsnd]
        exact hsupport.2
    have hreservoirGe :
        r ≤ G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c) :=
      G.extendedProfileReservoirSize_ge_r_of_pos R0 hr1 v _ hreservoirPos
    have hcoef : 0 ≤ 1 - a := sub_nonneg.mpr ha1
    have hslack : delta + 2 * β ≤
        (1 - a) * G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c) :=
      herror.trans (mul_le_mul_of_nonneg_left hreservoirGe hcoef)
    exact G.selectedNormalizedLarge_add_tinyIntegral_load_le_one_of_slack
      R0 hn hs hq hr0 hleftParam rho omega homega0 homega1 hrho choice
      bucket extraCount M hM decision a delta htinyFractional htinyIntegral
      v c hslack
  · have htinyZero :
        G.tinyResidualIntegralColorLoad decision v c = 0 := by
      unfold tinyResidualIntegralColorLoad
      apply Finset.sum_eq_zero
      intro e _he
      have hnot : ¬ (G.Inc v e.1 ∧ decision e = some c) := by
        intro he
        exact hex ⟨e, he⟩
      simp [hnot]
    have hlarge := G.selectedNormalizedLargeMatching_load_le_concreteSlotSum
      R0 hn hs hq hr0 hleftParam rho omega homega0 homega1 hrho choice
      bucket extraCount M hM v c
    have hslot := G.sum_selectedBlockConcreteSlotSize_le_one R0 choice v c
    rw [htinyZero, add_zero]
    exact hlarge.trans hslot

/-- The rowwise support closure gives a genuine feasible partial coloring on
the union of the selected large edges and the tiny edges that were colored.
Both parts use the same palette. -/
theorem selectedNormalizedLarge_tinyDecision_isFeasibleOn_of_support
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1)
    (hleftParam : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ)
    (M : Finset (QuantizedCopy N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice))))
    (hM : ((G.largeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
      bucket extraCount).quantized N
        (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
          (G.selectedBlockResidualOptionMass R0 rho omega choice))).IsPartialMatching M)
    (decision : {e : G.E // e ∈ G.selectedBlockTinyEdges β} →
      Option (Fin (B * k)))
    (htinySupport : ∀ e c, decision e = some c →
      0 < G.extendedProfileReservoirSize R0 (G.fst e.1)
          (G.decodedExtendedProfileBlockSelection
            R0 choice (G.fst e.1) c) ∧
        0 < G.extendedProfileReservoirSize R0 (G.snd e.1)
          (G.decodedExtendedProfileBlockSelection
            R0 choice (G.snd e.1) c))
    (a delta : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (htinyFractional : ∀ v c,
      G.selectedBlockNormalizedTinyReservoirLoad R0 rho omega choice (v, c) ≤
        a * G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c) + delta)
    (htinyIntegral : ∀ v c,
      G.tinyResidualIntegralColorLoad decision v c ≤
        G.selectedBlockNormalizedTinyReservoirLoad
          R0 rho omega choice (v, c) + 2 * β)
    (herror : delta + 2 * β ≤ (1 - a) * r) :
    let O := G.selectedOrdinaryBaseOptions
      (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
      (G.selectedBlockResidualOptionMass R0 rho omega choice) M
    let hO := G.selectedOrdinaryBaseOptions_isPartialMatching
      (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
      (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
      (G.selectedBlockResidualOptionMass R0 rho omega choice) M hM
    G.asMultigraph.IsFeasibleOn
      (G.ordinarySelectedEdges O ∪
        G.tinyDecisionColoredEdges (G.selectedBlockTinyEdges β) decision)
      (G.ordinaryTinyJointColor hn O hO
        (G.selectedBlockTinyEdges β) decision) := by
  dsimp only
  apply G.ordinaryTinyJoint_isFeasibleOn_of_load_le_one hn
  · exact G.selectedNormalizedLargeMatching_disjoint_tinyEdges
      R0 rho omega choice bucket extraCount M
  · intro v c
    exact G.selectedNormalizedLarge_add_tinyIntegral_load_le_one_of_support
      R0 hn hs hq hr0 hr1 hleftParam rho omega homega0 homega1 hrho choice
      bucket extraCount M hM decision htinySupport a delta ha0 ha1
      htinyFractional htinyIntegral herror v c

/-- The support-preserving normalized tiny rounding theorem feeds directly
into the preceding rowwise closure.  The returned decision retains all
support and residual-loss information while sharing the original palette
with the ordinary matching. -/
theorem exists_selectedBlockTinyColorDecision_joint_load_le_one
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1)
    (hleftParam : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ)
    (M : Finset (QuantizedCopy N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice))))
    (hM : ((G.largeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
      bucket extraCount).quantized N
        (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
          (G.selectedBlockResidualOptionMass R0 rho omega choice))).IsPartialMatching M)
    (a delta : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (htinyFractional : ∀ v c,
      G.selectedBlockNormalizedTinyReservoirLoad R0 rho omega choice (v, c) ≤
        a * G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c) + delta)
    (herror : delta + 2 * β ≤ (1 - a) * r) :
    ∃ decision : {e : G.E // e ∈ G.selectedBlockTinyEdges β} →
        Option (Fin (B * k)),
      (∀ e c, decision e = some c →
        0 < G.selectedBlockNormalizedTinyOptionMass
            R0 rho omega choice e.1 c ∧
          0 < G.extendedProfileReservoirSize R0 (G.fst e.1)
            (G.decodedExtendedProfileBlockSelection
              R0 choice (G.fst e.1) c) ∧
          0 < G.extendedProfileReservoirSize R0 (G.snd e.1)
            (G.decodedExtendedProfileBlockSelection
              R0 choice (G.snd e.1) c)) ∧
      (∀ e, decision e = none →
        0 < G.selectedBlockResidualOptionMass R0 rho omega choice e.1) ∧
      (∀ v c,
        let O := G.selectedOrdinaryBaseOptions
          (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
          (G.selectedBlockResidualOptionMass R0 rho omega choice) M
        let hO := G.selectedOrdinaryBaseOptions_isPartialMatching
          (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
          (G.selectedBlockResidualOptionMass R0 rho omega choice) M hM
        G.selectedOrdinaryIntegralColorLoad O hO v c +
          G.tinyResidualIntegralColorLoad decision v c ≤ 1) ∧
      ∀ v,
        G.tinyResidualIntegralLossLoad decision v ≤
          G.tinyResidualLossLoad (G.selectedBlockTinyEdges β)
            (fun e ↦ G.selectedBlockResidualOptionMass
              R0 rho omega choice e.1) v + 2 * β := by
  obtain ⟨decision, hpositive, hresidual, hcolor, hloss⟩ :=
    G.exists_selectedBlockTinyColorDecision R0
      hn hs hq hr0 hleftParam rho omega homega0 homega1 hrho choice
  refine ⟨decision, hpositive, hresidual, ?_, hloss⟩
  intro v c
  apply G.selectedNormalizedLarge_add_tinyIntegral_load_le_one_of_support
    R0 hn hs hq hr0 hr1 hleftParam rho omega homega0 homega1 hrho choice
    bucket extraCount M hM decision
      (fun e d hed ↦ ⟨(hpositive e d hed).2.1,
        (hpositive e d hed).2.2⟩)
    a delta ha0 ha1 htinyFractional hcolor herror v c

/-- Support-preserving tiny rounding, stated as the actual common-palette
partial coloring that the graph-level composition step consumes. -/
theorem exists_selectedBlockTinyColorDecision_joint_isFeasibleOn
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1)
    (hleftParam : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ)
    (M : Finset (QuantizedCopy N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice))))
    (hM : ((G.largeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
      bucket extraCount).quantized N
        (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
          (G.selectedBlockResidualOptionMass R0 rho omega choice))).IsPartialMatching M)
    (a delta : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (htinyFractional : ∀ v c,
      G.selectedBlockNormalizedTinyReservoirLoad R0 rho omega choice (v, c) ≤
        a * G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c) + delta)
    (herror : delta + 2 * β ≤ (1 - a) * r) :
    ∃ decision : {e : G.E // e ∈ G.selectedBlockTinyEdges β} →
        Option (Fin (B * k)),
      (∀ e c, decision e = some c →
        0 < G.selectedBlockNormalizedTinyOptionMass
            R0 rho omega choice e.1 c ∧
          0 < G.extendedProfileReservoirSize R0 (G.fst e.1)
            (G.decodedExtendedProfileBlockSelection
              R0 choice (G.fst e.1) c) ∧
          0 < G.extendedProfileReservoirSize R0 (G.snd e.1)
            (G.decodedExtendedProfileBlockSelection
              R0 choice (G.snd e.1) c)) ∧
      (∀ e, decision e = none →
        0 < G.selectedBlockResidualOptionMass R0 rho omega choice e.1) ∧
      (let O := G.selectedOrdinaryBaseOptions
          (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
          (G.selectedBlockResidualOptionMass R0 rho omega choice) M
       let hO := G.selectedOrdinaryBaseOptions_isPartialMatching
          (B * k) (explicitLargeSlotBound β q r) N bucket extraCount
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
          (G.selectedBlockResidualOptionMass R0 rho omega choice) M hM
       G.asMultigraph.IsFeasibleOn
         (G.ordinarySelectedEdges O ∪
           G.tinyDecisionColoredEdges (G.selectedBlockTinyEdges β) decision)
         (G.ordinaryTinyJointColor hn O hO
           (G.selectedBlockTinyEdges β) decision)) ∧
      ∀ v,
        G.tinyResidualIntegralLossLoad decision v ≤
          G.tinyResidualLossLoad (G.selectedBlockTinyEdges β)
            (fun e ↦ G.selectedBlockResidualOptionMass
              R0 rho omega choice e.1) v + 2 * β := by
  obtain ⟨decision, hpositive, hresidual, hload, hloss⟩ :=
    G.exists_selectedBlockTinyColorDecision_joint_load_le_one R0
      hn hs hq hr0 hr1 hleftParam rho omega homega0 homega1 hrho choice
      bucket extraCount M hM a delta ha0 ha1 htinyFractional herror
  refine ⟨decision, hpositive, hresidual, ?_, hloss⟩
  dsimp only
  apply G.ordinaryTinyJoint_isFeasibleOn_of_load_le_one hn
  · exact G.selectedNormalizedLargeMatching_disjoint_tinyEdges
      R0 rho omega choice bucket extraCount M
  · exact hload

end WeightedSimpleGraph

end

end WeightedEdgeColoring
