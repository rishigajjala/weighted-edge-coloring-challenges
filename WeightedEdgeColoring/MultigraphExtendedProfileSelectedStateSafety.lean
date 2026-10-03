import WeightedEdgeColoring.MultigraphExtendedProfileSelectedNormalizedOptions

/-!
# Concrete bin sizes carried by selected extended-profile states

An extended state either records one rounded profile, the large-repair
state, the tiny-repair state, or the inactive state.  This file assigns a
concrete size to every padded large place.  For an actual profile these are
exactly its rounded ordinary slot sizes; the large-repair state has one
slot of size one; the other two special states have no large slot.

The large slots and the tiny reservoir of every state fit together in one
unit bin.  Moreover, the support-side predicate `ExtendedLargeSlotFits`
means exactly what the later matching extraction needs: the edge fits in
the corresponding concrete slot.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- Concrete size of one padded large place in an extended profile state. -/
def extendedProfileConcreteSlotSize
    (v : G.V) (z : G.ExtendedProfileState R0 v)
    (i : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  match z with
  | Sum.inl P =>
      ∑ j : G.RoundedProfileOrdinarySlot (R0 v).law P.1,
        if G.paddedLargeSlotCode (R0 v) (some ⟨P, j⟩) = i then
          max 0 (G.roundedProfileOrdinarySlotSize (R0 v).law P.1 j)
        else 0
  | Sum.inr t =>
      if t.1 = 0 then
        if G.paddedLargeSlotCode (R0 v) none = i then 1 else 0
      else 0

theorem extendedProfileConcreteSlotSize_nonneg
    (v : G.V) (z : G.ExtendedProfileState R0 v)
    (i : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.extendedProfileConcreteSlotSize R0 v z i := by
  rcases z with P | t
  · unfold extendedProfileConcreteSlotSize
    exact Finset.sum_nonneg fun j _hj ↦ by
      split
      · exact le_max_left _ _
      · exact le_rfl
  · by_cases h0 : t.1 = 0
    · simp only [extendedProfileConcreteSlotSize, h0, if_true]
      split <;> norm_num
    · simp [extendedProfileConcreteSlotSize, h0]

/-- Truncating a rounded ordinary size at zero remains bounded by the raw
large-edge load from which that rounded profile was made.  The `max` makes
the later matching interface robust even though `BoundedProfileLaw` does
not expose nonnegativity of every unused kept bucket. -/
private theorem sum_max_roundedProfileOrdinarySlotSize_code_le
    (v : G.V) (a : Fin (R0 v).law.m) :
    (∑ j : G.RoundedProfileOrdinarySlot (R0 v).law
        (G.roundedProfileCode (R0 v).law hβ hr a),
      max 0 (G.roundedProfileOrdinarySlotSize (R0 v).law
        (G.roundedProfileCode (R0 v).law hβ hr a) j)) ≤
      ∑ e ∈ (G.rawProfile β ((R0 v).law.outcome a)).ordinary,
        G.weight e.1 := by
  classical
  let L := (R0 v).law
  let E := G.largeEdges β (L.outcome a)
  have hsupport : ∀ e ∈ E, G.weight e.1 ∈ G.lawSlotSupport β L.outcome := by
    intro e he
    apply Finset.mem_biUnion.mpr
    exact ⟨a, Finset.mem_univ a, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
  have hrange : ∀ e ∈ E, L.round (G.weight e.1) ∈ L.kept := by
    intro e he
    exact L.round_mem _ (hsupport e he)
  let count : ℝ → ℕ := fun z ↦ if hz : z ∈ L.kept then
    G.roundedMultiplicity L a ⟨z, hz⟩ else 0
  have hsub :
      (∑ z : {z // z ∈ L.kept},
        (G.roundedMultiplicity L a z : ℝ) * max 0 z.1) =
      ∑ z ∈ L.kept, (count z : ℝ) * max 0 z := by
    symm
    simpa [count] using Finset.sum_subtype
      (F := inferInstanceAs (Fintype {z // z ∈ L.kept})) L.kept
      (fun z ↦ Iff.rfl) (fun z ↦ (count z : ℝ) * max 0 z)
  have hfiber := Finset.sum_fiberwise_eq_sum_filter E L.kept
    (fun e ↦ L.round (G.weight e.1))
    (fun e ↦ max 0 (L.round (G.weight e.1)))
  simp only [Fintype.sum_sigma, roundedProfileOrdinarySlotSize,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  change (∑ z : {z // z ∈ L.kept},
      (G.roundedMultiplicity L a z : ℝ) * max 0 z.1) ≤ _
  rw [hsub]
  calc
    (∑ z ∈ L.kept, (count z : ℝ) * max 0 z) =
        ∑ z ∈ L.kept, ∑ e ∈ E with L.round (G.weight e.1) = z,
          max 0 (L.round (G.weight e.1)) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [show count z = G.roundedMultiplicity L a ⟨z, hz⟩ by
        simp [count, hz]]
      unfold roundedMultiplicity
      change (((E.filter fun e ↦ L.round (G.weight e.1) = z).card : ℕ) : ℝ) *
          max 0 z = _
      calc
        (((E.filter fun e ↦ L.round (G.weight e.1) = z).card : ℕ) : ℝ) *
            max 0 z =
            ∑ _e ∈ E.filter (fun e ↦ L.round (G.weight e.1) = z),
              max 0 z := by simp
        _ = ∑ e ∈ E with L.round (G.weight e.1) = z,
              max 0 (L.round (G.weight e.1)) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [(Finset.mem_filter.mp he).2]
    _ = ∑ e ∈ E with L.round (G.weight e.1) ∈ L.kept,
          max 0 (L.round (G.weight e.1)) := hfiber
    _ = ∑ e ∈ E, max 0 (L.round (G.weight e.1)) := by
      apply Finset.sum_congr
      · ext e
        simp only [Finset.mem_filter]
        constructor
        · exact fun he ↦ he.1
        · intro he
          exact ⟨he, hrange e he⟩
      · intro e _he
        rfl
    _ ≤ ∑ e ∈ E, G.weight e.1 := by
      apply Finset.sum_le_sum
      intro e he
      exact max_le (G.weight_nonneg e.1) (L.round_le _ (hsupport e he))
    _ = ∑ e ∈ (G.rawProfile β (L.outcome a)).ordinary,
          G.weight e.1 := by
      rw [rawProfile_ordinary]

/-- The large places and the tiny reservoir of one extended state fit in a
unit bin. -/
theorem sum_extendedProfileConcreteSlotSize_add_reservoir_le_one
    (v : G.V) (z : G.ExtendedProfileState R0 v) :
    (∑ i, G.extendedProfileConcreteSlotSize R0 v z i) +
        G.extendedProfileReservoirSize R0 v z ≤ 1 := by
  classical
  rcases z with P | t
  · rcases P with ⟨P, hP⟩
    rw [roundedProfileMenu, profileMenu, Finset.mem_image] at hP
    rcases hP with ⟨a, _ha, rfl⟩
    simp only [extendedProfileConcreteSlotSize,
      extendedProfileReservoirSize]
    rw [Finset.sum_comm]
    simp only [eq_comm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hlarge :=
      G.sum_max_roundedProfileOrdinarySlotSize_code_le R0 v a
    have hres := G.roundReservoir_eq_profileReservoir_of_code R0 v a
      (G.roundedProfileCode (R0 v).law hβ hr a) rfl
    rw [← hres]
    calc
      _ ≤ (∑ e ∈ (G.rawProfile β ((R0 v).law.outcome a)).ordinary,
            G.weight e.1) +
          roundReservoir r
            (G.rawProfile β ((R0 v).law.outcome a)).reservoir :=
        add_le_add_left hlarge _
      _ ≤ 1 := G.rawProfile_safe_after_roundReservoir
        (β := β) hr ((R0 v).law.feasible a)
  · by_cases h0 : t.1 = 0
    · have h1 : t.1 ≠ 1 := by omega
      simp [extendedProfileConcreteSlotSize,
        extendedProfileReservoirSize, h0, h1]
    · by_cases h1 : t.1 = 1
      · simp [extendedProfileConcreteSlotSize,
          extendedProfileReservoirSize, h0, h1]
      · simp [extendedProfileConcreteSlotSize,
          extendedProfileReservoirSize, h0, h1]

/-- Forgetting the nonnegative reservoir gives the ordinary-slot safety
bound needed by matching extraction. -/
theorem sum_extendedProfileConcreteSlotSize_le_one
    (v : G.V) (z : G.ExtendedProfileState R0 v) :
    (∑ i, G.extendedProfileConcreteSlotSize R0 v z i) ≤ 1 := by
  have hsafe :=
    G.sum_extendedProfileConcreteSlotSize_add_reservoir_le_one R0 v z
  have hres := G.extendedProfileReservoirSize_nonneg R0 v z
  linarith

/-- A place accepted by `ExtendedLargeSlotFits` is large enough for the
edge. -/
theorem weight_le_extendedProfileConcreteSlotSize_of_fits
    (v : G.V) (e : G.StarEdge v)
    (z : G.ExtendedProfileState R0 v)
    (i : Fin (explicitLargeSlotBound β q r))
    (hfit : G.ExtendedLargeSlotFits R0 v e z i) :
    G.weight e.1 ≤ G.extendedProfileConcreteSlotSize R0 v z i := by
  classical
  rcases z with P | t
  · rcases hfit with ⟨j, hcode, hweight⟩
    let code : G.RoundedProfileOrdinarySlot (R0 v).law P.1 →
        Fin (explicitLargeSlotBound β q r) := fun j' ↦
      G.paddedLargeSlotCode (R0 v) (some ⟨P, j'⟩)
    have hinj : Function.Injective code := by
      intro left right hlr
      have h := G.paddedLargeSlotCode_injective (R0 v) hlr
      exact eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2
    have hsum :
        (∑ j' : G.RoundedProfileOrdinarySlot (R0 v).law P.1,
          if code j' = i then
            max 0 (G.roundedProfileOrdinarySlotSize (R0 v).law P.1 j')
          else 0) =
        max 0 (G.roundedProfileOrdinarySlotSize (R0 v).law P.1 j) := by
      rw [Finset.sum_eq_single j]
      · simp [code, hcode]
      · intro j' _hj' hne
        have hcode' : code j' ≠ i := by
          intro hj'i
          exact hne (hinj (hj'i.trans hcode.symm))
        simp [hcode']
      · simp
    unfold extendedProfileConcreteSlotSize
    change G.weight e.1 ≤
      ∑ j' : G.RoundedProfileOrdinarySlot (R0 v).law P.1,
        if code j' = i then
          max 0 (G.roundedProfileOrdinarySlotSize (R0 v).law P.1 j')
        else 0
    rw [hsum]
    exact hweight.trans (le_max_right _ _)
  · rcases hfit with ⟨h0, hcode, hweight⟩
    simpa [extendedProfileConcreteSlotSize, h0, hcode] using hweight

/-- Concrete size of a large place in the selected state for a vertex and
colour. -/
def selectedBlockConcreteSlotSize
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (v : G.V) (c : Fin (B * k))
    (i : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  G.extendedProfileConcreteSlotSize R0 v
    (G.decodedExtendedProfileBlockSelection R0 choice v c) i

theorem selectedBlockConcreteSlotSize_nonneg
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (v : G.V) (c : Fin (B * k))
    (i : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.selectedBlockConcreteSlotSize R0 choice v c i := by
  exact G.extendedProfileConcreteSlotSize_nonneg R0 v _ i

theorem sum_selectedBlockConcreteSlotSize_add_reservoir_le_one
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (v : G.V) (c : Fin (B * k)) :
    (∑ i, G.selectedBlockConcreteSlotSize R0 choice v c i) +
      G.extendedProfileReservoirSize R0 v
        (G.decodedExtendedProfileBlockSelection R0 choice v c) ≤ 1 := by
  exact G.sum_extendedProfileConcreteSlotSize_add_reservoir_le_one
    R0 v (G.decodedExtendedProfileBlockSelection R0 choice v c)

theorem sum_selectedBlockConcreteSlotSize_le_one
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (v : G.V) (c : Fin (B * k)) :
    (∑ i, G.selectedBlockConcreteSlotSize R0 choice v c i) ≤ 1 := by
  exact G.sum_extendedProfileConcreteSlotSize_le_one
    R0 v (G.decodedExtendedProfileBlockSelection R0 choice v c)

/-- A positive normalized large option fits the selected concrete slot at
the first endpoint. -/
theorem weight_le_selectedBlockConcreteSlotSize_fst_of_large_pos
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (i j : Fin (explicitLargeSlotBound β q r))
    (hpos : 0 < G.selectedBlockNormalizedLargeOptionMass
      R0 rho omega choice e c i j) :
    G.weight e ≤
      G.selectedBlockConcreteSlotSize R0 choice (G.fst e) c i := by
  have hfits := G.selectedBlockNormalizedLargeOptionMass_pos_fits R0
    hn hs hq hr0 hleft homega0 homega1 hrho choice e c i j hpos
  exact G.weight_le_extendedProfileConcreteSlotSize_of_fits R0
    (G.fst e) (G.fstStarEdge e)
    (G.decodedExtendedProfileBlockSelection R0 choice (G.fst e) c) i
    hfits.1

/-- A positive normalized large option fits the selected concrete slot at
the second endpoint. -/
theorem weight_le_selectedBlockConcreteSlotSize_snd_of_large_pos
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (i j : Fin (explicitLargeSlotBound β q r))
    (hpos : 0 < G.selectedBlockNormalizedLargeOptionMass
      R0 rho omega choice e c i j) :
    G.weight e ≤
      G.selectedBlockConcreteSlotSize R0 choice (G.snd e) c j := by
  have hfits := G.selectedBlockNormalizedLargeOptionMass_pos_fits R0
    hn hs hq hr0 hleft homega0 homega1 hrho choice e c i j hpos
  exact G.weight_le_extendedProfileConcreteSlotSize_of_fits R0
    (G.snd e) (G.sndStarEdge e)
    (G.decodedExtendedProfileBlockSelection R0 choice (G.snd e) c) j
    hfits.2

end WeightedMultigraph

end

end WeightedEdgeColoring
