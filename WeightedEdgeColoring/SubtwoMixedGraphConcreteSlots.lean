import WeightedEdgeColoring.SubtwoMixedGraphQuantizedBridge
import WeightedEdgeColoring.MultigraphExtendedProfileSelectedStateSafety

/-!
# Concrete slots for a label-conditional local realization

Each active mixed atom contains a local bounded-profile realization.  The
ordinary slot sizes below are attached to that actual realization and do
not assume a common proposal at both endpoints.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {v : G.V} {φ : G.StarEdge v → ℝ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : G.BoundedProfileRealization φ s β q r hβ hr)

def localMixedConcreteSlotSize
    (z : G.LocalExtendedProfileState R)
    (i : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  match z with
  | Sum.inl P =>
      ∑ j : G.RoundedProfileOrdinarySlot R.law P.1,
        if G.paddedLargeSlotCode R (some ⟨P, j⟩) = i then
          max 0 (G.roundedProfileOrdinarySlotSize R.law P.1 j)
        else 0
  | Sum.inr k =>
      if k.1 = 0 then
        if G.paddedLargeSlotCode R none = i then 1 else 0
      else 0

def localMixedConcreteReservoirSize
    (z : G.LocalExtendedProfileState R) : ℝ :=
  match z with
  | Sum.inl P => r * P.1.2.val
  | Sum.inr k => if k.1 = 1 then 1 else 0

theorem localMixedConcreteSlotSize_nonneg
    (z : G.LocalExtendedProfileState R)
    (i : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.localMixedConcreteSlotSize R z i := by
  rcases z with P | k
  · unfold localMixedConcreteSlotSize
    exact Finset.sum_nonneg fun j _ ↦ by
      split
      · exact le_max_left _ _
      · exact le_rfl
  · by_cases hk : k.1 = 0
    · simp only [localMixedConcreteSlotSize, hk, if_true]
      split <;> norm_num
    · simp [localMixedConcreteSlotSize, hk]

theorem localMixedConcreteReservoirSize_nonneg
    (z : G.LocalExtendedProfileState R) :
    0 ≤ G.localMixedConcreteReservoirSize R z := by
  rcases z with P | k
  · exact mul_nonneg hr.le (Nat.cast_nonneg _)
  · simp only [localMixedConcreteReservoirSize]
    split <;> norm_num

private theorem localMixed_natFloor_cast_eq_intFloor_cast
    (a : ℝ) (ha : 0 ≤ a) :
    ((⌊a⌋₊ : ℕ) : ℝ) = ((⌊a⌋ : ℤ) : ℝ) := by
  have hn := (Nat.floor_eq_iff (n := ⌊a⌋₊) ha).mp rfl
  have hi : (⌊a⌋ : ℤ) = (⌊a⌋₊ : ℕ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact_mod_cast hn.1
    · exact_mod_cast hn.2
  rw [hi]
  norm_num

private theorem localMixed_roundReservoir_eq_code
    (a : Fin R.law.m) (P : G.RoundedProfileCode R.law)
    (hcode : G.roundedProfileCode R.law hβ hr a = P) :
    roundReservoir r (G.rawProfile β (R.law.outcome a)).reservoir =
      r * P.2.val := by
  have hR : 0 ≤ (G.rawProfile β (R.law.outcome a)).reservoir :=
    G.rawProfile_reservoir_nonneg (R.law.feasible a)
  have hcast := localMixed_natFloor_cast_eq_intFloor_cast
    ((G.rawProfile β (R.law.outcome a)).reservoir / r)
    (div_nonneg hR hr.le)
  unfold roundReservoir
  rw [← hcast]
  have hsecond : (G.roundedProfileCode R.law hβ hr a).2 = P.2 :=
    congrArg Prod.snd hcode
  change r * (⌊(G.rawProfile β (R.law.outcome a)).reservoir / r⌋₊ : ℕ) =
    r * (P.2.val : ℕ)
  rw [show ⌊(G.rawProfile β (R.law.outcome a)).reservoir / r⌋₊ =
      P.2.val by
    simpa [roundedProfileCode] using congrArg Fin.val hsecond]

private theorem localMixed_sum_max_slotSize_le_raw
    (a : Fin R.law.m) :
    (∑ j : G.RoundedProfileOrdinarySlot R.law
        (G.roundedProfileCode R.law hβ hr a),
      max 0 (G.roundedProfileOrdinarySlotSize R.law
        (G.roundedProfileCode R.law hβ hr a) j)) ≤
      ∑ e ∈ (G.rawProfile β (R.law.outcome a)).ordinary,
        G.weight e.1 := by
  classical
  let L := R.law
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

theorem sum_localMixedConcreteSlotSize_add_reservoir_le_one
    (z : G.LocalExtendedProfileState R) :
    (∑ i, G.localMixedConcreteSlotSize R z i) +
      G.localMixedConcreteReservoirSize R z ≤ 1 := by
  classical
  rcases z with P | k
  · rcases P with ⟨P, hP⟩
    rw [roundedProfileMenu, profileMenu, Finset.mem_image] at hP
    rcases hP with ⟨a, _ha, rfl⟩
    simp only [localMixedConcreteSlotSize,
      localMixedConcreteReservoirSize]
    rw [Finset.sum_comm]
    simp only [eq_comm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hlarge := G.localMixed_sum_max_slotSize_le_raw R a
    have hres := G.localMixed_roundReservoir_eq_code R a
      (G.roundedProfileCode R.law hβ hr a) rfl
    rw [← hres]
    calc
      _ ≤ (∑ e ∈ (G.rawProfile β (R.law.outcome a)).ordinary,
            G.weight e.1) +
          roundReservoir r
            (G.rawProfile β (R.law.outcome a)).reservoir :=
        add_le_add_left hlarge _
      _ ≤ 1 := G.rawProfile_safe_after_roundReservoir
        (β := β) hr (R.law.feasible a)
  · by_cases h0 : k.1 = 0
    · have h1 : k.1 ≠ 1 := by omega
      simp [localMixedConcreteSlotSize,
        localMixedConcreteReservoirSize, h0, h1]
    · by_cases h1 : k.1 = 1
      · simp [localMixedConcreteSlotSize,
          localMixedConcreteReservoirSize, h0, h1]
      · simp [localMixedConcreteSlotSize,
          localMixedConcreteReservoirSize, h0, h1]

theorem sum_localMixedConcreteSlotSize_le_one
    (z : G.LocalExtendedProfileState R) :
    (∑ i, G.localMixedConcreteSlotSize R z i) ≤ 1 := by
  have hsafe := G.sum_localMixedConcreteSlotSize_add_reservoir_le_one R z
  have hres := G.localMixedConcreteReservoirSize_nonneg R z
  linarith

/-- Positive local large assignment certifies that its physical edge fits
the concrete padded slot. -/
theorem weight_le_localMixedConcreteSlotSize_of_pos
    (e : G.StarEdge v) (z : G.LocalExtendedProfileState R)
    (i : Fin (explicitLargeSlotBound β q r))
    (hpos : 0 < G.localExtendedProfileLargeAssign R e z i) :
    G.weight e.1 ≤ G.localMixedConcreteSlotSize R z i := by
  classical
  rcases z with P | k
  · unfold localExtendedProfileLargeAssign localActualProfilePaddedAssign at hpos
    have hnonneg : ∀ j ∈ (Finset.univ : Finset
        (G.RoundedProfileOrdinarySlot R.law P.1)),
        0 ≤ (if G.paddedLargeSlotCode R (some ⟨P, j⟩) = i then
          R.largeAssign e (some ⟨P, j⟩) else 0) := by
      intro j _
      split
      · exact R.largeAssign_nonneg e (some ⟨P, j⟩)
      · exact le_rfl
    rcases (Finset.sum_pos_iff_of_nonneg hnonneg).mp hpos with
      ⟨j, _hj, hj⟩
    by_cases hcode : G.paddedLargeSlotCode R (some ⟨P, j⟩) = i
    · simp only [hcode, if_true] at hj
      have hfit := R.largeAssign_compatible e (some ⟨P, j⟩) hj
      have hweight : G.weight e.1 ≤
          G.roundedProfileOrdinarySlotSize R.law P.1 j := by
        simpa [explicitLargeSlotSize,
          roundedProfileOrdinarySlotSize] using hfit
      have hsize :
          G.weight e.1 ≤
            max 0 (G.roundedProfileOrdinarySlotSize R.law P.1 j) := by
        exact hweight.trans (le_max_right _ _)
      calc
        G.weight e.1 ≤
            max 0 (G.roundedProfileOrdinarySlotSize R.law P.1 j) := hsize
        _ ≤ G.localMixedConcreteSlotSize R (Sum.inl P) i := by
          let f : G.RoundedProfileOrdinarySlot R.law P.1 → ℝ :=
            fun j' ↦ if G.paddedLargeSlotCode R (some ⟨P, j'⟩) = i then
              max 0 (G.roundedProfileOrdinarySlotSize R.law P.1 j')
            else 0
          have hf0 : ∀ j', 0 ≤ f j' := by
            intro j'
            simp only [f]
            split <;> positivity
          have hsingle : f j ≤ ∑ j', f j' :=
            Finset.single_le_sum (fun j' _ ↦ hf0 j') (Finset.mem_univ j)
          simpa [f, hcode, localMixedConcreteSlotSize] using hsingle
    · simp [hcode] at hj
  · unfold localExtendedProfileLargeAssign at hpos
    by_cases hk : k.1 = 0
    · simp only [hk, if_true] at hpos
      by_cases hcode : G.paddedLargeSlotCode R none = i
      · simpa [localMixedConcreteSlotSize, hk, hcode] using G.weight_le_one e.1
      · simp [hcode] at hpos
    · simp [hk] at hpos

end WeightedMultigraph

end

end WeightedEdgeColoring
