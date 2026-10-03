import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileAtomAssignments
import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileSelectedNormalizedOptions
import WeightedEdgeColoring.MultigraphExtendedProfileSelectedStateSafety

/-!
# Safety of color-dependent selected profile states

For a fixed color, a color-dependent realization is an ordinary extended
profile realization.  The concrete padded slot sizes therefore satisfy the
same unit-bin inequality as in the uniform construction.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})
variable {Color : Type w} [Fintype Color] [DecidableEq Color]
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}

section CoordinateStateSafety

variable {proposal : G.E → Color → ℝ}
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- Concrete size of a padded large slot in a color-dependent state. -/
def colorDependentExtendedProfileConcreteSlotSize
    (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c)
    (i : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  match z with
  | Sum.inl P =>
      ∑ j : G.RoundedProfileOrdinarySlot (R v c).law P.1,
        if G.paddedLargeSlotCode (R v c) (some ⟨P, j⟩) = i then
          max 0 (G.roundedProfileOrdinarySlotSize (R v c).law P.1 j)
        else 0
  | Sum.inr t =>
      if t.1 = 0 then
        if G.paddedLargeSlotCode (R v c) none = i then 1 else 0
      else 0

theorem colorDependentExtendedProfileConcreteSlotSize_nonneg
    (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c)
    (i : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.colorDependentExtendedProfileConcreteSlotSize R v c z i := by
  rcases z with P | t
  · unfold colorDependentExtendedProfileConcreteSlotSize
    exact Finset.sum_nonneg fun j _hj ↦ by
      split
      · exact le_max_left _ _
      · exact le_rfl
  · by_cases h0 : t.1 = 0
    · simp only [colorDependentExtendedProfileConcreteSlotSize, h0, if_true]
      split <;> norm_num
    · simp [colorDependentExtendedProfileConcreteSlotSize, h0]

private theorem sum_max_colorDependentRoundedProfileOrdinarySlotSize_code_le
    (v : G.V) (c : Color) (a : Fin (R v c).law.m) :
    (∑ j : G.RoundedProfileOrdinarySlot (R v c).law
        (G.roundedProfileCode (R v c).law hβ hr a),
      max 0 (G.roundedProfileOrdinarySlotSize (R v c).law
        (G.roundedProfileCode (R v c).law hβ hr a) j)) ≤
      ∑ e ∈ (G.rawProfile β ((R v c).law.outcome a)).ordinary,
        G.weight e.1 := by
  classical
  let L := (R v c).law
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

/-- Large slots and the reservoir of one color-dependent state fit in one
unit bin. -/
theorem sum_colorDependentExtendedProfileConcreteSlotSize_add_reservoir_le_one
    (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c) :
    (∑ i, G.colorDependentExtendedProfileConcreteSlotSize R v c z i) +
      G.colorDependentExtendedProfileReservoirSize R v c z ≤ 1 := by
  classical
  rcases z with P | t
  · rcases P with ⟨P, hP⟩
    rw [roundedProfileMenu, profileMenu, Finset.mem_image] at hP
    rcases hP with ⟨a, _ha, rfl⟩
    simp only [colorDependentExtendedProfileConcreteSlotSize,
      colorDependentExtendedProfileReservoirSize]
    rw [Finset.sum_comm]
    simp only [eq_comm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hlarge :=
      G.sum_max_colorDependentRoundedProfileOrdinarySlotSize_code_le R v c a
    have hres :=
      G.roundReservoir_eq_colorDependentProfileReservoir_of_code R v c a
        (G.roundedProfileCode (R v c).law hβ hr a) rfl
    rw [← hres]
    calc
      _ ≤ (∑ e ∈ (G.rawProfile β ((R v c).law.outcome a)).ordinary,
            G.weight e.1) +
          roundReservoir r
            (G.rawProfile β ((R v c).law.outcome a)).reservoir :=
        add_le_add_left hlarge _
      _ ≤ 1 := G.rawProfile_safe_after_roundReservoir
        (β := β) hr ((R v c).law.feasible a)
  · by_cases h0 : t.1 = 0
    · have h1 : t.1 ≠ 1 := by omega
      simp [colorDependentExtendedProfileConcreteSlotSize,
        colorDependentExtendedProfileReservoirSize, h0, h1]
    · by_cases h1 : t.1 = 1
      · simp [colorDependentExtendedProfileConcreteSlotSize,
          colorDependentExtendedProfileReservoirSize, h0, h1]
      · simp [colorDependentExtendedProfileConcreteSlotSize,
          colorDependentExtendedProfileReservoirSize, h0, h1]

private theorem colorDependentActualProfilePaddedAssign_pos_compatible
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R v c).law hβ hr})
    (i : Fin (explicitLargeSlotBound β q r))
    (hpos : 0 < G.colorDependentActualProfilePaddedAssign R v c e P i) :
    ∃ j : G.RoundedProfileOrdinarySlot (R v c).law P.1,
      G.paddedLargeSlotCode (R v c) (some ⟨P, j⟩) = i ∧
      G.weight e.1 ≤
        G.roundedProfileOrdinarySlotSize (R v c).law P.1 j := by
  classical
  unfold colorDependentActualProfilePaddedAssign at hpos
  have hnonneg : ∀ j ∈ (Finset.univ : Finset
      (G.RoundedProfileOrdinarySlot (R v c).law P.1)),
      0 ≤ (if G.paddedLargeSlotCode (R v c) (some ⟨P, j⟩) = i then
        (R v c).largeAssign e (some ⟨P, j⟩) else 0) := by
    intro j _
    split
    · exact (R v c).largeAssign_nonneg e (some ⟨P, j⟩)
    · exact le_rfl
  rcases (Finset.sum_pos_iff_of_nonneg hnonneg).mp hpos with
    ⟨j, _hj, hj⟩
  by_cases hcode : G.paddedLargeSlotCode (R v c) (some ⟨P, j⟩) = i
  · simp only [hcode, if_true] at hj
    have hfit := (R v c).largeAssign_compatible e (some ⟨P, j⟩) hj
    exact ⟨j, hcode, by
      simpa [explicitLargeSlotSize, roundedProfileOrdinarySlotSize] using hfit⟩
  · simp [hcode] at hj

/-- Every positive color-dependent large assignment is carried by a
concrete slot large enough for its edge. -/
theorem weight_le_colorDependentExtendedProfileConcreteSlotSize_of_largeAssign_pos
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (z : G.ColorDependentExtendedProfileState R v c)
    (i : Fin (explicitLargeSlotBound β q r))
    (hpos : 0 < G.colorDependentExtendedProfileLargeAssign R v c e z i) :
    G.weight e.1 ≤
      G.colorDependentExtendedProfileConcreteSlotSize R v c z i := by
  classical
  rcases z with P | t
  · simp only [colorDependentExtendedProfileLargeAssign] at hpos
    rcases G.colorDependentActualProfilePaddedAssign_pos_compatible
        R v c e P i hpos with ⟨j, hcode, hweight⟩
    let code : G.RoundedProfileOrdinarySlot (R v c).law P.1 →
        Fin (explicitLargeSlotBound β q r) := fun j' ↦
      G.paddedLargeSlotCode (R v c) (some ⟨P, j'⟩)
    have hinj : Function.Injective code := by
      intro left right hlr
      have h := G.paddedLargeSlotCode_injective (R v c) hlr
      exact eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2
    have hsum :
        (∑ j' : G.RoundedProfileOrdinarySlot (R v c).law P.1,
          if code j' = i then
            max 0 (G.roundedProfileOrdinarySlotSize (R v c).law P.1 j')
          else 0) =
        max 0 (G.roundedProfileOrdinarySlotSize (R v c).law P.1 j) := by
      rw [Finset.sum_eq_single j]
      · simp [code, hcode]
      · intro j' _hj' hne
        have hcode' : code j' ≠ i := by
          intro hj'i
          exact hne (hinj (hj'i.trans hcode.symm))
        simp [hcode']
      · simp
    unfold colorDependentExtendedProfileConcreteSlotSize
    change G.weight e.1 ≤
      ∑ j' : G.RoundedProfileOrdinarySlot (R v c).law P.1,
        if code j' = i then
          max 0 (G.roundedProfileOrdinarySlotSize (R v c).law P.1 j')
        else 0
    rw [hsum]
    exact hweight.trans (le_max_right _ _)
  · unfold colorDependentExtendedProfileLargeAssign at hpos
    by_cases h0 : t.1 = 0
    · simp only [h0, if_true] at hpos
      by_cases hcode : G.paddedLargeSlotCode (R v c) none = i
      · simpa [colorDependentExtendedProfileConcreteSlotSize, h0, hcode] using
          G.weight_le_one e.1
      · simp [hcode] at hpos
    · simp [h0] at hpos

/-- A positive reservoir contains at least one rounding quantum. -/
theorem colorDependentExtendedProfileReservoirSize_ge_r_of_pos
    (hr1 : r ≤ 1) (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c)
    (hpos : 0 < G.colorDependentExtendedProfileReservoirSize R v c z) :
    r ≤ G.colorDependentExtendedProfileReservoirSize R v c z := by
  rcases z with P | t
  · have hn0 : P.1.2.val ≠ 0 := by
      intro hn
      simp [colorDependentExtendedProfileReservoirSize, hn] at hpos
    have hn : 1 ≤ P.1.2.val := Nat.one_le_iff_ne_zero.mpr hn0
    have hnReal : (1 : ℝ) ≤ (P.1.2.val : ℕ) := by exact_mod_cast hn
    simp only [colorDependentExtendedProfileReservoirSize]
    nlinarith
  · by_cases h1 : t.1 = 1
    · simp [colorDependentExtendedProfileReservoirSize, h1, hr1]
    · simp [colorDependentExtendedProfileReservoirSize, h1] at hpos

end CoordinateStateSafety

section SelectedOptionSafety

variable {B k : ℕ}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- A positive color-dependent product option fits its first selected
concrete slot. -/
theorem weight_le_colorDependentExtendedProfileConcreteSlotSize_fst_of_pos
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k)
    (i j : Fin (explicitLargeSlotBound β q r))
    (hpos : 0 < G.selectedColorDependentNormalizedLargeOptionMass
      proposal R rho omega choice e c i j) :
    G.weight e ≤ G.colorDependentExtendedProfileConcreteSlotSize R
      (G.fst e) c
      (G.decodeColorDependentExtendedProfileBlock proposal R
        (G.fst e, c.1) (choice (G.fst e, c.1)) c.2) i := by
  let P := G.decodeColorDependentExtendedProfileBlock proposal R
    (G.fst e, c.1) (choice (G.fst e, c.1)) c.2
  let Q := G.decodeColorDependentExtendedProfileBlock proposal R
    (G.snd e, c.1) (choice (G.snd e, c.1)) c.2
  have hraw :=
    (G.selectedColorDependentNormalizedLargeOptionMass_pos_iff
      proposal R rho omega choice e c i j).mp hpos
  have hy0 := G.colorDependentExtendedProfileLargeEdgeColorMass_nonneg
    proposal R e c
  have ha0 := G.colorDependentExtendedProfileLargeAssign_nonneg
    R (G.fst e) c (G.fstStarEdge e) P i
  have hb0 := G.colorDependentExtendedProfileLargeAssign_nonneg
    R (G.snd e) c (G.sndStarEdge e) Q j
  unfold selectedColorDependentLargeOptionMass
    colorDependentExtendedProfileLargeProductMass pairedOption at hraw
  split at hraw
  · simp at hraw
  · rename_i hy
    have hypos : 0 < G.colorDependentExtendedProfileLargeEdgeColorMass
        (s := s) (β := β) proposal e c := lt_of_le_of_ne hy0 (Ne.symm hy)
    have hden : 0 <
        G.colorDependentExtendedProfileLargeEdgeColorMass
            (s := s) (β := β) proposal e c *
          G.smoothedColorDependentExtendedProfileProbability
            R omega (G.fst e) c P *
          G.smoothedColorDependentExtendedProfileProbability
            R omega (G.snd e) c Q := by
      exact mul_pos (mul_pos hypos
        (G.smoothedColorDependentExtendedProfileProbability_pos R
          hs hq hr0 hleft homega0 homega1 (G.fst e) c P))
        (G.smoothedColorDependentExtendedProfileProbability_pos R
          hs hq hr0 hleft homega0 homega1 (G.snd e) c Q)
    have hnum : 0 < rho *
        G.colorDependentExtendedProfileLargeAssign
          R (G.fst e) c (G.fstStarEdge e) P i *
        G.colorDependentExtendedProfileLargeAssign
          R (G.snd e) c (G.sndStarEdge e) Q j := by
      rcases div_pos_iff.mp hraw with h | h
      · exact h.1
      · exact (not_lt_of_ge hden.le h.2).elim
    have ha : 0 < G.colorDependentExtendedProfileLargeAssign
        R (G.fst e) c (G.fstStarEdge e) P i := by
      rcases mul_pos_iff.mp hnum with h | h
      · rcases mul_pos_iff.mp h.1 with h' | h'
        · exact h'.2
        · exact (not_lt_of_ge ha0 h'.2).elim
      · exact (not_lt_of_ge hb0 h.2).elim
    exact G.weight_le_colorDependentExtendedProfileConcreteSlotSize_of_largeAssign_pos
      R (G.fst e) c (G.fstStarEdge e) P i ha

/-- The symmetric fit statement at the second endpoint. -/
theorem weight_le_colorDependentExtendedProfileConcreteSlotSize_snd_of_pos
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k)
    (i j : Fin (explicitLargeSlotBound β q r))
    (hpos : 0 < G.selectedColorDependentNormalizedLargeOptionMass
      proposal R rho omega choice e c i j) :
    G.weight e ≤ G.colorDependentExtendedProfileConcreteSlotSize R
      (G.snd e) c
      (G.decodeColorDependentExtendedProfileBlock proposal R
        (G.snd e, c.1) (choice (G.snd e, c.1)) c.2) j := by
  -- Reverse the two endpoint roles in the preceding product argument.
  let P := G.decodeColorDependentExtendedProfileBlock proposal R
    (G.fst e, c.1) (choice (G.fst e, c.1)) c.2
  let Q := G.decodeColorDependentExtendedProfileBlock proposal R
    (G.snd e, c.1) (choice (G.snd e, c.1)) c.2
  have hraw :=
    (G.selectedColorDependentNormalizedLargeOptionMass_pos_iff
      proposal R rho omega choice e c i j).mp hpos
  have hy0 := G.colorDependentExtendedProfileLargeEdgeColorMass_nonneg
    proposal R e c
  have ha0 := G.colorDependentExtendedProfileLargeAssign_nonneg
    R (G.fst e) c (G.fstStarEdge e) P i
  have hb0 := G.colorDependentExtendedProfileLargeAssign_nonneg
    R (G.snd e) c (G.sndStarEdge e) Q j
  unfold selectedColorDependentLargeOptionMass
    colorDependentExtendedProfileLargeProductMass pairedOption at hraw
  split at hraw
  · simp at hraw
  · rename_i hy
    have hypos : 0 < G.colorDependentExtendedProfileLargeEdgeColorMass
        (s := s) (β := β) proposal e c := lt_of_le_of_ne hy0 (Ne.symm hy)
    have hden : 0 <
        G.colorDependentExtendedProfileLargeEdgeColorMass
            (s := s) (β := β) proposal e c *
          G.smoothedColorDependentExtendedProfileProbability
            R omega (G.fst e) c P *
          G.smoothedColorDependentExtendedProfileProbability
            R omega (G.snd e) c Q := by
      exact mul_pos (mul_pos hypos
        (G.smoothedColorDependentExtendedProfileProbability_pos R
          hs hq hr0 hleft homega0 homega1 (G.fst e) c P))
        (G.smoothedColorDependentExtendedProfileProbability_pos R
          hs hq hr0 hleft homega0 homega1 (G.snd e) c Q)
    have hnum : 0 < rho *
        G.colorDependentExtendedProfileLargeAssign
          R (G.fst e) c (G.fstStarEdge e) P i *
        G.colorDependentExtendedProfileLargeAssign
          R (G.snd e) c (G.sndStarEdge e) Q j := by
      rcases div_pos_iff.mp hraw with h | h
      · exact h.1
      · exact (not_lt_of_ge hden.le h.2).elim
    have hb : 0 < G.colorDependentExtendedProfileLargeAssign
        R (G.snd e) c (G.sndStarEdge e) Q j := by
      rcases mul_pos_iff.mp hnum with h | h
      · exact h.2
      · exact (not_lt_of_ge hb0 h.2).elim
    exact G.weight_le_colorDependentExtendedProfileConcreteSlotSize_of_largeAssign_pos
      R (G.snd e) c (G.sndStarEdge e) Q j hb

end SelectedOptionSafety

end WeightedMultigraph

end

end WeightedEdgeColoring
