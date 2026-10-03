import WeightedEdgeColoring.MultigraphSelectedProfileConditionedOptions
import WeightedEdgeColoring.CoupledProfiles

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)

/-!
# Extended profile states and the equation-(23) product coupling

The state law contains every rounded profile, a large-repair state, a
tiny-repair state, and an inactive state.  The large-repair state carries
the realization's size-one repair slot.  Consequently the large assignment
has the same total at both ends of every edge.  This is the common
denominator required by the product coupling in equation (23).

No selected-pair minimum is taken.  Such a minimum can lose a factor equal
to the number of colors when an edge occurs in rare profiles.
-/

/-- Padded assignment belonging to one actual rounded profile. -/
def actualProfilePaddedAssign (v : G.V) (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr})
    (i : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  ∑ j : G.RoundedProfileOrdinarySlot (R0 v).law P.1,
    if G.paddedLargeSlotCode (R0 v) (some ⟨P, j⟩) = i then
      (R0 v).largeAssign e (some ⟨P, j⟩) else 0

theorem actualProfilePaddedAssign_nonneg (v : G.V) (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr})
    (i : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.actualProfilePaddedAssign R0 v e P i := by
  exact Finset.sum_nonneg fun j _ ↦ by
    split
    · exact (R0 v).largeAssign_nonneg e (some ⟨P, j⟩)
    · exact le_rfl

theorem actualProfilePaddedAssign_pos_compatible (v : G.V)
    (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr})
    (i : Fin (explicitLargeSlotBound β q r))
    (hpos : 0 < G.actualProfilePaddedAssign R0 v e P i) :
    ∃ j : G.RoundedProfileOrdinarySlot (R0 v).law P.1,
      G.paddedLargeSlotCode (R0 v) (some ⟨P, j⟩) = i ∧
      G.weight e.1 ≤ G.roundedProfileOrdinarySlotSize (R0 v).law P.1 j := by
  classical
  unfold actualProfilePaddedAssign at hpos
  have hnonneg : ∀ j ∈ (Finset.univ : Finset
      (G.RoundedProfileOrdinarySlot (R0 v).law P.1)),
      0 ≤ (if G.paddedLargeSlotCode (R0 v) (some ⟨P, j⟩) = i then
        (R0 v).largeAssign e (some ⟨P, j⟩) else 0) := by
    intro j _
    split
    · exact (R0 v).largeAssign_nonneg e (some ⟨P, j⟩)
    · exact le_rfl
  rcases (Finset.sum_pos_iff_of_nonneg hnonneg).mp hpos with ⟨j, _hj, hj⟩
  by_cases hcode : G.paddedLargeSlotCode (R0 v) (some ⟨P, j⟩) = i
  · simp only [hcode, if_true] at hj
    have hfit := (R0 v).largeAssign_compatible e (some ⟨P, j⟩) hj
    exact ⟨j, hcode, by
      simpa [explicitLargeSlotSize, roundedProfileOrdinarySlotSize] using hfit⟩
  · simp [hcode] at hj

theorem sum_actualProfilePaddedAssign (v : G.V) (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr}) :
    (∑ i, G.actualProfilePaddedAssign R0 v e P i) =
      ∑ j : G.RoundedProfileOrdinarySlot (R0 v).law P.1,
        (R0 v).largeAssign e (some ⟨P, j⟩) := by
  classical
  unfold actualProfilePaddedAssign
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

/-- Every padded place of one actual profile respects that profile's local
capacity. -/
theorem sum_actualProfilePaddedAssign_star_le (hs : 0 ≤ s)
    (v : G.V)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr})
    (i : Fin (explicitLargeSlotBound β q r)) :
    (∑ e : G.StarEdge v, G.actualProfilePaddedAssign R0 v e P i) ≤
      s * G.roundedProfileMass (R0 v).law hβ hr P.1 := by
  classical
  let code : G.RoundedProfileOrdinarySlot (R0 v).law P.1 →
      Fin (explicitLargeSlotBound β q r) := fun j ↦
    G.paddedLargeSlotCode (R0 v) (some ⟨P, j⟩)
  by_cases hex : ∃ j, code j = i
  · rcases hex with ⟨j0, hj0⟩
    have hinj : Function.Injective code := by
      intro j k hjk
      have h := G.paddedLargeSlotCode_injective (R0 v) hjk
      exact eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2
    calc
      (∑ e : G.StarEdge v, G.actualProfilePaddedAssign R0 v e P i) =
          ∑ e : G.StarEdge v, (R0 v).largeAssign e (some ⟨P, j0⟩) := by
        apply Finset.sum_congr rfl
        intro e _
        unfold actualProfilePaddedAssign
        rw [Finset.sum_eq_single j0]
        · simp [code, hj0]
        · intro j _ hne
          have hcode : code j ≠ i := by
            intro hj
            exact hne (hinj (hj.trans hj0.symm))
          simp [code, hcode]
        · simp
      _ ≤ G.explicitLargeSlotCapacity (R0 v).law hβ hr (some ⟨P, j0⟩) :=
        (R0 v).largeAssign_capacity (some ⟨P, j0⟩)
      _ = s * G.roundedProfileMass (R0 v).law hβ hr P.1 := rfl
  · have hzero : ∀ e : G.StarEdge v,
        G.actualProfilePaddedAssign R0 v e P i = 0 := by
      intro e
      unfold actualProfilePaddedAssign
      apply Finset.sum_eq_zero
      intro j _
      have hcode : code j ≠ i := fun h ↦ hex ⟨j, h⟩
      simp [code, hcode]
    simp_rw [hzero]
    simpa using mul_nonneg hs
      (G.roundedProfileMass_nonneg (R0 v).law hβ hr P.1)

/-- Actual rounded profiles, followed by the large repair, tiny repair, and
inactive states.  Tags `0`, `1`, and `2` have those three meanings. -/
abbrev ExtendedProfileState (v : G.V) :=
  Sum {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr} (Fin 3)

/-- Probability of an extended state before smoothing. -/
def extendedProfileProbability (v : G.V)
    (z : G.ExtendedProfileState R0 v) : ℝ :=
  match z with
  | Sum.inl P => s * G.roundedProfileMass (R0 v).law hβ hr P.1
  | Sum.inr k =>
      if k.1 = 0 then s * q
      else if k.1 = 1 then s * r
      else 1 - s * (1 + q + r)

theorem extendedProfileProbability_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (v : G.V) (z : G.ExtendedProfileState R0 v) :
    0 ≤ G.extendedProfileProbability R0 v z := by
  cases z with
  | inl P =>
      exact mul_nonneg hs
        (G.roundedProfileMass_nonneg (R0 v).law hβ hr P.1)
  | inr k =>
      by_cases hk0 : k.1 = 0
      · simp only [extendedProfileProbability, hk0, if_true]
        exact mul_nonneg hs hq
      · by_cases hk1 : k.1 = 1
        · simp only [extendedProfileProbability, hk0, if_false, hk1, if_true]
          exact mul_nonneg hs hr0
        · simpa [extendedProfileProbability, hk0, hk1] using hleft

theorem sum_extendedProfileProbability (v : G.V) :
    (∑ z : G.ExtendedProfileState R0 v,
      G.extendedProfileProbability R0 v z) = 1 := by
  classical
  have hmenu :
      (∑ P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr},
        G.roundedProfileMass (R0 v).law hβ hr P.1) = 1 := by
    calc
      _ = ∑ P ∈ G.roundedProfileMenu (R0 v).law hβ hr,
          G.roundedProfileMass (R0 v).law hβ hr P := by
        symm
        exact Finset.sum_subtype _ (fun _ ↦ Iff.rfl) _
      _ = 1 := G.sum_roundedProfileMass (R0 v).law hβ hr
  rw [Fintype.sum_sum_type]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  simp only [extendedProfileProbability, Fin.val_zero, if_pos, Fin.val_succ,
    Nat.succ_ne_zero, ↓reduceIte, Nat.reduceAdd, zero_add]
  rw [← Finset.mul_sum, hmenu]
  norm_num
  ring

/-- Large assignment carried by an extended state.  Only actual profiles
and the large-repair state carry large slots. -/
def extendedProfileLargeAssign (v : G.V) (e : G.StarEdge v)
    (z : G.ExtendedProfileState R0 v)
    (i : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  match z with
  | Sum.inl P => G.actualProfilePaddedAssign R0 v e P i
  | Sum.inr k =>
      if k.1 = 0 then
        if G.paddedLargeSlotCode (R0 v) none = i then
          (R0 v).largeAssign e none else 0
      else 0

theorem extendedProfileLargeAssign_nonneg (v : G.V) (e : G.StarEdge v)
    (z : G.ExtendedProfileState R0 v)
    (i : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.extendedProfileLargeAssign R0 v e z i := by
  rcases z with P | k
  · exact G.actualProfilePaddedAssign_nonneg R0 v e P i
  · simp only [extendedProfileLargeAssign]
    by_cases hk : k.1 = 0
    · simp only [hk, if_true]
      split
      · exact (R0 v).largeAssign_nonneg e none
      · exact le_rfl
    · simp [hk]

/-- A positive extended-state assignment is supported either by a fitting
slot of an actual profile or by the size-one large-repair slot. -/
def ExtendedLargeSlotFits (v : G.V) (e : G.StarEdge v)
    (z : G.ExtendedProfileState R0 v)
    (i : Fin (explicitLargeSlotBound β q r)) : Prop :=
  match z with
  | Sum.inl P => ∃ j : G.RoundedProfileOrdinarySlot (R0 v).law P.1,
      G.paddedLargeSlotCode (R0 v) (some ⟨P, j⟩) = i ∧
      G.weight e.1 ≤ G.roundedProfileOrdinarySlotSize (R0 v).law P.1 j
  | Sum.inr k => k.1 = 0 ∧
      G.paddedLargeSlotCode (R0 v) none = i ∧ G.weight e.1 ≤ 1

theorem extendedProfileLargeAssign_pos_fits (v : G.V) (e : G.StarEdge v)
    (z : G.ExtendedProfileState R0 v)
    (i : Fin (explicitLargeSlotBound β q r))
    (hpos : 0 < G.extendedProfileLargeAssign R0 v e z i) :
    G.ExtendedLargeSlotFits R0 v e z i := by
  rcases z with P | k
  · exact G.actualProfilePaddedAssign_pos_compatible R0 v e P i hpos
  · unfold extendedProfileLargeAssign at hpos
    by_cases hk : k.1 = 0
    · simp only [hk, if_true] at hpos
      by_cases hcode : G.paddedLargeSlotCode (R0 v) none = i
      · exact ⟨hk, hcode, G.weight_le_one e.1⟩
      · simp [hcode] at hpos
    · simp [hk] at hpos

/-- Each large place of an extended state has total star load at most the
probability mass of that state. -/
theorem sum_extendedProfileLargeAssign_star_le
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (v : G.V) (z : G.ExtendedProfileState R0 v)
    (i : Fin (explicitLargeSlotBound β q r)) :
    (∑ e : G.StarEdge v, G.extendedProfileLargeAssign R0 v e z i) ≤
      G.extendedProfileProbability R0 v z := by
  rcases z with P | k
  · exact G.sum_actualProfilePaddedAssign_star_le R0 hs v P i
  · by_cases hk0 : k.1 = 0
    · by_cases hcode : G.paddedLargeSlotCode (R0 v) none = i
      · simp only [extendedProfileLargeAssign, extendedProfileProbability,
          hk0, hcode, if_true]
        have hcap := (R0 v).largeAssign_capacity none
        simpa only [explicitLargeSlotCapacity] using hcap
      · simp only [extendedProfileLargeAssign, extendedProfileProbability,
          hk0, hcode, if_true, if_false, Finset.sum_const_zero]
        exact mul_nonneg hs hq
    · have hprob := G.extendedProfileProbability_nonneg R0 hs hq hr0 hleft
          v (Sum.inr k)
      simpa [extendedProfileLargeAssign, hk0] using hprob

/-- Summing the extended states and their padded places recovers the full
large transport, including the size-one repair slot. -/
theorem sum_extendedProfileLargeAssign (v : G.V) (e : G.StarEdge v) :
    (∑ z : G.ExtendedProfileState R0 v,
      ∑ i, G.extendedProfileLargeAssign R0 v e z i) =
      if β ≤ G.weight e.1 then s * ((1 : ℝ) / n) else 0 := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [extendedProfileLargeAssign]
  simp_rw [G.sum_actualProfilePaddedAssign R0 v e]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  simp only [extendedProfileLargeAssign, Fin.val_zero, if_pos, Fin.val_succ,
    Nat.succ_ne_zero, ↓reduceIte, Finset.sum_const_zero, add_zero]
  have hrepair :
      (∑ i : Fin (explicitLargeSlotBound β q r),
        if G.paddedLargeSlotCode (R0 v) none = i then
          (R0 v).largeAssign e none else 0) =
        (R0 v).largeAssign e none := by simp
  rw [hrepair]
  have hmarginal := (R0 v).largeAssign_marginal e
  rw [Fintype.sum_option, Fintype.sum_sigma] at hmarginal
  rw [add_comm]
  exact hmarginal

/-- The common edge--color mass in equation (23). -/
def extendedProfileEdgeColorMass (e : G.E) : ℝ :=
  if β ≤ G.weight e then s * ((1 : ℝ) / n) else 0

theorem extendedProfileEdgeColorMass_nonneg (hs : 0 ≤ s) (hn : 0 < n)
    (e : G.E) :
    0 ≤ G.extendedProfileEdgeColorMass (s := s) (β := β) (n := n) e := by
  unfold extendedProfileEdgeColorMass
  split
  · exact mul_nonneg hs (by positivity)
  · exact le_rfl

theorem sum_extendedProfileLargeAssign_fst (e : G.E) :
    (∑ z : G.ExtendedProfileState R0 (G.fst e),
      ∑ i, G.extendedProfileLargeAssign R0 (G.fst e)
        (G.fstStarEdge e) z i) =
      G.extendedProfileEdgeColorMass (s := s) (β := β) (n := n) e := by
  exact G.sum_extendedProfileLargeAssign R0 _ _

theorem sum_extendedProfileLargeAssign_snd (e : G.E) :
    (∑ z : G.ExtendedProfileState R0 (G.snd e),
      ∑ i, G.extendedProfileLargeAssign R0 (G.snd e)
        (G.sndStarEdge e) z i) =
      G.extendedProfileEdgeColorMass (s := s) (β := β) (n := n) e := by
  exact G.sum_extendedProfileLargeAssign R0 _ _

/-- Uniform smoothing of the finite extended state law. -/
def smoothedExtendedProfileProbability (omega : ℝ) (v : G.V)
    (z : G.ExtendedProfileState R0 v) : ℝ :=
  (1 - omega) * G.extendedProfileProbability R0 v z +
    omega / Fintype.card (G.ExtendedProfileState R0 v)

theorem sum_smoothedExtendedProfileProbability (omega : ℝ) (v : G.V) :
    (∑ z : G.ExtendedProfileState R0 v,
      G.smoothedExtendedProfileProbability R0 omega v z) = 1 := by
  classical
  unfold smoothedExtendedProfileProbability
  have hcard : Fintype.card (G.ExtendedProfileState R0 v) ≠ 0 := by
    simp [ExtendedProfileState]
  have huniform :
      (∑ _z : G.ExtendedProfileState R0 v,
        omega / Fintype.card (G.ExtendedProfileState R0 v)) = omega := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcardR : (Fintype.card (G.ExtendedProfileState R0 v) : ℝ) ≠ 0 := by
      exact_mod_cast hcard
    field_simp [hcardR]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    G.sum_extendedProfileProbability R0 v, huniform]
  ring

theorem smoothedExtendedProfileProbability_pos
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V) (z : G.ExtendedProfileState R0 v) :
    0 < G.smoothedExtendedProfileProbability R0 omega v z := by
  unfold smoothedExtendedProfileProbability
  have hbase := G.extendedProfileProbability_nonneg R0 hs hq hr0 hleft v z
  have hfirst : 0 ≤ (1 - omega) * G.extendedProfileProbability R0 v z :=
    mul_nonneg (sub_nonneg.mpr homega1) hbase
  have hcard : 0 < (Fintype.card (G.ExtendedProfileState R0 v) : ℝ) := by
    positivity
  have hsecond : 0 < omega /
      Fintype.card (G.ExtendedProfileState R0 v) := div_pos homega0 hcard
  linarith

/-- Equation (23) on the extended and smoothed profile laws. -/
def extendedProfileProductOptionMass (rho omega : ℝ) (e : G.E)
    (P : G.ExtendedProfileState R0 (G.fst e))
    (Q : G.ExtendedProfileState R0 (G.snd e))
    (i j : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  pairedOption rho
    (G.extendedProfileEdgeColorMass (s := s) (β := β) (n := n) e)
    (G.smoothedExtendedProfileProbability R0 omega (G.fst e))
    (G.smoothedExtendedProfileProbability R0 omega (G.snd e))
    (G.extendedProfileLargeAssign R0 (G.fst e) (G.fstStarEdge e))
    (G.extendedProfileLargeAssign R0 (G.snd e) (G.sndStarEdge e))
    P Q i j

theorem extendedProfileProductOptionMass_nonneg
    (hs : 0 ≤ s) (hn : 0 < n)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (e : G.E)
    (P : G.ExtendedProfileState R0 (G.fst e))
    (Q : G.ExtendedProfileState R0 (G.snd e))
    (i j : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.extendedProfileProductOptionMass R0 rho omega e P Q i j := by
  unfold extendedProfileProductOptionMass pairedOption
  split
  · exact le_rfl
  · apply div_nonneg
    · exact mul_nonneg
        (mul_nonneg hrho
          (G.extendedProfileLargeAssign_nonneg R0 _ _ P i))
        (G.extendedProfileLargeAssign_nonneg R0 _ _ Q j)
    · exact mul_nonneg
        (mul_nonneg
          (G.extendedProfileEdgeColorMass_nonneg hs hn e)
          (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
            homega0 homega1 _ P).le)
        (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
          homega0 homega1 _ Q).le

/-- Positive equation-(23) mass uses fitting large slots at both endpoints. -/
theorem extendedProfileProductOptionMass_pos_fits
    (hs : 0 ≤ s) (hn : 0 < n)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (hy : 0 < G.extendedProfileEdgeColorMass
      (s := s) (β := β) (n := n) e)
    (P : G.ExtendedProfileState R0 (G.fst e))
    (Q : G.ExtendedProfileState R0 (G.snd e))
    (i j : Fin (explicitLargeSlotBound β q r))
    (hpos : 0 < G.extendedProfileProductOptionMass R0 rho omega e P Q i j) :
    G.ExtendedLargeSlotFits R0 (G.fst e) (G.fstStarEdge e) P i ∧
      G.ExtendedLargeSlotFits R0 (G.snd e) (G.sndStarEdge e) Q j := by
  have hlamP := G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
    homega0 homega1 (G.fst e) P
  have hlamQ := G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
    homega0 homega1 (G.snd e) Q
  have ha0 := G.extendedProfileLargeAssign_nonneg R0
    (G.fst e) (G.fstStarEdge e) P i
  have hb0 := G.extendedProfileLargeAssign_nonneg R0
    (G.snd e) (G.sndStarEdge e) Q j
  unfold extendedProfileProductOptionMass pairedOption at hpos
  simp only [hy.ne', if_false] at hpos
  have hden : 0 <
      G.extendedProfileEdgeColorMass (s := s) (β := β) (n := n) e *
        G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
        G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q :=
    mul_pos (mul_pos hy hlamP) hlamQ
  have hnum : 0 < rho *
      G.extendedProfileLargeAssign R0 (G.fst e) (G.fstStarEdge e) P i *
      G.extendedProfileLargeAssign R0 (G.snd e) (G.sndStarEdge e) Q j := by
    rcases div_pos_iff.mp hpos with h | h
    · exact h.1
    · exact (not_lt_of_ge hden.le h.2).elim
  have hb : 0 < G.extendedProfileLargeAssign R0
      (G.snd e) (G.sndStarEdge e) Q j := by
    rcases mul_pos_iff.mp hnum with h | h
    · exact h.2
    · exact (not_lt_of_ge hb0 h.2).elim
  have hra : 0 < rho * G.extendedProfileLargeAssign R0
      (G.fst e) (G.fstStarEdge e) P i := by
    rcases mul_pos_iff.mp hnum with h | h
    · exact h.1
    · exact (not_lt_of_ge hb0 h.2).elim
  have ha : 0 < G.extendedProfileLargeAssign R0
      (G.fst e) (G.fstStarEdge e) P i := by
    rcases mul_pos_iff.mp hra with h | h
    · exact h.2
    · exact (not_lt_of_ge hrho h.1).elim
  exact ⟨G.extendedProfileLargeAssign_pos_fits R0 _ _ P i ha,
    G.extendedProfileLargeAssign_pos_fits R0 _ _ Q j hb⟩

/-- Expected row mass at a fixed left state and place.  This is the exact
resource identity used before applying the local capacity estimate. -/
theorem extendedProfileProductOptionMass_right_expectation
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hy : G.extendedProfileEdgeColorMass
      (s := s) (β := β) (n := n) e ≠ 0)
    (P : G.ExtendedProfileState R0 (G.fst e))
    (i : Fin (explicitLargeSlotBound β q r)) :
    (∑ Q : G.ExtendedProfileState R0 (G.snd e),
      G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
        ∑ j, G.extendedProfileProductOptionMass R0 rho omega e P Q i j) =
      rho * G.extendedProfileLargeAssign R0 (G.fst e)
        (G.fstStarEdge e) P i /
        G.smoothedExtendedProfileProbability R0 omega (G.fst e) P := by
  unfold extendedProfileProductOptionMass
  apply sum_pairedOption_right
  · exact hy
  · exact (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
      homega0 homega1 _ P).ne'
  · intro Q
    exact (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
      homega0 homega1 _ Q).ne'
  · exact G.sum_extendedProfileLargeAssign_snd R0 e

/-- Averaging equation (23) over the two independently sampled extended
states retains exactly `rho` times the common edge--color mass. -/
theorem extendedProfileProductOptionMass_expectation
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hy : G.extendedProfileEdgeColorMass
      (s := s) (β := β) (n := n) e ≠ 0) :
    (∑ P : G.ExtendedProfileState R0 (G.fst e),
      G.smoothedExtendedProfileProbability R0 omega (G.fst e) P * ∑ i,
        ∑ Q : G.ExtendedProfileState R0 (G.snd e),
          G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q * ∑ j,
            G.extendedProfileProductOptionMass R0 rho omega e P Q i j) =
      rho * G.extendedProfileEdgeColorMass
        (s := s) (β := β) (n := n) e := by
  unfold extendedProfileProductOptionMass
  apply sum_pairedOption
  · exact hy
  · intro P
    exact (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
      homega0 homega1 _ P).ne'
  · intro Q
    exact (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
      homega0 homega1 _ Q).ne'
  · exact G.sum_extendedProfileLargeAssign_fst R0 e
  · exact G.sum_extendedProfileLargeAssign_snd R0 e

/-- A selected extended-state word. -/
abbrev ExtendedSelectedProfileWord :=
  ∀ v (c : Fin n), G.ExtendedProfileState R0 v

def rotateExtendedSelectedProfileWord
    (selected : G.ExtendedSelectedProfileWord R0)
    (shift : G.V → Fin n) : G.ExtendedSelectedProfileWord R0 :=
  fun v c ↦ selected v (c + shift v)

/-- Equation-(23) option mass after selecting one extended state in each
vertex--color bin. -/
def selectedExtendedProfileProductOptionMass (rho omega : ℝ)
    (selected : G.ExtendedSelectedProfileWord R0)
    (e : G.E) (c : Fin n)
    (i j : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  G.extendedProfileProductOptionMass R0 rho omega e
    (selected (G.fst e) c) (selected (G.snd e) c) i j

theorem rotate_selectedExtendedProfileProductOptionMass
    (rho omega : ℝ) (selected : G.ExtendedSelectedProfileWord R0)
    (shift : G.V → Fin n) (e : G.E) (c : Fin n)
    (i j : Fin (explicitLargeSlotBound β q r)) :
    G.selectedExtendedProfileProductOptionMass R0 rho omega
        (G.rotateExtendedSelectedProfileWord R0 selected shift) e c i j =
      G.extendedProfileProductOptionMass R0 rho omega e
        (selected (G.fst e) (c + shift (G.fst e)))
        (selected (G.snd e) (c + shift (G.snd e))) i j := by
  rfl

end WeightedMultigraph

end

end WeightedEdgeColoring
