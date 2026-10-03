import WeightedEdgeColoring.SelectedProfileCyclicSynchronization
import WeightedEdgeColoring.ProfileOptionBridge

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})
variable {n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}

/-!
# Ordinary options conditioned on concrete selected profiles

The transport stored in a bounded profile realization assigns an edge to
slots of the whole rounded-profile menu.  Once one profile is selected, only
the slots carried by that profile may be used.  This file restricts the
transport to those slots and divides by the probability of the selected
profile.  The division is the usual conditioning operation.  A slot then
has total conditioned load at most `s`.

The two endpoints of an edge need not retain the same conditioned mass.
We therefore scale both endpoint arrays to the smaller total and couple the
two scaled arrays.  This loses exactly half the absolute difference between
the endpoint totals.  The absolute difference is a concrete profile-pair
cost, so it can be fed directly to the cyclic synchronization theorem.
-/

variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)

/-- Assignment to one actual ordinary slot, conditioned on selecting the
profile which contains that slot.  Zero-probability profiles are assigned
zero by convention. -/
def conditionedProfileSlotAssign (v : G.V) (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr})
    (j : G.RoundedProfileOrdinarySlot (R0 v).law P.1) : ℝ :=
  if G.roundedProfileMass (R0 v).law hβ hr P.1 = 0 then 0 else
    (R0 v).largeAssign e (some ⟨P, j⟩) /
      G.roundedProfileMass (R0 v).law hβ hr P.1

theorem conditionedProfileSlotAssign_nonneg (v : G.V)
    (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr})
    (j : G.RoundedProfileOrdinarySlot (R0 v).law P.1) :
    0 ≤ G.conditionedProfileSlotAssign R0 v e P j := by
  unfold conditionedProfileSlotAssign
  split
  · exact le_rfl
  · exact div_nonneg ((R0 v).largeAssign_nonneg e (some ⟨P, j⟩))
      (G.roundedProfileMass_nonneg (R0 v).law hβ hr P.1)

/-- A fixed concrete slot has conditioned load at most `s`. -/
theorem sum_conditionedProfileSlotAssign_le (hs : 0 ≤ s)
    (v : G.V)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr})
    (j : G.RoundedProfileOrdinarySlot (R0 v).law P.1) :
    (∑ e : G.StarEdge v, G.conditionedProfileSlotAssign R0 v e P j) ≤ s := by
  classical
  let lam := G.roundedProfileMass (R0 v).law hβ hr P.1
  by_cases hlam : lam = 0
  · simp [conditionedProfileSlotAssign, lam, hlam, hs]
  · have hlam0 : 0 < lam := lt_of_le_of_ne
      (G.roundedProfileMass_nonneg (R0 v).law hβ hr P.1) (Ne.symm hlam)
    have hmass : G.roundedProfileMass (R0 v).law hβ hr P.1 ≠ 0 := by
      simpa only [lam] using hlam
    have hcap := (R0 v).largeAssign_capacity (some ⟨P, j⟩)
    have hcap' : (∑ f : G.StarEdge v,
        (R0 v).largeAssign f (some ⟨P, j⟩)) ≤
        s * G.roundedProfileMass (R0 v).law hβ hr P.1 := by
      simpa only [explicitLargeSlotCapacity] using hcap
    change (∑ f : G.StarEdge v, (R0 v).largeAssign f (some ⟨P, j⟩)) ≤
      s * G.roundedProfileMass (R0 v).law hβ hr P.1 at hcap
    simp_rw [conditionedProfileSlotAssign, hmass, if_false]
    change (∑ e : G.StarEdge v,
      (R0 v).largeAssign e (some ⟨P, j⟩) / lam) ≤ s
    rw [← Finset.sum_div]
    calc
      (∑ e : G.StarEdge v, (R0 v).largeAssign e (some ⟨P, j⟩)) / lam
          ≤ (s * lam) / lam :=
        div_le_div_of_nonneg_right hcap hlam0.le
      _ = s := by field_simp [hlam]

/-- Each single edge uses at most `s` of a conditioned concrete slot. -/
theorem conditionedProfileSlotAssign_le (hs : 0 ≤ s)
    (v : G.V) (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr})
    (j : G.RoundedProfileOrdinarySlot (R0 v).law P.1) :
    G.conditionedProfileSlotAssign R0 v e P j ≤ s := by
  calc
    G.conditionedProfileSlotAssign R0 v e P j ≤
        ∑ f : G.StarEdge v, G.conditionedProfileSlotAssign R0 v f P j :=
      Finset.single_le_sum
        (fun f _ ↦ G.conditionedProfileSlotAssign_nonneg R0 v f P j)
        (Finset.mem_univ e)
    _ ≤ s := G.sum_conditionedProfileSlotAssign_le R0 hs v P j

/-- Positive conditioned mass can only use a slot large enough for the
edge. -/
theorem conditionedProfileSlotAssign_compatible (v : G.V)
    (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr})
    (j : G.RoundedProfileOrdinarySlot (R0 v).law P.1)
    (hpos : 0 < G.conditionedProfileSlotAssign R0 v e P j) :
    G.weight e.1 ≤ G.roundedProfileOrdinarySlotSize (R0 v).law P.1 j := by
  unfold conditionedProfileSlotAssign at hpos
  by_cases hlam : G.roundedProfileMass (R0 v).law hβ hr P.1 = 0
  · simp [hlam] at hpos
  · simp only [hlam, if_false] at hpos
    have ha : 0 < (R0 v).largeAssign e (some ⟨P, j⟩) := by
      rcases div_pos_iff.mp hpos with h | h
      · exact h.1
      · exact (not_lt_of_ge (G.roundedProfileMass_nonneg
          (R0 v).law hβ hr P.1) h.2).elim
    have hfit := (R0 v).largeAssign_compatible e (some ⟨P, j⟩) ha
    simpa [explicitLargeSlotSize, roundedProfileOrdinarySlotSize] using hfit

/-- Multiplying a conditioned slot assignment by the profile probability
recovers the original transport mass.  This remains true for a zero-mass
profile because its slot capacity, and hence its assignment, is zero. -/
theorem roundedProfileMass_mul_conditionedProfileSlotAssign
    (v : G.V) (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr})
    (j : G.RoundedProfileOrdinarySlot (R0 v).law P.1) :
    G.roundedProfileMass (R0 v).law hβ hr P.1 *
        G.conditionedProfileSlotAssign R0 v e P j =
      (R0 v).largeAssign e (some ⟨P, j⟩) := by
  classical
  let lam := G.roundedProfileMass (R0 v).law hβ hr P.1
  by_cases hlam : lam = 0
  · have hsingle : (R0 v).largeAssign e (some ⟨P, j⟩) ≤
        ∑ f : G.StarEdge v, (R0 v).largeAssign f (some ⟨P, j⟩) :=
      Finset.single_le_sum
        (fun f _ ↦ (R0 v).largeAssign_nonneg f (some ⟨P, j⟩))
        (Finset.mem_univ e)
    have hcap := (R0 v).largeAssign_capacity (some ⟨P, j⟩)
    have hcap' : (∑ f : G.StarEdge v,
        (R0 v).largeAssign f (some ⟨P, j⟩)) ≤
        s * G.roundedProfileMass (R0 v).law hβ hr P.1 := by
      simpa only [explicitLargeSlotCapacity] using hcap
    have hzero : (R0 v).largeAssign e (some ⟨P, j⟩) = 0 := by
      apply le_antisymm
      · calc
          (R0 v).largeAssign e (some ⟨P, j⟩) ≤
              ∑ f : G.StarEdge v, (R0 v).largeAssign f (some ⟨P, j⟩) :=
            hsingle
          _ ≤ s * lam := by simpa only [lam] using hcap'
          _ = 0 := by rw [hlam, mul_zero]
      · exact (R0 v).largeAssign_nonneg e (some ⟨P, j⟩)
    simp [conditionedProfileSlotAssign, lam, hlam, hzero]
  · have hmass : G.roundedProfileMass (R0 v).law hβ hr P.1 ≠ 0 := by
      simpa only [lam] using hlam
    simp only [conditionedProfileSlotAssign, hmass, if_false]
    field_simp [hmass]

/-- The total conditioned ordinary mass of one incident edge in one
profile. -/
def conditionedProfileEdgeMass (v : G.V) (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr}) : ℝ :=
  ∑ j : G.RoundedProfileOrdinarySlot (R0 v).law P.1,
    G.conditionedProfileSlotAssign R0 v e P j

theorem conditionedProfileEdgeMass_nonneg (v : G.V) (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr}) :
    0 ≤ G.conditionedProfileEdgeMass R0 v e P := by
  exact Finset.sum_nonneg fun j _ ↦
    G.conditionedProfileSlotAssign_nonneg R0 v e P j

/-- Averaging the conditioned edge mass over the rounded-profile law gives
exactly the part of the original transport placed in non-repair slots. -/
theorem sum_profileMass_mul_conditionedProfileEdgeMass
    (v : G.V) (e : G.StarEdge v) :
    (∑ P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr},
      G.roundedProfileMass (R0 v).law hβ hr P.1 *
        G.conditionedProfileEdgeMass R0 v e P) =
      ∑ P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr},
        ∑ j : G.RoundedProfileOrdinarySlot (R0 v).law P.1,
          (R0 v).largeAssign e (some ⟨P, j⟩) := by
  unfold conditionedProfileEdgeMass
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact G.roundedProfileMass_mul_conditionedProfileSlotAssign R0 v e P j

/-- The averaged non-repair mass plus the repair-slot mass is the exact
large-edge marginal stored in the bounded realization. -/
theorem sum_profileMass_mul_conditionedProfileEdgeMass_add_repair
    (v : G.V) (e : G.StarEdge v) :
    (∑ P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr},
      G.roundedProfileMass (R0 v).law hβ hr P.1 *
        G.conditionedProfileEdgeMass R0 v e P) +
      (R0 v).largeAssign e none =
        if β ≤ G.weight e.1 then s * ((1 : ℝ) / n) else 0 := by
  rw [G.sum_profileMass_mul_conditionedProfileEdgeMass R0 v e]
  have hmarginal := (R0 v).largeAssign_marginal e
  rw [Fintype.sum_option] at hmarginal
  rw [Fintype.sum_sigma] at hmarginal
  rw [add_comm]
  exact hmarginal

/-- The concrete ordinary slots of one profile inject into the common
padded slot range. -/
theorem roundedProfileOrdinarySlot_card_le (v : G.V)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr}) :
    Fintype.card (G.RoundedProfileOrdinarySlot (R0 v).law P.1) ≤
      explicitLargeSlotBound β q r := by
  let code : G.RoundedProfileOrdinarySlot (R0 v).law P.1 →
      Fin (explicitLargeSlotBound β q r) := fun j ↦
    G.paddedLargeSlotCode (R0 v) (some ⟨P, j⟩)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective code (by
    intro i j hij
    have h := G.paddedLargeSlotCode_injective (R0 v) hij
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2)

/-- A profile retains at most `K*s` conditioned mass from one edge, where
`K` is the common padded slot bound. -/
theorem conditionedProfileEdgeMass_le (hs : 0 ≤ s)
    (v : G.V) (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr}) :
    G.conditionedProfileEdgeMass R0 v e P ≤
      (explicitLargeSlotBound β q r : ℝ) * s := by
  unfold conditionedProfileEdgeMass
  calc
    (∑ j : G.RoundedProfileOrdinarySlot (R0 v).law P.1,
        G.conditionedProfileSlotAssign R0 v e P j) ≤
        ∑ _j : G.RoundedProfileOrdinarySlot (R0 v).law P.1, s := by
      exact Finset.sum_le_sum fun j _ ↦
        G.conditionedProfileSlotAssign_le R0 hs v e P j
    _ = (Fintype.card (G.RoundedProfileOrdinarySlot
          (R0 v).law P.1) : ℝ) * s := by simp
    _ ≤ (explicitLargeSlotBound β q r : ℝ) * s := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast G.roundedProfileOrdinarySlot_card_le R0 v P) hs

/-- Restrict the conditioned assignment to the selected profile and pad its
concrete slots into the common place range. -/
def selectedConditionedPaddedAssign
    (selected : G.SelectedProfileWord R0) (v : G.V) (c : Fin n)
    (e : G.StarEdge v) (i : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  ∑ j : G.RoundedProfileOrdinarySlot (R0 v).law (selected v c).1,
    if G.paddedLargeSlotCode (R0 v) (some ⟨selected v c, j⟩) = i then
      G.conditionedProfileSlotAssign R0 v e (selected v c) j else 0

theorem selectedConditionedPaddedAssign_nonneg
    (selected : G.SelectedProfileWord R0) (v : G.V) (c : Fin n)
    (e : G.StarEdge v) (i : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.selectedConditionedPaddedAssign R0 selected v c e i := by
  exact Finset.sum_nonneg fun j _ ↦ by
    split
    · exact G.conditionedProfileSlotAssign_nonneg R0 v e (selected v c) j
    · exact le_rfl

/-- Padding neither creates nor loses conditioned mass. -/
theorem sum_selectedConditionedPaddedAssign
    (selected : G.SelectedProfileWord R0) (v : G.V) (c : Fin n)
    (e : G.StarEdge v) :
    (∑ i, G.selectedConditionedPaddedAssign R0 selected v c e i) =
      G.conditionedProfileEdgeMass R0 v e (selected v c) := by
  classical
  unfold selectedConditionedPaddedAssign conditionedProfileEdgeMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  simp

/-- Positive padded mass is witnessed by a concrete slot of the selected
profile, and that slot fits the edge. -/
theorem selectedConditionedPaddedAssign_pos_compatible
    (selected : G.SelectedProfileWord R0) (v : G.V) (c : Fin n)
    (e : G.StarEdge v) (i : Fin (explicitLargeSlotBound β q r))
    (hpos : 0 < G.selectedConditionedPaddedAssign R0 selected v c e i) :
    ∃ j : G.RoundedProfileOrdinarySlot (R0 v).law (selected v c).1,
      G.paddedLargeSlotCode (R0 v) (some ⟨selected v c, j⟩) = i ∧
      0 < G.conditionedProfileSlotAssign R0 v e (selected v c) j ∧
      G.weight e.1 ≤ G.roundedProfileOrdinarySlotSize
        (R0 v).law (selected v c).1 j := by
  classical
  unfold selectedConditionedPaddedAssign at hpos
  have hnonneg : ∀ j ∈ (Finset.univ : Finset
      (G.RoundedProfileOrdinarySlot (R0 v).law (selected v c).1)),
      0 ≤ (if G.paddedLargeSlotCode (R0 v) (some ⟨selected v c, j⟩) = i then
        G.conditionedProfileSlotAssign R0 v e (selected v c) j else 0) := by
    intro j _
    split
    · exact G.conditionedProfileSlotAssign_nonneg R0 v e (selected v c) j
    · exact le_rfl
  rcases (Finset.sum_pos_iff_of_nonneg hnonneg).mp hpos with ⟨j, _hj, hj⟩
  by_cases hcode :
      G.paddedLargeSlotCode (R0 v) (some ⟨selected v c, j⟩) = i
  · simp only [hcode, if_true] at hj
    exact ⟨j, hcode, hj,
      G.conditionedProfileSlotAssign_compatible R0 v e (selected v c) j hj⟩
  · simp [hcode] at hj

/-- Scale a nonnegative array of total `A` to total `min A B`. -/
def scaleToMin {I : Type*} (A B : ℝ) (a : I → ℝ) (i : I) : ℝ :=
  if A = 0 then 0 else min A B * a i / A

theorem scaleToMin_nonneg {I : Type*} (A B : ℝ) (a : I → ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : ∀ i, 0 ≤ a i) (i : I) :
    0 ≤ scaleToMin A B a i := by
  unfold scaleToMin
  split
  · exact le_rfl
  · exact div_nonneg (mul_nonneg (le_min hA hB) (ha i)) hA

theorem sum_scaleToMin {I : Type*} [Fintype I]
    (A B : ℝ) (a : I → ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsum : ∑ i, a i = A) :
    (∑ i, scaleToMin A B a i) = min A B := by
  classical
  by_cases hAz : A = 0
  · rw [hAz]
    simp [scaleToMin, hB]
  · unfold scaleToMin
    simp only [hAz, if_false]
    rw [← Finset.sum_div, ← Finset.mul_sum, hsum]
    field_simp [hAz]

/-- Couple two endpoint arrays after scaling both to their smaller total. -/
def minEndpointPairMass {I J : Type*} [Fintype I] [Fintype J]
    (A B : ℝ) (a : I → ℝ) (b : J → ℝ) (i : I) (j : J) : ℝ :=
  endpointPairMass (min A B) (scaleToMin A B a) (scaleToMin B A b) i j

theorem minEndpointPairMass_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (A B : ℝ) (a : I → ℝ) (b : J → ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (i : I) (j : J) :
    0 ≤ minEndpointPairMass A B a b i j := by
  apply endpointPairMass_nonneg
  · exact le_min hA hB
  · exact scaleToMin_nonneg A B a hA hB ha
  · exact scaleToMin_nonneg B A b hB hA hb

theorem sum_minEndpointPairMass {I J : Type*} [Fintype I] [Fintype J]
    (A B : ℝ) (a : I → ℝ) (b : J → ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hsumA : ∑ i, a i = A) (hsumB : ∑ j, b j = B) :
    (∑ i, ∑ j, minEndpointPairMass A B a b i j) = min A B := by
  apply sum_endpointPairMass
  · exact scaleToMin_nonneg A B a hA hB ha
  · exact scaleToMin_nonneg B A b hB hA hb
  · exact sum_scaleToMin A B a hA hB hsumA
  · simpa [min_comm] using sum_scaleToMin B A b hB hA hsumB

theorem sum_minEndpointPairMass_right {I J : Type*}
    [Fintype I] [Fintype J]
    (A B : ℝ) (a : I → ℝ) (b : J → ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hsumA : ∑ i, a i = A) (hsumB : ∑ j, b j = B) (i : I) :
    (∑ j, minEndpointPairMass A B a b i j) = scaleToMin A B a i := by
  apply sum_endpointPairMass_right
  · exact scaleToMin_nonneg A B a hA hB ha
  · exact scaleToMin_nonneg B A b hB hA hb
  · exact sum_scaleToMin A B a hA hB hsumA
  · simpa [min_comm] using sum_scaleToMin B A b hB hA hsumB

theorem sum_minEndpointPairMass_left {I J : Type*}
    [Fintype I] [Fintype J]
    (A B : ℝ) (a : I → ℝ) (b : J → ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hsumA : ∑ i, a i = A) (hsumB : ∑ j, b j = B) (j : J) :
    (∑ i, minEndpointPairMass A B a b i j) = scaleToMin B A b j := by
  apply sum_endpointPairMass_left
  · exact scaleToMin_nonneg A B a hA hB ha
  · exact scaleToMin_nonneg B A b hB hA hb
  · exact sum_scaleToMin A B a hA hB hsumA
  · simpa [min_comm] using sum_scaleToMin B A b hB hA hsumB

/-- The two endpoint totals for an edge and a pair of concrete profiles. -/
def conditionedProfilePairLeftMass (e : G.E)
    (P : {P // P ∈ G.roundedProfileMenu (R0 (G.fst e)).law hβ hr}) : ℝ :=
  G.conditionedProfileEdgeMass R0 (G.fst e) (G.fstStarEdge e) P

def conditionedProfilePairRightMass (e : G.E)
    (Q : {P // P ∈ G.roundedProfileMenu (R0 (G.snd e)).law hβ hr}) : ℝ :=
  G.conditionedProfileEdgeMass R0 (G.snd e) (G.sndStarEdge e) Q

/-- The cost paid when the two selected endpoint profiles retain different
conditioned amounts of the same edge. -/
def conditionedProfilePairCost : G.SelectedProfilePairCost R0 :=
  fun e P Q ↦ |G.conditionedProfilePairLeftMass R0 e P -
    G.conditionedProfilePairRightMass R0 e Q|

theorem conditionedProfilePairCost_nonneg :
    ∀ e P Q, 0 ≤ G.conditionedProfilePairCost R0 e P Q := by
  intro e P Q
  exact abs_nonneg _

/-- The synchronization cost is uniformly bounded by the number of padded
ordinary places times `s`. -/
theorem conditionedProfilePairCost_le (hs : 0 ≤ s) :
    ∀ e P Q, G.conditionedProfilePairCost R0 e P Q ≤
      (explicitLargeSlotBound β q r : ℝ) * s := by
  intro e P Q
  have hL0 := G.conditionedProfileEdgeMass_nonneg R0
    (G.fst e) (G.fstStarEdge e) P
  have hR0 := G.conditionedProfileEdgeMass_nonneg R0
    (G.snd e) (G.sndStarEdge e) Q
  have hL := G.conditionedProfileEdgeMass_le R0 hs
    (G.fst e) (G.fstStarEdge e) P
  have hR := G.conditionedProfileEdgeMass_le R0 hs
    (G.snd e) (G.sndStarEdge e) Q
  unfold conditionedProfilePairCost conditionedProfilePairLeftMass
    conditionedProfilePairRightMass
  rw [abs_le]
  constructor <;> linarith

/-- Exact pointwise accounting: coupling keeps the smaller endpoint total,
which is the average of the two totals minus half their discrepancy. -/
theorem min_conditionedProfilePairMass_eq (e : G.E)
    (P : {P // P ∈ G.roundedProfileMenu (R0 (G.fst e)).law hβ hr})
    (Q : {P // P ∈ G.roundedProfileMenu (R0 (G.snd e)).law hβ hr}) :
    min (G.conditionedProfilePairLeftMass R0 e P)
        (G.conditionedProfilePairRightMass R0 e Q) =
      (G.conditionedProfilePairLeftMass R0 e P +
        G.conditionedProfilePairRightMass R0 e Q -
        G.conditionedProfilePairCost R0 e P Q) / 2 := by
  let A := G.conditionedProfilePairLeftMass R0 e P
  let B := G.conditionedProfilePairRightMass R0 e Q
  by_cases hAB : A ≤ B
  · rw [min_eq_left hAB]
    have habs : |A - B| = B - A := by
      rw [abs_of_nonpos (sub_nonpos.mpr hAB)]
      ring
    simp only [conditionedProfilePairCost, conditionedProfilePairLeftMass,
      conditionedProfilePairRightMass, A, B] at habs ⊢
    rw [habs]
    ring
  · have hBA : B ≤ A := le_of_not_ge hAB
    rw [min_eq_right hBA]
    have habs : |A - B| = A - B := abs_of_nonneg (sub_nonneg.mpr hBA)
    simp only [conditionedProfilePairCost, conditionedProfilePairLeftMass,
      conditionedProfilePairRightMass, A, B] at habs ⊢
    rw [habs]
    ring

/-- Concrete coupled option mass for one edge and one pair of endpoint
profiles.  Its support lies in the slots of exactly those two profiles. -/
def conditionedProfilePairOptionMass (e : G.E)
    (P : {P // P ∈ G.roundedProfileMenu (R0 (G.fst e)).law hβ hr})
    (Q : {P // P ∈ G.roundedProfileMenu (R0 (G.snd e)).law hβ hr})
    (i j : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  minEndpointPairMass
    (G.conditionedProfilePairLeftMass R0 e P)
    (G.conditionedProfilePairRightMass R0 e Q)
    (fun i ↦ ∑ ji : G.RoundedProfileOrdinarySlot (R0 (G.fst e)).law P.1,
      if G.paddedLargeSlotCode (R0 (G.fst e)) (some ⟨P, ji⟩) = i then
        G.conditionedProfileSlotAssign R0 (G.fst e) (G.fstStarEdge e) P ji
      else 0)
    (fun j ↦ ∑ jj : G.RoundedProfileOrdinarySlot (R0 (G.snd e)).law Q.1,
      if G.paddedLargeSlotCode (R0 (G.snd e)) (some ⟨Q, jj⟩) = j then
        G.conditionedProfileSlotAssign R0 (G.snd e) (G.sndStarEdge e) Q jj
      else 0) i j

theorem conditionedProfilePairOptionMass_nonneg (e : G.E)
    (P : {P // P ∈ G.roundedProfileMenu (R0 (G.fst e)).law hβ hr})
    (Q : {P // P ∈ G.roundedProfileMenu (R0 (G.snd e)).law hβ hr})
    (i j : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.conditionedProfilePairOptionMass R0 e P Q i j := by
  apply minEndpointPairMass_nonneg
  · exact G.conditionedProfileEdgeMass_nonneg R0 _ _ P
  · exact G.conditionedProfileEdgeMass_nonneg R0 _ _ Q
  · intro k
    exact Finset.sum_nonneg fun ji _ ↦ by
      split
      · exact G.conditionedProfileSlotAssign_nonneg R0 _ _ P ji
      · exact le_rfl
  · intro k
    exact Finset.sum_nonneg fun jj _ ↦ by
      split
      · exact G.conditionedProfileSlotAssign_nonneg R0 _ _ Q jj
      · exact le_rfl

/-- The coupled option array has total mass equal to the smaller conditioned
endpoint total. -/
theorem sum_conditionedProfilePairOptionMass (e : G.E)
    (P : {P // P ∈ G.roundedProfileMenu (R0 (G.fst e)).law hβ hr})
    (Q : {P // P ∈ G.roundedProfileMenu (R0 (G.snd e)).law hβ hr}) :
    (∑ i, ∑ j, G.conditionedProfilePairOptionMass R0 e P Q i j) =
      min (G.conditionedProfilePairLeftMass R0 e P)
        (G.conditionedProfilePairRightMass R0 e Q) := by
  classical
  apply sum_minEndpointPairMass
  · exact G.conditionedProfileEdgeMass_nonneg R0 _ _ P
  · exact G.conditionedProfileEdgeMass_nonneg R0 _ _ Q
  · intro k
    exact Finset.sum_nonneg fun ji _ ↦ by
      split
      · exact G.conditionedProfileSlotAssign_nonneg R0 _ _ P ji
      · exact le_rfl
  · intro k
    exact Finset.sum_nonneg fun jj _ ↦ by
      split
      · exact G.conditionedProfileSlotAssign_nonneg R0 _ _ Q jj
      · exact le_rfl
  · unfold conditionedProfilePairLeftMass conditionedProfileEdgeMass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ji _
    simp
  · unfold conditionedProfilePairRightMass conditionedProfileEdgeMass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro jj _
    simp

/-- Combining the coupling identity with the discrepancy identity gives a
pointwise formula ready for cyclic profile synchronization. -/
theorem sum_conditionedProfilePairOptionMass_eq_cost (e : G.E)
    (P : {P // P ∈ G.roundedProfileMenu (R0 (G.fst e)).law hβ hr})
    (Q : {P // P ∈ G.roundedProfileMenu (R0 (G.snd e)).law hβ hr}) :
    (∑ i, ∑ j, G.conditionedProfilePairOptionMass R0 e P Q i j) =
      (G.conditionedProfilePairLeftMass R0 e P +
        G.conditionedProfilePairRightMass R0 e Q -
        G.conditionedProfilePairCost R0 e P Q) / 2 := by
  rw [G.sum_conditionedProfilePairOptionMass R0 e P Q]
  exact G.min_conditionedProfilePairMass_eq R0 e P Q

end WeightedSimpleGraph

end

end WeightedEdgeColoring
