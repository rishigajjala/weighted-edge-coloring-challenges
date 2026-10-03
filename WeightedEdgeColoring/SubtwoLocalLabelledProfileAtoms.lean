import WeightedEdgeColoring.SubtwoLabelGraphTransport
import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileAtomAssignments

/-!
# Local extended profile atoms for endpoint-dependent proposals

The existing color-dependent profile atoms require the same proposal function
at both endpoints.  A conditional endpoint-label proposal has a different
normalization at each endpoint.  These definitions extract the purely local
state, its probability, and its large and tiny assignments directly from one
bounded profile realization, without requiring a global edge proposal.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {v : G.V} {φ : G.StarEdge v → ℝ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : G.BoundedProfileRealization φ s β q r hβ hr)

/-- One rounded profile, or one of the three auxiliary states. -/
abbrev LocalExtendedProfileState :=
  Sum {P // P ∈ G.roundedProfileMenu R.law hβ hr} (Fin 3)

def localExtendedProfileProbability
    (z : G.LocalExtendedProfileState R) : ℝ :=
  match z with
  | Sum.inl P => s * G.roundedProfileMass R.law hβ hr P.1
  | Sum.inr k =>
      if k.1 = 0 then s * q
      else if k.1 = 1 then s * r
      else 1 - s * (1 + q + r)

theorem localExtendedProfileProbability_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (z : G.LocalExtendedProfileState R) :
    0 ≤ G.localExtendedProfileProbability R z := by
  cases z with
  | inl P =>
      exact mul_nonneg hs (G.roundedProfileMass_nonneg R.law hβ hr P.1)
  | inr k =>
      by_cases hk0 : k.1 = 0
      · simp [localExtendedProfileProbability, hk0, mul_nonneg hs hq]
      · by_cases hk1 : k.1 = 1
        · simp [localExtendedProfileProbability, hk0, hk1,
            mul_nonneg hs hr0]
        · simpa [localExtendedProfileProbability, hk0, hk1] using hleft

theorem sum_localExtendedProfileProbability :
    (∑ z : G.LocalExtendedProfileState R,
      G.localExtendedProfileProbability R z) = 1 := by
  classical
  have hmenu :
      (∑ P : {P // P ∈ G.roundedProfileMenu R.law hβ hr},
        G.roundedProfileMass R.law hβ hr P.1) = 1 := by
    calc
      _ = ∑ P ∈ G.roundedProfileMenu R.law hβ hr,
          G.roundedProfileMass R.law hβ hr P := by
        symm
        exact Finset.sum_subtype _ (fun _ ↦ Iff.rfl) _
      _ = 1 := G.sum_roundedProfileMass R.law hβ hr
  rw [Fintype.sum_sum_type]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  simp only [localExtendedProfileProbability, Fin.val_zero, if_pos,
    Fin.val_succ, Nat.succ_ne_zero, if_false, Nat.reduceAdd, zero_add]
  rw [← Finset.mul_sum, hmenu]
  norm_num
  ring

/-- Large assignment in a padded ordinary slot. -/
def localActualProfilePaddedAssign
    (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu R.law hβ hr})
    (i : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  ∑ j : G.RoundedProfileOrdinarySlot R.law P.1,
    if G.paddedLargeSlotCode R (some ⟨P, j⟩) = i then
      R.largeAssign e (some ⟨P, j⟩) else 0

def localExtendedProfileLargeAssign
    (e : G.StarEdge v) (z : G.LocalExtendedProfileState R)
    (i : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  match z with
  | Sum.inl P => G.localActualProfilePaddedAssign R e P i
  | Sum.inr k =>
      if k.1 = 0 then
        if G.paddedLargeSlotCode R none = i then R.largeAssign e none else 0
      else 0

theorem sum_localActualProfilePaddedAssign
    (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu R.law hβ hr}) :
    (∑ i, G.localActualProfilePaddedAssign R e P i) =
      ∑ j : G.RoundedProfileOrdinarySlot R.law P.1,
        R.largeAssign e (some ⟨P, j⟩) := by
  classical
  unfold localActualProfilePaddedAssign
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

theorem localActualProfilePaddedAssign_nonneg
    (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu R.law hβ hr})
    (i : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.localActualProfilePaddedAssign R e P i := by
  exact Finset.sum_nonneg fun j _ ↦ by
    split
    · exact R.largeAssign_nonneg e (some ⟨P, j⟩)
    · exact le_rfl

theorem localExtendedProfileLargeAssign_nonneg
    (e : G.StarEdge v) (z : G.LocalExtendedProfileState R)
    (i : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.localExtendedProfileLargeAssign R e z i := by
  rcases z with P | k
  · exact G.localActualProfilePaddedAssign_nonneg R e P i
  · simp only [localExtendedProfileLargeAssign]
    by_cases hk : k.1 = 0
    · simp only [hk, if_true]
      split
      · exact R.largeAssign_nonneg e none
      · exact le_rfl
    · simp [hk]

theorem sum_localActualProfilePaddedAssign_star_le
    (hs : 0 ≤ s)
    (P : {P // P ∈ G.roundedProfileMenu R.law hβ hr})
    (i : Fin (explicitLargeSlotBound β q r)) :
    (∑ e : G.StarEdge v,
      G.localActualProfilePaddedAssign R e P i) ≤
      s * G.roundedProfileMass R.law hβ hr P.1 := by
  classical
  let code : G.RoundedProfileOrdinarySlot R.law P.1 →
      Fin (explicitLargeSlotBound β q r) := fun j ↦
    G.paddedLargeSlotCode R (some ⟨P, j⟩)
  by_cases hex : ∃ j, code j = i
  · rcases hex with ⟨j0, hj0⟩
    have hinj : Function.Injective code := by
      intro j k hjk
      have h := G.paddedLargeSlotCode_injective R hjk
      exact eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2
    calc
      (∑ e : G.StarEdge v,
        G.localActualProfilePaddedAssign R e P i) =
          ∑ e : G.StarEdge v, R.largeAssign e (some ⟨P, j0⟩) := by
        apply Finset.sum_congr rfl
        intro e _
        unfold localActualProfilePaddedAssign
        rw [Finset.sum_eq_single j0]
        · simp [code, hj0]
        · intro j _ hne
          have hcode : code j ≠ i := fun hj ↦
            hne (hinj (hj.trans hj0.symm))
          simp [code, hcode]
        · simp
      _ ≤ G.explicitLargeSlotCapacity R.law hβ hr
          (some ⟨P, j0⟩) := R.largeAssign_capacity (some ⟨P, j0⟩)
      _ = s * G.roundedProfileMass R.law hβ hr P.1 := rfl
  · have hzero : ∀ e : G.StarEdge v,
        G.localActualProfilePaddedAssign R e P i = 0 := by
      intro e
      unfold localActualProfilePaddedAssign
      apply Finset.sum_eq_zero
      intro j _
      have hcode : code j ≠ i := fun h ↦ hex ⟨j, h⟩
      simp [code, hcode]
    calc
      (∑ e : G.StarEdge v,
        G.localActualProfilePaddedAssign R e P i) = 0 := by
          simp [hzero]
      _ ≤ s * G.roundedProfileMass R.law hβ hr P.1 :=
        mul_nonneg hs (G.roundedProfileMass_nonneg R.law hβ hr P.1)

theorem sum_localExtendedProfileLargeAssign_star_le
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (z : G.LocalExtendedProfileState R)
    (i : Fin (explicitLargeSlotBound β q r)) :
    (∑ e : G.StarEdge v,
      G.localExtendedProfileLargeAssign R e z i) ≤
      G.localExtendedProfileProbability R z := by
  rcases z with P | k
  · exact G.sum_localActualProfilePaddedAssign_star_le R hs P i
  · by_cases hk0 : k.1 = 0
    · by_cases hcode : G.paddedLargeSlotCode R none = i
      · simp only [localExtendedProfileLargeAssign,
          localExtendedProfileProbability, hk0, hcode, if_true]
        simpa only [explicitLargeSlotCapacity] using
          R.largeAssign_capacity none
      · simp only [localExtendedProfileLargeAssign,
          localExtendedProfileProbability, hk0, hcode, if_true,
          if_false, Finset.sum_const_zero]
        exact mul_nonneg hs hq
    · have hprob := G.localExtendedProfileProbability_nonneg R
        hs hq hr0 hleft (Sum.inr k)
      simpa [localExtendedProfileLargeAssign, hk0] using hprob

theorem sum_localExtendedProfileLargeAssign
    (e : G.StarEdge v) :
    (∑ z : G.LocalExtendedProfileState R,
      ∑ i, G.localExtendedProfileLargeAssign R e z i) =
      if β ≤ G.weight e.1 then s * φ e else 0 := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [localExtendedProfileLargeAssign]
  simp_rw [G.sum_localActualProfilePaddedAssign R e]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  simp only [Fin.val_zero, if_pos, Fin.val_succ, Nat.succ_ne_zero,
    if_false, Finset.sum_const_zero, add_zero]
  have hrepair :
      (∑ i : Fin (explicitLargeSlotBound β q r),
        if G.paddedLargeSlotCode R none = i then
          R.largeAssign e none else 0) = R.largeAssign e none := by simp
  rw [hrepair]
  have hmarginal := R.largeAssign_marginal e
  rw [Fintype.sum_option, Fintype.sum_sigma] at hmarginal
  rw [add_comm]
  exact hmarginal

def localExtendedProfileTinyAssign
    (e : G.StarEdge v) (z : G.LocalExtendedProfileState R) : ℝ :=
  match z with
  | Sum.inl P => R.tinyAssign e (some P)
  | Sum.inr k => if k.1 = 1 then R.tinyAssign e none else 0

theorem localExtendedProfileTinyAssign_nonneg
    (e : G.StarEdge v) (z : G.LocalExtendedProfileState R) :
    0 ≤ G.localExtendedProfileTinyAssign R e z := by
  rcases z with P | k
  · exact R.tinyAssign_nonneg e (some P)
  · simp only [localExtendedProfileTinyAssign]
    split
    · exact R.tinyAssign_nonneg e none
    · exact le_rfl

theorem localRoundedProfileReservoirMass_le_profileMass
    (P : G.RoundedProfileCode R.law) :
    G.roundedProfileReservoirMass R.law hβ hr P ≤
      G.roundedProfileMass R.law hβ hr P := by
  classical
  unfold roundedProfileReservoirMass roundedProfileMass fiberMass
  apply Finset.sum_le_sum
  intro k _
  have hraw0 : 0 ≤
      (G.rawProfile β (R.law.outcome k)).reservoir :=
    G.rawProfile_reservoir_nonneg (R.law.feasible k)
  have hround : roundReservoir r
      (G.rawProfile β (R.law.outcome k)).reservoir ≤ 1 :=
    (roundReservoir_le hr hraw0).trans
      (G.rawProfile_reservoir_le_one
        (β := β) (S := R.law.outcome k))
  have hp0 := R.law.probability_nonneg k
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hround hp0

theorem sum_weight_mul_localExtendedProfileTinyAssign_le
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (z : G.LocalExtendedProfileState R) :
    (∑ e : G.StarEdge v,
      G.weight e.1 * G.localExtendedProfileTinyAssign R e z) ≤
      G.localExtendedProfileProbability R z := by
  rcases z with P | k
  · have hcap := R.tinyAssign_capacity (some P)
    have hcap' :
        (∑ e : G.StarEdge v,
          G.weight e.1 * R.tinyAssign e (some P)) ≤
            s * G.roundedProfileReservoirMass R.law hβ hr P.1 := by
      simpa only [explicitTinyProfileCapacity] using hcap
    calc
      (∑ e : G.StarEdge v,
        G.weight e.1 *
          G.localExtendedProfileTinyAssign R e (Sum.inl P)) ≤
        s * G.roundedProfileReservoirMass R.law hβ hr P.1 := by
          simpa [localExtendedProfileTinyAssign] using hcap'
      _ ≤ s * G.roundedProfileMass R.law hβ hr P.1 :=
        mul_le_mul_of_nonneg_left
          (G.localRoundedProfileReservoirMass_le_profileMass R P.1) hs
      _ = G.localExtendedProfileProbability R (Sum.inl P) := rfl
  · by_cases hk1 : k.1 = 1
    · simp only [localExtendedProfileTinyAssign,
        localExtendedProfileProbability, hk1, if_true]
      simp only [if_false, one_ne_zero]
      simpa only [explicitTinyProfileCapacity] using
        R.tinyAssign_capacity none
    · simp only [localExtendedProfileTinyAssign, hk1, if_false,
        mul_zero, Finset.sum_const_zero]
      exact G.localExtendedProfileProbability_nonneg R
        hs hq hr0 hleft (Sum.inr k)

theorem sum_localExtendedProfileTinyAssign
    (e : G.StarEdge v) :
    (∑ z : G.LocalExtendedProfileState R,
      G.localExtendedProfileTinyAssign R e z) =
      if G.weight e.1 < β then s * φ e else 0 := by
  classical
  rw [Fintype.sum_sum_type]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  simp only [localExtendedProfileTinyAssign, Fin.val_zero,
    zero_ne_one, if_false, Fin.val_succ, Nat.reduceAdd, if_true]
  have hmarginal := R.tinyAssign_marginal e
  rw [Fintype.sum_option] at hmarginal
  rw [add_comm]
  simpa [tinyOccurrenceDemand] using hmarginal

end WeightedMultigraph

end

end WeightedEdgeColoring
