import WeightedEdgeColoring.MultigraphSelectedProfileConditionedGlobal

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
# Tiny-reservoir assignments on the extended profile states

The extended state law already used by the large-slot construction has one
actual state for every rounded profile and three special states.  This file
puts the rounded tiny-edge transport on the actual states and puts the lost
reservoir mass on special state `1`.  Special states `0` and `2` carry no
tiny edges.  Thus the same state law simultaneously supports the ordinary
slots and the tiny reservoir.

This is only the local coupling layer.  It does not select a profile word.
-/

private theorem natFloor_cast_eq_intFloor_cast (a : ℝ) (ha : 0 ≤ a) :
    ((⌊a⌋₊ : ℕ) : ℝ) = ((⌊a⌋ : ℤ) : ℝ) := by
  have hn := (Nat.floor_eq_iff (n := ⌊a⌋₊) ha).mp rfl
  have hi : (⌊a⌋ : ℤ) = (⌊a⌋₊ : ℕ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact_mod_cast hn.1
    · exact_mod_cast hn.2
  rw [hi]
  norm_num

/-- The concrete tiny reservoir carried by an extended state.  An actual
profile carries its rounded reservoir.  State `1` is the size-one repair
reservoir. -/
def extendedProfileReservoirSize (v : G.V)
    (z : G.ExtendedProfileState R0 v) : ℝ :=
  match z with
  | Sum.inl P => r * P.1.2.val
  | Sum.inr k => if k.1 = 1 then 1 else 0

theorem extendedProfileReservoirSize_nonneg (v : G.V)
    (z : G.ExtendedProfileState R0 v) :
    0 ≤ G.extendedProfileReservoirSize R0 v z := by
  rcases z with P | k
  · exact mul_nonneg hr.le (Nat.cast_nonneg _)
  · simp only [extendedProfileReservoirSize]
    split <;> norm_num

/-- On a fiber of the rounded-profile map, the rounded reservoir is the
reservoir recorded by the common profile code. -/
theorem roundReservoir_eq_profileReservoir_of_code
    (v : G.V) (k : Fin (R0 v).law.m)
    (P : G.RoundedProfileCode (R0 v).law)
    (hcode : G.roundedProfileCode (R0 v).law hβ hr k = P) :
    roundReservoir r
        (G.rawProfile β ((R0 v).law.outcome k)).reservoir =
      r * P.2.val := by
  have hR : 0 ≤ (G.rawProfile β ((R0 v).law.outcome k)).reservoir :=
    G.rawProfile_reservoir_nonneg ((R0 v).law.feasible k)
  have hcast := natFloor_cast_eq_intFloor_cast
    ((G.rawProfile β ((R0 v).law.outcome k)).reservoir / r)
    (div_nonneg hR hr.le)
  unfold roundReservoir
  rw [← hcast]
  have hsecond :
      (G.roundedProfileCode (R0 v).law hβ hr k).2 = P.2 :=
    congrArg Prod.snd hcode
  change r * (⌊(G.rawProfile β ((R0 v).law.outcome k)).reservoir / r⌋₊ : ℕ) =
    r * (P.2.val : ℕ)
  rw [show ⌊(G.rawProfile β ((R0 v).law.outcome k)).reservoir / r⌋₊ =
      P.2.val by
    simpa [roundedProfileCode] using congrArg Fin.val hsecond]

theorem extendedProfileReservoirSize_le_one (v : G.V)
    (z : G.ExtendedProfileState R0 v) :
    G.extendedProfileReservoirSize R0 v z ≤ 1 := by
  rcases z with P | k
  · have hP := P.2
    change P.1 ∈ (Finset.univ.image
      (G.roundedProfileCode (R0 v).law hβ hr)) at hP
    rw [Finset.mem_image] at hP
    rcases hP with ⟨k, _hk, hcode⟩
    have hR : 0 ≤ (G.rawProfile β ((R0 v).law.outcome k)).reservoir :=
      G.rawProfile_reservoir_nonneg ((R0 v).law.feasible k)
    have hround : roundReservoir r
        (G.rawProfile β ((R0 v).law.outcome k)).reservoir ≤
        (G.rawProfile β ((R0 v).law.outcome k)).reservoir :=
      roundReservoir_le hr hR
    have hraw := G.rawProfile_reservoir_le_one
      (β := β) (S := (R0 v).law.outcome k)
    simp only [extendedProfileReservoirSize]
    rw [← G.roundReservoir_eq_profileReservoir_of_code R0 v k P.1 hcode]
    exact hround.trans hraw
  · simp only [extendedProfileReservoirSize]
    split <;> norm_num


/-- Aggregated reservoir mass factors into profile probability times the
concrete reservoir size recorded by the profile. -/
theorem roundedProfileReservoirMass_eq_mul_size
    (v : G.V)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr}) :
    G.roundedProfileReservoirMass (R0 v).law hβ hr P.1 =
      G.roundedProfileMass (R0 v).law hβ hr P.1 * (r * P.1.2.val) := by
  classical
  unfold roundedProfileReservoirMass roundedProfileMass fiberMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hcode : G.roundedProfileCode (R0 v).law hβ hr k = P.1 :=
    (Finset.mem_filter.mp hk).2
  change (R0 v).law.probability k *
      roundReservoir r (G.rawProfile β ((R0 v).law.outcome k)).reservoir =
    (R0 v).law.probability k * (r * (P.1.2.val : ℝ))
  rw [G.roundReservoir_eq_profileReservoir_of_code R0 v k P.1 hcode]

/-- Tiny transport carried by one extended state. -/
def extendedProfileTinyAssign (v : G.V) (e : G.StarEdge v)
    (z : G.ExtendedProfileState R0 v) : ℝ :=
  match z with
  | Sum.inl P => (R0 v).tinyAssign e (some P)
  | Sum.inr k => if k.1 = 1 then (R0 v).tinyAssign e none else 0

theorem extendedProfileTinyAssign_nonneg (v : G.V) (e : G.StarEdge v)
    (z : G.ExtendedProfileState R0 v) :
    0 ≤ G.extendedProfileTinyAssign R0 v e z := by
  rcases z with P | k
  · exact (R0 v).tinyAssign_nonneg e (some P)
  · simp only [extendedProfileTinyAssign]
    split
    · exact (R0 v).tinyAssign_nonneg e none
    · exact le_rfl

/-- Each state's assigned tiny weight fits inside its probability-scaled
reservoir. -/
theorem sum_weight_mul_extendedProfileTinyAssign_le
    (v : G.V) (z : G.ExtendedProfileState R0 v) :
    (∑ e : G.StarEdge v,
      G.weight e.1 * G.extendedProfileTinyAssign R0 v e z) ≤
      G.extendedProfileProbability R0 v z *
        G.extendedProfileReservoirSize R0 v z := by
  rcases z with P | k
  · have hcap := (R0 v).tinyAssign_capacity (some P)
    change (∑ e : G.StarEdge v,
      G.weight e.1 * (R0 v).tinyAssign e (some P)) ≤
        s * G.roundedProfileReservoirMass (R0 v).law hβ hr P.1 at hcap
    rw [G.roundedProfileReservoirMass_eq_mul_size R0 v P] at hcap
    simpa [extendedProfileTinyAssign, extendedProfileProbability,
      extendedProfileReservoirSize, mul_assoc] using hcap
  · by_cases hk1 : k.1 = 1
    · simp only [extendedProfileTinyAssign, extendedProfileProbability,
        extendedProfileReservoirSize, hk1, if_true]
      simp only [if_false, mul_one, one_ne_zero]
      simpa only [explicitTinyProfileCapacity] using
        (R0 v).tinyAssign_capacity none
    · simp only [extendedProfileTinyAssign, extendedProfileReservoirSize,
        hk1, if_false, mul_zero, Finset.sum_const_zero]
      exact le_rfl

/-- The tiny edge--color marginal common to both endpoints. -/
def extendedProfileTinyEdgeColorMass (e : G.E) : ℝ :=
  if G.weight e < β then s * ((1 : ℝ) / n) else 0

theorem extendedProfileTinyEdgeColorMass_nonneg (hs : 0 ≤ s) (hn : 0 < n)
    (e : G.E) :
    0 ≤ G.extendedProfileTinyEdgeColorMass
      (s := s) (β := β) (n := n) e := by
  unfold extendedProfileTinyEdgeColorMass
  split
  · exact mul_nonneg hs (by positivity)
  · exact le_rfl

/-- Summing all extended states recovers the full tiny transport, including
the repair reservoir. -/
theorem sum_extendedProfileTinyAssign (v : G.V) (e : G.StarEdge v) :
    (∑ z : G.ExtendedProfileState R0 v,
      G.extendedProfileTinyAssign R0 v e z) =
      if G.weight e.1 < β then s * ((1 : ℝ) / n) else 0 := by
  classical
  rw [Fintype.sum_sum_type]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  simp only [extendedProfileTinyAssign, Fin.val_zero, zero_ne_one, if_false,
    Fin.val_succ, Nat.reduceAdd, if_true]
  have hmarginal := (R0 v).tinyAssign_marginal e
  rw [Fintype.sum_option] at hmarginal
  rw [add_comm]
  simpa [tinyOccurrenceDemand] using hmarginal

theorem sum_extendedProfileTinyAssign_fst (e : G.E) :
    (∑ z : G.ExtendedProfileState R0 (G.fst e),
      G.extendedProfileTinyAssign R0 (G.fst e) (G.fstStarEdge e) z) =
      G.extendedProfileTinyEdgeColorMass
        (s := s) (β := β) (n := n) e := by
  exact G.sum_extendedProfileTinyAssign R0 _ _

theorem sum_extendedProfileTinyAssign_snd (e : G.E) :
    (∑ z : G.ExtendedProfileState R0 (G.snd e),
      G.extendedProfileTinyAssign R0 (G.snd e) (G.sndStarEdge e) z) =
      G.extendedProfileTinyEdgeColorMass
        (s := s) (β := β) (n := n) e := by
  exact G.sum_extendedProfileTinyAssign R0 _ _

/-- Positive tiny transport is supported on an edge below the tiny threshold
and on a state with a positive reservoir. -/
theorem extendedProfileTinyAssign_pos_fit
    (v : G.V) (e : G.StarEdge v)
    (z : G.ExtendedProfileState R0 v)
    (hpos : 0 < G.extendedProfileTinyAssign R0 v e z) :
    G.weight e.1 < β ∧ 0 < G.extendedProfileReservoirSize R0 v z := by
  have htiny : G.weight e.1 < β := by
    by_contra hnot
    have hmarg : (∑ z' : G.ExtendedProfileState R0 v,
        G.extendedProfileTinyAssign R0 v e z') = 0 := by
      rw [G.sum_extendedProfileTinyAssign R0 v e]
      simp [hnot]
    have hsingle : G.extendedProfileTinyAssign R0 v e z ≤
        ∑ z' : G.ExtendedProfileState R0 v,
          G.extendedProfileTinyAssign R0 v e z' :=
      Finset.single_le_sum
        (fun z' _ ↦ G.extendedProfileTinyAssign_nonneg R0 v e z')
        (Finset.mem_univ z)
    rw [hmarg] at hsingle
    linarith
  refine ⟨htiny, ?_⟩
  have hcap := G.sum_weight_mul_extendedProfileTinyAssign_le R0 v z
  have hsingle : G.weight e.1 * G.extendedProfileTinyAssign R0 v e z ≤
      ∑ f : G.StarEdge v,
        G.weight f.1 * G.extendedProfileTinyAssign R0 v f z :=
    Finset.single_le_sum
      (fun f _ ↦ mul_nonneg (G.weight_nonneg f.1)
        (G.extendedProfileTinyAssign_nonneg R0 v f z))
      (Finset.mem_univ e)
  have hweighted : 0 < G.weight e.1 *
      G.extendedProfileTinyAssign R0 v e z :=
    mul_pos (G.weight_pos e.1) hpos
  have hprod : 0 < G.extendedProfileProbability R0 v z *
      G.extendedProfileReservoirSize R0 v z :=
    lt_of_lt_of_le hweighted (hsingle.trans hcap)
  rcases mul_pos_iff.mp hprod with h | h
  · exact h.2
  · exact (not_lt_of_ge
      (G.extendedProfileReservoirSize_nonneg R0 v z) h.2).elim

/-- Equation (23) for the two tiny-reservoir assignments. -/
def extendedProfileTinyProductOptionMass (rho omega : ℝ) (e : G.E)
    (P : G.ExtendedProfileState R0 (G.fst e))
    (Q : G.ExtendedProfileState R0 (G.snd e)) : ℝ :=
  pairedOption rho
    (G.extendedProfileTinyEdgeColorMass (s := s) (β := β) (n := n) e)
    (G.smoothedExtendedProfileProbability R0 omega (G.fst e))
    (G.smoothedExtendedProfileProbability R0 omega (G.snd e))
    (fun P (_ : Unit) ↦
      G.extendedProfileTinyAssign R0 (G.fst e) (G.fstStarEdge e) P)
    (fun Q (_ : Unit) ↦
      G.extendedProfileTinyAssign R0 (G.snd e) (G.sndStarEdge e) Q)
    P Q () ()

theorem extendedProfileTinyProductOptionMass_nonneg
    (hs : 0 ≤ s) (hn : 0 < n)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (e : G.E)
    (P : G.ExtendedProfileState R0 (G.fst e))
    (Q : G.ExtendedProfileState R0 (G.snd e)) :
    0 ≤ G.extendedProfileTinyProductOptionMass R0 rho omega e P Q := by
  unfold extendedProfileTinyProductOptionMass pairedOption
  split
  · exact le_rfl
  · apply div_nonneg
    · exact mul_nonneg
        (mul_nonneg hrho
          (G.extendedProfileTinyAssign_nonneg R0 _ _ P))
        (G.extendedProfileTinyAssign_nonneg R0 _ _ Q)
    · exact mul_nonneg
        (mul_nonneg
          (G.extendedProfileTinyEdgeColorMass_nonneg hs hn e)
          (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
            homega0 homega1 _ P).le)
        (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
          homega0 homega1 _ Q).le

/-- Positive coupled tiny mass is supported by fitting reservoirs at both
endpoints. -/
theorem extendedProfileTinyProductOptionMass_pos_fit
    (hs : 0 ≤ s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (hy : 0 < G.extendedProfileTinyEdgeColorMass
      (s := s) (β := β) (n := n) e)
    (P : G.ExtendedProfileState R0 (G.fst e))
    (Q : G.ExtendedProfileState R0 (G.snd e))
    (hpos : 0 < G.extendedProfileTinyProductOptionMass
      R0 rho omega e P Q) :
    (G.weight e < β ∧
      0 < G.extendedProfileReservoirSize R0 (G.fst e) P) ∧
    (G.weight e < β ∧
      0 < G.extendedProfileReservoirSize R0 (G.snd e) Q) := by
  have hlamP := G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
    homega0 homega1 (G.fst e) P
  have hlamQ := G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
    homega0 homega1 (G.snd e) Q
  have ha0 := G.extendedProfileTinyAssign_nonneg R0
    (G.fst e) (G.fstStarEdge e) P
  have hb0 := G.extendedProfileTinyAssign_nonneg R0
    (G.snd e) (G.sndStarEdge e) Q
  unfold extendedProfileTinyProductOptionMass pairedOption at hpos
  simp only [hy.ne', if_false] at hpos
  have hden : 0 <
      G.extendedProfileTinyEdgeColorMass (s := s) (β := β) (n := n) e *
        G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
        G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q :=
    mul_pos (mul_pos hy hlamP) hlamQ
  have hnum : 0 < rho *
      G.extendedProfileTinyAssign R0 (G.fst e) (G.fstStarEdge e) P *
      G.extendedProfileTinyAssign R0 (G.snd e) (G.sndStarEdge e) Q := by
    rcases div_pos_iff.mp hpos with h | h
    · exact h.1
    · exact (not_lt_of_ge hden.le h.2).elim
  have hb : 0 < G.extendedProfileTinyAssign R0
      (G.snd e) (G.sndStarEdge e) Q := by
    rcases mul_pos_iff.mp hnum with h | h
    · exact h.2
    · exact (not_lt_of_ge hb0 h.2).elim
  have hra : 0 < rho * G.extendedProfileTinyAssign R0
      (G.fst e) (G.fstStarEdge e) P := by
    rcases mul_pos_iff.mp hnum with h | h
    · exact h.1
    · exact (not_lt_of_ge hb0 h.2).elim
  have ha : 0 < G.extendedProfileTinyAssign R0
      (G.fst e) (G.fstStarEdge e) P := by
    rcases mul_pos_iff.mp hra with h | h
    · exact h.2
    · exact (not_lt_of_ge hrho h.1).elim
  exact ⟨G.extendedProfileTinyAssign_pos_fit R0 _ _ P ha,
    G.extendedProfileTinyAssign_pos_fit R0 _ _ Q hb⟩

/-- Exact expected use of a fixed left reservoir after averaging the right
endpoint state. -/
theorem extendedProfileTinyProductOptionMass_right_expectation
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hy : G.extendedProfileTinyEdgeColorMass
      (s := s) (β := β) (n := n) e ≠ 0)
    (P : G.ExtendedProfileState R0 (G.fst e)) :
    (∑ Q : G.ExtendedProfileState R0 (G.snd e),
      G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
        G.extendedProfileTinyProductOptionMass R0 rho omega e P Q) =
      rho * G.extendedProfileTinyAssign R0 (G.fst e)
        (G.fstStarEdge e) P /
        G.smoothedExtendedProfileProbability R0 omega (G.fst e) P := by
  have h := sum_pairedOption_right rho
    (G.extendedProfileTinyEdgeColorMass (s := s) (β := β) (n := n) e)
    (G.smoothedExtendedProfileProbability R0 omega (G.fst e))
    (G.smoothedExtendedProfileProbability R0 omega (G.snd e))
    (fun P (_ : Unit) ↦
      G.extendedProfileTinyAssign R0 (G.fst e) (G.fstStarEdge e) P)
    (fun Q (_ : Unit) ↦
      G.extendedProfileTinyAssign R0 (G.snd e) (G.sndStarEdge e) Q)
    P () hy
    (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
      homega0 homega1 _ P).ne'
    (fun Q ↦ (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
      homega0 homega1 _ Q).ne')
    (by simpa using G.sum_extendedProfileTinyAssign_snd R0 e)
  simpa [extendedProfileTinyProductOptionMass] using h

/-- Averaging over both independently sampled endpoint states gives exactly
`rho` times the common tiny edge--color marginal. -/
theorem extendedProfileTinyProductOptionMass_expectation
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hy : G.extendedProfileTinyEdgeColorMass
      (s := s) (β := β) (n := n) e ≠ 0) :
    (∑ P : G.ExtendedProfileState R0 (G.fst e),
      G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
        ∑ Q : G.ExtendedProfileState R0 (G.snd e),
          G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
            G.extendedProfileTinyProductOptionMass R0 rho omega e P Q) =
      rho * G.extendedProfileTinyEdgeColorMass
        (s := s) (β := β) (n := n) e := by
  have h := sum_pairedOption rho
    (G.extendedProfileTinyEdgeColorMass (s := s) (β := β) (n := n) e)
    (G.smoothedExtendedProfileProbability R0 omega (G.fst e))
    (G.smoothedExtendedProfileProbability R0 omega (G.snd e))
    (fun P (_ : Unit) ↦
      G.extendedProfileTinyAssign R0 (G.fst e) (G.fstStarEdge e) P)
    (fun Q (_ : Unit) ↦
      G.extendedProfileTinyAssign R0 (G.snd e) (G.sndStarEdge e) Q)
    hy
    (fun P ↦ (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
      homega0 homega1 _ P).ne')
    (fun Q ↦ (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
      homega0 homega1 _ Q).ne')
    (by simpa using G.sum_extendedProfileTinyAssign_fst R0 e)
    (by simpa using G.sum_extendedProfileTinyAssign_snd R0 e)
  simpa [extendedProfileTinyProductOptionMass] using h

end WeightedMultigraph

end

end WeightedEdgeColoring
