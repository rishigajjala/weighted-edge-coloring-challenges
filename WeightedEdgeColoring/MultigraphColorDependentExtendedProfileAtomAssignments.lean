import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileWordPadding
import WeightedEdgeColoring.MultigraphSelectedProfileTinyGlobal

/-!
# Large-slot and tiny-reservoir atoms for color-dependent realizations

This ports the local extended-profile assignments from the uniform `1/n`
realization to an arbitrary proposal realization `R v c`.  The identities
are pointwise in the color.  In particular, summing the extended states
recovers exactly `s * proposal e c` on the appropriate large/tiny side of
the threshold.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})
variable {Color : Type w} [Fintype Color] [DecidableEq Color]
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}

private theorem natFloor_cast_eq_intFloor_cast_colorDependent
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

section AssignmentAtoms

variable {proposal : G.E → Color → ℝ}
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

theorem roundReservoir_eq_colorDependentProfileReservoir_of_code
    (v : G.V) (c : Color) (k : Fin (R v c).law.m)
    (P : G.RoundedProfileCode (R v c).law)
    (hcode : G.roundedProfileCode (R v c).law hβ hr k = P) :
    roundReservoir r
        (G.rawProfile β ((R v c).law.outcome k)).reservoir =
      r * P.2.val := by
  have hR : 0 ≤ (G.rawProfile β ((R v c).law.outcome k)).reservoir :=
    G.rawProfile_reservoir_nonneg ((R v c).law.feasible k)
  have hcast := natFloor_cast_eq_intFloor_cast_colorDependent
    ((G.rawProfile β ((R v c).law.outcome k)).reservoir / r)
    (div_nonneg hR hr.le)
  unfold roundReservoir
  rw [← hcast]
  have hsecond :
      (G.roundedProfileCode (R v c).law hβ hr k).2 = P.2 :=
    congrArg Prod.snd hcode
  change r * (⌊(G.rawProfile β ((R v c).law.outcome k)).reservoir / r⌋₊ : ℕ) =
    r * (P.2.val : ℕ)
  rw [show ⌊(G.rawProfile β ((R v c).law.outcome k)).reservoir / r⌋₊ =
      P.2.val by
    simpa [roundedProfileCode] using congrArg Fin.val hsecond]

/-- Padded large assignment belonging to one actual rounded profile. -/
def colorDependentActualProfilePaddedAssign
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R v c).law hβ hr})
    (i : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  ∑ j : G.RoundedProfileOrdinarySlot (R v c).law P.1,
    if G.paddedLargeSlotCode (R v c) (some ⟨P, j⟩) = i then
      (R v c).largeAssign e (some ⟨P, j⟩) else 0

theorem colorDependentActualProfilePaddedAssign_nonneg
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R v c).law hβ hr})
    (i : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.colorDependentActualProfilePaddedAssign R v c e P i := by
  exact Finset.sum_nonneg fun j _ ↦ by
    split
    · exact (R v c).largeAssign_nonneg e (some ⟨P, j⟩)
    · exact le_rfl

theorem sum_colorDependentActualProfilePaddedAssign
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (P : {P // P ∈ G.roundedProfileMenu (R v c).law hβ hr}) :
    (∑ i, G.colorDependentActualProfilePaddedAssign R v c e P i) =
      ∑ j : G.RoundedProfileOrdinarySlot (R v c).law P.1,
        (R v c).largeAssign e (some ⟨P, j⟩) := by
  classical
  unfold colorDependentActualProfilePaddedAssign
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  simp

theorem sum_colorDependentActualProfilePaddedAssign_star_le
    (hs : 0 ≤ s) (v : G.V) (c : Color)
    (P : {P // P ∈ G.roundedProfileMenu (R v c).law hβ hr})
    (i : Fin (explicitLargeSlotBound β q r)) :
    (∑ e : G.StarEdge v,
      G.colorDependentActualProfilePaddedAssign R v c e P i) ≤
      s * G.roundedProfileMass (R v c).law hβ hr P.1 := by
  classical
  let code : G.RoundedProfileOrdinarySlot (R v c).law P.1 →
      Fin (explicitLargeSlotBound β q r) := fun j ↦
    G.paddedLargeSlotCode (R v c) (some ⟨P, j⟩)
  by_cases hex : ∃ j, code j = i
  · rcases hex with ⟨j0, hj0⟩
    have hinj : Function.Injective code := by
      intro j k hjk
      have h := G.paddedLargeSlotCode_injective (R v c) hjk
      exact eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2
    calc
      (∑ e : G.StarEdge v,
        G.colorDependentActualProfilePaddedAssign R v c e P i) =
          ∑ e : G.StarEdge v, (R v c).largeAssign e (some ⟨P, j0⟩) := by
        apply Finset.sum_congr rfl
        intro e _he
        unfold colorDependentActualProfilePaddedAssign
        rw [Finset.sum_eq_single j0]
        · simp [code, hj0]
        · intro j _hj hne
          have hcode : code j ≠ i := fun hj ↦
            hne (hinj (hj.trans hj0.symm))
          simp [code, hcode]
        · simp
      _ ≤ G.explicitLargeSlotCapacity (R v c).law hβ hr
          (some ⟨P, j0⟩) := (R v c).largeAssign_capacity (some ⟨P, j0⟩)
      _ = s * G.roundedProfileMass (R v c).law hβ hr P.1 := rfl
  · have hzero : ∀ e : G.StarEdge v,
        G.colorDependentActualProfilePaddedAssign R v c e P i = 0 := by
      intro e
      unfold colorDependentActualProfilePaddedAssign
      apply Finset.sum_eq_zero
      intro j _hj
      have hcode : code j ≠ i := fun h ↦ hex ⟨j, h⟩
      simp [code, hcode]
    calc
      (∑ e : G.StarEdge v,
        G.colorDependentActualProfilePaddedAssign R v c e P i) = 0 := by
          simp [hzero]
      _ ≤ s * G.roundedProfileMass (R v c).law hβ hr P.1 :=
        mul_nonneg hs
          (G.roundedProfileMass_nonneg (R v c).law hβ hr P.1)

/-- Large assignment carried by a color-dependent extended state. -/
def colorDependentExtendedProfileLargeAssign
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (z : G.ColorDependentExtendedProfileState R v c)
    (i : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  match z with
  | Sum.inl P =>
      G.colorDependentActualProfilePaddedAssign R v c e P i
  | Sum.inr k =>
      if k.1 = 0 then
        if G.paddedLargeSlotCode (R v c) none = i then
          (R v c).largeAssign e none else 0
      else 0

theorem colorDependentExtendedProfileLargeAssign_nonneg
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (z : G.ColorDependentExtendedProfileState R v c)
    (i : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.colorDependentExtendedProfileLargeAssign R v c e z i := by
  rcases z with P | k
  · exact G.colorDependentActualProfilePaddedAssign_nonneg R v c e P i
  · simp only [colorDependentExtendedProfileLargeAssign]
    by_cases hk : k.1 = 0
    · simp only [hk, if_true]
      split
      · exact (R v c).largeAssign_nonneg e none
      · exact le_rfl
    · simp [hk]

theorem sum_colorDependentExtendedProfileLargeAssign_star_le
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c)
    (i : Fin (explicitLargeSlotBound β q r)) :
    (∑ e : G.StarEdge v,
      G.colorDependentExtendedProfileLargeAssign R v c e z i) ≤
      G.colorDependentExtendedProfileProbability R v c z := by
  rcases z with P | k
  · exact G.sum_colorDependentActualProfilePaddedAssign_star_le
      R hs v c P i
  · by_cases hk0 : k.1 = 0
    · by_cases hcode : G.paddedLargeSlotCode (R v c) none = i
      · simp only [colorDependentExtendedProfileLargeAssign,
          colorDependentExtendedProfileProbability, hk0, hcode, if_true]
        simpa only [explicitLargeSlotCapacity] using
          (R v c).largeAssign_capacity none
      · simp only [colorDependentExtendedProfileLargeAssign,
          colorDependentExtendedProfileProbability, hk0, hcode, if_true,
          if_false, Finset.sum_const_zero]
        exact mul_nonneg hs hq
    · have hprob :=
        G.colorDependentExtendedProfileProbability_nonneg R
          hs hq hr0 hleft v c (Sum.inr k)
      simpa [colorDependentExtendedProfileLargeAssign, hk0] using hprob

end AssignmentAtoms

section LargeMarginal

variable (proposal : G.E → Color → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- Exact large marginal at one edge and color. -/
theorem sum_colorDependentExtendedProfileLargeAssign
    (v : G.V) (c : Color) (e : G.StarEdge v) :
    (∑ z : G.ColorDependentExtendedProfileState R v c,
      ∑ i, G.colorDependentExtendedProfileLargeAssign R v c e z i) =
      if β ≤ G.weight e.1 then s * proposal e.1 c else 0 := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [colorDependentExtendedProfileLargeAssign]
  simp_rw [G.sum_colorDependentActualProfilePaddedAssign R v c e]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  simp only [Fin.val_zero, if_pos, Fin.val_succ, Nat.succ_ne_zero,
    if_false, Finset.sum_const_zero, add_zero]
  have hrepair :
      (∑ i : Fin (explicitLargeSlotBound β q r),
        if G.paddedLargeSlotCode (R v c) none = i then
          (R v c).largeAssign e none else 0) =
        (R v c).largeAssign e none := by simp
  rw [hrepair]
  have hmarginal := (R v c).largeAssign_marginal e
  rw [Fintype.sum_option, Fintype.sum_sigma] at hmarginal
  rw [add_comm]
  exact hmarginal

end LargeMarginal

section ReservoirAndTinyAtoms

variable {proposal : G.E → Color → ℝ}
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- Reservoir size carried by one color-dependent extended state. -/
def colorDependentExtendedProfileReservoirSize
    (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c) : ℝ :=
  match z with
  | Sum.inl P => r * P.1.2.val
  | Sum.inr k => if k.1 = 1 then 1 else 0

theorem colorDependentExtendedProfileReservoirSize_nonneg
    (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c) :
    0 ≤ G.colorDependentExtendedProfileReservoirSize R v c z := by
  rcases z with P | k
  · exact mul_nonneg hr.le (Nat.cast_nonneg _)
  · simp only [colorDependentExtendedProfileReservoirSize]
    split <;> norm_num

theorem colorDependentExtendedProfileReservoirSize_le_one
    (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c) :
    G.colorDependentExtendedProfileReservoirSize R v c z ≤ 1 := by
  rcases z with P | k
  · have hP := P.2
    change P.1 ∈ (Finset.univ.image
      (G.roundedProfileCode (R v c).law hβ hr)) at hP
    rw [Finset.mem_image] at hP
    rcases hP with ⟨k, _hk, hcode⟩
    have hR : 0 ≤ (G.rawProfile β ((R v c).law.outcome k)).reservoir :=
      G.rawProfile_reservoir_nonneg ((R v c).law.feasible k)
    have hround : roundReservoir r
        (G.rawProfile β ((R v c).law.outcome k)).reservoir ≤
        (G.rawProfile β ((R v c).law.outcome k)).reservoir :=
      roundReservoir_le hr hR
    have hraw := G.rawProfile_reservoir_le_one
      (β := β) (S := (R v c).law.outcome k)
    simp only [colorDependentExtendedProfileReservoirSize]
    rw [← G.roundReservoir_eq_colorDependentProfileReservoir_of_code
      R v c k P.1 hcode]
    exact hround.trans hraw
  · simp only [colorDependentExtendedProfileReservoirSize]
    split <;> norm_num

theorem roundedProfileReservoirMass_eq_mul_size_colorDependent
    (v : G.V) (c : Color)
    (P : {P // P ∈ G.roundedProfileMenu (R v c).law hβ hr}) :
    G.roundedProfileReservoirMass (R v c).law hβ hr P.1 =
      G.roundedProfileMass (R v c).law hβ hr P.1 * (r * P.1.2.val) := by
  classical
  unfold roundedProfileReservoirMass roundedProfileMass fiberMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hcode : G.roundedProfileCode (R v c).law hβ hr k = P.1 :=
    (Finset.mem_filter.mp hk).2
  change (R v c).law.probability k *
      roundReservoir r (G.rawProfile β ((R v c).law.outcome k)).reservoir =
    (R v c).law.probability k * (r * (P.1.2.val : ℝ))
  rw [G.roundReservoir_eq_colorDependentProfileReservoir_of_code
    R v c k P.1 hcode]

/-- Tiny assignment carried by one color-dependent extended state. -/
def colorDependentExtendedProfileTinyAssign
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (z : G.ColorDependentExtendedProfileState R v c) : ℝ :=
  match z with
  | Sum.inl P => (R v c).tinyAssign e (some P)
  | Sum.inr k => if k.1 = 1 then (R v c).tinyAssign e none else 0

theorem colorDependentExtendedProfileTinyAssign_nonneg
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (z : G.ColorDependentExtendedProfileState R v c) :
    0 ≤ G.colorDependentExtendedProfileTinyAssign R v c e z := by
  rcases z with P | k
  · exact (R v c).tinyAssign_nonneg e (some P)
  · simp only [colorDependentExtendedProfileTinyAssign]
    split
    · exact (R v c).tinyAssign_nonneg e none
    · exact le_rfl

theorem roundedProfileReservoirMass_le_profileMass_colorDependent
    (v : G.V) (c : Color)
    (P : G.RoundedProfileCode (R v c).law) :
    G.roundedProfileReservoirMass (R v c).law hβ hr P ≤
      G.roundedProfileMass (R v c).law hβ hr P := by
  classical
  unfold roundedProfileReservoirMass roundedProfileMass fiberMass
  apply Finset.sum_le_sum
  intro k hk
  have hraw0 : 0 ≤
      (G.rawProfile β ((R v c).law.outcome k)).reservoir :=
    G.rawProfile_reservoir_nonneg ((R v c).law.feasible k)
  have hround : roundReservoir r
      (G.rawProfile β ((R v c).law.outcome k)).reservoir ≤ 1 :=
    (roundReservoir_le hr hraw0).trans
      (G.rawProfile_reservoir_le_one
        (β := β) (S := (R v c).law.outcome k))
  have hp0 := (R v c).law.probability_nonneg k
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hround hp0

/-- Every tiny reservoir row at one vertex and color is bounded by the
probability of its extended state. -/
theorem sum_weight_mul_colorDependentExtendedProfileTinyAssign_le
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c) :
    (∑ e : G.StarEdge v,
      G.weight e.1 *
        G.colorDependentExtendedProfileTinyAssign R v c e z) ≤
      G.colorDependentExtendedProfileProbability R v c z := by
  rcases z with P | k
  · have hcap := (R v c).tinyAssign_capacity (some P)
    have hcap' :
        (∑ e : G.StarEdge v,
          G.weight e.1 * (R v c).tinyAssign e (some P)) ≤
            s * G.roundedProfileReservoirMass
              (R v c).law hβ hr P.1 := by
      simpa only [explicitTinyProfileCapacity] using hcap
    calc
      (∑ e : G.StarEdge v,
        G.weight e.1 *
          G.colorDependentExtendedProfileTinyAssign R v c e (Sum.inl P)) ≤
        s * G.roundedProfileReservoirMass
          (R v c).law hβ hr P.1 := by
            simpa [colorDependentExtendedProfileTinyAssign] using hcap'
      _ ≤ s * G.roundedProfileMass (R v c).law hβ hr P.1 :=
        mul_le_mul_of_nonneg_left
          (G.roundedProfileReservoirMass_le_profileMass_colorDependent
            R v c P.1) hs
      _ = G.colorDependentExtendedProfileProbability
          R v c (Sum.inl P) := rfl
  · by_cases hk1 : k.1 = 1
    · simp only [colorDependentExtendedProfileTinyAssign,
        colorDependentExtendedProfileProbability, hk1, if_true]
      simp only [if_false, one_ne_zero]
      simpa only [explicitTinyProfileCapacity] using
        (R v c).tinyAssign_capacity none
    · simp only [colorDependentExtendedProfileTinyAssign, hk1, if_false,
        mul_zero, Finset.sum_const_zero]
      exact G.colorDependentExtendedProfileProbability_nonneg R
        hs hq hr0 hleft v c (Sum.inr k)

/-- Sharp reservoir-sensitive local capacity.  Unlike the coarse bound
above, this vanishes when the selected extended state has no reservoir. -/
theorem sum_weight_mul_colorDependentExtendedProfileTinyAssign_le_probability_mul_reservoir
    (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c) :
    (∑ e : G.StarEdge v,
      G.weight e.1 *
        G.colorDependentExtendedProfileTinyAssign R v c e z) ≤
      G.colorDependentExtendedProfileProbability R v c z *
        G.colorDependentExtendedProfileReservoirSize R v c z := by
  rcases z with P | k
  · have hcap := (R v c).tinyAssign_capacity (some P)
    change (∑ e : G.StarEdge v,
      G.weight e.1 * (R v c).tinyAssign e (some P)) ≤
        s * G.roundedProfileReservoirMass (R v c).law hβ hr P.1 at hcap
    rw [G.roundedProfileReservoirMass_eq_mul_size_colorDependent R v c P]
      at hcap
    simpa [colorDependentExtendedProfileTinyAssign,
      colorDependentExtendedProfileProbability,
      colorDependentExtendedProfileReservoirSize, mul_assoc] using hcap
  · by_cases hk1 : k.1 = 1
    · simp only [colorDependentExtendedProfileTinyAssign,
        colorDependentExtendedProfileProbability,
        colorDependentExtendedProfileReservoirSize, hk1, if_true]
      simp only [if_false, mul_one, one_ne_zero]
      simpa only [explicitTinyProfileCapacity] using
        (R v c).tinyAssign_capacity none
    · simp only [colorDependentExtendedProfileTinyAssign,
        colorDependentExtendedProfileReservoirSize, hk1, if_false,
        mul_zero, Finset.sum_const_zero]
      exact le_rfl

end ReservoirAndTinyAtoms

section EdgeAndProductMasses

variable (proposal : G.E → Color → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- Exact tiny marginal at one edge and color. -/
theorem sum_colorDependentExtendedProfileTinyAssign
    (v : G.V) (c : Color) (e : G.StarEdge v) :
    (∑ z : G.ColorDependentExtendedProfileState R v c,
      G.colorDependentExtendedProfileTinyAssign R v c e z) =
      if G.weight e.1 < β then s * proposal e.1 c else 0 := by
  classical
  rw [Fintype.sum_sum_type]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  simp only [colorDependentExtendedProfileTinyAssign, Fin.val_zero,
    zero_ne_one, if_false, Fin.val_succ, Nat.reduceAdd, if_true]
  have hmarginal := (R v c).tinyAssign_marginal e
  rw [Fintype.sum_option] at hmarginal
  rw [add_comm]
  simpa [tinyOccurrenceDemand] using hmarginal

/-- Common large and tiny edge--color masses at the two endpoints. -/
def colorDependentExtendedProfileLargeEdgeColorMass
    (e : G.E) (c : Color) : ℝ :=
  if β ≤ G.weight e then s * proposal e c else 0

def colorDependentExtendedProfileTinyEdgeColorMass
    (e : G.E) (c : Color) : ℝ :=
  if G.weight e < β then s * proposal e c else 0

include R

theorem colorDependentExtendedProfileLargeEdgeColorMass_nonneg
    (e : G.E) (c : Color) :
    0 ≤ G.colorDependentExtendedProfileLargeEdgeColorMass
      (s := s) (β := β) proposal e c := by
  calc
    0 ≤ ∑ z : G.ColorDependentExtendedProfileState R (G.fst e) c,
        ∑ i, G.colorDependentExtendedProfileLargeAssign
          R (G.fst e) c (G.fstStarEdge e) z i :=
      Finset.sum_nonneg fun z _hz ↦ Finset.sum_nonneg fun i _hi ↦
        G.colorDependentExtendedProfileLargeAssign_nonneg
          R (G.fst e) c (G.fstStarEdge e) z i
    _ = G.colorDependentExtendedProfileLargeEdgeColorMass
        (s := s) (β := β) proposal e c := by
      simpa [colorDependentExtendedProfileLargeEdgeColorMass] using
        G.sum_colorDependentExtendedProfileLargeAssign
          proposal R (G.fst e) c (G.fstStarEdge e)

theorem colorDependentExtendedProfileTinyEdgeColorMass_nonneg
    (e : G.E) (c : Color) :
    0 ≤ G.colorDependentExtendedProfileTinyEdgeColorMass
      (s := s) (β := β) proposal e c := by
  calc
    0 ≤ ∑ z : G.ColorDependentExtendedProfileState R (G.fst e) c,
        G.colorDependentExtendedProfileTinyAssign
          R (G.fst e) c (G.fstStarEdge e) z :=
      Finset.sum_nonneg fun z _hz ↦
        G.colorDependentExtendedProfileTinyAssign_nonneg
          R (G.fst e) c (G.fstStarEdge e) z
    _ = G.colorDependentExtendedProfileTinyEdgeColorMass
        (s := s) (β := β) proposal e c := by
      simpa [colorDependentExtendedProfileTinyEdgeColorMass] using
        G.sum_colorDependentExtendedProfileTinyAssign
          proposal R (G.fst e) c (G.fstStarEdge e)

theorem colorDependentExtendedProfileLargeAssign_le_edgeColorMass
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (z : G.ColorDependentExtendedProfileState R v c)
    (i : Fin (explicitLargeSlotBound β q r)) :
    G.colorDependentExtendedProfileLargeAssign R v c e z i ≤
      G.colorDependentExtendedProfileLargeEdgeColorMass
        (s := s) (β := β) proposal e.1 c := by
  calc
    G.colorDependentExtendedProfileLargeAssign R v c e z i ≤
        ∑ j, G.colorDependentExtendedProfileLargeAssign R v c e z j :=
      Finset.single_le_sum
        (fun j _hj ↦ G.colorDependentExtendedProfileLargeAssign_nonneg
          R v c e z j) (Finset.mem_univ i)
    _ ≤ ∑ z', ∑ j,
        G.colorDependentExtendedProfileLargeAssign R v c e z' j :=
      Finset.single_le_sum
        (fun z' _hz ↦ Finset.sum_nonneg fun j _hj ↦
          G.colorDependentExtendedProfileLargeAssign_nonneg
            R v c e z' j) (Finset.mem_univ z)
    _ = G.colorDependentExtendedProfileLargeEdgeColorMass
          (s := s) (β := β) proposal e.1 c := by
      simpa [colorDependentExtendedProfileLargeEdgeColorMass] using
        G.sum_colorDependentExtendedProfileLargeAssign proposal R v c e

theorem sum_colorDependentExtendedProfileLargeAssign_le_edgeColorMass
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (z : G.ColorDependentExtendedProfileState R v c) :
    (∑ i, G.colorDependentExtendedProfileLargeAssign R v c e z i) ≤
      G.colorDependentExtendedProfileLargeEdgeColorMass
        (s := s) (β := β) proposal e.1 c := by
  calc
    (∑ i, G.colorDependentExtendedProfileLargeAssign R v c e z i) ≤
        ∑ z', ∑ i,
          G.colorDependentExtendedProfileLargeAssign R v c e z' i :=
      Finset.single_le_sum
        (fun z' _hz ↦ Finset.sum_nonneg fun i _hi ↦
          G.colorDependentExtendedProfileLargeAssign_nonneg
            R v c e z' i) (Finset.mem_univ z)
    _ = G.colorDependentExtendedProfileLargeEdgeColorMass
          (s := s) (β := β) proposal e.1 c := by
      simpa [colorDependentExtendedProfileLargeEdgeColorMass] using
        G.sum_colorDependentExtendedProfileLargeAssign proposal R v c e

theorem colorDependentExtendedProfileTinyAssign_le_edgeColorMass
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (z : G.ColorDependentExtendedProfileState R v c) :
    G.colorDependentExtendedProfileTinyAssign R v c e z ≤
      G.colorDependentExtendedProfileTinyEdgeColorMass
        (s := s) (β := β) proposal e.1 c := by
  calc
    G.colorDependentExtendedProfileTinyAssign R v c e z ≤
        ∑ z', G.colorDependentExtendedProfileTinyAssign R v c e z' :=
      Finset.single_le_sum
        (fun z' _hz ↦ G.colorDependentExtendedProfileTinyAssign_nonneg
          R v c e z') (Finset.mem_univ z)
    _ = G.colorDependentExtendedProfileTinyEdgeColorMass
          (s := s) (β := β) proposal e.1 c := by
      simpa [colorDependentExtendedProfileTinyEdgeColorMass] using
        G.sum_colorDependentExtendedProfileTinyAssign proposal R v c e

/-- Equation-(23) coupling for one large edge--color and two endpoint
states. -/
def colorDependentExtendedProfileLargeProductMass
    (rho omega : ℝ) (e : G.E) (c : Color)
    (P : G.ColorDependentExtendedProfileState R (G.fst e) c)
    (Q : G.ColorDependentExtendedProfileState R (G.snd e) c)
    (i j : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  pairedOption rho
    (G.colorDependentExtendedProfileLargeEdgeColorMass
      (s := s) (β := β) proposal e c)
    (G.smoothedColorDependentExtendedProfileProbability R omega (G.fst e) c)
    (G.smoothedColorDependentExtendedProfileProbability R omega (G.snd e) c)
    (G.colorDependentExtendedProfileLargeAssign R
      (G.fst e) c (G.fstStarEdge e))
    (G.colorDependentExtendedProfileLargeAssign R
      (G.snd e) c (G.sndStarEdge e)) P Q i j

/-- Equation-(23) coupling for one tiny edge--color. -/
def colorDependentExtendedProfileTinyProductMass
    (rho omega : ℝ) (e : G.E) (c : Color)
    (P : G.ColorDependentExtendedProfileState R (G.fst e) c)
    (Q : G.ColorDependentExtendedProfileState R (G.snd e) c) : ℝ :=
  pairedOption rho
    (G.colorDependentExtendedProfileTinyEdgeColorMass
      (s := s) (β := β) proposal e c)
    (G.smoothedColorDependentExtendedProfileProbability R omega (G.fst e) c)
    (G.smoothedColorDependentExtendedProfileProbability R omega (G.snd e) c)
    (fun P (_ : Fin 1) ↦
      G.colorDependentExtendedProfileTinyAssign R
        (G.fst e) c (G.fstStarEdge e) P)
    (fun Q (_ : Fin 1) ↦
      G.colorDependentExtendedProfileTinyAssign R
        (G.snd e) c (G.sndStarEdge e) Q)
    P Q 0 0

theorem colorDependentExtendedProfileLargeProductMass_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (e : G.E) (c : Color)
    (P : G.ColorDependentExtendedProfileState R (G.fst e) c)
    (Q : G.ColorDependentExtendedProfileState R (G.snd e) c)
    (i j : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.colorDependentExtendedProfileLargeProductMass
      proposal R rho omega e c P Q i j := by
  unfold colorDependentExtendedProfileLargeProductMass pairedOption
  split
  · exact le_rfl
  · rename_i hy
    have hy0 := G.colorDependentExtendedProfileLargeEdgeColorMass_nonneg
      proposal R e c
    have hypos : 0 < G.colorDependentExtendedProfileLargeEdgeColorMass
        (s := s) (β := β) proposal e c :=
      lt_of_le_of_ne hy0 (Ne.symm hy)
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg hrho
          (G.colorDependentExtendedProfileLargeAssign_nonneg
            R (G.fst e) c (G.fstStarEdge e) P i))
        (G.colorDependentExtendedProfileLargeAssign_nonneg
          R (G.snd e) c (G.sndStarEdge e) Q j))
      (mul_nonneg
        (mul_nonneg hypos.le
          (G.smoothedColorDependentExtendedProfileProbability_pos R
            hs hq hr0 hleft homega0 homega1 (G.fst e) c P).le)
        (G.smoothedColorDependentExtendedProfileProbability_pos R
          hs hq hr0 hleft homega0 homega1 (G.snd e) c Q).le)

theorem colorDependentExtendedProfileTinyProductMass_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (e : G.E) (c : Color)
    (P : G.ColorDependentExtendedProfileState R (G.fst e) c)
    (Q : G.ColorDependentExtendedProfileState R (G.snd e) c) :
    0 ≤ G.colorDependentExtendedProfileTinyProductMass
      proposal R rho omega e c P Q := by
  unfold colorDependentExtendedProfileTinyProductMass pairedOption
  split
  · exact le_rfl
  · rename_i hy
    have hy0 := G.colorDependentExtendedProfileTinyEdgeColorMass_nonneg
      proposal R e c
    have hypos : 0 < G.colorDependentExtendedProfileTinyEdgeColorMass
        (s := s) (β := β) proposal e c :=
      lt_of_le_of_ne hy0 (Ne.symm hy)
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg hrho
          (G.colorDependentExtendedProfileTinyAssign_nonneg
            R (G.fst e) c (G.fstStarEdge e) P))
        (G.colorDependentExtendedProfileTinyAssign_nonneg
          R (G.snd e) c (G.sndStarEdge e) Q))
      (mul_nonneg
        (mul_nonneg hypos.le
          (G.smoothedColorDependentExtendedProfileProbability_pos R
            hs hq hr0 hleft homega0 homega1 (G.fst e) c P).le)
        (G.smoothedColorDependentExtendedProfileProbability_pos R
          hs hq hr0 hleft homega0 homega1 (G.snd e) c Q).le)

end EdgeAndProductMasses

section ReservoirPositivity

variable {proposal : G.E → Color → ℝ}
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- A positive tiny assignment forces a positive reservoir in that state. -/
theorem colorDependentExtendedProfileReservoirSize_pos_of_tinyAssign_pos
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (z : G.ColorDependentExtendedProfileState R v c)
    (hpos : 0 < G.colorDependentExtendedProfileTinyAssign R v c e z) :
    0 < G.colorDependentExtendedProfileReservoirSize R v c z := by
  have hcap :=
    G.sum_weight_mul_colorDependentExtendedProfileTinyAssign_le_probability_mul_reservoir
      R v c z
  have hsingle : G.weight e.1 *
        G.colorDependentExtendedProfileTinyAssign R v c e z ≤
      ∑ f : G.StarEdge v, G.weight f.1 *
        G.colorDependentExtendedProfileTinyAssign R v c f z :=
    Finset.single_le_sum
      (fun f _ ↦ mul_nonneg (G.weight_nonneg f.1)
        (G.colorDependentExtendedProfileTinyAssign_nonneg R v c f z))
      (Finset.mem_univ e)
  have hweighted : 0 < G.weight e.1 *
      G.colorDependentExtendedProfileTinyAssign R v c e z :=
    mul_pos (G.weight_pos e.1) hpos
  have hprod : 0 <
      G.colorDependentExtendedProfileProbability R v c z *
        G.colorDependentExtendedProfileReservoirSize R v c z :=
    lt_of_lt_of_le hweighted (hsingle.trans hcap)
  rcases mul_pos_iff.mp hprod with h | h
  · exact h.2
  · exact (not_lt_of_ge
      (G.colorDependentExtendedProfileReservoirSize_nonneg R v c z) h.2).elim

end ReservoirPositivity

section ProductConsequences

variable (proposal : G.E → Color → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- A positive coupled tiny option has a positive reservoir at both
endpoints. -/
theorem colorDependentExtendedProfileTinyProductMass_pos_reservoirs
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (e : G.E) (c : Color)
    (P : G.ColorDependentExtendedProfileState R (G.fst e) c)
    (Q : G.ColorDependentExtendedProfileState R (G.snd e) c)
    (hpos : 0 < G.colorDependentExtendedProfileTinyProductMass
      proposal R rho omega e c P Q) :
    0 < G.colorDependentExtendedProfileReservoirSize R (G.fst e) c P ∧
      0 < G.colorDependentExtendedProfileReservoirSize R (G.snd e) c Q := by
  let y := G.colorDependentExtendedProfileTinyEdgeColorMass
    (s := s) (β := β) proposal e c
  have hy0 := G.colorDependentExtendedProfileTinyEdgeColorMass_nonneg
    proposal R e c
  have hy : 0 < y := by
    by_contra hnot
    have hzero : y = 0 := le_antisymm (le_of_not_gt hnot) hy0
    unfold colorDependentExtendedProfileTinyProductMass pairedOption at hpos
    simp [y, hzero] at hpos
  have hlamP := G.smoothedColorDependentExtendedProfileProbability_pos R
    hs hq hr0 hleft homega0 homega1 (G.fst e) c P
  have hlamQ := G.smoothedColorDependentExtendedProfileProbability_pos R
    hs hq hr0 hleft homega0 homega1 (G.snd e) c Q
  have ha0 := G.colorDependentExtendedProfileTinyAssign_nonneg R
    (G.fst e) c (G.fstStarEdge e) P
  have hb0 := G.colorDependentExtendedProfileTinyAssign_nonneg R
    (G.snd e) c (G.sndStarEdge e) Q
  have hden : 0 < y *
      G.smoothedColorDependentExtendedProfileProbability
        R omega (G.fst e) c P *
      G.smoothedColorDependentExtendedProfileProbability
        R omega (G.snd e) c Q := mul_pos (mul_pos hy hlamP) hlamQ
  unfold colorDependentExtendedProfileTinyProductMass pairedOption at hpos
  change 0 < if y = 0 then 0 else
      (rho * G.colorDependentExtendedProfileTinyAssign
          R (G.fst e) c (G.fstStarEdge e) P *
        G.colorDependentExtendedProfileTinyAssign
          R (G.snd e) c (G.sndStarEdge e) Q) /
        (y * G.smoothedColorDependentExtendedProfileProbability
            R omega (G.fst e) c P *
          G.smoothedColorDependentExtendedProfileProbability
            R omega (G.snd e) c Q) at hpos
  rw [if_neg hy.ne'] at hpos
  have hnum : 0 < rho *
      G.colorDependentExtendedProfileTinyAssign
        R (G.fst e) c (G.fstStarEdge e) P *
      G.colorDependentExtendedProfileTinyAssign
        R (G.snd e) c (G.sndStarEdge e) Q := by
    rcases div_pos_iff.mp hpos with h | h
    · exact h.1
    · exact (not_lt_of_ge hden.le h.2).elim
  have hb : 0 < G.colorDependentExtendedProfileTinyAssign
      R (G.snd e) c (G.sndStarEdge e) Q := by
    rcases mul_pos_iff.mp hnum with h | h
    · exact h.2
    · exact (not_lt_of_ge hb0 h.2).elim
  have hra : 0 < rho * G.colorDependentExtendedProfileTinyAssign
      R (G.fst e) c (G.fstStarEdge e) P := by
    rcases mul_pos_iff.mp hnum with h | h
    · exact h.1
    · exact (not_lt_of_ge hb0 h.2).elim
  have ha : 0 < G.colorDependentExtendedProfileTinyAssign
      R (G.fst e) c (G.fstStarEdge e) P := by
    rcases mul_pos_iff.mp hra with h | h
    · exact h.2
    · exact (not_lt_of_ge hrho h.1).elim
  exact ⟨
    G.colorDependentExtendedProfileReservoirSize_pos_of_tinyAssign_pos
      R (G.fst e) c (G.fstStarEdge e) P ha,
    G.colorDependentExtendedProfileReservoirSize_pos_of_tinyAssign_pos
      R (G.snd e) c (G.sndStarEdge e) Q hb⟩

/-- Averaging the state at the second endpoint leaves the normalized first
endpoint large assignment. -/
theorem colorDependentLargeProductMass_right_expectation
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    {e : G.E} {c : Color}
    (hy : G.colorDependentExtendedProfileLargeEdgeColorMass
      (s := s) (β := β) proposal e c ≠ 0)
    (P : G.ColorDependentExtendedProfileState R (G.fst e) c)
    (i : Fin (explicitLargeSlotBound β q r)) :
    (∑ Q : G.ColorDependentExtendedProfileState R (G.snd e) c,
      G.smoothedColorDependentExtendedProfileProbability
          R omega (G.snd e) c Q * ∑ j,
        G.colorDependentExtendedProfileLargeProductMass
          proposal R rho omega e c P Q i j) =
      rho * G.colorDependentExtendedProfileLargeAssign
          R (G.fst e) c (G.fstStarEdge e) P i /
        G.smoothedColorDependentExtendedProfileProbability
          R omega (G.fst e) c P := by
  unfold colorDependentExtendedProfileLargeProductMass
  apply sum_pairedOption_right
  · exact hy
  · exact (G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 (G.fst e) c P).ne'
  · intro Q
    exact (G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 (G.snd e) c Q).ne'
  · simpa [colorDependentExtendedProfileLargeEdgeColorMass] using
      G.sum_colorDependentExtendedProfileLargeAssign
        proposal R (G.snd e) c (G.sndStarEdge e)

/-- Tiny analogue of the one-endpoint expectation identity. -/
theorem colorDependentTinyProductMass_right_expectation
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    {e : G.E} {c : Color}
    (hy : G.colorDependentExtendedProfileTinyEdgeColorMass
      (s := s) (β := β) proposal e c ≠ 0)
    (P : G.ColorDependentExtendedProfileState R (G.fst e) c) :
    (∑ Q : G.ColorDependentExtendedProfileState R (G.snd e) c,
      G.smoothedColorDependentExtendedProfileProbability
          R omega (G.snd e) c Q *
        G.colorDependentExtendedProfileTinyProductMass
          proposal R rho omega e c P Q) =
      rho * G.colorDependentExtendedProfileTinyAssign
          R (G.fst e) c (G.fstStarEdge e) P /
        G.smoothedColorDependentExtendedProfileProbability
          R omega (G.fst e) c P := by
  have h := sum_pairedOption_right
    rho
    (G.colorDependentExtendedProfileTinyEdgeColorMass
      (s := s) (β := β) proposal e c)
    (G.smoothedColorDependentExtendedProfileProbability R omega (G.fst e) c)
    (G.smoothedColorDependentExtendedProfileProbability R omega (G.snd e) c)
    (fun P (_ : Fin 1) ↦
      G.colorDependentExtendedProfileTinyAssign R
        (G.fst e) c (G.fstStarEdge e) P)
    (fun Q (_ : Fin 1) ↦
      G.colorDependentExtendedProfileTinyAssign R
        (G.snd e) c (G.sndStarEdge e) Q)
    P 0 hy
    (G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 (G.fst e) c P).ne'
    (fun Q ↦ (G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 (G.snd e) c Q).ne')
    (by
      simpa [colorDependentExtendedProfileTinyEdgeColorMass] using
        G.sum_colorDependentExtendedProfileTinyAssign
          proposal R (G.snd e) c (G.sndStarEdge e))
  simpa [colorDependentExtendedProfileTinyProductMass] using h

theorem colorDependentLargeProductMass_left_expectation
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    {e : G.E} {c : Color}
    (hy : G.colorDependentExtendedProfileLargeEdgeColorMass
      (s := s) (β := β) proposal e c ≠ 0)
    (Q : G.ColorDependentExtendedProfileState R (G.snd e) c)
    (j : Fin (explicitLargeSlotBound β q r)) :
    (∑ P : G.ColorDependentExtendedProfileState R (G.fst e) c,
      G.smoothedColorDependentExtendedProfileProbability
          R omega (G.fst e) c P * ∑ i,
        G.colorDependentExtendedProfileLargeProductMass
          proposal R rho omega e c P Q i j) =
      rho * G.colorDependentExtendedProfileLargeAssign
          R (G.snd e) c (G.sndStarEdge e) Q j /
        G.smoothedColorDependentExtendedProfileProbability
          R omega (G.snd e) c Q := by
  unfold colorDependentExtendedProfileLargeProductMass
  apply sum_pairedOption_left
  · exact hy
  · intro P
    exact (G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 (G.fst e) c P).ne'
  · exact (G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 (G.snd e) c Q).ne'
  · simpa [colorDependentExtendedProfileLargeEdgeColorMass] using
      G.sum_colorDependentExtendedProfileLargeAssign
        proposal R (G.fst e) c (G.fstStarEdge e)

theorem colorDependentTinyProductMass_left_expectation
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    {e : G.E} {c : Color}
    (hy : G.colorDependentExtendedProfileTinyEdgeColorMass
      (s := s) (β := β) proposal e c ≠ 0)
    (Q : G.ColorDependentExtendedProfileState R (G.snd e) c) :
    (∑ P : G.ColorDependentExtendedProfileState R (G.fst e) c,
      G.smoothedColorDependentExtendedProfileProbability
          R omega (G.fst e) c P *
        G.colorDependentExtendedProfileTinyProductMass
          proposal R rho omega e c P Q) =
      rho * G.colorDependentExtendedProfileTinyAssign
          R (G.snd e) c (G.sndStarEdge e) Q /
        G.smoothedColorDependentExtendedProfileProbability
          R omega (G.snd e) c Q := by
  have h := sum_pairedOption_left
    rho
    (G.colorDependentExtendedProfileTinyEdgeColorMass
      (s := s) (β := β) proposal e c)
    (G.smoothedColorDependentExtendedProfileProbability R omega (G.fst e) c)
    (G.smoothedColorDependentExtendedProfileProbability R omega (G.snd e) c)
    (fun P (_ : Fin 1) ↦
      G.colorDependentExtendedProfileTinyAssign R
        (G.fst e) c (G.fstStarEdge e) P)
    (fun Q (_ : Fin 1) ↦
      G.colorDependentExtendedProfileTinyAssign R
        (G.snd e) c (G.sndStarEdge e) Q)
    Q 0 hy
    (fun P ↦ (G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 (G.fst e) c P).ne')
    (G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 (G.snd e) c Q).ne'
    (by
      simpa [colorDependentExtendedProfileTinyEdgeColorMass] using
        G.sum_colorDependentExtendedProfileTinyAssign
          proposal R (G.fst e) c (G.fstStarEdge e))
  simpa [colorDependentExtendedProfileTinyProductMass] using h

theorem colorDependentLargeProductMass_expectation
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    {e : G.E} {c : Color}
    (hy : G.colorDependentExtendedProfileLargeEdgeColorMass
      (s := s) (β := β) proposal e c ≠ 0) :
    (∑ P : G.ColorDependentExtendedProfileState R (G.fst e) c,
      G.smoothedColorDependentExtendedProfileProbability
          R omega (G.fst e) c P * ∑ i,
        ∑ Q : G.ColorDependentExtendedProfileState R (G.snd e) c,
          G.smoothedColorDependentExtendedProfileProbability
              R omega (G.snd e) c Q * ∑ j,
            G.colorDependentExtendedProfileLargeProductMass
              proposal R rho omega e c P Q i j) =
      rho * G.colorDependentExtendedProfileLargeEdgeColorMass
        (s := s) (β := β) proposal e c := by
  unfold colorDependentExtendedProfileLargeProductMass
  apply sum_pairedOption
  · exact hy
  · intro P
    exact (G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 (G.fst e) c P).ne'
  · intro Q
    exact (G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 (G.snd e) c Q).ne'
  · simpa [colorDependentExtendedProfileLargeEdgeColorMass] using
      G.sum_colorDependentExtendedProfileLargeAssign
        proposal R (G.fst e) c (G.fstStarEdge e)
  · simpa [colorDependentExtendedProfileLargeEdgeColorMass] using
      G.sum_colorDependentExtendedProfileLargeAssign
        proposal R (G.snd e) c (G.sndStarEdge e)

theorem colorDependentTinyProductMass_expectation
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    {e : G.E} {c : Color}
    (hy : G.colorDependentExtendedProfileTinyEdgeColorMass
      (s := s) (β := β) proposal e c ≠ 0) :
    (∑ P : G.ColorDependentExtendedProfileState R (G.fst e) c,
      G.smoothedColorDependentExtendedProfileProbability
          R omega (G.fst e) c P *
        ∑ Q : G.ColorDependentExtendedProfileState R (G.snd e) c,
          G.smoothedColorDependentExtendedProfileProbability
              R omega (G.snd e) c Q *
            G.colorDependentExtendedProfileTinyProductMass
              proposal R rho omega e c P Q) =
      rho * G.colorDependentExtendedProfileTinyEdgeColorMass
        (s := s) (β := β) proposal e c := by
  have h := sum_pairedOption
    rho
    (G.colorDependentExtendedProfileTinyEdgeColorMass
      (s := s) (β := β) proposal e c)
    (G.smoothedColorDependentExtendedProfileProbability R omega (G.fst e) c)
    (G.smoothedColorDependentExtendedProfileProbability R omega (G.snd e) c)
    (fun P (_ : Fin 1) ↦
      G.colorDependentExtendedProfileTinyAssign R
        (G.fst e) c (G.fstStarEdge e) P)
    (fun Q (_ : Fin 1) ↦
      G.colorDependentExtendedProfileTinyAssign R
        (G.snd e) c (G.sndStarEdge e) Q)
    hy
    (fun P ↦ (G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 (G.fst e) c P).ne')
    (fun Q ↦ (G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 (G.snd e) c Q).ne')
    (by
      simpa [colorDependentExtendedProfileTinyEdgeColorMass] using
        G.sum_colorDependentExtendedProfileTinyAssign
          proposal R (G.fst e) c (G.fstStarEdge e))
    (by
      simpa [colorDependentExtendedProfileTinyEdgeColorMass] using
        G.sum_colorDependentExtendedProfileTinyAssign
          proposal R (G.snd e) c (G.sndStarEdge e))
  simpa [colorDependentExtendedProfileTinyProductMass] using h

end ProductConsequences

end WeightedMultigraph

end

end WeightedEdgeColoring
