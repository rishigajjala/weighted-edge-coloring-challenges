import WeightedEdgeColoring.SubtwoMixedGraphReservoirSlack

/-!
# Reservoir-relative tiny candidate means
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {v : G.V} {φ : G.StarEdge v → ℝ}
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : G.BoundedProfileRealization φ s β qstep r hβ hr)

theorem roundedProfileReservoirMass_eq_mass_mul_code
    (P : G.RoundedProfileCode R.law) :
    G.roundedProfileReservoirMass R.law hβ hr P =
      G.roundedProfileMass R.law hβ hr P * (r * P.2.val) := by
  classical
  unfold roundedProfileReservoirMass roundedProfileMass fiberMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have hcode : G.roundedProfileCode R.law hβ hr a = P :=
    (Finset.mem_filter.mp ha).2
  have hR : 0 ≤ (G.rawProfile β (R.law.outcome a)).reservoir :=
    G.rawProfile_reservoir_nonneg (R.law.feasible a)
  have hcast :
      ((⌊(G.rawProfile β (R.law.outcome a)).reservoir / r⌋₊ : ℕ) : ℝ) =
      ((⌊(G.rawProfile β (R.law.outcome a)).reservoir / r⌋ : ℤ) : ℝ) := by
    have hn := (Nat.floor_eq_iff
      (n := ⌊(G.rawProfile β (R.law.outcome a)).reservoir / r⌋₊)
      (div_nonneg hR hr.le)).mp rfl
    have hi :
        (⌊(G.rawProfile β (R.law.outcome a)).reservoir / r⌋ : ℤ) =
        (⌊(G.rawProfile β (R.law.outcome a)).reservoir / r⌋₊ : ℕ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast hn.1
      · exact_mod_cast hn.2
    rw [hi]
    norm_num
  have hsecond : (G.roundedProfileCode R.law hβ hr a).2 = P.2 :=
    congrArg Prod.snd hcode
  have hfloor : ⌊(G.rawProfile β (R.law.outcome a)).reservoir / r⌋₊ =
      P.2.val := by
    simpa [roundedProfileCode] using congrArg Fin.val hsecond
  have hround : roundReservoir r
      (G.rawProfile β (R.law.outcome a)).reservoir = r * P.2.val := by
    unfold roundReservoir
    rw [← hcast, hfloor]
  change R.law.probability a *
    roundReservoir r (G.rawProfile β (R.law.outcome a)).reservoir = _
  rw [hround]

theorem sum_weight_mul_localExtendedProfileTinyAssign_le_reservoir
    (hs : 0 ≤ s)
    (z : G.LocalExtendedProfileState R) :
    (∑ e : G.StarEdge v,
      G.weight e.1 * G.localExtendedProfileTinyAssign R e z) ≤
      G.localExtendedProfileProbability R z *
        G.localMixedConcreteReservoirSize R z := by
  rcases z with P | k
  · have hcap := R.tinyAssign_capacity (some P)
    have hmass := G.roundedProfileReservoirMass_eq_mass_mul_code R P.1
    simpa [localExtendedProfileTinyAssign,
      localExtendedProfileProbability, localMixedConcreteReservoirSize,
      explicitTinyProfileCapacity, hmass, mul_assoc] using hcap
  · fin_cases k
    · simp [localExtendedProfileTinyAssign,
        localExtendedProfileProbability, localMixedConcreteReservoirSize]
    · simpa [localExtendedProfileTinyAssign,
        localExtendedProfileProbability, localMixedConcreteReservoirSize,
        explicitTinyProfileCapacity] using R.tinyAssign_capacity none
    · simp [localExtendedProfileTinyAssign,
        localExtendedProfileProbability, localMixedConcreteReservoirSize]

variable {Color Label : Type*} [Fintype Color] [DecidableEq Color]
  [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → Color → ℝ)
variable (edgeLabel : ∀ w : G.V, G.StarEdge w → Label)
variable (qLaw : ∀ w : G.V, Color → Finset (G.StarEdge w) → ℝ)
variable (RG : ∀ w c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel w)
      (fun e : G.StarEdge w ↦ proposal e.1 c) (qLaw w c) label)
    s β qstep r hβ hr)

theorem sum_weight_mul_mixedGraphTinyAssign_le_concreteReservoir
    (hq0 : ∀ w c S, 0 ≤ qLaw w c S)
    (hs : 0 ≤ s)
    (w : G.V) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw RG w c) :
    (∑ e : G.StarEdge w,
      G.weight e.1 *
        G.mixedGraphTinyAssign proposal edgeLabel qLaw RG w c e a) ≤
      G.mixedGraphProbability proposal edgeLabel qLaw RG w c a *
        G.mixedGraphConcreteReservoirSize proposal edgeLabel qLaw RG w c a := by
  classical
  rcases a with _ | ⟨label, z⟩
  · simp [mixedGraphTinyAssign, mixedLabelGraphTinyAssign,
      mixedGraphConcreteReservoirSize]
  · have hlocal := G.sum_weight_mul_localExtendedProfileTinyAssign_le_reservoir
      (RG w c label) hs z
    have hlabel := G.subsetLabelMass_nonneg_local
      (edgeLabel w) (qLaw w c) (hq0 w c) label
    simp only [mixedGraphTinyAssign, mixedLabelGraphTinyAssign,
      mixedGraphProbability, mixedLabelGraphAtomProbability,
      Subtwo.labelMixtureAtomProbability,
      mixedGraphConcreteReservoirSize] at *
    calc
      (∑ e : G.StarEdge w,
        G.weight e.1 *
          (subsetLabelMass (edgeLabel w) (qLaw w c) label *
            G.localExtendedProfileTinyAssign (RG w c label) e z)) =
          subsetLabelMass (edgeLabel w) (qLaw w c) label *
            (∑ e : G.StarEdge w,
              G.weight e.1 *
                G.localExtendedProfileTinyAssign (RG w c label) e z) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e _
            ring
      _ ≤ subsetLabelMass (edgeLabel w) (qLaw w c) label *
          (G.localExtendedProfileProbability (RG w c label) z *
            G.localMixedConcreteReservoirSize (RG w c label) z) :=
        mul_le_mul_of_nonneg_left hlocal hlabel
      _ = _ := by ring

theorem mixedTinyCandidateAtomMean_le_concreteReservoir
    (rho omega : ℝ)
    (hq0 : ∀ w c S, 0 ≤ qLaw w c S)
    (hqmarg : ∀ w c (f : G.StarEdge w),
      (∑ S, if f ∈ S then qLaw w c S else 0) = proposal f.1 c)
    (hqsingle : ∀ w c S, qLaw w c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel w f = label)
    (hqsum : ∀ w c, ∑ S, qLaw w c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (c : Color)
    (row : G.MixedTinyCandidateRow proposal edgeLabel qLaw RG c) :
    (∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw RG source c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw RG
          omega source c z *
          G.mixedCandidateAtomUse proposal edgeLabel qLaw RG
            rho omega source c z (Sum.inr row)) ≤
      rho / (1 - omega) *
        G.mixedGraphConcreteReservoirSize proposal edgeLabel qLaw RG
          row.center c row.candidate := by
  rw [G.mixedTinyCandidateAtomMean_eq proposal edgeLabel qLaw RG
    rho omega hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
    homega0 homega1.le c row]
  let A := ∑ e : G.StarEdge row.center, G.weight e.1 *
    G.mixedGraphTinyAssign proposal edgeLabel qLaw RG
      row.center c e row.candidate
  let p := G.mixedGraphProbability proposal edgeLabel qLaw RG
    row.center c row.candidate
  let lam := G.smoothedMixedGraphProbability proposal edgeLabel qLaw RG
    omega row.center c row.candidate
  let reservoir := G.mixedGraphConcreteReservoirSize proposal edgeLabel qLaw RG
    row.center c row.candidate
  have hA : A ≤ p * reservoir :=
    G.sum_weight_mul_mixedGraphTinyAssign_le_concreteReservoir
      proposal edgeLabel qLaw RG hq0 hs row.center c row.candidate
  have hres0 : 0 ≤ reservoir :=
    G.mixedGraphConcreteReservoirSize_nonneg
      proposal edgeLabel qLaw RG row.center c row.candidate
  have hlam : 0 < lam := G.smoothedMixedGraphProbability_pos
    proposal edgeLabel qLaw RG hq0 hqsum hqsingle
    hs hqstep hr0 hleft homega0 homega1.le
    row.center c row.candidate
  have hone : 0 < 1 - omega := sub_pos.mpr homega1
  have hbase : (1 - omega) * p ≤ lam := by
    unfold lam smoothedMixedGraphProbability
    exact le_add_of_nonneg_right
      (div_nonneg homega0.le (Nat.cast_nonneg _))
  have hratio : A / lam ≤ reservoir / (1 - omega) := by
    apply (div_le_div_iff₀ hlam hone).2
    calc
      A * (1 - omega) ≤ (p * reservoir) * (1 - omega) :=
        mul_le_mul_of_nonneg_right hA hone.le
      _ = ((1 - omega) * p) * reservoir := by ring
      _ ≤ reservoir * lam := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_right hbase hres0
  calc
    rho / lam * A = rho * (A / lam) := by ring
    _ ≤ rho * (reservoir / (1 - omega)) :=
      mul_le_mul_of_nonneg_left hratio hrho
    _ = rho / (1 - omega) * reservoir := by ring

end WeightedMultigraph

end

end WeightedEdgeColoring
