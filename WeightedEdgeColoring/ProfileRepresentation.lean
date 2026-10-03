import WeightedEdgeColoring.BoundedProfiles

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph)

/-!
# Explicit bounded rounded profiles

This file turns the rounded law into an actual finite menu.  A profile records
the multiplicity of every kept ordinary size and the integral reservoir level.
Equal records are aggregated before slots are exposed.  The extra `none`
profile is the size-one repair profile.
-/

/-- Ambient finite type for rounded profiles.  Its two coordinates are the
ordinary multiplicities and the rounded-reservoir level. -/
abbrev RoundedProfileCode {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r) :=
  ({z // z ∈ L.kept} → Fin (⌊1 / β⌋₊ + 1)) × Fin (⌊1 / r⌋₊ + 1)

/-- Multiplicity of a kept size in one rounded raw profile. -/
noncomputable def roundedMultiplicity {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (k : Fin L.m) (z : {z // z ∈ L.kept}) : ℕ :=
  ((G.largeEdges β (L.outcome k)).filter
    (fun e ↦ L.round (G.weight e.1) = z.1)).card

theorem roundedMultiplicity_le_floor {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β)
    (k : Fin L.m) (z : {z // z ∈ L.kept}) :
    G.roundedMultiplicity L k z ≤ ⌊1 / β⌋₊ := by
  have hsub : G.roundedMultiplicity L k z ≤
      (G.rawProfile β (L.outcome k)).ordinary.card := by
    unfold roundedMultiplicity
    rw [rawProfile_ordinary]
    exact Finset.card_filter_le _ _
  have hreal : (((G.rawProfile β (L.outcome k)).ordinary.card : ℕ) : ℝ) ≤
      1 / β := by
    apply (le_div_iff₀ hβ).2
    simpa [mul_comm] using G.rawProfile_card_mul_beta_le_one (L.feasible k)
  have hfloor : (G.rawProfile β (L.outcome k)).ordinary.card ≤ ⌊1 / β⌋₊ :=
    Nat.le_floor hreal
  exact hsub.trans hfloor

theorem rawProfile_reservoir_le_one {v : G.V} {β : ℝ}
    {S : Finset (G.StarEdge v)} :
    (G.rawProfile β S).reservoir ≤ 1 := by
  rw [rawProfile_reservoir]
  have hsum : 0 ≤ ∑ e ∈ G.largeEdges β S, G.weight e.1 :=
    Finset.sum_nonneg fun e _he ↦ G.weight_nonneg e.1
  linarith

theorem reservoirLevel_le_floor {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hr : 0 < r) (k : Fin L.m) :
    ⌊(G.rawProfile β (L.outcome k)).reservoir / r⌋₊ ≤ ⌊1 / r⌋₊ := by
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_right (G.rawProfile_reservoir_le_one) hr.le

/-- The bounded code of an outcome. -/
noncomputable def roundedProfileCode {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (hβ : 0 < β) (hr : 0 < r) (k : Fin L.m) : G.RoundedProfileCode L :=
  (fun z ↦ ⟨G.roundedMultiplicity L k z,
      Nat.lt_succ_of_le (G.roundedMultiplicity_le_floor L hβ k z)⟩,
    ⟨⌊(G.rawProfile β (L.outcome k)).reservoir / r⌋₊,
      Nat.lt_succ_of_le (G.reservoirLevel_le_floor L hr k)⟩)

/-- Aggregated menu of rounded profiles actually occurring in the law. -/
noncomputable def roundedProfileMenu {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (hβ : 0 < β) (hr : 0 < r) : Finset (G.RoundedProfileCode L) :=
  profileMenu (G.roundedProfileCode L hβ hr)

/-- Probability mass of one aggregated rounded profile. -/
noncomputable def roundedProfileMass {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (hβ : 0 < β) (hr : 0 < r) (P : G.RoundedProfileCode L) : ℝ :=
  fiberMass L.probability (G.roundedProfileCode L hβ hr) P

theorem roundedProfileMass_nonneg {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (hβ : 0 < β) (hr : 0 < r) (P : G.RoundedProfileCode L) :
    0 ≤ G.roundedProfileMass L hβ hr P :=
  fiberMass_nonneg L.probability_nonneg _ P

theorem sum_roundedProfileMass {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (hβ : 0 < β) (hr : 0 < r) :
    (∑ P ∈ G.roundedProfileMenu L hβ hr,
      G.roundedProfileMass L hβ hr P) = 1 := by
  exact (sum_fiberMass_profileMenu L.probability
    (G.roundedProfileCode L hβ hr)).trans L.probability_sum

theorem roundedProfileMenu_card_le {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (hβ : 0 < β) (hr : 0 < r) :
    (G.roundedProfileMenu L hβ hr).card ≤
      (⌊1 / β⌋₊ + 1) ^ L.kept.card * (⌊1 / r⌋₊ + 1) := by
  calc
    (G.roundedProfileMenu L hβ hr).card ≤
        Fintype.card (G.RoundedProfileCode L) := by
      simpa using Finset.card_le_card
        (Finset.subset_univ (G.roundedProfileMenu L hβ hr))
    _ = (⌊1 / β⌋₊ + 1) ^ L.kept.card * (⌊1 / r⌋₊ + 1) := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin, Fintype.card_coe]

/-- The actual rounded profiles, together with the extra size-one repair
profile (`none`). -/
abbrev RoundedProfileIndex {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (hβ : 0 < β) (hr : 0 < r) :=
  Option {P // P ∈ G.roundedProfileMenu L hβ hr}

/-- The menu has an explicit parameter-only bound, including the repair
profile. -/
theorem roundedProfileIndex_card_le {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (hβ : 0 < β) (hr : 0 < r) :
    Fintype.card (G.RoundedProfileIndex L hβ hr) ≤
      (⌊1 / β⌋₊ + 1) ^ L.kept.card * (⌊1 / r⌋₊ + 1) + 1 := by
  simpa using Nat.add_le_add_right (G.roundedProfileMenu_card_le L hβ hr) 1

/-- Fully parameter-only menu bound obtained from the kept-size bound. -/
theorem roundedProfileIndex_card_le_parameters {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r) :
    Fintype.card (G.RoundedProfileIndex L hβ hr) ≤
      (⌊1 / β⌋₊ + 1) ^ (⌊(1 / β) / q⌋₊ + 1) *
        (⌊1 / r⌋₊ + 1) + 1 := by
  refine (G.roundedProfileIndex_card_le L hβ hr).trans ?_
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_right
  exact pow_le_pow_right' (Nat.succ_le_succ (Nat.zero_le _)) L.kept_card_le

/-- Explicit large slots of the aggregated menu.  An ordinary slot carries
its profile, kept size, and ordinal within the profile.  `none` is the sole
slot of the size-one repair profile. -/
abbrev ExplicitLargeSlot {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (hβ : 0 < β) (hr : 0 < r) :=
  Option (Σ P : {P // P ∈ G.roundedProfileMenu L hβ hr},
    Σ z : {z // z ∈ L.kept}, Fin ((P.1.1 z).val))

noncomputable def explicitLargeSlotSize {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r) :
    G.ExplicitLargeSlot L hβ hr → ℝ
  | none => 1
  | some slot => slot.2.1.1

noncomputable def explicitLargeSlotCapacity {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r) :
    G.ExplicitLargeSlot L hβ hr → ℝ
  | none => s * q
  | some slot => s * G.roundedProfileMass L hβ hr slot.1.1

theorem explicitLargeSlotCapacity_nonneg {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (j : G.ExplicitLargeSlot L hβ hr) :
    0 ≤ G.explicitLargeSlotCapacity L hβ hr j := by
  cases j with
  | none => exact mul_nonneg hs hq
  | some j =>
      exact mul_nonneg hs (G.roundedProfileMass_nonneg L hβ hr j.1.1)

/-- Number of ordinary slots at or above a threshold in a bounded code. -/
noncomputable def roundedCodeCountAbove {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (P : G.RoundedProfileCode L) (t : ℝ) : ℕ :=
  ∑ z : {z // z ∈ L.kept}, if t ≤ z.1 then (P.1 z).val else 0

theorem roundedCodeCountAbove_code {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r t : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r)
    (k : Fin L.m) :
    G.roundedCodeCountAbove L (G.roundedProfileCode L hβ hr k) t =
      ((G.largeEdges β (L.outcome k)).filter
        (fun e ↦ t ≤ L.round (G.weight e.1))).card := by
  classical
  let T : Finset ℝ := L.kept.filter fun z ↦ t ≤ z
  have hrange : ∀ e ∈ G.largeEdges β (L.outcome k),
      L.round (G.weight e.1) ∈ L.kept := by
    intro e he
    apply L.round_mem
    apply Finset.mem_biUnion.mpr
    exact ⟨k, Finset.mem_univ k, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    (G.largeEdges β (L.outcome k)) T
    (fun e ↦ L.round (G.weight e.1)) (fun _e ↦ (1 : ℕ))
  unfold roundedCodeCountAbove roundedProfileCode
  simp only
  let c : ℝ → ℕ := fun z ↦ if hz : z ∈ L.kept then
    G.roundedMultiplicity L k ⟨z, hz⟩ else 0
  have hsub :
      (∑ z : {z // z ∈ L.kept},
        if t ≤ z.1 then G.roundedMultiplicity L k z else 0) =
      ∑ z ∈ L.kept, if t ≤ z then c z else 0 := by
    symm
    simpa [c] using Finset.sum_subtype
      (F := inferInstanceAs (Fintype {z // z ∈ L.kept})) L.kept
      (fun z ↦ Iff.rfl) (fun z ↦ if t ≤ z then c z else 0)
  rw [hsub, ← Finset.sum_filter]
  calc
    (∑ z ∈ T, c z) =
        ∑ z ∈ T, ∑ e ∈ G.largeEdges β (L.outcome k) with
          L.round (G.weight e.1) = z, 1 := by
      apply Finset.sum_congr rfl
      intro z hz
      have hzkept : z ∈ L.kept := (Finset.mem_filter.mp hz).1
      rw [show c z = G.roundedMultiplicity L k ⟨z, hzkept⟩ by simp [c, hzkept]]
      rw [roundedMultiplicity, Finset.card_eq_sum_ones]
    _ = ∑ e ∈ G.largeEdges β (L.outcome k) with
        L.round (G.weight e.1) ∈ T, 1 := hfiber
    _ = ((G.largeEdges β (L.outcome k)).filter
        (fun e ↦ t ≤ L.round (G.weight e.1))).card := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr
      · ext e
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨he, hT⟩
          exact ⟨he, by simpa [T, hrange e he] using hT⟩
        · rintro ⟨he, ht⟩
          exact ⟨he, by simpa [T, hrange e he] using ht⟩
      · intro e _he
        rfl

/-- Aggregating duplicate profile codes preserves every ordinary slot-count
statistic. -/
theorem sum_profileMass_mul_countAbove {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r t : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r) :
    (∑ P ∈ G.roundedProfileMenu L hβ hr,
      G.roundedProfileMass L hβ hr P *
        (G.roundedCodeCountAbove L P t : ℝ)) =
      ∑ k, L.probability k *
        (G.roundedCodeCountAbove L (G.roundedProfileCode L hβ hr k) t : ℝ) := by
  classical
  calc
    (∑ P ∈ G.roundedProfileMenu L hβ hr,
      G.roundedProfileMass L hβ hr P *
        (G.roundedCodeCountAbove L P t : ℝ)) =
        ∑ P ∈ G.roundedProfileMenu L hβ hr,
          fiberMass (fun k ↦ L.probability k *
            (G.roundedCodeCountAbove L
              (G.roundedProfileCode L hβ hr k) t : ℝ))
            (G.roundedProfileCode L hβ hr) P := by
      apply Finset.sum_congr rfl
      intro P hP
      unfold roundedProfileMass fiberMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hcode : G.roundedProfileCode L hβ hr k = P :=
        (Finset.mem_filter.mp hk).2
      change L.probability k *
          (G.roundedCodeCountAbove L P t : ℝ) =
        L.probability k *
          (G.roundedCodeCountAbove L (G.roundedProfileCode L hβ hr k) t : ℝ)
      rw [hcode]
    _ = ∑ k, L.probability k *
        (G.roundedCodeCountAbove L (G.roundedProfileCode L hβ hr k) t : ℝ) :=
      sum_fiberMass_profileMenu _ _

theorem roundedSlotUpperTail_eq_outcomes {v : G.V} {m : ℕ}
    (p : Fin m → ℝ) (β : ℝ)
    (outcome : Fin m → Finset (G.StarEdge v)) (round : ℝ → ℝ) (t : ℝ) :
    roundedSlotUpperTail (G.lawSlotSupport β outcome)
        (G.lawSlotMass p β outcome) round t =
      ∑ k, p k * (((G.largeEdges β (outcome k)).filter
        (fun e ↦ t ≤ round (G.weight e.1))).card : ℝ) := by
  classical
  unfold roundedSlotUpperTail lawSlotMass
  calc
    (∑ b ∈ G.lawSlotSupport β outcome,
      if t ≤ round b then
        ∑ k, ∑ e ∈ G.largeEdges β (outcome k),
          if G.weight e.1 = b then p k else 0
      else 0) =
      ∑ b ∈ G.lawSlotSupport β outcome,
        ∑ k, ∑ e ∈ G.largeEdges β (outcome k),
          if t ≤ round b ∧ G.weight e.1 = b then p k else 0 := by
        apply Finset.sum_congr rfl
        intro b _hb
        by_cases htb : t ≤ round b <;> simp [htb]
    _ = ∑ k, ∑ e ∈ G.largeEdges β (outcome k),
        ∑ b ∈ G.lawSlotSupport β outcome,
          if t ≤ round b ∧ G.weight e.1 = b then p k else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ e ∈ G.largeEdges β (outcome k),
        if t ≤ round (G.weight e.1) then p k else 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro e he
      have hmem : G.weight e.1 ∈ G.lawSlotSupport β outcome := by
        apply Finset.mem_biUnion.mpr
        exact ⟨k, Finset.mem_univ k, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
      by_cases ht : t ≤ round (G.weight e.1)
      · rw [Finset.sum_eq_single_of_mem (G.weight e.1) hmem]
        · simp [ht]
        · intro b hb hne
          by_cases hbe : G.weight e.1 = b
          · exact (hne hbe.symm).elim
          · simp [hbe]
      · rw [if_neg ht]
        apply Finset.sum_eq_zero
        intro b hb
        by_cases hbe : G.weight e.1 = b
        · subst b
          simp [ht]
        · simp [hbe]
    _ = ∑ k, p k * (((G.largeEdges β (outcome k)).filter
        (fun e ↦ t ≤ round (G.weight e.1))).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [← Finset.sum_filter]
      simp [mul_comm]

theorem explicitLargeSlot_upperTail {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r t : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r) :
    finiteUpperTail Finset.univ (G.explicitLargeSlotSize L hβ hr)
        (G.explicitLargeSlotCapacity L hβ hr) t =
      s * roundedSlotUpperTail (G.lawSlotSupport β L.outcome)
        (G.lawSlotMass L.probability β L.outcome) L.round t +
      s * repairSlotUpperTail q t := by
  classical
  unfold finiteUpperTail explicitLargeSlotSize explicitLargeSlotCapacity
  rw [Fintype.sum_option]
  simp_rw [Fintype.sum_sigma]
  change (if t ≤ 1 then s * q else 0) +
      (∑ P : {P // P ∈ G.roundedProfileMenu L hβ hr},
        ∑ z : {z // z ∈ L.kept},
          ∑ _i : Fin ((P.1.1 z).val),
            if t ≤ z.1 then s * G.roundedProfileMass L hβ hr P.1 else 0) = _
  simp only [Finset.sum_const_zero, Finset.sum_ite_irrel, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  rw [G.roundedSlotUpperTail_eq_outcomes]
  have houtcomes :
      (∑ k, L.probability k *
        (((G.largeEdges β (L.outcome k)).filter
          (fun e ↦ t ≤ L.round (G.weight e.1))).card : ℝ)) =
      ∑ k, L.probability k *
        (G.roundedCodeCountAbove L
          (G.roundedProfileCode L hβ hr k) t : ℝ) := by
    apply Finset.sum_congr rfl
    intro k _hk
    rw [G.roundedCodeCountAbove_code L hβ hr k]
  rw [houtcomes]
  rw [← G.sum_profileMass_mul_countAbove L hβ hr]
  have hprofileSum :
      (∑ P ∈ G.roundedProfileMenu L hβ hr,
        G.roundedProfileMass L hβ hr P *
          (G.roundedCodeCountAbove L P t : ℝ)) =
      ∑ P : {P // P ∈ G.roundedProfileMenu L hβ hr},
        G.roundedProfileMass L hβ hr P.1 *
          (G.roundedCodeCountAbove L P.1 t : ℝ) := by
    apply Finset.sum_subtype
    intro P
    rfl
  rw [hprofileSum]
  unfold roundedCodeCountAbove repairSlotUpperTail
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  rw [Finset.mul_sum]
  rw [add_comm (if t ≤ 1 then s * q else 0)]
  congr 1
  · apply Finset.sum_congr rfl
    intro P _hP
    rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _hz
    by_cases htz : t ≤ z.1 <;> simp [htz]
    ring
  · by_cases ht1 : t ≤ 1 <;> simp [ht1]

/-- Large-edge transport on actual aggregated profile slots.  Thus the
capacity bound is per copy of a slot in a concrete rounded profile, rather
than merely per rounded size bucket. -/
theorem BoundedProfileLaw.exists_profileLargeTransport {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hs : 0 ≤ s)
    (hβ : 0 < β) (hq : 0 < q) (hr : 0 < r) :
    ∃ assign : G.StarEdge v → G.ExplicitLargeSlot L hβ hr → ℝ,
      (∀ e j, 0 ≤ assign e j) ∧
      (∀ e j, 0 < assign e j →
        G.weight e.1 ≤ G.explicitLargeSlotSize L hβ hr j) ∧
      (∀ e, (∑ j, assign e j) =
        if β ≤ G.weight e.1 then s * x e else 0) ∧
      (∀ j, (∑ e, assign e j) ≤
        G.explicitLargeSlotCapacity L hβ hr j) := by
  classical
  have hcapacity : ∀ j, 0 ≤ G.explicitLargeSlotCapacity L hβ hr j :=
    G.explicitLargeSlotCapacity_nonneg L hβ hr hs hq.le
  have htail : ∀ t,
      finiteUpperTail Finset.univ (fun e : G.StarEdge v ↦ G.weight e.1)
          (G.largeTransportDemand L) t ≤
        finiteUpperTail Finset.univ (G.explicitLargeSlotSize L hβ hr)
          (G.explicitLargeSlotCapacity L hβ hr) t := by
    intro t
    by_cases ht : t ≤ 1
    · rw [G.largeTransportDemand_upperTail L,
          G.explicitLargeSlot_upperTail L hβ hr]
      exact L.tail_repaired t ht
    · have hleft :
          finiteUpperTail Finset.univ (fun e : G.StarEdge v ↦ G.weight e.1)
            (G.largeTransportDemand L) t = 0 := by
        unfold finiteUpperTail
        apply Finset.sum_eq_zero
        intro e _he
        have hnot : ¬t ≤ G.weight e.1 := fun h ↦
          ht (h.trans (G.weight_le_one e.1))
        simp [hnot]
      rw [hleft]
      unfold finiteUpperTail
      exact Finset.sum_nonneg fun j _hj ↦ by
        split
        · exact hcapacity j
        · exact le_rfl
  rcases exists_thresholdTransport
      (fun e : G.StarEdge v ↦ G.weight e.1)
      (G.explicitLargeSlotSize L hβ hr) (G.largeTransportDemand L)
      (G.explicitLargeSlotCapacity L hβ hr)
      (G.largeTransportDemand_nonneg L hs) hcapacity htail with
    ⟨assign, hnonneg, hsupport, hrow, hcol⟩
  refine ⟨assign, hnonneg, hsupport, ?_, hcol⟩
  intro e
  rw [hrow e, G.largeTransportDemand_eq L e]

/-- Rounded reservoir capacity contributed by all outcomes in one aggregated
profile, before the global retention factor `s`. -/
noncomputable def roundedProfileReservoirMass {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r)
    (P : G.RoundedProfileCode L) : ℝ :=
  fiberMass (fun k ↦ L.probability k *
    roundReservoir r (G.rawProfile β (L.outcome k)).reservoir)
    (G.roundedProfileCode L hβ hr) P

theorem roundedProfileReservoirMass_nonneg {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r)
    (P : G.RoundedProfileCode L) :
    0 ≤ G.roundedProfileReservoirMass L hβ hr P := by
  apply fiberMass_nonneg
  intro k
  exact mul_nonneg (L.probability_nonneg k)
    (roundReservoir_nonneg hr.le
      (G.rawProfile_reservoir_nonneg (L.feasible k)))

theorem sum_roundedProfileReservoirMass {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r) :
    (∑ P ∈ G.roundedProfileMenu L hβ hr,
      G.roundedProfileReservoirMass L hβ hr P) =
      ∑ k, L.probability k *
        roundReservoir r (G.rawProfile β (L.outcome k)).reservoir := by
  exact sum_fiberMass_profileMenu _ _

/-- Reservoir resources are indexed by the same aggregated profile menu;
`none` is the reservoir-repair profile of capacity `s*r`. -/
noncomputable def explicitTinyProfileCapacity {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r) :
    G.RoundedProfileIndex L hβ hr → ℝ
  | none => s * r
  | some P => s * G.roundedProfileReservoirMass L hβ hr P.1

theorem explicitTinyProfileCapacity_nonneg {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r)
    (hs : 0 ≤ s) (P : G.RoundedProfileIndex L hβ hr) :
    0 ≤ G.explicitTinyProfileCapacity L hβ hr P := by
  cases P with
  | none => exact mul_nonneg hs hr.le
  | some P =>
      exact mul_nonneg hs (G.roundedProfileReservoirMass_nonneg L hβ hr P.1)

theorem sum_explicitTinyProfileCapacity {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r) :
    (∑ P, G.explicitTinyProfileCapacity L hβ hr P) =
      s * (∑ k, L.probability k *
        roundReservoir r (G.rawProfile β (L.outcome k)).reservoir) + s * r := by
  classical
  unfold explicitTinyProfileCapacity
  rw [Fintype.sum_option]
  simp only
  have hsub :
      (∑ P : {P // P ∈ G.roundedProfileMenu L hβ hr},
        G.roundedProfileReservoirMass L hβ hr P.1) =
      ∑ P ∈ G.roundedProfileMenu L hβ hr,
        G.roundedProfileReservoirMass L hβ hr P := by
    symm
    apply Finset.sum_subtype
    intro P
    rfl
  rw [← Finset.mul_sum, hsub, G.sum_roundedProfileReservoirMass L hβ hr]
  ac_rfl

/-- Occurrence demand of a tiny edge. -/
noncomputable def tinyOccurrenceDemand {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (_L : G.BoundedProfileLaw x s β q r)
    (e : G.StarEdge v) : ℝ :=
  if G.weight e.1 < β then s * x e else 0

theorem BoundedProfileLaw.x_nonneg {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (e : G.StarEdge v) : 0 ≤ x e := by
  rw [← L.original_marginal e]
  exact Finset.sum_nonneg fun k _hk ↦ by
    split
    · exact L.probability_nonneg k
    · exact le_rfl

theorem tinyOccurrenceDemand_nonneg {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hs : 0 ≤ s)
    (e : G.StarEdge v) : 0 ≤ G.tinyOccurrenceDemand L e := by
  unfold tinyOccurrenceDemand
  split
  · exact mul_nonneg hs (BoundedProfileLaw.x_nonneg (G := G) L e)
  · exact le_rfl

/-- Tiny items admit an exact per-profile occurrence assignment.  The column
constraint is the reservoir's weighted capacity, which is the divisible-item
constraint used by the profile lemma. -/
theorem BoundedProfileLaw.exists_profileTinyTransport {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hs : 0 ≤ s)
    (hβ : 0 < β) (hr : 0 < r) :
    ∃ assign : G.StarEdge v → G.RoundedProfileIndex L hβ hr → ℝ,
      (∀ e P, 0 ≤ assign e P) ∧
      (∀ e, (∑ P, assign e P) = G.tinyOccurrenceDemand L e) ∧
      (∀ P, (∑ e, G.weight e.1 * assign e P) ≤
        G.explicitTinyProfileCapacity L hβ hr P) := by
  classical
  let weightedDemand : G.StarEdge v → ℝ := fun e ↦
    G.weight e.1 * G.tinyOccurrenceDemand L e
  have hdemand : ∀ e, 0 ≤ weightedDemand e := fun e ↦
    mul_nonneg (G.weight_nonneg e.1) (G.tinyOccurrenceDemand_nonneg L hs e)
  have hcapacity : ∀ P, 0 ≤ G.explicitTinyProfileCapacity L hβ hr P :=
    G.explicitTinyProfileCapacity_nonneg L hβ hr hs
  have htotal : (∑ e, weightedDemand e) ≤
      ∑ P, G.explicitTinyProfileCapacity L hβ hr P := by
    rw [G.sum_explicitTinyProfileCapacity L hβ hr]
    unfold weightedDemand tinyOccurrenceDemand
    convert L.tiny_demand_repaired using 1
    apply Finset.sum_congr rfl
    intro e _he
    by_cases hetiny : G.weight e.1 < β <;> simp [hetiny]
  have htail : ∀ t,
      finiteUpperTail Finset.univ (fun _e : G.StarEdge v ↦ (0 : ℝ))
          weightedDemand t ≤
        finiteUpperTail Finset.univ
          (fun _P : G.RoundedProfileIndex L hβ hr ↦ (0 : ℝ))
          (G.explicitTinyProfileCapacity L hβ hr) t := by
    intro t
    by_cases ht : t ≤ 0
    · simpa [finiteUpperTail, ht] using htotal
    · have hnot : ¬t ≤ (0 : ℝ) := ht
      simp [finiteUpperTail, hnot]
  rcases exists_thresholdTransport
      (fun _e : G.StarEdge v ↦ (0 : ℝ))
      (fun _P : G.RoundedProfileIndex L hβ hr ↦ (0 : ℝ))
      weightedDemand (G.explicitTinyProfileCapacity L hβ hr)
      hdemand hcapacity htail with
    ⟨weightedAssign, hnonneg, _hsupport, hrow, hcol⟩
  let assign : G.StarEdge v → G.RoundedProfileIndex L hβ hr → ℝ :=
    fun e P ↦ weightedAssign e P / G.weight e.1
  refine ⟨assign, ?_, ?_, ?_⟩
  · intro e P
    exact div_nonneg (hnonneg e P) (G.weight_nonneg e.1)
  · intro e
    unfold assign
    rw [← Finset.sum_div, hrow e]
    unfold weightedDemand
    exact (mul_div_cancel_left₀ (G.tinyOccurrenceDemand L e)
      (G.weight_pos e.1).ne')
  · intro P
    calc
      (∑ e, G.weight e.1 * assign e P) = ∑ e, weightedAssign e P := by
        apply Finset.sum_congr rfl
        intro e _he
        unfold assign
        exact mul_div_cancel₀ (weightedAssign e P) (G.weight_pos e.1).ne'
      _ ≤ G.explicitTinyProfileCapacity L hβ hr P := hcol P

/-- Final bounded-profile interface: a bounded aggregated profile menu, an
exact compatible assignment of all retained large-edge marginals to its
ordinary slots (plus the size-one repair profile), and an exact assignment
of all retained tiny-edge marginals to its rounded reservoirs (plus the
reservoir-repair profile). -/
structure BoundedProfileRealization {v : G.V} (x : G.StarEdge v → ℝ)
    (s β q r : ℝ) (hβ : 0 < β) (hr : 0 < r) where
  law : G.BoundedProfileLaw x s β q r
  menu_card_le : Fintype.card (G.RoundedProfileIndex law hβ hr) ≤
    (⌊1 / β⌋₊ + 1) ^ (⌊(1 / β) / q⌋₊ + 1) *
      (⌊1 / r⌋₊ + 1) + 1
  largeAssign : G.StarEdge v → G.ExplicitLargeSlot law hβ hr → ℝ
  largeAssign_nonneg : ∀ e j, 0 ≤ largeAssign e j
  largeAssign_compatible : ∀ e j, 0 < largeAssign e j →
    G.weight e.1 ≤ G.explicitLargeSlotSize law hβ hr j
  largeAssign_marginal : ∀ e, (∑ j, largeAssign e j) =
    if β ≤ G.weight e.1 then s * x e else 0
  largeAssign_capacity : ∀ j, (∑ e, largeAssign e j) ≤
    G.explicitLargeSlotCapacity law hβ hr j
  tinyAssign : G.StarEdge v → G.RoundedProfileIndex law hβ hr → ℝ
  tinyAssign_nonneg : ∀ e P, 0 ≤ tinyAssign e P
  tinyAssign_marginal : ∀ e, (∑ P, tinyAssign e P) =
    G.tinyOccurrenceDemand law e
  tinyAssign_capacity : ∀ P, (∑ e, G.weight e.1 * tinyAssign e P) ≤
    G.explicitTinyProfileCapacity law hβ hr P

/-- Every local-polytope point has a fully explicit bounded rounded-profile
realization. -/
theorem exists_boundedProfileRealization {v : G.V}
    {x : G.StarEdge v → ℝ} (hx : G.IsAverageOfStarFeasibleSets v x)
    {s β q r : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hq : 0 < q) (hr : 0 < r) :
    Nonempty (G.BoundedProfileRealization x s β q r hβ hr) := by
  classical
  rcases G.exists_boundedProfileLaw hx hs hs1 hβ hq hr with ⟨L⟩
  rcases BoundedProfileLaw.exists_profileLargeTransport (G := G) L hs hβ hq hr with
    ⟨largeAssign, hlarge0, hlargeSupport, hlargeRow, hlargeCol⟩
  rcases BoundedProfileLaw.exists_profileTinyTransport (G := G) L hs hβ hr with
    ⟨tinyAssign, htiny0, htinyRow, htinyCol⟩
  exact ⟨⟨L, G.roundedProfileIndex_card_le_parameters L hβ hr,
    largeAssign, hlarge0, hlargeSupport, hlargeRow, hlargeCol,
    tinyAssign, htiny0, htinyRow, htinyCol⟩⟩



end WeightedSimpleGraph
end WeightedEdgeColoring
