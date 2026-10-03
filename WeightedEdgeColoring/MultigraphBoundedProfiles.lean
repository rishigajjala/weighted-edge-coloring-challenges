import WeightedEdgeColoring.MultigraphProfileKeptSizes
import WeightedEdgeColoring.ThresholdTransport

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-!
# Bounded finite profile data

This file combines the lossless finite-profile law, reservoir rounding, and
the finite kept-size construction.  The resulting package has a bounded
alphabet of ordinary slot sizes, safe rounded reservoirs, exact raw scaled
marginals and capacity bounds, and the upper-tail inequality needed to
reassign large edges after rounding.
-/

/-- All ordinary slot sizes occurring in a finite law. -/
noncomputable def lawSlotSupport {v : G.V} {m : ℕ} (β : ℝ)
    (outcome : Fin m → Finset (G.StarEdge v)) : Finset ℝ :=
  Finset.univ.biUnion fun k ↦
    (G.largeEdges β (outcome k)).image fun e ↦ G.weight e.1

/-- Expected multiplicity of ordinary slots of size `b` in a finite law. -/
noncomputable def lawSlotMass {v : G.V} {m : ℕ} (p : Fin m → ℝ) (β : ℝ)
    (outcome : Fin m → Finset (G.StarEdge v)) (b : ℝ) : ℝ :=
  ∑ k, ∑ e ∈ G.largeEdges β (outcome k),
    if G.weight e.1 = b then p k else 0

theorem lawSlotMass_nonneg {v : G.V} {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ k, 0 ≤ p k) (β : ℝ)
    (outcome : Fin m → Finset (G.StarEdge v)) (b : ℝ) :
    0 ≤ G.lawSlotMass p β outcome b := by
  unfold lawSlotMass
  apply Finset.sum_nonneg
  intro k _hk
  apply Finset.sum_nonneg
  intro e _he
  split
  · exact hp k
  · exact le_rfl

theorem sum_lawSlotMass {v : G.V} {m : ℕ} (p : Fin m → ℝ) (β : ℝ)
    (outcome : Fin m → Finset (G.StarEdge v)) :
    (∑ b ∈ G.lawSlotSupport β outcome, G.lawSlotMass p β outcome b) =
      ∑ k, p k * ((G.largeEdges β (outcome k)).card : ℝ) := by
  classical
  unfold lawSlotMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Finset.sum_comm]
  calc
    (∑ e ∈ G.largeEdges β (outcome k),
        ∑ b ∈ G.lawSlotSupport β outcome,
          if G.weight e.1 = b then p k else 0) =
        ∑ _e ∈ G.largeEdges β (outcome k), p k := by
      apply Finset.sum_congr rfl
      intro e he
      have hmem : G.weight e.1 ∈ G.lawSlotSupport β outcome := by
        apply Finset.mem_biUnion.mpr
        refine ⟨k, Finset.mem_univ k, ?_⟩
        exact Finset.mem_image.mpr ⟨e, he, rfl⟩
      simp [hmem]
    _ = p k * ((G.largeEdges β (outcome k)).card : ℝ) := by
      simp [mul_comm]

/-- The total expected ordinary-slot multiplicity is at most `1 / β`. -/
theorem sum_lawSlotMass_le_inv {v : G.V} {m : ℕ}
    (p : Fin m → ℝ) (hp : ∀ k, 0 ≤ p k) (hpsum : ∑ k, p k = 1)
    { β : ℝ} (hβ : 0 < β)
    (outcome : Fin m → Finset (G.StarEdge v))
    (hfeasible : ∀ k, G.StarFeasible v (outcome k)) :
    (∑ b ∈ G.lawSlotSupport β outcome, G.lawSlotMass p β outcome b) ≤
      1 / β := by
  rw [G.sum_lawSlotMass p β outcome]
  calc
    (∑ k, p k * ((G.largeEdges β (outcome k)).card : ℝ)) ≤
        ∑ k, p k * (1 / β) := by
      apply Finset.sum_le_sum
      intro k _hk
      apply mul_le_mul_of_nonneg_left _ (hp k)
      apply (le_div_iff₀ hβ).2
      simpa [rawProfile_ordinary] using
        G.rawProfile_card_mul_beta_le_one (hfeasible k)
    _ = 1 / β := by rw [← Finset.sum_mul, hpsum, one_mul]

/-- The canonical expected slot-size measure has the expected upper-tail
interpretation: it counts, with law mass, all ordinary slots above `t`. -/
theorem lawSlotUpperTail_eq {v : G.V} {m : ℕ}
    (p : Fin m → ℝ) (β : ℝ)
    (outcome : Fin m → Finset (G.StarEdge v)) (t : ℝ) :
    slotUpperTail (G.lawSlotSupport β outcome)
        (G.lawSlotMass p β outcome) t =
      ∑ k, ∑ e ∈ G.largeEdges β (outcome k),
        if t ≤ G.weight e.1 then p k else 0 := by
  classical
  unfold slotUpperTail lawSlotMass
  calc
    (∑ b ∈ G.lawSlotSupport β outcome,
        if t ≤ b then
          ∑ k, ∑ e ∈ G.largeEdges β (outcome k),
            if G.weight e.1 = b then p k else 0
        else 0) =
        ∑ b ∈ G.lawSlotSupport β outcome,
          ∑ k, ∑ e ∈ G.largeEdges β (outcome k),
            if t ≤ b ∧ G.weight e.1 = b then p k else 0 := by
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases htb : t ≤ b <;> simp [htb]
    _ = ∑ k, ∑ e ∈ G.largeEdges β (outcome k),
          ∑ b ∈ G.lawSlotSupport β outcome,
            if t ≤ b ∧ G.weight e.1 = b then p k else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ e ∈ G.largeEdges β (outcome k),
          if t ≤ G.weight e.1 then p k else 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro e he
      have hmem : G.weight e.1 ∈ G.lawSlotSupport β outcome := by
        apply Finset.mem_biUnion.mpr
        refine ⟨k, Finset.mem_univ k, ?_⟩
        exact Finset.mem_image.mpr ⟨e, he, rfl⟩
      have hiff (b : ℝ) :
          (t ≤ b ∧ G.weight e.1 = b) ↔
            (b = G.weight e.1 ∧ t ≤ G.weight e.1) := by
        constructor
        · rintro ⟨htb, hbe⟩
          exact ⟨hbe.symm, hbe ▸ htb⟩
        · rintro ⟨hbe, hte⟩
          exact ⟨hbe ▸ hte, hbe.symm⟩
      by_cases ht : t ≤ G.weight e.1
      · simp [hiff, ht, hmem]
      · simp [hiff, ht]

/-- With the manuscript choices `s = 1 - δ` and `q = r = δ / 4`,
the scaled original law and the two repair profiles have total mass at most
one. -/
theorem retained_add_repairs_le_one {δ : ℝ} (hδ : 0 ≤ δ) :
    (1 - δ) * (1 + δ / 4 + δ / 4) ≤ 1 := by
  nlinarith [sq_nonneg δ]

/-- The combined output currently available from the finite-profile
development.  It includes the complete raw occurrence assignment and the
bounded compression data.  `tail_repaired` is the Hall-type supply inequality
for the later large-edge reassignment. -/
structure BoundedProfileLaw {v : G.V} (x : G.StarEdge v → ℝ)
    (s β q r : ℝ) where
  m : ℕ
  probability : Fin m → ℝ
  outcome : Fin m → Finset (G.StarEdge v)
  probability_nonneg : ∀ k, 0 ≤ probability k
  probability_sum : ∑ k, probability k = 1
  feasible : ∀ k, G.StarFeasible v (outcome k)
  original_marginal : ∀ e,
    (∑ k, if e ∈ outcome k then probability k else 0) = x e
  raw_scaled_marginal : ∀ e,
    (∑ k, ((∑ i, G.rawSlotOccurrence s (probability k) β (outcome k) e i) +
      G.rawReservoirOccurrence s (probability k) β (outcome k) e)) = s * x e
  raw_slot_capacity : ∀ k i,
    (∑ e, G.rawSlotOccurrence s (probability k) β (outcome k) e i) ≤ probability k
  raw_reservoir_capacity : ∀ k,
    (∑ e, G.weight e.1 *
      G.rawReservoirOccurrence s (probability k) β (outcome k) e) ≤
        probability k * (G.rawProfile β (outcome k)).reservoir
  kept : Finset ℝ
  round : ℝ → ℝ
  round_le : ∀ b ∈ G.lawSlotSupport β outcome, round b ≤ b
  round_monotone : ∀ a ∈ G.lawSlotSupport β outcome,
    ∀ b ∈ G.lawSlotSupport β outcome, a ≤ b → round a ≤ round b
  round_mem : ∀ b ∈ G.lawSlotSupport β outcome, round b ∈ kept
  round_greatest : ∀ z ∈ kept, ∀ b ∈ G.lawSlotSupport β outcome,
    z ≤ b → z ≤ round b
  open_cell_lt : ∀ z ∈ kept,
    floorCellMass (G.lawSlotSupport β outcome)
      (G.lawSlotMass probability β outcome) round z < q
  kept_card_le : kept.card ≤ ⌊(1 / β) / q⌋₊ + 1
  tail_repaired : ∀ t, t ≤ 1 →
    s * slotUpperTail (G.lawSlotSupport β outcome)
      (G.lawSlotMass probability β outcome) t ≤
    s * roundedSlotUpperTail (G.lawSlotSupport β outcome)
      (G.lawSlotMass probability β outcome) round t +
      s * repairSlotUpperTail q t
  rounded_profile_safe : ∀ k,
    (∑ e ∈ (G.rawProfile β (outcome k)).ordinary, G.weight e.1) +
      roundReservoir r (G.rawProfile β (outcome k)).reservoir ≤ 1
  rounded_reservoir_zero_or_ge : ∀ k,
    roundReservoir r (G.rawProfile β (outcome k)).reservoir = 0 ∨
      r ≤ roundReservoir r (G.rawProfile β (outcome k)).reservoir
  rounded_reservoir_expectation :
    (∑ k, probability k *
      roundReservoir r (G.rawProfile β (outcome k)).reservoir) ≥
    (∑ k, probability k * (G.rawProfile β (outcome k)).reservoir) - r
  tiny_demand_repaired :
    (∑ e, if G.weight e.1 < β then G.weight e.1 * (s * x e) else 0) ≤
      s * (∑ k, probability k *
        roundReservoir r (G.rawProfile β (outcome k)).reservoir) + s * r

/-- Slot buckets used for the large-edge transportation: one bucket for each
original size in the finite support, plus the full-size repair bucket. -/
abbrev CompressedLawSlot {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r) :=
  Option {b // b ∈ G.lawSlotSupport β L.outcome}

noncomputable def compressedLawSlotSize {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r) :
    G.CompressedLawSlot L → ℝ
  | none => 1
  | some b => L.round b.1

noncomputable def compressedLawSlotCapacity {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) : G.CompressedLawSlot L → ℝ
  | none => s * q
  | some b => s * G.lawSlotMass L.probability β L.outcome b.1

/-- Large-edge demand represented directly by the original finite law. -/
noncomputable def largeTransportDemand {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (e : G.StarEdge v) : ℝ :=
  ∑ k, if e ∈ G.largeEdges β (L.outcome k) then s * L.probability k else 0

theorem largeTransportDemand_eq {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (e : G.StarEdge v) :
    G.largeTransportDemand L e =
      if β ≤ G.weight e.1 then s * x e else 0 := by
  classical
  unfold largeTransportDemand
  by_cases he : β ≤ G.weight e.1
  · rw [if_pos he, ← L.original_marginal e, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hek : e ∈ L.outcome k
    · have helarge : e ∈ G.largeEdges β (L.outcome k) :=
        G.mem_largeEdges.mpr ⟨hek, he⟩
      simp [hek, helarge]
    · have helarge : e ∉ G.largeEdges β (L.outcome k) := fun h ↦
        hek (G.largeEdges_subset β (L.outcome k) h)
      simp [hek, helarge]
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro k _hk
    have helarge : e ∉ G.largeEdges β (L.outcome k) := by
      intro h
      exact he (G.mem_largeEdges.mp h).2
    simp [helarge]

theorem largeTransportDemand_nonneg {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (hs : 0 ≤ s) (e : G.StarEdge v) :
    0 ≤ G.largeTransportDemand L e := by
  unfold largeTransportDemand
  exact Finset.sum_nonneg fun k _hk ↦ by
    split
    · exact mul_nonneg hs (L.probability_nonneg k)
    · exact le_rfl

theorem largeTransportDemand_upperTail {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r t : ℝ}
    (L : G.BoundedProfileLaw x s β q r) :
    finiteUpperTail Finset.univ (fun e : G.StarEdge v ↦ G.weight e.1)
        (G.largeTransportDemand L) t =
      s * slotUpperTail (G.lawSlotSupport β L.outcome)
        (G.lawSlotMass L.probability β L.outcome) t := by
  classical
  rw [G.lawSlotUpperTail_eq]
  unfold finiteUpperTail largeTransportDemand
  calc
    (∑ e, if t ≤ G.weight e.1 then
        ∑ k, if e ∈ G.largeEdges β (L.outcome k) then
          s * L.probability k else 0 else 0) =
        ∑ e, ∑ k, if t ≤ G.weight e.1 ∧
          e ∈ G.largeEdges β (L.outcome k) then
            s * L.probability k else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hte : t ≤ G.weight e.1 <;> simp [hte]
    _ = ∑ k, ∑ e, if t ≤ G.weight e.1 ∧
          e ∈ G.largeEdges β (L.outcome k) then
            s * L.probability k else 0 := Finset.sum_comm
    _ = ∑ k, s * (∑ e ∈ G.largeEdges β (L.outcome k),
          if t ≤ G.weight e.1 then L.probability k else 0) := by
      apply Finset.sum_congr rfl
      intro k _hk
      have hlarge_eq : G.largeEdges β (L.outcome k) =
          Finset.univ.filter fun e ↦ e ∈ G.largeEdges β (L.outcome k) := by
        ext e
        simp
      rw [hlarge_eq, Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hte : t ≤ G.weight e.1 <;>
        by_cases hel : e ∈ G.largeEdges β (L.outcome k) <;>
          simp [hte, hel]
    _ = s * (∑ k, ∑ e ∈ G.largeEdges β (L.outcome k),
          if t ≤ G.weight e.1 then L.probability k else 0) := by
      rw [Finset.mul_sum]

theorem compressedLawSlot_upperTail {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r t : ℝ}
    (L : G.BoundedProfileLaw x s β q r) :
    finiteUpperTail Finset.univ (G.compressedLawSlotSize L)
        (G.compressedLawSlotCapacity L) t =
      s * roundedSlotUpperTail (G.lawSlotSupport β L.outcome)
        (G.lawSlotMass L.probability β L.outcome) L.round t +
      s * repairSlotUpperTail q t := by
  classical
  unfold finiteUpperTail compressedLawSlotSize compressedLawSlotCapacity
    roundedSlotUpperTail repairSlotUpperTail
  simp [Finset.mul_sum, mul_ite]
  change ((if t ≤ 1 then s * q else 0) +
      ∑ b : {b // b ∈ G.lawSlotSupport β L.outcome},
        if t ≤ L.round b.1 then
          s * G.lawSlotMass L.probability β L.outcome b.1 else 0) = _
  have hsub :
      (∑ b ∈ G.lawSlotSupport β L.outcome,
        if t ≤ L.round b then
          s * G.lawSlotMass L.probability β L.outcome b else 0) =
      ∑ b : {b // b ∈ G.lawSlotSupport β L.outcome},
        if t ≤ L.round b.1 then
          s * G.lawSlotMass L.probability β L.outcome b.1 else 0 := by
    apply Finset.sum_subtype
    intro b
    rfl
  rw [← hsub]
  ac_rfl

/-- The repaired upper-tail bound produces an actual compatible fractional
assignment of every large-edge demand to the compressed slot buckets. -/
theorem BoundedProfileLaw.exists_largeTransport {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hs : 0 ≤ s) (hq : 0 < q) :
    ∃ assign : G.StarEdge v → G.CompressedLawSlot L → ℝ,
      (∀ e j, 0 ≤ assign e j) ∧
      (∀ e j, 0 < assign e j →
        G.weight e.1 ≤ G.compressedLawSlotSize L j) ∧
      (∀ e, (∑ j, assign e j) =
        if β ≤ G.weight e.1 then s * x e else 0) ∧
      (∀ j, (∑ e, assign e j) ≤ G.compressedLawSlotCapacity L j) := by
  classical
  have hcapacity : ∀ j, 0 ≤ G.compressedLawSlotCapacity L j := by
    intro j
    cases j with
    | none => exact mul_nonneg hs hq.le
    | some b =>
        exact mul_nonneg hs
          (G.lawSlotMass_nonneg L.probability L.probability_nonneg β L.outcome b.1)
  have htail : ∀ t,
      finiteUpperTail Finset.univ (fun e : G.StarEdge v ↦ G.weight e.1)
          (G.largeTransportDemand L) t ≤
        finiteUpperTail Finset.univ (G.compressedLawSlotSize L)
          (G.compressedLawSlotCapacity L) t := by
    intro t
    by_cases ht : t ≤ 1
    · rw [G.largeTransportDemand_upperTail L,
          G.compressedLawSlot_upperTail L]
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
      (G.compressedLawSlotSize L) (G.largeTransportDemand L)
      (G.compressedLawSlotCapacity L)
      (G.largeTransportDemand_nonneg L hs) hcapacity htail with
    ⟨assign, hnonneg, hsupport, hrow, hcol⟩
  refine ⟨assign, hnonneg, hsupport, ?_, hcol⟩
  intro e
  rw [hrow e, G.largeTransportDemand_eq L e]

/-- Every local-polytope point has the combined bounded compression package.
This theorem stops at the exact upper-tail supply inequality; constructing
the post-compression large-edge transportation assignment is a separate
finite matching/flow step. -/
theorem exists_boundedProfileLaw {v : G.V} {x : G.StarEdge v → ℝ}
    (hx : G.IsAverageOfStarFeasibleSets v x)
    {s β q r : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hq : 0 < q) (hr : 0 < r) :
    Nonempty (G.BoundedProfileLaw x s β q r) := by
  classical
  rcases hx with ⟨m, p, outcome, hp, hpsum, hfeasible, horiginal⟩
  have hmarginal : ∀ e,
      (∑ k, ((∑ i, G.rawSlotOccurrence s (p k) β (outcome k) e i) +
        G.rawReservoirOccurrence s (p k) β (outcome k) e)) = s * x e :=
    fun e ↦ G.rawOccurrence_marginal s β p outcome x horiginal e
  have hslot : ∀ k i,
      (∑ e, G.rawSlotOccurrence s (p k) β (outcome k) e i) ≤ p k :=
    fun k i ↦ G.rawSlotOccurrence_capacity hs hs1 (hp k) (outcome k) i
  have hreservoir : ∀ k,
      (∑ e, G.weight e.1 * G.rawReservoirOccurrence s (p k) β (outcome k) e) ≤
        p k * (G.rawProfile β (outcome k)).reservoir :=
    fun k ↦ G.rawReservoirOccurrence_capacity hs hs1 (hp k) (hfeasible k)
  have hmass : ∀ b ∈ G.lawSlotSupport β outcome,
      0 ≤ G.lawSlotMass p β outcome b := by
    intro b _hb
    exact G.lawSlotMass_nonneg p hp β outcome b
  have htotal :
      (∑ b ∈ G.lawSlotSupport β outcome, G.lawSlotMass p β outcome b) ≤
        1 / β :=
    G.sum_lawSlotMass_le_inv p hp hpsum hβ outcome hfeasible
  rcases exists_keptSizes_floor (G.lawSlotSupport β outcome)
      (G.lawSlotMass p β outcome) hmass htotal hq with
    ⟨kept, round, hround, hmono, hrange, hgreatest, hcell, hcard⟩
  have hroundExpectation :
      (∑ k, p k * roundReservoir r (G.rawProfile β (outcome k)).reservoir) ≥
        (∑ k, p k * (G.rawProfile β (outcome k)).reservoir) - r :=
    sum_roundReservoir_ge_sub hr p
      (fun k ↦ (G.rawProfile β (outcome k)).reservoir) hp
      (fun k ↦ G.rawProfile_reservoir_nonneg (hfeasible k)) hpsum
  refine ⟨⟨m, p, outcome, hp, hpsum, hfeasible, horiginal, hmarginal, hslot,
    hreservoir, kept, round, hround, hmono, hrange, hgreatest, hcell,
    hcard, ?_, ?_, ?_, hroundExpectation, ?_⟩⟩
  · intro t ht
    exact scaled_tail_le_rounded_plus_repair
      (G.lawSlotSupport β outcome) kept (G.lawSlotMass p β outcome) round
      hround hmass hmono hrange hgreatest hq hs ht hcell
  · intro k
    exact G.rawProfile_safe_after_roundReservoir hr (hfeasible k)
  · intro k
    exact roundReservoir_eq_zero_or_ge hr
      (G.rawProfile_reservoir_nonneg (hfeasible k))
  · have hdemand_eq :
        (∑ e, if G.weight e.1 < β then G.weight e.1 * (s * x e) else 0) =
          ∑ k, ∑ e, G.weight e.1 *
            G.rawReservoirOccurrence s (p k) β (outcome k) e := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _he_univ
      by_cases hetiny : G.weight e.1 < β
      · have hnotlarge : ∀ k, e ∉ G.largeEdges β (outcome k) := by
          intro k he
          exact (not_lt_of_ge (G.mem_largeEdges.mp he).2) hetiny
        have hslot_zero : ∀ k,
            (∑ i, G.rawSlotOccurrence s (p k) β (outcome k) e i) = 0 := by
          intro k
          rw [G.sum_rawSlotOccurrence]
          simp [hnotlarge k]
        have hres_marginal :
            (∑ k, G.rawReservoirOccurrence s (p k) β (outcome k) e) =
              s * x e := by
          calc
            (∑ k, G.rawReservoirOccurrence s (p k) β (outcome k) e) =
                ∑ k, ((∑ i,
                  G.rawSlotOccurrence s (p k) β (outcome k) e i) +
                    G.rawReservoirOccurrence s (p k) β (outcome k) e) := by
              apply Finset.sum_congr rfl
              intro k _hk
              rw [hslot_zero k, zero_add]
            _ = s * x e := hmarginal e
        simp only [hetiny, if_true]
        rw [← Finset.mul_sum, hres_marginal]
      · have hres_zero : ∀ k,
            G.rawReservoirOccurrence s (p k) β (outcome k) e = 0 := by
          intro k
          unfold rawReservoirOccurrence
          split
          next he => exact (hetiny (G.mem_tinyEdges.mp he).2).elim
          next => rfl
        simp [hetiny, hres_zero]
    have hscaled_capacity :
        (∑ k, ∑ e, G.weight e.1 *
            G.rawReservoirOccurrence s (p k) β (outcome k) e) ≤
          s * (∑ k, p k * (G.rawProfile β (outcome k)).reservoir) := by
      calc
        (∑ k, ∑ e, G.weight e.1 *
            G.rawReservoirOccurrence s (p k) β (outcome k) e) ≤
            ∑ k, (s * p k) * (G.rawProfile β (outcome k)).reservoir := by
          apply Finset.sum_le_sum
          intro k _hk
          rw [G.weighted_rawReservoirOccurrence]
          exact mul_le_mul_of_nonneg_left
            (G.tinyWeight_le_rawProfile_reservoir (hfeasible k))
            (mul_nonneg hs (hp k))
        _ = s * (∑ k, p k * (G.rawProfile β (outcome k)).reservoir) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          ring
    rw [hdemand_eq]
    have hscaled_round := mul_le_mul_of_nonneg_left hroundExpectation hs
    linarith

end WeightedMultigraph
end WeightedEdgeColoring
