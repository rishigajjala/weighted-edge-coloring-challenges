import WeightedEdgeColoring.LocalPolytope
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph)

/-!
# Finite local profiles

This file formalizes the first, lossless layer of the finite-profile lemma.
Given a finite law on feasible subsets of one star, every outcome is replaced
by a profile consisting of one labelled-slot candidate for each edge of weight
at least `β`, and one reservoir containing the unused capacity.  The
occurrence masses below retain a factor `s`; the application uses
`s = 1 - δ`.

The later discretization can merge outcomes with equal rounded profiles.  The
raw identities proved here are independent of that merging step.
-/

section FiniteAggregation

variable {I P : Type*} [Fintype I] [DecidableEq P]

/-- The finite menu obtained by forgetting which outcomes produced the same
profile.  This is the exact compression operation used after discretization. -/
def profileMenu (profile : I → P) : Finset P :=
  Finset.univ.image profile

/-- Push a finite mass function forward along a profile map. -/
def fiberMass (mass : I → ℝ) (profile : I → P) (Q : P) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i ↦ profile i = Q), mass i

theorem profileMenu_card_le (profile : I → P) :
    (profileMenu profile).card ≤ Fintype.card I := by
  simpa [profileMenu] using
    (Finset.card_image_le :
      ((Finset.univ : Finset I).image profile).card ≤ Finset.univ.card)

theorem fiberMass_nonneg {mass : I → ℝ} (hmass : ∀ i, 0 ≤ mass i)
    (profile : I → P) (Q : P) :
    0 ≤ fiberMass mass profile Q := by
  exact Finset.sum_nonneg fun i _hi ↦ hmass i

/-- Aggregating equal profiles preserves the total probability exactly. -/
theorem sum_fiberMass_profileMenu (mass : I → ℝ) (profile : I → P) :
    (∑ Q ∈ profileMenu profile, fiberMass mass profile Q) = ∑ i, mass i := by
  classical
  unfold profileMenu fiberMass
  rw [Finset.sum_fiberwise_eq_sum_filter]
  simp

/-- The same pushforward identity for an arbitrary family of occurrence
masses, pointwise in the resource or edge parameter `a`. -/
theorem sum_fiberMass_profileMenu_apply {A : Type*}
    (mass : I → A → ℝ) (profile : I → P) (a : A) :
    (∑ Q ∈ profileMenu profile, fiberMass (fun i ↦ mass i a) profile Q) =
      ∑ i, mass i a :=
  sum_fiberMass_profileMenu (fun i ↦ mass i a) profile

end FiniteAggregation

/-- The raw profile attached to one feasible star set.  Its ordinary slots
are still labelled by the edges that created them; this makes the lossless
construction canonical. -/
structure RawProfile (v : G.V) where
  ordinary : Finset (G.StarEdge v)
  reservoir : ℝ

/-- Edges whose weights are large enough to receive ordinary slots. -/
noncomputable def largeEdges {v : G.V} (β : ℝ) (S : Finset (G.StarEdge v)) :
    Finset (G.StarEdge v) :=
  S.filter fun e ↦ β ≤ G.weight e.1

/-- Edges assigned to the reservoir. -/
noncomputable def tinyEdges {v : G.V} (β : ℝ) (S : Finset (G.StarEdge v)) :
    Finset (G.StarEdge v) :=
  S.filter fun e ↦ G.weight e.1 < β

/-- The raw profile of a feasible set: large edges become ordinary slots and
all capacity not used by those slots is left in the reservoir. -/
noncomputable def rawProfile {v : G.V} (β : ℝ) (S : Finset (G.StarEdge v)) :
    G.RawProfile v where
  ordinary := G.largeEdges β S
  reservoir := 1 - ∑ e ∈ G.largeEdges β S, G.weight e.1

@[simp] theorem rawProfile_ordinary {v : G.V} (β : ℝ)
    (S : Finset (G.StarEdge v)) :
    (G.rawProfile β S).ordinary = G.largeEdges β S := rfl

@[simp] theorem rawProfile_reservoir {v : G.V} (β : ℝ)
    (S : Finset (G.StarEdge v)) :
    (G.rawProfile β S).reservoir =
      1 - ∑ e ∈ G.largeEdges β S, G.weight e.1 := rfl

theorem largeEdges_subset {v : G.V} (β : ℝ)
    (S : Finset (G.StarEdge v)) : G.largeEdges β S ⊆ S := by
  intro e he
  exact (Finset.mem_filter.mp he).1

theorem tinyEdges_subset {v : G.V} (β : ℝ)
    (S : Finset (G.StarEdge v)) : G.tinyEdges β S ⊆ S := by
  intro e he
  exact (Finset.mem_filter.mp he).1

theorem mem_largeEdges {v : G.V} {β : ℝ}
    {S : Finset (G.StarEdge v)} {e : G.StarEdge v} :
    e ∈ G.largeEdges β S ↔ e ∈ S ∧ β ≤ G.weight e.1 := by
  simp [largeEdges]

theorem mem_tinyEdges {v : G.V} {β : ℝ}
    {S : Finset (G.StarEdge v)} {e : G.StarEdge v} :
    e ∈ G.tinyEdges β S ↔ e ∈ S ∧ G.weight e.1 < β := by
  simp [tinyEdges]

/-- The large and tiny parts partition a star set. -/
theorem sum_largeEdges_add_sum_tinyEdges {v : G.V} (β : ℝ)
    (S : Finset (G.StarEdge v)) :
    (∑ e ∈ G.largeEdges β S, G.weight e.1) +
        ∑ e ∈ G.tinyEdges β S, G.weight e.1 =
      ∑ e ∈ S, G.weight e.1 := by
  classical
  rw [largeEdges, tinyEdges]
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not S
      (fun e : G.StarEdge v ↦ β ≤ G.weight e.1)
      (fun e : G.StarEdge v ↦ G.weight e.1))

/-- A feasible set gives a nonnegative raw reservoir. -/
theorem rawProfile_reservoir_nonneg {v : G.V} {β : ℝ}
    {S : Finset (G.StarEdge v)} (hS : G.StarFeasible v S) :
    0 ≤ (G.rawProfile β S).reservoir := by
  rw [rawProfile_reservoir]
  have hlarge :
      (∑ e ∈ G.largeEdges β S, G.weight e.1) ≤
        ∑ e ∈ S, G.weight e.1 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (G.largeEdges_subset β S) (fun e _heS _heL ↦ G.weight_nonneg e.1)
  exact sub_nonneg.mpr (hlarge.trans hS)

/-- The total weight of reservoir edges fits in the raw reservoir. -/
theorem tinyWeight_le_rawProfile_reservoir {v : G.V} {β : ℝ}
    {S : Finset (G.StarEdge v)} (hS : G.StarFeasible v S) :
    (∑ e ∈ G.tinyEdges β S, G.weight e.1) ≤
      (G.rawProfile β S).reservoir := by
  rw [rawProfile_reservoir]
  have hpartition := G.sum_largeEdges_add_sum_tinyEdges β S
  change (∑ e ∈ S, G.weight e.1) ≤ 1 at hS
  linarith

/-- Any outcome containing a tiny edge has a positive reservoir. -/
theorem rawProfile_reservoir_pos_of_mem_tiny {v : G.V} {β : ℝ}
    {S : Finset (G.StarEdge v)} (hS : G.StarFeasible v S)
    {e : G.StarEdge v} (he : e ∈ G.tinyEdges β S) :
    0 < (G.rawProfile β S).reservoir := by
  have hle := G.tinyWeight_le_rawProfile_reservoir (β := β) hS
  have hepos : 0 < G.weight e.1 := G.weight_pos e.1
  have hweight : G.weight e.1 ≤
      ∑ f ∈ G.tinyEdges β S, G.weight f.1 := by
    exact Finset.single_le_sum
      (fun f _hf ↦ G.weight_nonneg f.1) he
  exact lt_of_lt_of_le hepos (hweight.trans hle)

/-- A raw profile contains at most `1 / β` ordinary slots in the weighted
sense.  This avoids integer rounding and is the form needed to derive any
chosen natural-number bound. -/
theorem rawProfile_card_mul_beta_le_one {v : G.V} {β : ℝ}
    {S : Finset (G.StarEdge v)}
    (hS : G.StarFeasible v S) :
    ((G.rawProfile β S).ordinary.card : ℝ) * β ≤ 1 := by
  rw [rawProfile_ordinary]
  have hterm : ∀ e ∈ G.largeEdges β S, β ≤ G.weight e.1 := by
    intro e he
    exact (G.mem_largeEdges.mp he).2
  calc
    ((G.largeEdges β S).card : ℝ) * β =
        ∑ _e ∈ G.largeEdges β S, β := by simp
    _ ≤ ∑ e ∈ G.largeEdges β S, G.weight e.1 := by
      exact Finset.sum_le_sum hterm
    _ ≤ ∑ e ∈ S, G.weight e.1 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (G.largeEdges_subset β S) (fun e _heS _heL ↦ G.weight_nonneg e.1)
    _ ≤ 1 := hS

/-- A convenient natural-number version of the large-slot bound. -/
theorem rawProfile_card_lt {v : G.V} {β : ℝ} (hβ : 0 < β)
    {S : Finset (G.StarEdge v)} (hS : G.StarFeasible v S)
    (K : ℕ) (hK : 1 < (K : ℝ) * β) :
    (G.rawProfile β S).ordinary.card < K := by
  by_contra h
  have hKcard : K ≤ (G.rawProfile β S).ordinary.card := Nat.le_of_not_gt h
  have hcast : (K : ℝ) ≤ ((G.rawProfile β S).ordinary.card : ℝ) := by
    exact_mod_cast hKcard
  have hmul : (K : ℝ) * β ≤
      ((G.rawProfile β S).ordinary.card : ℝ) * β :=
    mul_le_mul_of_nonneg_right hcast hβ.le
  exact (not_lt_of_ge
    (hmul.trans (G.rawProfile_card_mul_beta_le_one hS))) hK

/-- Mass with which edge `e` uses ordinary slot `i` in one raw outcome. -/
noncomputable def rawSlotOccurrence {v : G.V} (s p β : ℝ)
    (S : Finset (G.StarEdge v))
    (e i : G.StarEdge v) : ℝ :=
  if e = i then if i ∈ G.largeEdges β S then s * p else 0 else 0

/-- Mass with which edge `e` uses the reservoir in one raw outcome. -/
noncomputable def rawReservoirOccurrence {v : G.V} (s p β : ℝ)
    (S : Finset (G.StarEdge v)) (e : G.StarEdge v) : ℝ :=
  if e ∈ G.tinyEdges β S then s * p else 0

theorem rawSlotOccurrence_nonneg {v : G.V} {s p β : ℝ}
    (hs : 0 ≤ s) (hp : 0 ≤ p) (S : Finset (G.StarEdge v))
    (e i : G.StarEdge v) :
    0 ≤ G.rawSlotOccurrence s p β S e i := by
  by_cases hei : e = i <;>
    by_cases hi : i ∈ G.largeEdges β S <;>
      simp [rawSlotOccurrence, hei, hi, mul_nonneg hs hp]

theorem rawReservoirOccurrence_nonneg {v : G.V} {s p β : ℝ}
    (hs : 0 ≤ s) (hp : 0 ≤ p) (S : Finset (G.StarEdge v))
    (e : G.StarEdge v) :
    0 ≤ G.rawReservoirOccurrence s p β S e := by
  by_cases he : e ∈ G.tinyEdges β S
  · simp [rawReservoirOccurrence, he, mul_nonneg hs hp]
  · simp [rawReservoirOccurrence, he]

/-- Summing all ordinary resources in one outcome leaves precisely the large
edge occurrence. -/
theorem sum_rawSlotOccurrence {v : G.V} (s p β : ℝ)
    (S : Finset (G.StarEdge v)) (e : G.StarEdge v) :
    (∑ i, G.rawSlotOccurrence s p β S e i) =
      if e ∈ G.largeEdges β S then s * p else 0 := by
  classical
  simp [rawSlotOccurrence]

/-- In one outcome every selected edge has total occurrence `s*p`, in
exactly one of the ordinary or reservoir resource classes. -/
theorem rawOccurrence_one_outcome {v : G.V} (s p β : ℝ)
    (S : Finset (G.StarEdge v)) (e : G.StarEdge v) :
    (∑ i, G.rawSlotOccurrence s p β S e i) +
        G.rawReservoirOccurrence s p β S e =
      if e ∈ S then s * p else 0 := by
  classical
  rw [G.sum_rawSlotOccurrence s p β S e]
  by_cases he : e ∈ S
  · by_cases hlarge : β ≤ G.weight e.1
    · have hel : e ∈ G.largeEdges β S := G.mem_largeEdges.mpr ⟨he, hlarge⟩
      have het : e ∉ G.tinyEdges β S := by
        intro het
        exact (not_lt_of_ge hlarge) (G.mem_tinyEdges.mp het).2
      simp [hel, het, he, rawReservoirOccurrence]
    · have htiny : e ∈ G.tinyEdges β S :=
        G.mem_tinyEdges.mpr ⟨he, lt_of_not_ge hlarge⟩
      have hel : e ∉ G.largeEdges β S := by
        intro hel
        exact hlarge (G.mem_largeEdges.mp hel).2
      simp [hel, htiny, he, rawReservoirOccurrence]
  · have hel : e ∉ G.largeEdges β S := fun h ↦ he (G.largeEdges_subset β S h)
    have het : e ∉ G.tinyEdges β S := fun h ↦ he (G.tinyEdges_subset β S h)
    simp [hel, het, he, rawReservoirOccurrence]

/-- Exact scaled marginals for the raw construction. -/
theorem rawOccurrence_marginal {v : G.V} {m : ℕ}
    (s β : ℝ) (p : Fin m → ℝ)
    (outcome : Fin m → Finset (G.StarEdge v))
    (x : G.StarEdge v → ℝ)
    (hmarginal : ∀ e,
      (∑ k, if e ∈ outcome k then p k else 0) = x e)
    (e : G.StarEdge v) :
    (∑ k, ((∑ i, G.rawSlotOccurrence s (p k) β (outcome k) e i) +
      G.rawReservoirOccurrence s (p k) β (outcome k) e)) = s * x e := by
  calc
    (∑ k, ((∑ i, G.rawSlotOccurrence s (p k) β (outcome k) e i) +
      G.rawReservoirOccurrence s (p k) β (outcome k) e)) =
        ∑ k, if e ∈ outcome k then s * p k else 0 := by
          apply Finset.sum_congr rfl
          intro k _hk
          exact G.rawOccurrence_one_outcome s (p k) β (outcome k) e
    _ = s * ∑ k, if e ∈ outcome k then p k else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      by_cases he : e ∈ outcome k <;> simp [he]
    _ = s * x e := by rw [hmarginal e]

/-- One ordinary occurrence cannot exceed the complete scaled marginal of
that edge.  This is the pointwise bound stated at the end of the finite
profiles lemma, before equal profiles are aggregated. -/
theorem rawSlotOccurrence_le_scaledMarginal {v : G.V} {m : ℕ}
    {s β : ℝ} (hs : 0 ≤ s) (p : Fin m → ℝ) (hp : ∀ k, 0 ≤ p k)
    (outcome : Fin m → Finset (G.StarEdge v))
    (x : G.StarEdge v → ℝ)
    (hmarginal : ∀ e,
      (∑ k, if e ∈ outcome k then p k else 0) = x e)
    (e : G.StarEdge v) (k : Fin m) (i : G.StarEdge v) :
    G.rawSlotOccurrence s (p k) β (outcome k) e i ≤ s * x e := by
  rw [← G.rawOccurrence_marginal s β p outcome x hmarginal e]
  have hslot : G.rawSlotOccurrence s (p k) β (outcome k) e i ≤
      ∑ j, G.rawSlotOccurrence s (p k) β (outcome k) e j := by
    exact Finset.single_le_sum
      (fun j _hj ↦ G.rawSlotOccurrence_nonneg hs (hp k) (outcome k) e j)
      (Finset.mem_univ i)
  have hwithin : G.rawSlotOccurrence s (p k) β (outcome k) e i ≤
      (∑ j, G.rawSlotOccurrence s (p k) β (outcome k) e j) +
        G.rawReservoirOccurrence s (p k) β (outcome k) e :=
    hslot.trans (le_add_of_nonneg_right
      (G.rawReservoirOccurrence_nonneg hs (hp k) (outcome k) e))
  exact hwithin.trans (Finset.single_le_sum
    (fun l _hl ↦ add_nonneg
      (Finset.sum_nonneg fun j _hj ↦
        G.rawSlotOccurrence_nonneg hs (hp l) (outcome l) e j)
      (G.rawReservoirOccurrence_nonneg hs (hp l) (outcome l) e))
    (Finset.mem_univ k))

/-- The reservoir occurrence has the same pointwise marginal bound. -/
theorem rawReservoirOccurrence_le_scaledMarginal {v : G.V} {m : ℕ}
    {s β : ℝ} (hs : 0 ≤ s) (p : Fin m → ℝ) (hp : ∀ k, 0 ≤ p k)
    (outcome : Fin m → Finset (G.StarEdge v))
    (x : G.StarEdge v → ℝ)
    (hmarginal : ∀ e,
      (∑ k, if e ∈ outcome k then p k else 0) = x e)
    (e : G.StarEdge v) (k : Fin m) :
    G.rawReservoirOccurrence s (p k) β (outcome k) e ≤ s * x e := by
  rw [← G.rawOccurrence_marginal s β p outcome x hmarginal e]
  have hwithin : G.rawReservoirOccurrence s (p k) β (outcome k) e ≤
      (∑ j, G.rawSlotOccurrence s (p k) β (outcome k) e j) +
        G.rawReservoirOccurrence s (p k) β (outcome k) e :=
    le_add_of_nonneg_left (Finset.sum_nonneg fun j _hj ↦
      G.rawSlotOccurrence_nonneg hs (hp k) (outcome k) e j)
  exact hwithin.trans (Finset.single_le_sum
    (fun l _hl ↦ add_nonneg
      (Finset.sum_nonneg fun j _hj ↦
        G.rawSlotOccurrence_nonneg hs (hp l) (outcome l) e j)
      (G.rawReservoirOccurrence_nonneg hs (hp l) (outcome l) e))
    (Finset.mem_univ k))

/-- The total use of an ordinary raw slot is either zero or exactly `s*p`. -/
theorem sum_rawSlotOccurrence_edge {v : G.V} (s p β : ℝ)
    (S : Finset (G.StarEdge v)) (i : G.StarEdge v) :
    (∑ e, G.rawSlotOccurrence s p β S e i) =
      if i ∈ G.largeEdges β S then s * p else 0 := by
  classical
  simp [rawSlotOccurrence]

/-- Ordinary-slot capacity in every raw outcome. -/
theorem rawSlotOccurrence_capacity {v : G.V} {s p β : ℝ}
    (_hs : 0 ≤ s) (hs1 : s ≤ 1) (hp : 0 ≤ p)
    (S : Finset (G.StarEdge v)) (i : G.StarEdge v) :
    (∑ e, G.rawSlotOccurrence s p β S e i) ≤ p := by
  rw [G.sum_rawSlotOccurrence_edge s p β S i]
  split
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hs1 hp
  · exact hp

/-- The weighted reservoir occurrence is the retained fraction of the tiny
weight in that outcome. -/
theorem weighted_rawReservoirOccurrence {v : G.V} (s p β : ℝ)
    (S : Finset (G.StarEdge v)) :
    (∑ e, G.weight e.1 * G.rawReservoirOccurrence s p β S e) =
      (s * p) * ∑ e ∈ G.tinyEdges β S, G.weight e.1 := by
  classical
  simp [rawReservoirOccurrence, Finset.mul_sum, mul_comm]

/-- Reservoir capacity in every raw outcome. -/
theorem rawReservoirOccurrence_capacity {v : G.V} {s p β : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hp : 0 ≤ p)
    {S : Finset (G.StarEdge v)} (hS : G.StarFeasible v S) :
    (∑ e, G.weight e.1 * G.rawReservoirOccurrence s p β S e) ≤
      p * (G.rawProfile β S).reservoir := by
  rw [G.weighted_rawReservoirOccurrence s p β S]
  have hsp : 0 ≤ s * p := mul_nonneg hs hp
  have hR := G.rawProfile_reservoir_nonneg (β := β) hS
  calc
    (s * p) * ∑ e ∈ G.tinyEdges β S, G.weight e.1 ≤
        (s * p) * (G.rawProfile β S).reservoir := by
      exact mul_le_mul_of_nonneg_left
        (G.tinyWeight_le_rawProfile_reservoir hS) hsp
    _ ≤ p * (G.rawProfile β S).reservoir := by
      have hsp_le : s * p ≤ p := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hs1 hp
      exact mul_le_mul_of_nonneg_right hsp_le hR

/-- Ordinary occurrences use a present slot, and the edge fits that slot
exactly (its raw slot size is its own weight). -/
theorem rawSlotOccurrence_support {v : G.V} {s p β : ℝ}
    {S : Finset (G.StarEdge v)} {e i : G.StarEdge v}
    (hpos : 0 < G.rawSlotOccurrence s p β S e i) :
    e = i ∧ i ∈ (G.rawProfile β S).ordinary ∧
      G.weight e.1 ≤ G.weight i.1 := by
  simp only [rawSlotOccurrence] at hpos
  split at hpos
  next hei =>
    split at hpos
    next hi => exact ⟨hei, hi, le_of_eq (congrArg (fun z ↦ G.weight z.1) hei)⟩
    next => simp at hpos
  next => simp at hpos

/-- A positive reservoir occurrence is tiny and uses a positive reservoir. -/
theorem rawReservoirOccurrence_support {v : G.V} {s p β : ℝ}
    {S : Finset (G.StarEdge v)} (hS : G.StarFeasible v S)
    {e : G.StarEdge v}
    (hpos : 0 < G.rawReservoirOccurrence s p β S e) :
    G.weight e.1 < β ∧ 0 < (G.rawProfile β S).reservoir := by
  simp only [rawReservoirOccurrence] at hpos
  split at hpos
  next he =>
    exact ⟨(G.mem_tinyEdges.mp he).2,
      G.rawProfile_reservoir_pos_of_mem_tiny hS he⟩
  next => simp at hpos

/-- Every raw occurrence is bounded by the scaled marginal contribution of
its edge in that outcome. -/
theorem rawSlotOccurrence_le {v : G.V} {s p β : ℝ}
    (hs : 0 ≤ s) (hp : 0 ≤ p) (S : Finset (G.StarEdge v))
    (e i : G.StarEdge v) :
    G.rawSlotOccurrence s p β S e i ≤ s * p := by
  by_cases hei : e = i <;>
    by_cases hi : i ∈ G.largeEdges β S <;>
      simp [rawSlotOccurrence, hei, hi, mul_nonneg hs hp]

theorem rawReservoirOccurrence_le {v : G.V} {s p β : ℝ}
    (hs : 0 ≤ s) (hp : 0 ≤ p) (S : Finset (G.StarEdge v))
    (e : G.StarEdge v) :
    G.rawReservoirOccurrence s p β S e ≤ s * p := by
  by_cases he : e ∈ G.tinyEdges β S
  · simp [rawReservoirOccurrence, he]
  · simp [rawReservoirOccurrence, he, mul_nonneg hs hp]

/-- Packaged raw-profile conclusion directly from the finite-law witness in
`IsAverageOfStarFeasibleSets`.  It exposes the same witness because the
subsequent discretization acts on its finite family of raw profiles. -/
theorem exists_rawProfile_law {v : G.V} {x : G.StarEdge v → ℝ}
    (hx : G.IsAverageOfStarFeasibleSets v x)
    {s β : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ (m : ℕ) (p : Fin m → ℝ)
      (outcome : Fin m → Finset (G.StarEdge v)),
      (∀ k, 0 ≤ p k) ∧
      (∑ k, p k = 1) ∧
      (∀ k, G.StarFeasible v (outcome k)) ∧
      (∀ e,
        (∑ k, ((∑ i, G.rawSlotOccurrence s (p k) β (outcome k) e i) +
          G.rawReservoirOccurrence s (p k) β (outcome k) e)) = s * x e) ∧
      (∀ k i, (∑ e, G.rawSlotOccurrence s (p k) β (outcome k) e i) ≤ p k) ∧
      (∀ k,
        (∑ e, G.weight e.1 *
          G.rawReservoirOccurrence s (p k) β (outcome k) e) ≤
            p k * (G.rawProfile β (outcome k)).reservoir) := by
  rcases hx with ⟨m, p, outcome, hp, hpsum, hfeasible, hmarginal⟩
  refine ⟨m, p, outcome, hp, hpsum, hfeasible, ?_, ?_, ?_⟩
  · exact fun e ↦ G.rawOccurrence_marginal s β p outcome x hmarginal e
  · intro k i
    exact G.rawSlotOccurrence_capacity hs hs1 (hp k) (outcome k) i
  · intro k
    exact G.rawReservoirOccurrence_capacity hs hs1 (hp k) (hfeasible k)

end WeightedSimpleGraph
end WeightedEdgeColoring
