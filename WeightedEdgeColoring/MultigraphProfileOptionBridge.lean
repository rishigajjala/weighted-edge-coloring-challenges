import WeightedEdgeColoring.MultigraphProfileRepresentation
import WeightedEdgeColoring.ProfileOptionBridge
import WeightedEdgeColoring.OrdinarySlotOptions

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})

/-!
# From bounded profile realizations to ordinary option masses

The profile theorem produces a finite, vertex-dependent type of concrete
places.  This file pads those types into one parameter-only `Fin K`, and
then couples the two endpoint assignments of an edge.  No simultaneous
choice of profiles is used here.
-/

/-- A parameter-only upper bound for the number of explicit ordinary places
in one bounded profile realization. -/
def explicitLargeSlotBound (β q r : ℝ) : ℕ :=
  1 +
    ((⌊1 / β⌋₊ + 1) ^ (⌊(1 / β) / q⌋₊ + 1) *
        (⌊1 / r⌋₊ + 1) + 1) *
      (⌊(1 / β) / q⌋₊ + 1) * (⌊1 / β⌋₊)

theorem explicitLargeSlot_card_le {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr) :
    Fintype.card (G.ExplicitLargeSlot R.law hβ hr) ≤
      explicitLargeSlotBound β q r := by
  classical
  let A := ⌊1 / β⌋₊
  let Z := ⌊(1 / β) / q⌋₊ + 1
  let M := (A + 1) ^ Z * (⌊1 / r⌋₊ + 1) + 1
  have hmult : ∀ (P : {P // P ∈ G.roundedProfileMenu R.law hβ hr})
      (z : {z // z ∈ R.law.kept}), (P.1.1 z).val ≤ A := by
    intro P z
    rcases Finset.mem_image.mp P.2 with ⟨k, _hk, hk⟩
    rw [← hk]
    exact G.roundedMultiplicity_le_floor R.law hβ k z
  have hmenu : Fintype.card {P // P ∈ G.roundedProfileMenu R.law hβ hr} ≤ M := by
    have hidx := R.menu_card_le
    have hidx' :
        Fintype.card {P // P ∈ G.roundedProfileMenu R.law hβ hr} + 1 ≤ M := by
      simpa only [RoundedProfileIndex, Fintype.card_option, Fintype.card_coe,
        M, A, Z] using hidx
    omega
  have hkept : Fintype.card {z // z ∈ R.law.kept} ≤ Z := by
    simpa [Z, Fintype.card_coe] using R.law.kept_card_le
  simp only [ExplicitLargeSlot, Fintype.card_option, Fintype.card_sigma,
    Fintype.card_fin]
  calc
    (∑ P : {P // P ∈ G.roundedProfileMenu R.law hβ hr},
        ∑ z : {z // z ∈ R.law.kept}, (P.1.1 z).val) + 1
        ≤ (∑ _P : {P // P ∈ G.roundedProfileMenu R.law hβ hr},
            ∑ _z : {z // z ∈ R.law.kept}, A) + 1 := by
          apply Nat.add_le_add_right
          apply Finset.sum_le_sum
          intro P _hP
          apply Finset.sum_le_sum
          intro z _hz
          exact hmult P z
    _ = Fintype.card {P // P ∈ G.roundedProfileMenu R.law hβ hr} *
          (Fintype.card {z // z ∈ R.law.kept} * A) + 1 := by simp
    _ ≤ M * (Z * A) + 1 := by gcongr
    _ = explicitLargeSlotBound β q r := by
      simp [explicitLargeSlotBound, M, Z, A, Nat.mul_assoc, Nat.add_comm]

/-- Canonical padding of the realization's dependent place type into the
common parameter-only range. -/
def paddedLargeSlotCode {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr) :
    G.ExplicitLargeSlot R.law hβ hr → Fin (explicitLargeSlotBound β q r) :=
  fun j ↦ Fin.castLE (G.explicitLargeSlot_card_le R)
    (Fintype.equivFin (G.ExplicitLargeSlot R.law hβ hr) j)

theorem paddedLargeSlotCode_injective {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr) :
    Function.Injective (G.paddedLargeSlotCode R) := by
  intro i j hij
  apply (Fintype.equivFin (G.ExplicitLargeSlot R.law hβ hr)).injective
  apply Fin.ext
  have hv := congrArg Fin.val hij
  change ((Fintype.equivFin (G.ExplicitLargeSlot R.law hβ hr)) i).val =
    ((Fintype.equivFin (G.ExplicitLargeSlot R.law hβ hr)) j).val at hv
  exact hv

/-- Assignment mass at a padded place.  Codes not used by the realization
carry zero mass. -/
def paddedLargeAssign {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr)
    (e : G.StarEdge v) (i : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  ∑ j, if G.paddedLargeSlotCode R j = i then R.largeAssign e j else 0

/-- Capacity of a padded place. -/
def paddedLargeCapacity {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr)
    (i : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  ∑ j, if G.paddedLargeSlotCode R j = i then
    G.explicitLargeSlotCapacity R.law hβ hr j else 0

theorem paddedLargeAssign_nonneg {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr)
    (e : G.StarEdge v) (i : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.paddedLargeAssign R e i := by
  exact Finset.sum_nonneg fun j _ ↦ by
    split <;> simp_all [R.largeAssign_nonneg]

theorem sum_paddedLargeAssign {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr)
    (e : G.StarEdge v) :
    (∑ i, G.paddedLargeAssign R e i) =
      if β ≤ G.weight e.1 then s * x e else 0 := by
  classical
  rw [← R.largeAssign_marginal e]
  unfold paddedLargeAssign
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  simp

theorem paddedLargeAssign_capacity {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr)
    (i : Fin (explicitLargeSlotBound β q r)) :
    (∑ e, G.paddedLargeAssign R e i) ≤ G.paddedLargeCapacity R i := by
  classical
  unfold paddedLargeAssign paddedLargeCapacity
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _hj
  by_cases hj : G.paddedLargeSlotCode R j = i
  · simp only [hj, if_true]
    exact R.largeAssign_capacity j
  · simp [hj]

/-- Looking up a code that is actually used recovers exactly the capacity of
the corresponding concrete place. -/
theorem paddedLargeCapacity_code {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr)
    (j : G.ExplicitLargeSlot R.law hβ hr) :
    G.paddedLargeCapacity R (G.paddedLargeSlotCode R j) =
      G.explicitLargeSlotCapacity R.law hβ hr j := by
  classical
  unfold paddedLargeCapacity
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _hk hkj
    have hcode : G.paddedLargeSlotCode R k ≠ G.paddedLargeSlotCode R j := by
      intro h
      exact hkj (G.paddedLargeSlotCode_injective R h)
    simp [hcode]
  · simp

/-- One edge's mass at a padded place is bounded by that place's full local
capacity. -/
theorem paddedLargeAssign_le_capacity {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr)
    (e : G.StarEdge v) (i : Fin (explicitLargeSlotBound β q r)) :
    G.paddedLargeAssign R e i ≤ G.paddedLargeCapacity R i := by
  calc
    G.paddedLargeAssign R e i ≤ ∑ f, G.paddedLargeAssign R f i :=
      Finset.single_le_sum
        (fun f _ ↦ G.paddedLargeAssign_nonneg R f i)
        (Finset.mem_univ e)
    _ ≤ G.paddedLargeCapacity R i := G.paddedLargeAssign_capacity R i

/-- Every aggregated profile atom has probability at most one. -/
theorem roundedProfileMass_le_one {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (hβ : 0 < β) (hr : 0 < r)
    (P : {P // P ∈ G.roundedProfileMenu L hβ hr}) :
    G.roundedProfileMass L hβ hr P.1 ≤ 1 := by
  have hsingle : G.roundedProfileMass L hβ hr P.1 ≤
      ∑ Q ∈ G.roundedProfileMenu L hβ hr,
        G.roundedProfileMass L hβ hr Q := by
    exact Finset.single_le_sum
      (fun Q _ ↦ G.roundedProfileMass_nonneg L hβ hr Q) P.2
  rwa [G.sum_roundedProfileMass L hβ hr] at hsingle

/-- The repair place has capacity exactly `s*q`. -/
theorem paddedLargeCapacity_repair {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr) :
    G.paddedLargeCapacity R (G.paddedLargeSlotCode R none) = s * q := by
  rw [G.paddedLargeCapacity_code R none]
  rfl

/-- Every non-repair padded place has capacity at most `s`.  This includes
unused padding codes, whose capacity is zero. -/
theorem paddedLargeCapacity_le_s_of_ne_repair {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr) (hs : 0 ≤ s)
    (i : Fin (explicitLargeSlotBound β q r))
    (hi : i ≠ G.paddedLargeSlotCode R none) :
    G.paddedLargeCapacity R i ≤ s := by
  classical
  by_cases hex : ∃ j, G.paddedLargeSlotCode R j = i
  · rcases hex with ⟨j, hj⟩
    cases j with
    | none => exact (hi hj.symm).elim
    | some j =>
        rw [← hj, G.paddedLargeCapacity_code R]
        change s * G.roundedProfileMass R.law hβ hr j.1.1 ≤ s
        calc
          s * G.roundedProfileMass R.law hβ hr j.1.1 ≤ s * 1 :=
            mul_le_mul_of_nonneg_left
              (G.roundedProfileMass_le_one R.law hβ hr j.1) hs
          _ = s := mul_one s
  · unfold paddedLargeCapacity
    have hzero : ∀ j : G.ExplicitLargeSlot R.law hβ hr,
        (if G.paddedLargeSlotCode R j = i then
          G.explicitLargeSlotCapacity R.law hβ hr j else 0) = 0 := by
      intro j
      have hne : G.paddedLargeSlotCode R j ≠ i := fun h ↦ hex ⟨j, h⟩
      simp [hne]
    simp_rw [hzero]
    simpa using hs

/-- Parameter-only capacity bound.  It is sharp for the present interface:
the repair place may have capacity `s*q`, while one aggregated ordinary
profile may have probability one and hence capacity `s`. -/
theorem paddedLargeCapacity_le_parameter {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr)
    (hs : 0 ≤ s)
    (i : Fin (explicitLargeSlotBound β q r)) :
    G.paddedLargeCapacity R i ≤ s * max q 1 := by
  by_cases hi : i = G.paddedLargeSlotCode R none
  · rw [hi, G.paddedLargeCapacity_repair R]
    exact mul_le_mul_of_nonneg_left (le_max_left q 1) hs
  · calc
      G.paddedLargeCapacity R i ≤ s :=
        G.paddedLargeCapacity_le_s_of_ne_repair R hs i hi
      _ = s * 1 := (mul_one s).symm
      _ ≤ s * max q 1 :=
        mul_le_mul_of_nonneg_left (le_max_right q 1) hs

theorem paddedLargeAssign_pos_compatible {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr)
    (e : G.StarEdge v) (i : Fin (explicitLargeSlotBound β q r))
    (hi : 0 < G.paddedLargeAssign R e i) :
    ∃ j, G.paddedLargeSlotCode R j = i ∧ 0 < R.largeAssign e j ∧
      G.weight e.1 ≤ G.explicitLargeSlotSize R.law hβ hr j := by
  classical
  unfold paddedLargeAssign at hi
  have hnonneg : ∀ j ∈ (Finset.univ : Finset (G.ExplicitLargeSlot R.law hβ hr)),
      0 ≤ (if G.paddedLargeSlotCode R j = i then R.largeAssign e j else 0) := by
    intro j _hj
    split
    · exact R.largeAssign_nonneg e j
    · exact le_rfl
  rcases (Finset.sum_pos_iff_of_nonneg hnonneg).mp hi with ⟨j, _hj, hj⟩
  by_cases hcode : G.paddedLargeSlotCode R j = i
  · simp only [hcode, if_true] at hj
    exact ⟨j, hcode, hj, R.largeAssign_compatible e j hj⟩
  · simp [hcode] at hj

end WeightedMultigraph


/-! The algebraic coupling declarations are shared with `ProfileOptionBridge`. -/

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})
variable {Color : Type w} [Fintype Color] [DecidableEq Color]

/-- The canonical copy of an edge in its first endpoint star. -/
def fstStarEdge (e : G.E) : G.StarEdge (G.fst e) := ⟨e, Or.inl rfl⟩

/-- The canonical copy of an edge in its second endpoint star. -/
def sndStarEdge (e : G.E) : G.StarEdge (G.snd e) := ⟨e, Or.inr rfl⟩

variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → Color → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- Local star-polytope witnesses give a simultaneous family of explicit
bounded profile realizations, one for every vertex and colour. -/
theorem exists_boundedProfileRealization_family
    (hlocal : ∀ v c,
      G.IsAverageOfStarFeasibleSets v
        (fun e : G.StarEdge v ↦ proposal e.1 c))
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hq : 0 < q) :
    Nonempty (∀ v c, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr) := by
  classical
  exact ⟨fun v c ↦ Classical.choice
    (G.exists_boundedProfileRealization (hlocal v c) hs hs1 hβ hq hr)⟩

/-- Retained mass of one edge in one colour. -/
def profileRetainedMass (s β : ℝ) (proposal : G.E → Color → ℝ)
    (e : G.E) (c : Color) : ℝ :=
  if β ≤ G.weight e then s * proposal e c else 0

/-- The ordinary option array obtained by coupling the two padded endpoint
assignments. -/
def profileOrdinaryMass (e : G.E) (c : Color)
    (i j : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  endpointPairMass (G.profileRetainedMass s β proposal e c)
    (G.paddedLargeAssign (R (G.fst e) c) (G.fstStarEdge e))
    (G.paddedLargeAssign (R (G.snd e) c) (G.sndStarEdge e)) i j

theorem profileRetainedMass_nonneg
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c) (e : G.E) (c : Color) :
    0 ≤ G.profileRetainedMass s β proposal e c := by
  unfold profileRetainedMass
  split
  · exact mul_nonneg hs (hp e c)
  · exact le_rfl

theorem profileOrdinaryMass_nonneg
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color) (i j : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.profileOrdinaryMass proposal R e c i j := by
  unfold profileOrdinaryMass
  apply endpointPairMass_nonneg
  · exact G.profileRetainedMass_nonneg proposal hs hp e c
  · exact G.paddedLargeAssign_nonneg (R (G.fst e) c) (G.fstStarEdge e)
  · exact G.paddedLargeAssign_nonneg (R (G.snd e) c) (G.sndStarEdge e)

theorem sum_profileOrdinaryMass_row (e : G.E) (c : Color)
    (i : Fin (explicitLargeSlotBound β q r)) :
    (∑ j, G.profileOrdinaryMass proposal R e c i j) =
      G.paddedLargeAssign (R (G.fst e) c) (G.fstStarEdge e) i := by
  unfold profileOrdinaryMass
  apply sum_endpointPairMass_right
  · exact G.paddedLargeAssign_nonneg (R (G.fst e) c) (G.fstStarEdge e)
  · exact G.paddedLargeAssign_nonneg (R (G.snd e) c) (G.sndStarEdge e)
  · exact G.sum_paddedLargeAssign (R (G.fst e) c) (G.fstStarEdge e)
  · exact G.sum_paddedLargeAssign (R (G.snd e) c) (G.sndStarEdge e)

theorem sum_profileOrdinaryMass_col (e : G.E) (c : Color)
    (j : Fin (explicitLargeSlotBound β q r)) :
    (∑ i, G.profileOrdinaryMass proposal R e c i j) =
      G.paddedLargeAssign (R (G.snd e) c) (G.sndStarEdge e) j := by
  unfold profileOrdinaryMass
  apply sum_endpointPairMass_left
  · exact G.paddedLargeAssign_nonneg (R (G.fst e) c) (G.fstStarEdge e)
  · exact G.paddedLargeAssign_nonneg (R (G.snd e) c) (G.sndStarEdge e)
  · exact G.sum_paddedLargeAssign (R (G.fst e) c) (G.fstStarEdge e)
  · exact G.sum_paddedLargeAssign (R (G.snd e) c) (G.sndStarEdge e)

theorem sum_profileOrdinaryMass_color (e : G.E) (c : Color) :
    (∑ i, ∑ j, G.profileOrdinaryMass proposal R e c i j) =
      G.profileRetainedMass s β proposal e c := by
  unfold profileOrdinaryMass
  apply sum_endpointPairMass
  · exact G.paddedLargeAssign_nonneg (R (G.fst e) c) (G.fstStarEdge e)
  · exact G.paddedLargeAssign_nonneg (R (G.snd e) c) (G.sndStarEdge e)
  · exact G.sum_paddedLargeAssign (R (G.fst e) c) (G.fstStarEdge e)
  · exact G.sum_paddedLargeAssign (R (G.snd e) c) (G.sndStarEdge e)

/-- Exact ordinary mass of one edge, summed over all colours and padded
endpoint places. -/
theorem sum_profileOrdinaryMass (e : G.E) :
    (∑ c, ∑ i, ∑ j, G.profileOrdinaryMass proposal R e c i j) =
      ∑ c, G.profileRetainedMass s β proposal e c := by
  apply Finset.sum_congr rfl
  intro c _hc
  exact G.sum_profileOrdinaryMass_color proposal R e c

/-- The same exact job-mass identity stated directly for the ordinary
rank-three option system consumed by `LargeEdgeOptions`. -/
theorem sum_ordinarySlotChoice_profileMass_fiber (e : G.E) :
    (∑ z ∈ (OrdinarySlotChoice.system G.fst G.snd
        (explicitLargeSlotBound β q r)).fiber e,
      OrdinarySlotChoice.mass (explicitLargeSlotBound β q r)
        (G.profileOrdinaryMass proposal R) z) =
      ∑ c, G.profileRetainedMass s β proposal e c := by
  rw [OrdinarySlotChoice.sum_mass_fiber G.fst G.snd
    (explicitLargeSlotBound β q r) (G.profileOrdinaryMass proposal R) e]
  exact G.sum_profileOrdinaryMass proposal R e

/-- One coupled option is no larger than its left endpoint assignment. -/
theorem profileOrdinaryMass_le_leftAssign
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color) (i j : Fin (explicitLargeSlotBound β q r)) :
    G.profileOrdinaryMass proposal R e c i j ≤
      G.paddedLargeAssign (R (G.fst e) c) (G.fstStarEdge e) i := by
  unfold profileOrdinaryMass
  apply endpointPairMass_le_left
  · exact G.profileRetainedMass_nonneg proposal hs hp e c
  · exact G.paddedLargeAssign_nonneg (R (G.fst e) c) (G.fstStarEdge e)
  · exact G.paddedLargeAssign_nonneg (R (G.snd e) c) (G.sndStarEdge e)
  · exact G.sum_paddedLargeAssign (R (G.fst e) c) (G.fstStarEdge e)
  · exact G.sum_paddedLargeAssign (R (G.snd e) c) (G.sndStarEdge e)

/-- One coupled option is no larger than its right endpoint assignment. -/
theorem profileOrdinaryMass_le_rightAssign
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color) (i j : Fin (explicitLargeSlotBound β q r)) :
    G.profileOrdinaryMass proposal R e c i j ≤
      G.paddedLargeAssign (R (G.snd e) c) (G.sndStarEdge e) j := by
  unfold profileOrdinaryMass
  apply endpointPairMass_le_right
  · exact G.profileRetainedMass_nonneg proposal hs hp e c
  · exact G.paddedLargeAssign_nonneg (R (G.fst e) c) (G.fstStarEdge e)
  · exact G.paddedLargeAssign_nonneg (R (G.snd e) c) (G.sndStarEdge e)
  · exact G.sum_paddedLargeAssign (R (G.fst e) c) (G.fstStarEdge e)
  · exact G.sum_paddedLargeAssign (R (G.snd e) c) (G.sndStarEdge e)

/-- Positive option mass is supported by one compatible concrete profile
place at each endpoint. -/
theorem profileOrdinaryMass_pos_compatible
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color) (i j : Fin (explicitLargeSlotBound β q r))
    (hpos : 0 < G.profileOrdinaryMass proposal R e c i j) :
    ∃ ji jk,
      G.paddedLargeSlotCode (R (G.fst e) c) ji = i ∧
      G.paddedLargeSlotCode (R (G.snd e) c) jk = j ∧
      0 < (R (G.fst e) c).largeAssign (G.fstStarEdge e) ji ∧
      0 < (R (G.snd e) c).largeAssign (G.sndStarEdge e) jk ∧
      G.weight e ≤ G.explicitLargeSlotSize (R (G.fst e) c).law hβ hr ji ∧
      G.weight e ≤ G.explicitLargeSlotSize (R (G.snd e) c).law hβ hr jk := by
  have hleft : 0 < G.paddedLargeAssign
      (R (G.fst e) c) (G.fstStarEdge e) i :=
    hpos.trans_le (G.profileOrdinaryMass_le_leftAssign proposal R hs hp e c i j)
  have hright : 0 < G.paddedLargeAssign
      (R (G.snd e) c) (G.sndStarEdge e) j :=
    hpos.trans_le (G.profileOrdinaryMass_le_rightAssign proposal R hs hp e c i j)
  rcases G.paddedLargeAssign_pos_compatible (R (G.fst e) c)
      (G.fstStarEdge e) i hleft with ⟨ji, hji, hji0, hjic⟩
  rcases G.paddedLargeAssign_pos_compatible (R (G.snd e) c)
      (G.sndStarEdge e) j hright with ⟨jk, hjk, hjk0, hjkc⟩
  exact ⟨ji, jk, hji, hjk, hji0, hjk0, hjic, hjkc⟩

/-- Local mass seen by a padded place at one endpoint.  The row and column
identities above identify this with the corresponding side of the coupled
array. -/
def profileIncidentSlotMass (v : G.V) (c : Color)
    (i : Fin (explicitLargeSlotBound β q r)) (e : G.StarEdge v) : ℝ :=
  G.paddedLargeAssign (R v c) e i

theorem profileIncidentSlotMass_eq_assign (v : G.V) (c : Color)
    (i : Fin (explicitLargeSlotBound β q r)) (e : G.StarEdge v) :
    G.profileIncidentSlotMass proposal R v c i e =
      G.paddedLargeAssign (R v c) e i := by
  rfl

/-- The coupled ordinary array respects every padded local slot capacity. -/
theorem sum_profileIncidentSlotMass_le_capacity (v : G.V) (c : Color)
    (i : Fin (explicitLargeSlotBound β q r)) :
    (∑ e : G.StarEdge v, G.profileIncidentSlotMass proposal R v c i e) ≤
      G.paddedLargeCapacity (R v c) i := by
  simp_rw [G.profileIncidentSlotMass_eq_assign proposal R v c i]
  exact G.paddedLargeAssign_capacity (R v c) i

/-- A uniform padded-capacity bound is a uniform pointwise bound for the
ordinary option array. -/
theorem profileOrdinaryMass_le_of_capacities
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c) (tau : ℝ)
    (hcap : ∀ v c i, G.paddedLargeCapacity (R v c) i ≤ tau)
    (e : G.E) (c : Color) (i j : Fin (explicitLargeSlotBound β q r)) :
    G.profileOrdinaryMass proposal R e c i j ≤ tau := by
  calc
    G.profileOrdinaryMass proposal R e c i j ≤
        G.paddedLargeAssign (R (G.fst e) c) (G.fstStarEdge e) i :=
      G.profileOrdinaryMass_le_leftAssign proposal R hs hp e c i j
    _ ≤ ∑ f, G.paddedLargeAssign (R (G.fst e) c) f i :=
      Finset.single_le_sum
        (fun f _ ↦ G.paddedLargeAssign_nonneg (R (G.fst e) c) f i)
        (Finset.mem_univ (G.fstStarEdge e))
    _ ≤ G.paddedLargeCapacity (R (G.fst e) c) i :=
      G.paddedLargeAssign_capacity (R (G.fst e) c) i
    _ ≤ tau := hcap (G.fst e) c i

/-- Unconditional parameter-only pointwise bound supplied by the bounded
profile realization. -/
theorem profileOrdinaryMass_le_parameter
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color) (i j : Fin (explicitLargeSlotBound β q r)) :
    G.profileOrdinaryMass proposal R e c i j ≤ s * max q 1 := by
  apply G.profileOrdinaryMass_le_of_capacities proposal R hs hp
  intro v d k
  exact G.paddedLargeCapacity_le_parameter (R v d) hs k

/-- If the left padded place is the repair place, its exact capacity gives
the sharper pointwise bound `s*q`. -/
theorem profileOrdinaryMass_le_repair_left
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color) (j : Fin (explicitLargeSlotBound β q r)) :
    G.profileOrdinaryMass proposal R e c
        (G.paddedLargeSlotCode (R (G.fst e) c) none) j ≤ s * q := by
  calc
    G.profileOrdinaryMass proposal R e c
        (G.paddedLargeSlotCode (R (G.fst e) c) none) j ≤
      G.paddedLargeAssign (R (G.fst e) c) (G.fstStarEdge e)
        (G.paddedLargeSlotCode (R (G.fst e) c) none) :=
      G.profileOrdinaryMass_le_leftAssign proposal R hs hp e c _ j
    _ ≤ G.paddedLargeCapacity (R (G.fst e) c)
        (G.paddedLargeSlotCode (R (G.fst e) c) none) :=
      G.paddedLargeAssign_le_capacity (R (G.fst e) c) (G.fstStarEdge e) _
    _ = s * q := G.paddedLargeCapacity_repair (R (G.fst e) c)

/-- A non-repair left place gives the sharper pointwise bound `s`. -/
theorem profileOrdinaryMass_le_nonrepair_left
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color) (i j : Fin (explicitLargeSlotBound β q r))
    (hi : i ≠ G.paddedLargeSlotCode (R (G.fst e) c) none) :
    G.profileOrdinaryMass proposal R e c i j ≤ s := by
  calc
    G.profileOrdinaryMass proposal R e c i j ≤
      G.paddedLargeAssign (R (G.fst e) c) (G.fstStarEdge e) i :=
      G.profileOrdinaryMass_le_leftAssign proposal R hs hp e c i j
    _ ≤ G.paddedLargeCapacity (R (G.fst e) c) i :=
      G.paddedLargeAssign_le_capacity (R (G.fst e) c) (G.fstStarEdge e) i
    _ ≤ s := G.paddedLargeCapacity_le_s_of_ne_repair
      (R (G.fst e) c) hs i hi

/-- Right-end repair analogue. -/
theorem profileOrdinaryMass_le_repair_right
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color) (i : Fin (explicitLargeSlotBound β q r)) :
    G.profileOrdinaryMass proposal R e c i
        (G.paddedLargeSlotCode (R (G.snd e) c) none) ≤ s * q := by
  calc
    G.profileOrdinaryMass proposal R e c i
        (G.paddedLargeSlotCode (R (G.snd e) c) none) ≤
      G.paddedLargeAssign (R (G.snd e) c) (G.sndStarEdge e)
        (G.paddedLargeSlotCode (R (G.snd e) c) none) :=
      G.profileOrdinaryMass_le_rightAssign proposal R hs hp e c i _
    _ ≤ G.paddedLargeCapacity (R (G.snd e) c)
        (G.paddedLargeSlotCode (R (G.snd e) c) none) :=
      G.paddedLargeAssign_le_capacity (R (G.snd e) c) (G.sndStarEdge e) _
    _ = s * q := G.paddedLargeCapacity_repair (R (G.snd e) c)

/-- Right-end non-repair analogue. -/
theorem profileOrdinaryMass_le_nonrepair_right
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color) (i j : Fin (explicitLargeSlotBound β q r))
    (hj : j ≠ G.paddedLargeSlotCode (R (G.snd e) c) none) :
    G.profileOrdinaryMass proposal R e c i j ≤ s := by
  calc
    G.profileOrdinaryMass proposal R e c i j ≤
      G.paddedLargeAssign (R (G.snd e) c) (G.sndStarEdge e) j :=
      G.profileOrdinaryMass_le_rightAssign proposal R hs hp e c i j
    _ ≤ G.paddedLargeCapacity (R (G.snd e) c) j :=
      G.paddedLargeAssign_le_capacity (R (G.snd e) c) (G.sndStarEdge e) j
    _ ≤ s := G.paddedLargeCapacity_le_s_of_ne_repair
      (R (G.snd e) c) hs j hj

end WeightedMultigraph

end

end WeightedEdgeColoring
