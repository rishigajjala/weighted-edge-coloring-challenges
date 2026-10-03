import WeightedEdgeColoring.ProfileOptionBridge
import WeightedEdgeColoring.GraphLargeEdgeBounds

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# The concrete profile-based large-edge family

This module combines the ordinary mass obtained from bounded profile
realizations with the graph-indexed extra-slot construction.  The residual
of an edge is defined to be one minus its retained ordinary mass.  Local
hypotheses specify the assumptions on the surrounding rounding argument;
no global capacity estimate is assumed here.
-/

noncomputable section

universe u w₁ w₂

namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph.{u})
variable {Color : Type w₁} {Class : Type w₂}
  [Fintype Color] [DecidableEq Color]
  [Fintype Class] [DecidableEq Class]

variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → Color → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- The mass of an edge not retained by its ordinary profile options. -/
def profileResidual (s β : ℝ) (proposal : G.E → Color → ℝ) (e : G.E) : ℝ :=
  1 - ∑ c, G.profileRetainedMass s β proposal e c

theorem profileResidual_nonneg
    (hretained : ∀ e, (∑ c, G.profileRetainedMass s β proposal e c) ≤ 1)
    (e : G.E) :
    0 ≤ G.profileResidual s β proposal e := by
  unfold profileResidual
  linarith [hretained e]

theorem profileResidual_le_one
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c) (e : G.E) :
    G.profileResidual s β proposal e ≤ 1 := by
  have hsum : 0 ≤ ∑ c, G.profileRetainedMass s β proposal e c :=
    Finset.sum_nonneg fun c _ ↦
      G.profileRetainedMass_nonneg proposal hs hp e c
  unfold profileResidual
  linarith

theorem profileResidual_mem_Icc
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (hretained : ∀ e, (∑ c, G.profileRetainedMass s β proposal e c) ≤ 1)
    (e : G.E) :
    G.profileResidual s β proposal e ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨G.profileResidual_nonneg proposal hretained e,
    G.profileResidual_le_one proposal hs hp e⟩

/-- The combined ordinary/extra option system with the profile residual used
to choose every graph-indexed extra-slot count. -/
def profileLargeEdgeOptionSystem
    (bucket : G.E → Class) (gamma : ℝ) (t : ℕ) :=
  G.largeEdgeOptionSystem (Color := Color)
    (explicitLargeSlotBound β q r) bucket
    (G.graphExtraSlotCount bucket (G.profileResidual s β proposal) gamma t)

/-- Fractional mass on the concrete profile-based combined option family. -/
def profileLargeEdgeMass
    (bucket : G.E → Class) (gamma : ℝ) (t : ℕ) :=
  G.largeEdgeMass (explicitLargeSlotBound β q r) bucket
    (G.graphExtraSlotCount bucket (G.profileResidual s β proposal) gamma t)
    (G.profileOrdinaryMass proposal R) (G.profileResidual s β proposal)

/-- Under the honest retained-mass upper bound, every combined option has
nonnegative mass. -/
theorem profileLargeEdgeMass_nonneg
    (bucket : G.E → Class) (gamma : ℝ) (t : ℕ)
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (hretained : ∀ e, (∑ c, G.profileRetainedMass s β proposal e c) ≤ 1) :
    ∀ z, 0 ≤ G.profileLargeEdgeMass proposal R bucket gamma t z := by
  exact G.largeEdgeMass_nonneg (explicitLargeSlotBound β q r) bucket
    (G.graphExtraSlotCount bucket (G.profileResidual s β proposal) gamma t)
    (G.profileOrdinaryMass proposal R) (G.profileResidual s β proposal)
    (G.profileOrdinaryMass_nonneg proposal R hs hp)
    (G.profileResidual_nonneg proposal hretained)

/-- Each job fibre has total mass exactly one. -/
theorem sum_profileLargeEdgeMass_fiber_eq_one
    (bucket : G.E → Class) (gamma : ℝ) {t : ℕ} (ht : 0 < t)
    (e : G.E) :
    (∑ z ∈ (G.profileLargeEdgeOptionSystem
        (Color := Color) proposal bucket gamma t).fiber e,
      G.profileLargeEdgeMass proposal R bucket gamma t z) = 1 := by
  apply G.sum_largeEdgeMass_fiber_eq_one
    (explicitLargeSlotBound β q r) bucket
    (G.graphExtraSlotCount bucket (G.profileResidual s β proposal) gamma t)
    (G.profileOrdinaryMass proposal R) (G.profileResidual s β proposal)
  · intro k
    exact G.graphExtraSlotCount_pos bucket (G.profileResidual s β proposal)
      gamma ht (G.fst k) (bucket k)
  · intro k
    exact G.graphExtraSlotCount_pos bucket (G.profileResidual s β proposal)
      gamma ht (G.snd k) (bucket k)
  · intro k
    rw [G.sum_profileOrdinaryMass proposal R k]
    unfold profileResidual
    ring

/-- Every graph-indexed extra slot in the profile family has copied degree
at most `(1-gamma)N`. -/
theorem profileLargeEdge_extraSlotDegree_le
    (bucket : G.E → Class) (gamma : ℝ) (t N : ℕ)
    (hretained : ∀ e, (∑ c, G.profileRetainedMass s β proposal e c) ≤ 1)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (ht : 0 < t)
    (z : ExtraSlot G.V Class
      (G.graphExtraSlotCount bucket (G.profileResidual s β proposal) gamma t)) :
    ((((G.profileLargeEdgeOptionSystem
        (Color := Color) proposal bucket gamma t).quantized N
      (G.profileLargeEdgeMass proposal R bucket gamma t)).slotDegree
        (Sum.inr z) : ℕ) : ℝ) ≤ (1 - gamma) * N := by
  exact G.largeEdge_graphExtra_slotDegree_inr_le
    (explicitLargeSlotBound β q r) bucket (G.profileResidual s β proposal)
    (G.profileOrdinaryMass proposal R)
    (G.profileResidual_nonneg proposal hretained) gamma t N
    hgamma0 hgamma1 ht z

/-- Exact unit fibre mass turns the generic floor estimate into an explicit
lower bound on the copied degree of every job. -/
theorem profileLargeEdge_quantizedJobDegree_lower
    (bucket : G.E → Class) (gamma : ℝ) {t : ℕ} (ht : 0 < t)
    (N : ℕ) (e : G.E) :
    (N : ℝ) -
        ((Fintype.card Color * explicitLargeSlotBound β q r *
            explicitLargeSlotBound β q r : ℕ) +
          G.graphExtraSlotCount bucket (G.profileResidual s β proposal) gamma t
              (G.fst e) (bucket e) *
            G.graphExtraSlotCount bucket (G.profileResidual s β proposal) gamma t
              (G.snd e) (bucket e) : ℕ) ≤
      ((G.profileLargeEdgeOptionSystem proposal bucket gamma t).quantizedJobDegree
        N (G.profileLargeEdgeMass proposal R bucket gamma t) e : ℝ) := by
  have hbase := G.largeEdge_quantizedJobDegree_lower
    (explicitLargeSlotBound β q r) bucket
    (G.graphExtraSlotCount bucket (G.profileResidual s β proposal) gamma t)
    (G.profileOrdinaryMass proposal R) (G.profileResidual s β proposal)
    (fun k ↦ G.graphExtraSlotCount_pos bucket (G.profileResidual s β proposal)
      gamma ht (G.fst k) (bucket k))
    (fun k ↦ G.graphExtraSlotCount_pos bucket (G.profileResidual s β proposal)
      gamma ht (G.snd k) (bucket k)) N e
  rw [G.sum_profileOrdinaryMass proposal R e] at hbase
  simpa [profileLargeEdgeOptionSystem, profileLargeEdgeMass, profileResidual,
    Nat.cast_add, Nat.cast_mul, pow_two, sub_eq_add_neg, add_assoc] using hbase

/-- The ordinary job--slot codegree is controlled by the retained mass of
the slot's colour. -/
theorem profileLargeEdge_ordinaryJobSlotCodegree_le
    (bucket : G.E → Class) (gamma : ℝ) (t N : ℕ)
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (e : G.E)
    (z : OrdinarySlot G.V Color (explicitLargeSlotBound β q r)) :
    (((G.profileLargeEdgeOptionSystem proposal bucket gamma t).quantized N
      (G.profileLargeEdgeMass proposal R bucket gamma t)).jobSlotCodegree
        e (Sum.inl z) : ℝ) ≤
      (N : ℝ) * G.profileRetainedMass s β proposal e z.color := by
  have hbase := G.largeEdge_quantized_jobSlotCodegree_inl_le
    (explicitLargeSlotBound β q r) bucket
    (G.graphExtraSlotCount bucket (G.profileResidual s β proposal) gamma t)
    (G.profileOrdinaryMass proposal R) (G.profileResidual s β proposal)
    (G.profileOrdinaryMass_nonneg proposal R hs hp) N e z
  rw [G.sum_profileOrdinaryMass_color proposal R e z.color] at hbase
  exact hbase

/-- The extra job--slot codegree is at most `N/t`. -/
theorem profileLargeEdge_extraJobSlotCodegree_le
    (bucket : G.E → Class) (gamma : ℝ) {t : ℕ} (ht : 0 < t) (N : ℕ)
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (hretained : ∀ e, (∑ c, G.profileRetainedMass s β proposal e c) ≤ 1)
    (e : G.E)
    (z : ExtraSlot G.V Class
      (G.graphExtraSlotCount bucket (G.profileResidual s β proposal) gamma t)) :
    (((G.profileLargeEdgeOptionSystem
        (Color := Color) proposal bucket gamma t).quantized N
      (G.profileLargeEdgeMass proposal R bucket gamma t)).jobSlotCodegree
        e (Sum.inr z) : ℝ) ≤ (N : ℝ) * (1 / (t : ℝ)) := by
  exact G.largeEdge_graphExtra_jobSlotCodegree_inr_le
    (explicitLargeSlotBound β q r) bucket (G.profileResidual s β proposal)
    (G.profileOrdinaryMass proposal R)
    (G.profileResidual_nonneg proposal hretained)
    (G.profileResidual_le_one proposal hs hp) gamma ht N e z

/-- A local padded-capacity bound of `1/t^2` makes every distinct combined
slot pair have copied codegree at most `N/t^2`.  This hypothesis is the only
ordinary-side smallness input; its global proof belongs to the later
many-sums argument. -/
theorem profileLargeEdge_slotPairCodegree_le
    (bucket : G.E → Class) (gamma : ℝ) {t : ℕ} (ht : 0 < t) (N : ℕ)
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (hretained : ∀ e, (∑ c, G.profileRetainedMass s β proposal e c) ≤ 1)
    (hcap : ∀ v c i,
      G.paddedLargeCapacity (R v c) i ≤ 1 / (t : ℝ) ^ 2)
    {z z' : G.LargeEdgeSlot (Color := Color)
      (explicitLargeSlotBound β q r)
      (G.graphExtraSlotCount bucket (G.profileResidual s β proposal) gamma t)}
    (hne : z ≠ z') :
    ((((G.profileLargeEdgeOptionSystem proposal bucket gamma t).quantized N
      (G.profileLargeEdgeMass proposal R bucket gamma t)).slotPairCodegree
        z z' : ℕ) : ℝ) ≤ (N : ℝ) * (1 / (t : ℝ) ^ 2) := by
  apply G.largeEdge_graphExtra_slotPairCodegree_le
    (explicitLargeSlotBound β q r) bucket (G.profileResidual s β proposal)
    (G.profileOrdinaryMass proposal R) gamma ht
  · exact G.profileOrdinaryMass_nonneg proposal R hs hp
  · exact G.profileOrdinaryMass_le_of_capacities proposal R hs hp
      (1 / (t : ℝ) ^ 2) hcap
  · exact G.profileResidual_nonneg proposal hretained
  · exact G.profileResidual_le_one proposal hs hp
  · exact hne

end WeightedSimpleGraph

end

end WeightedEdgeColoring
