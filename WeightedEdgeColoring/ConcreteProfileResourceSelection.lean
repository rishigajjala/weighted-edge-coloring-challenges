import WeightedEdgeColoring.ProfileOptionBridge
import WeightedEdgeColoring.ProfileSynchronizationSelection

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u w

variable (G : WeightedSimpleGraph.{u})
variable {Color : Type w} [Fintype Color] [DecidableEq Color]
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → Color → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- Common padded range for every rounded profile menu. -/
def profileStateBound (β q r : ℝ) : ℕ :=
  (⌊1 / β⌋₊ + 1) ^ (⌊(1 / β) / q⌋₊ + 1) *
    (⌊1 / r⌋₊ + 1) + 1

theorem profileMenu_card_le_stateBound (v : G.V) (c : Color) :
    Fintype.card {P // P ∈
      G.roundedProfileMenu (R v c).law hβ hr} ≤ profileStateBound β q r := by
  have hmenu : Fintype.card {P // P ∈
      G.roundedProfileMenu (R v c).law hβ hr} ≤
      Fintype.card (G.RoundedProfileIndex (R v c).law hβ hr) := by
    simp [RoundedProfileIndex]
  exact hmenu.trans
    (G.roundedProfileIndex_card_le_parameters (R v c).law hβ hr)

/-- Inject a source-dependent profile menu into the common `Fin M`. -/
def profileStateCode (v : G.V) (c : Color) :
    {P // P ∈ G.roundedProfileMenu (R v c).law hβ hr} →
      Fin (profileStateBound β q r) :=
  fun P ↦ Fin.castLE (G.profileMenu_card_le_stateBound
    (proposal := proposal) (R := R) v c)
    (Fintype.equivFin _ P)

theorem profileStateCode_injective (v : G.V) (c : Color) :
    Function.Injective (G.profileStateCode (proposal := proposal) (R := R) v c) := by
  intro P Q hPQ
  unfold profileStateCode at hPQ
  apply (Fintype.equivFin _).injective
  apply Fin.ext
  have hval := congrArg Fin.val hPQ
  change ((Fintype.equivFin _) P).val =
    ((Fintype.equivFin _) Q).val at hval
  exact hval

/-- The rounded profile law padded by zero on unused common states. -/
def paddedProfileProbability (src : G.ProfileSource Color)
    (a : Fin (profileStateBound β q r)) : ℝ :=
  ∑ P : {P // P ∈ G.roundedProfileMenu (R src.1 src.2).law hβ hr},
    if G.profileStateCode (proposal := proposal) (R := R) src.1 src.2 P = a then
      G.roundedProfileMass (R src.1 src.2).law hβ hr P.1 else 0

theorem paddedProfileProbability_nonneg (src : G.ProfileSource Color)
    (a : Fin (profileStateBound β q r)) :
    0 ≤ G.paddedProfileProbability (proposal := proposal) (R := R) src a := by
  apply Finset.sum_nonneg
  intro P _
  split
  · exact G.roundedProfileMass_nonneg (R src.1 src.2).law hβ hr P.1
  · exact le_rfl

/-- Padding preserves total probability one. -/
theorem sum_paddedProfileProbability (src : G.ProfileSource Color) :
    ∑ a, G.paddedProfileProbability (proposal := proposal) (R := R) src a = 1 := by
  classical
  unfold paddedProfileProbability
  rw [Finset.sum_comm]
  calc
    (∑ P : {P // P ∈ G.roundedProfileMenu (R src.1 src.2).law hβ hr},
        ∑ a, if G.profileStateCode (proposal := proposal) (R := R) src.1 src.2 P = a then
          G.roundedProfileMass (R src.1 src.2).law hβ hr P.1 else 0) =
        ∑ P : {P // P ∈ G.roundedProfileMenu (R src.1 src.2).law hβ hr},
          G.roundedProfileMass (R src.1 src.2).law hβ hr P.1 := by simp
    _ = ∑ P ∈ G.roundedProfileMenu (R src.1 src.2).law hβ hr,
          G.roundedProfileMass (R src.1 src.2).law hβ hr P := by
      symm
      exact Finset.sum_subtype _ (fun _ ↦ Iff.rfl) _
    _ = 1 := G.sum_roundedProfileMass (R src.1 src.2).law hβ hr

theorem paddedProfileProbability_at_code (src : G.ProfileSource Color)
    (P : {P // P ∈ G.roundedProfileMenu (R src.1 src.2).law hβ hr}) :
    G.paddedProfileProbability (proposal := proposal) (R := R) src
        (G.profileStateCode (proposal := proposal) (R := R) src.1 src.2 P) =
      G.roundedProfileMass (R src.1 src.2).law hβ hr P.1 := by
  classical
  unfold paddedProfileProbability
  have hinj := G.profileStateCode_injective
    (proposal := proposal) (R := R) src.1 src.2
  simp only [hinj.eq_iff]
  simp

/-- An ordinary resource is an actual (non-repair) explicit slot, tagged by
its vertex--colour source. -/
abbrev OrdinaryProfileResourceRow :=
  Σ src : G.ProfileSource Color,
    Σ P : {P // P ∈ G.roundedProfileMenu (R src.1 src.2).law hβ hr},
      Σ z : {z // z ∈ (R src.1 src.2).law.kept}, Fin ((P.1.1 z).val)

/-- A selected profile opens each of its ordinary slots with mass `s`. -/
def ordinaryProfileResourceUse (src : G.ProfileSource Color)
    (a : Fin (profileStateBound β q r))
    (row : G.OrdinaryProfileResourceRow (proposal := proposal) (R := R)) : ℝ :=
  if src = row.1 ∧
      a = G.profileStateCode (proposal := proposal) (R := R)
        row.1.1 row.1.2 row.2.1 then s else 0

theorem ordinaryProfileResourceUse_nonneg (hs : 0 ≤ s)
    (src : G.ProfileSource Color) (a : Fin (profileStateBound β q r))
    (row : G.OrdinaryProfileResourceRow (proposal := proposal) (R := R)) :
    0 ≤ G.ordinaryProfileResourceUse (proposal := proposal) (R := R) src a row := by
  unfold ordinaryProfileResourceUse
  split <;> positivity

theorem ordinaryProfileResourceUse_le_one (hs1 : s ≤ 1)
    (src : G.ProfileSource Color) (a : Fin (profileStateBound β q r))
    (row : G.OrdinaryProfileResourceRow (proposal := proposal) (R := R)) :
    G.ordinaryProfileResourceUse (proposal := proposal) (R := R) src a row ≤ 1 := by
  unfold ordinaryProfileResourceUse
  split
  · exact hs1
  · norm_num

/-- The expected opening mass of an ordinary resource is exactly the
capacity assigned to its profile. -/
theorem ordinaryProfileResource_rowMean_eq (row :
    G.OrdinaryProfileResourceRow (proposal := proposal) (R := R)) :
    FiniteCategoricalSelection.rowMean
        (G.paddedProfileProbability (proposal := proposal) (R := R))
        (G.ordinaryProfileResourceUse (proposal := proposal) (R := R)) row =
      G.explicitLargeSlotCapacity (R row.1.1 row.1.2).law hβ hr (some row.2) := by
  classical
  unfold FiniteCategoricalSelection.rowMean ordinaryProfileResourceUse
  rw [Finset.sum_eq_single row.1]
  · rw [Finset.sum_eq_single
      (G.profileStateCode (proposal := proposal) (R := R)
        row.1.1 row.1.2 row.2.1)]
    · rw [G.paddedProfileProbability_at_code
        (proposal := proposal) (R := R)]
      simp [explicitLargeSlotCapacity, mul_comm]
    · intro a _ hne
      simp [hne]
    · simp
  · intro src _ hne
    simp [hne]
  · simp

theorem ordinaryProfileResource_rowSupport_card_le_one (row :
    G.OrdinaryProfileResourceRow (proposal := proposal) (R := R)) :
    (FiniteCategoricalSelection.rowSupport
      (G.ordinaryProfileResourceUse (proposal := proposal) (R := R)) row).card ≤ 1 := by
  classical
  have hsub : FiniteCategoricalSelection.rowSupport
      (G.ordinaryProfileResourceUse (proposal := proposal) (R := R)) row ⊆ {row.1} := by
    intro src hsrc
    simp only [FiniteCategoricalSelection.rowSupport, Finset.mem_filter,
      Finset.mem_univ, true_and] at hsrc
    rcases hsrc with ⟨a, ha⟩
    by_contra hne
    have hne' : src ≠ row.1 := by simpa using hne
    simp [ordinaryProfileResourceUse, hne'] at ha
  exact (Finset.card_le_card hsub).trans (by simp)

private theorem ordinaryProfileResource_source_eq_of_mem
    (src : G.ProfileSource Color)
    (row : G.OrdinaryProfileResourceRow (proposal := proposal) (R := R))
    (hrow : row ∈ FiniteCategoricalSelection.rowSupportIncidence
      (G.ordinaryProfileResourceUse (proposal := proposal) (R := R)) src) :
    src = row.1 := by
  simp only [FiniteCategoricalSelection.rowSupportIncidence,
    Finset.mem_filter, Finset.mem_univ, true_and,
    FiniteCategoricalSelection.rowSupport] at hrow
  rcases hrow with ⟨a, ha⟩
  by_contra hne
  simp [ordinaryProfileResourceUse, hne] at ha

/-- A source occurs in at most the parameter-only number of explicit
ordinary slots.  The proof injects every incident row into its realization's
padded explicit-slot range. -/
theorem ordinaryProfileResource_sourceIncidence_card_le
    (src : G.ProfileSource Color) :
    (FiniteCategoricalSelection.rowSupportIncidence
      (G.ordinaryProfileResourceUse (proposal := proposal) (R := R)) src).card ≤
      explicitLargeSlotBound β q r := by
  classical
  let Inc := {row : G.OrdinaryProfileResourceRow
      (proposal := proposal) (R := R) //
    row ∈ FiniteCategoricalSelection.rowSupportIncidence
      (G.ordinaryProfileResourceUse (proposal := proposal) (R := R)) src}
  let code : Inc → Fin (explicitLargeSlotBound β q r) := fun row ↦
    G.paddedLargeSlotCode (R row.1.1.1 row.1.1.2) (some row.1.2)
  have hcode : Function.Injective code := by
    intro x y hxy
    apply Subtype.ext
    rcases x with ⟨⟨sx, tx⟩, hx⟩
    rcases y with ⟨⟨sy, ty⟩, hy⟩
    have hsx : src = sx := G.ordinaryProfileResource_source_eq_of_mem
      (proposal := proposal) (R := R) src ⟨sx, tx⟩ hx
    have hsy : src = sy := G.ordinaryProfileResource_source_eq_of_mem
      (proposal := proposal) (R := R) src ⟨sy, ty⟩ hy
    subst sx
    subst sy
    dsimp only [code] at hxy
    have ht : tx = ty := Option.some.inj
      (G.paddedLargeSlotCode_injective (R src.1 src.2) hxy)
    exact Sigma.ext rfl (heq_of_eq ht)
  simpa only [Inc, Fintype.card_coe, Fintype.card_fin] using
    (Fintype.card_le_of_injective code hcode)

/-- Ordinary resource rows: one padded place for every vertex--colour
source. -/
abbrev ProfileResourceRow (Color : Type w) :=
  G.ProfileSource Color × Fin (explicitLargeSlotBound β q r)

/-- Lift any concrete per-profile-state resource contribution to the global
row family.  A source contributes only to rows with the same vertex and
colour. -/
def profileResourceUse
    (localUse : G.ProfileSource Color → Fin (profileStateBound β q r) →
      Fin (explicitLargeSlotBound β q r) → ℝ)
    (src : G.ProfileSource Color) (a : Fin (profileStateBound β q r))
    (row : G.ProfileResourceRow (β := β) (q := q) (r := r) Color) : ℝ :=
  if src = row.1 then localUse src a row.2 else 0

/-- Exact expected load of a resource row under the padded profile law. -/
theorem profileResource_rowMean_eq
    (localUse : G.ProfileSource Color → Fin (profileStateBound β q r) →
      Fin (explicitLargeSlotBound β q r) → ℝ)
    (row : G.ProfileResourceRow (β := β) (q := q) (r := r) Color) :
    FiniteCategoricalSelection.rowMean
        (G.paddedProfileProbability (proposal := proposal) (R := R))
        (G.profileResourceUse localUse) row =
      ∑ a, G.paddedProfileProbability (proposal := proposal) (R := R) row.1 a *
        localUse row.1 a row.2 := by
  unfold FiniteCategoricalSelection.rowMean profileResourceUse
  rw [Finset.sum_eq_single row.1]
  · simp
  · intro src _ hne
    simp [hne]
  · simp

/-- Every ordinary resource row reads at most its unique vertex--colour
source. -/
theorem profileResource_rowSupport_card_le_one
    (localUse : G.ProfileSource Color → Fin (profileStateBound β q r) →
      Fin (explicitLargeSlotBound β q r) → ℝ)
    (row : G.ProfileResourceRow (β := β) (q := q) (r := r) Color) :
    (FiniteCategoricalSelection.rowSupport
      (G.profileResourceUse localUse) row).card ≤ 1 := by
  have hsub : FiniteCategoricalSelection.rowSupport
      (G.profileResourceUse localUse) row ⊆ {row.1} := by
    intro src hsrc
    simp only [FiniteCategoricalSelection.rowSupport, Finset.mem_filter,
      Finset.mem_univ, true_and] at hsrc
    rcases hsrc with ⟨a, ha⟩
    by_contra hne
    have hne' : src ≠ row.1 := by simpa using hne
    simp [profileResourceUse, hne'] at ha
  exact (Finset.card_le_card hsub).trans (by simp)

/-- One source is read by at most the number of padded ordinary places. -/
theorem profileResource_sourceIncidence_card_le
    (localUse : G.ProfileSource Color → Fin (profileStateBound β q r) →
      Fin (explicitLargeSlotBound β q r) → ℝ)
    (src : G.ProfileSource Color) :
    (FiniteCategoricalSelection.rowSupportIncidence
      (G.profileResourceUse localUse) src).card ≤
      explicitLargeSlotBound β q r := by
  let fiber : Finset (G.ProfileResourceRow (β := β) (q := q) (r := r) Color) :=
    Finset.univ.filter fun row ↦ row.1 = src
  have hsub : FiniteCategoricalSelection.rowSupportIncidence
      (G.profileResourceUse localUse) src ⊆ fiber := by
    intro row hrow
    simp only [FiniteCategoricalSelection.rowSupportIncidence,
      Finset.mem_filter, Finset.mem_univ, true_and] at hrow
    simp only [FiniteCategoricalSelection.rowSupport, Finset.mem_filter,
      Finset.mem_univ, true_and] at hrow
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hrow with ⟨a, ha⟩
    by_contra hne
    have hne' : src ≠ row.1 := fun h ↦ hne h.symm
    simp [profileResourceUse, hne'] at ha
  calc
    _ ≤ fiber.card := Finset.card_le_card hsub
    _ = explicitLargeSlotBound β q r := by
      classical
      have hfiber : fiber = ({src} : Finset (G.ProfileSource Color)) ×ˢ Finset.univ := by
        ext ⟨src', i⟩
        simp [fiber, eq_comm]
      rw [hfiber, Finset.card_product]
      simp

end WeightedSimpleGraph

end

end WeightedEdgeColoring
