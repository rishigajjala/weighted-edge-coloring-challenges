import WeightedEdgeColoring.MultigraphProfileRepresentation

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-! # Safety of a selected rounded profile -/

/-- The concrete load encoded by a rounded profile: one copy of every
ordinary rounded size for each recorded multiplicity, followed by the rounded
reservoir. -/
noncomputable def roundedProfileLoad {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (P : G.RoundedProfileCode L) : ℝ :=
  (∑ z : {z // z ∈ L.kept}, (P.1 z).val * z.1) + r * P.2.val

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


private theorem roundedOrdinaryLoad_code_le {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r)
    (k : Fin L.m) :
    (∑ z : {z // z ∈ L.kept},
        (((G.roundedProfileCode L hβ hr k).1 z).val : ℝ) * z.1) ≤
      ∑ e ∈ (G.rawProfile β (L.outcome k)).ordinary, G.weight e.1 := by
  classical
  let E := G.largeEdges β (L.outcome k)
  have hsupport : ∀ e ∈ E, G.weight e.1 ∈ G.lawSlotSupport β L.outcome := by
    intro e he
    apply Finset.mem_biUnion.mpr
    exact ⟨k, Finset.mem_univ k, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
  have hrange : ∀ e ∈ E, L.round (G.weight e.1) ∈ L.kept := by
    intro e he
    exact L.round_mem _ (hsupport e he)
  let c : ℝ → ℕ := fun z ↦ if hz : z ∈ L.kept then
    G.roundedMultiplicity L k ⟨z, hz⟩ else 0
  have hsub :
      (∑ z : {z // z ∈ L.kept},
        (G.roundedMultiplicity L k z : ℝ) * z.1) =
      ∑ z ∈ L.kept, (c z : ℝ) * z := by
    symm
    simpa [c] using Finset.sum_subtype
      (F := inferInstanceAs (Fintype {z // z ∈ L.kept})) L.kept
      (fun z ↦ Iff.rfl) (fun z ↦ (c z : ℝ) * z)
  have hfiber := Finset.sum_fiberwise_eq_sum_filter E L.kept
    (fun e ↦ L.round (G.weight e.1))
    (fun e ↦ L.round (G.weight e.1))
  change (∑ z : {z // z ∈ L.kept},
      (G.roundedMultiplicity L k z : ℝ) * z.1) ≤ _
  rw [hsub]
  calc
    (∑ z ∈ L.kept, (c z : ℝ) * z) =
        ∑ z ∈ L.kept, ∑ e ∈ E with L.round (G.weight e.1) = z,
          L.round (G.weight e.1) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [show c z = G.roundedMultiplicity L k ⟨z, hz⟩ by simp [c, hz]]
      unfold roundedMultiplicity
      change (((E.filter fun e ↦ L.round (G.weight e.1) = z).card : ℕ) : ℝ) * z = _
      calc
        (((E.filter fun e ↦ L.round (G.weight e.1) = z).card : ℕ) : ℝ) * z =
            ∑ _e ∈ E.filter (fun e ↦ L.round (G.weight e.1) = z), z := by simp
        _ = ∑ e ∈ E with L.round (G.weight e.1) = z,
              L.round (G.weight e.1) := by
          apply Finset.sum_congr rfl
          intro e he
          exact (Finset.mem_filter.mp he).2.symm
    _ = ∑ e ∈ E with L.round (G.weight e.1) ∈ L.kept,
          L.round (G.weight e.1) := hfiber
    _ = ∑ e ∈ E, L.round (G.weight e.1) := by
      apply Finset.sum_congr
      · ext e
        simp only [Finset.mem_filter]
        constructor
        · exact fun he ↦ he.1
        · intro he
          exact ⟨he, hrange e he⟩
      · intro e _he
        rfl
    _ ≤ ∑ e ∈ E, G.weight e.1 := by
      apply Finset.sum_le_sum
      intro e he
      exact L.round_le _ (hsupport e he)
    _ = ∑ e ∈ (G.rawProfile β (L.outcome k)).ordinary, G.weight e.1 := by
      rw [rawProfile_ordinary]


/-- Every actual rounded profile code has concrete load at most one. -/
theorem roundedProfileLoad_code_le_one {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r)
    (k : Fin L.m) :
    G.roundedProfileLoad L (G.roundedProfileCode L hβ hr k) ≤ 1 := by
  have hR : 0 ≤ (G.rawProfile β (L.outcome k)).reservoir :=
    G.rawProfile_reservoir_nonneg (L.feasible k)
  have hres :
      r * (((G.roundedProfileCode L hβ hr k).2.val : ℕ) : ℝ) =
        roundReservoir r (G.rawProfile β (L.outcome k)).reservoir := by
    unfold roundedProfileCode roundReservoir
    simp only
    rw [natFloor_cast_eq_intFloor_cast _
      (div_nonneg hR hr.le)]
  unfold roundedProfileLoad
  rw [hres]
  calc
    _ ≤ (∑ e ∈ (G.rawProfile β (L.outcome k)).ordinary, G.weight e.1) +
        roundReservoir r (G.rawProfile β (L.outcome k)).reservoir :=
      add_le_add_left (G.roundedOrdinaryLoad_code_le L hβ hr k) _
    _ ≤ 1 := G.rawProfile_safe_after_roundReservoir hr (L.feasible k)

/-- Every code in the aggregated menu is safe. -/
theorem roundedProfileLoad_le_one_of_mem_menu {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r)
    (P : G.RoundedProfileCode L)
    (hP : P ∈ G.roundedProfileMenu L hβ hr) :
    G.roundedProfileLoad L P ≤ 1 := by
  rw [roundedProfileMenu, profileMenu, Finset.mem_image] at hP
  rcases hP with ⟨k, _hk, rfl⟩
  exact G.roundedProfileLoad_code_le_one L hβ hr k


/-- The ordinary slots belonging to one rounded profile code. -/
abbrev RoundedProfileOrdinarySlot {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (P : G.RoundedProfileCode L) :=
  Σ z : {z // z ∈ L.kept}, Fin ((P.1 z).val)

/-- The size of an ordinary slot belonging to a rounded profile. -/
noncomputable def roundedProfileOrdinarySlotSize {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (P : G.RoundedProfileCode L) :
    G.RoundedProfileOrdinarySlot L P → ℝ
  | ⟨z, _i⟩ => z.1

/-- Summing the sizes of the explicitly indexed ordinary slots gives exactly
multiplicity times size in every rounded bucket. -/
theorem sum_roundedProfileOrdinarySlotSize {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (P : G.RoundedProfileCode L) :
    (∑ j : G.RoundedProfileOrdinarySlot L P,
      G.roundedProfileOrdinarySlotSize L P j) =
    ∑ z : {z // z ∈ L.kept}, (P.1 z).val * z.1 := by
  classical
  simp only [Fintype.sum_sigma, roundedProfileOrdinarySlotSize,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]

/-- The explicit ordinary slots of any menu profile, together with its rounded
reservoir, fit in a unit bin. -/
theorem sum_roundedProfileOrdinarySlotSize_add_reservoir_le_one {v : G.V}
    {x : G.StarEdge v → ℝ} {s β q r : ℝ}
    (L : G.BoundedProfileLaw x s β q r) (hβ : 0 < β) (hr : 0 < r)
    (P : G.RoundedProfileCode L)
    (hP : P ∈ G.roundedProfileMenu L hβ hr) :
    (∑ j : G.RoundedProfileOrdinarySlot L P,
      G.roundedProfileOrdinarySlotSize L P j) + r * P.2.val ≤ 1 := by
  rw [G.sum_roundedProfileOrdinarySlotSize L P]
  exact G.roundedProfileLoad_le_one_of_mem_menu L hβ hr P hP

end WeightedMultigraph
end WeightedEdgeColoring
