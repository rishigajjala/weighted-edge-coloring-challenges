import WeightedEdgeColoring.UniformConcreteProfileBalancing
import WeightedEdgeColoring.SelectedRoundedProfileSafety

/-!
# Concrete supported profile words for uniform proposals

The balancing theorem chooses padded state codes.  Support preservation lets
us decode every chosen code to an actual positive-mass rounded profile.  This
file packages those decoded profiles and their unit-bin safety.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

universe u w

variable (G : WeightedSimpleGraph.{u})
variable {Color : Type w} [Fintype Color] [DecidableEq Color]
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}

/-- A support-preserving balanced padded word can be decoded, color by
color, to actual rounded profiles.  The decoded word keeps the simultaneous
one-vertex statistic bound, every chosen profile has positive mass, and its
concrete ordinary slots plus reservoir fit in one unit bin. -/
theorem exists_balanced_selectedProfile_family
    (base : G.E → ℝ)
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ base e.1) s β q r hβ hr)
    (c0 : Color) :
    ∃ selected : ∀ v c, {P // P ∈
        G.roundedProfileMenu (R0 v).law hβ hr},
      (∀ v c, 0 <
        G.roundedProfileMass (R0 v).law hβ hr (selected v c).1) ∧
      (∀ v c,
        G.roundedProfileLoad (R0 v).law (selected v c).1 ≤ 1) ∧
      ∀ v
        (f : Fin (profileStateBound β q r) → ℝ) (B : ℝ),
        (∀ a, 0 ≤ f a) → (∀ a, f a ≤ B) →
        |(∑ c : Color, f (G.profileStateCode
            (proposal := G.colorIndependentProposal base)
            (R := G.colorIndependentRealization base R0)
            v c (selected v c))) -
          (Fintype.card Color : ℝ) *
            (∑ a : Fin (profileStateBound β q r),
              G.paddedProfileProbability
                (proposal := G.colorIndependentProposal base)
                (R := G.colorIndependentRealization base R0) (v, c0) a *
              f a)| ≤
          profileStateBound β q r * B := by
  rcases G.exists_supported_balanced_colorIndependentProfile_choice
      base R0 c0 with ⟨choice, hsupport, hbalanced⟩
  have hexists : ∀ v c, ∃ P : {P // P ∈
      G.roundedProfileMenu (R0 v).law hβ hr},
      G.profileStateCode
          (proposal := G.colorIndependentProposal base)
          (R := G.colorIndependentRealization base R0) v c P = choice v c ∧
        0 < G.roundedProfileMass (R0 v).law hβ hr P.1 := by
    intro v c
    have hpos : 0 < G.paddedProfileProbability
        (proposal := G.colorIndependentProposal base)
        (R := G.colorIndependentRealization base R0) (v, c) (choice v c) := by
      simpa only [G.paddedProfileProbability_colorIndependent
        base R0 v c0 c (choice v c)] using hsupport v c
    exact G.exists_profile_of_paddedProfileProbability_pos
      base R0 (v, c) (choice v c) hpos
  let selected : ∀ v c, {P // P ∈
      G.roundedProfileMenu (R0 v).law hβ hr} :=
    fun v c ↦ Classical.choose (hexists v c)
  have hcode : ∀ v c,
      G.profileStateCode
          (proposal := G.colorIndependentProposal base)
          (R := G.colorIndependentRealization base R0)
          v c (selected v c) = choice v c := by
    intro v c
    exact (Classical.choose_spec (hexists v c)).1
  refine ⟨selected, ?_, ?_, ?_⟩
  · intro v c
    exact (Classical.choose_spec (hexists v c)).2
  · intro v c
    exact G.roundedProfileLoad_le_one_of_mem_menu
      (R0 v).law hβ hr (selected v c).1 (selected v c).2
  · intro v f B hf0 hfB
    simpa only [hcode] using hbalanced v f B hf0 hfB

end WeightedSimpleGraph

end

end WeightedEdgeColoring
