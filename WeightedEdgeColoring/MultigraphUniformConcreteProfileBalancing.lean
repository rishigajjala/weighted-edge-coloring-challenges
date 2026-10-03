import WeightedEdgeColoring.MultigraphConcreteProfileResourceSelection
import WeightedEdgeColoring.MultigraphLocalPolytope
import WeightedEdgeColoring.UniformProfileBalancing

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})
variable {Color : Type w} [Fintype Color] [DecidableEq Color]
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}

/-- A proposal which is identical in every color. -/
def colorIndependentProposal (base : G.E → ℝ) : G.E → Color → ℝ :=
  fun e _c ↦ base e

/-- Reuse one bounded profile realization at a vertex in every color.  This
is the canonical realization family for a color-independent proposal. -/
def colorIndependentRealization
    (base : G.E → ℝ)
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ base e.1) s β q r hβ hr) :
    ∀ v (c : Color), G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦
        G.colorIndependentProposal (Color := Color) base e.1 c)
        s β q r hβ hr :=
  fun v _c ↦ R0 v

/-- A color-independent local-polytope point needs only one bounded profile
realization per vertex.  Reusing it in all colors is therefore a valid
choice of the full realization family. -/
theorem exists_colorIndependentRealization_family
    (base : G.E → ℝ)
    (hlocal : ∀ v,
      G.IsAverageOfStarFeasibleSets v
        (fun e : G.StarEdge v ↦ base e.1))
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hq : 0 < q) :
    Nonempty (∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ base e.1) s β q r hβ hr) := by
  classical
  exact ⟨fun v ↦ Classical.choice
    (G.exists_boundedProfileRealization (hlocal v) hs hs1 hβ hq hr)⟩

/-- In the simple coefficient-one application, local `n`-bin packings give
one common `1/n` profile realization at each vertex, which can then be
reused in every color. -/
theorem exists_uniformRealization_family_of_localPacking
    {n : ℕ} (hn : 0 < n) (hpack : G.LocallyPacksInto n)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hq : 0 < q) :
    Nonempty (∀ v, G.BoundedProfileRealization
      (fun _e : G.StarEdge v ↦ 1 / (n : ℝ)) s β q r hβ hr) := by
  apply G.exists_colorIndependentRealization_family
    (base := fun _e ↦ 1 / (n : ℝ))
    (hlocal := fun v ↦ G.uniform_average_of_packsStarInto hn (hpack v))
    hs hs1 hq

/-- With the reused realization family, the padded profile law at a vertex
is definitionally independent of the color label. -/
theorem paddedProfileProbability_colorIndependent
    (base : G.E → ℝ)
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ base e.1) s β q r hβ hr)
    (v : G.V) (c d : Color)
    (a : Fin (profileStateBound β q r)) :
    G.paddedProfileProbability
        (proposal := G.colorIndependentProposal base)
        (R := G.colorIndependentRealization base R0) (v, c) a =
      G.paddedProfileProbability
        (proposal := G.colorIndependentProposal base)
        (R := G.colorIndependentRealization base R0) (v, d) a := by
  rfl

/-- A padded state of positive probability is the code of an actual rounded
profile of positive mass.  Thus support-preserving state balancing never
selects a padding-only code. -/
theorem exists_profile_of_paddedProfileProbability_pos
    (base : G.E → ℝ)
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ base e.1) s β q r hβ hr)
    (src : G.ProfileSource Color)
    (a : Fin (profileStateBound β q r))
    (ha : 0 < G.paddedProfileProbability
      (proposal := G.colorIndependentProposal base)
      (R := G.colorIndependentRealization base R0) src a) :
    ∃ P : {P // P ∈
        G.roundedProfileMenu (R0 src.1).law hβ hr},
      G.profileStateCode
          (proposal := G.colorIndependentProposal base)
          (R := G.colorIndependentRealization base R0) src.1 src.2 P = a ∧
        0 < G.roundedProfileMass (R0 src.1).law hβ hr P.1 := by
  classical
  unfold paddedProfileProbability at ha
  have hnonneg : ∀ P : {P // P ∈
      G.roundedProfileMenu (R0 src.1).law hβ hr},
      0 ≤ (if G.profileStateCode
          (proposal := G.colorIndependentProposal base)
          (R := G.colorIndependentRealization base R0) src.1 src.2 P = a then
        G.roundedProfileMass (R0 src.1).law hβ hr P.1 else 0) := by
    intro P
    split
    · exact G.roundedProfileMass_nonneg (R0 src.1).law hβ hr P.1
    · exact le_rfl
  rcases (Finset.sum_pos_iff_of_nonneg
      (fun P _hP ↦ hnonneg P)).mp ha with ⟨P, _hP, hP⟩
  by_cases hcode : G.profileStateCode
      (proposal := G.colorIndependentProposal base)
      (R := G.colorIndependentRealization base R0) src.1 src.2 P = a
  · have hmass : 0 <
        G.roundedProfileMass (R0 src.1).law hβ hr P.1 := by
      simpa [hcode] using hP
    exact ⟨P, hcode, hmass⟩
  · simp [hcode] at hP

/-- For a fixed reference color, balance the concrete padded profile law at
every vertex across all colors.  The chosen state word controls every
bounded function of one local profile state with parameter-only additive
error `profileStateBound * B`.

The conclusion is intentionally quantified over `f` after `choice`: all
ordinary-slot, local-load, and local-loss statistics that depend on one
vertex's selected profile state can therefore be inserted later without a
new selection argument. -/
theorem exists_balanced_colorIndependentProfile_choice
    (base : G.E → ℝ)
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ base e.1) s β q r hβ hr)
    (c0 : Color) :
    ∃ choice : G.V → Color → Fin (profileStateBound β q r),
      ∀ v
        (f : Fin (profileStateBound β q r) → ℝ) (B : ℝ),
        (∀ a, 0 ≤ f a) → (∀ a, f a ≤ B) →
        |(∑ c, f (choice v c)) -
          (Fintype.card Color : ℝ) *
            (∑ a,
              G.paddedProfileProbability
                (proposal := G.colorIndependentProposal base)
                (R := G.colorIndependentRealization base R0) (v, c0) a *
              f a)| ≤
          profileStateBound β q r * B := by
  let prob : G.V → Fin (profileStateBound β q r) → ℝ :=
    fun v a ↦ G.paddedProfileProbability
      (proposal := G.colorIndependentProposal base)
      (R := G.colorIndependentRealization base R0) (v, c0) a
  have hp0 : ∀ v a, 0 ≤ prob v a := by
    intro v a
    exact G.paddedProfileProbability_nonneg
      (proposal := G.colorIndependentProposal base)
      (R := G.colorIndependentRealization base R0) (v, c0) a
  have hpsum : ∀ v, ∑ a, prob v a = 1 := by
    intro v
    exact G.sum_paddedProfileProbability
      (proposal := G.colorIndependentProposal base)
      (R := G.colorIndependentRealization base R0) (v, c0)
  simpa [prob] using
    (exists_vertexwise_choice_all_bounded_statistics
      (Color := Color) prob hp0 hpsum)

/-- Support-preserving concrete balancing.  In addition to the same
parameter-only error for every local statistic, each selected padded state
is certified to encode a real positive-mass profile. -/
theorem exists_supported_balanced_colorIndependentProfile_choice
    (base : G.E → ℝ)
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ base e.1) s β q r hβ hr)
    (c0 : Color) :
    ∃ choice : G.V → Color → Fin (profileStateBound β q r),
      (∀ v c, 0 <
        G.paddedProfileProbability
          (proposal := G.colorIndependentProposal base)
          (R := G.colorIndependentRealization base R0) (v, c0) (choice v c)) ∧
      ∀ v
        (f : Fin (profileStateBound β q r) → ℝ) (B : ℝ),
        (∀ a, 0 ≤ f a) → (∀ a, f a ≤ B) →
        |(∑ c, f (choice v c)) -
          (Fintype.card Color : ℝ) *
            (∑ a,
              G.paddedProfileProbability
                (proposal := G.colorIndependentProposal base)
                (R := G.colorIndependentRealization base R0) (v, c0) a *
              f a)| ≤
          profileStateBound β q r * B := by
  let prob : G.V → Fin (profileStateBound β q r) → ℝ :=
    fun v a ↦ G.paddedProfileProbability
      (proposal := G.colorIndependentProposal base)
      (R := G.colorIndependentRealization base R0) (v, c0) a
  have hp0 : ∀ v a, 0 ≤ prob v a := by
    intro v a
    exact G.paddedProfileProbability_nonneg
      (proposal := G.colorIndependentProposal base)
      (R := G.colorIndependentRealization base R0) (v, c0) a
  have hpsum : ∀ v, ∑ a, prob v a = 1 := by
    intro v
    exact G.sum_paddedProfileProbability
      (proposal := G.colorIndependentProposal base)
      (R := G.colorIndependentRealization base R0) (v, c0)
  simpa [prob] using
    (exists_vertexwise_supported_choice_all_bounded_statistics
      (Color := Color) prob hp0 hpsum)

/-- Concrete state-count form of the preceding theorem. -/
theorem exists_balanced_colorIndependentProfile_stateCount
    (base : G.E → ℝ)
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ base e.1) s β q r hβ hr)
    (c0 : Color) :
    ∃ choice : G.V → Color → Fin (profileStateBound β q r),
      ∀ v a,
        (((Finset.univ : Finset Color).filter
          (fun c ↦ choice v c = a)).card : ℝ) ≤
          (Fintype.card Color : ℝ) *
            G.paddedProfileProbability
              (proposal := G.colorIndependentProposal base)
              (R := G.colorIndependentRealization base R0) (v, c0) a + 1 := by
  let prob : G.V → Fin (profileStateBound β q r) → ℝ :=
    fun v a ↦ G.paddedProfileProbability
      (proposal := G.colorIndependentProposal base)
      (R := G.colorIndependentRealization base R0) (v, c0) a
  have hp0 : ∀ v a, 0 ≤ prob v a := by
    intro v a
    exact G.paddedProfileProbability_nonneg
      (proposal := G.colorIndependentProposal base)
      (R := G.colorIndependentRealization base R0) (v, c0) a
  have hpsum : ∀ v, ∑ a, prob v a = 1 := by
    intro v
    exact G.sum_paddedProfileProbability
      (proposal := G.colorIndependentProposal base)
      (R := G.colorIndependentRealization base R0) (v, c0)
  have hv : ∀ v : G.V, ∃ choice : Color → Fin (profileStateBound β q r),
      ∀ a,
        (((Finset.univ : Finset Color).filter
          (fun c ↦ choice c = a)).card : ℝ) ≤
          (Fintype.card Color : ℝ) * prob v a + 1 := by
    intro v
    exact exists_choice_stateCount_le (Color := Color) (prob v) (hp0 v) (hpsum v)
  let choice : G.V → Color → Fin (profileStateBound β q r) :=
    fun v ↦ Classical.choose (hv v)
  refine ⟨choice, ?_⟩
  intro v a
  simpa [prob, choice] using (Classical.choose_spec (hv v) a)

end WeightedMultigraph

end

end WeightedEdgeColoring
