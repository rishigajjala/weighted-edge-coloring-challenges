import WeightedEdgeColoring.UniformSelectedProfileFamily
import WeightedEdgeColoring.GlobalCyclicProfileShiftLocal
import WeightedEdgeColoring.GlobalCyclicProfileShiftTail

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

/-!
# Cyclic synchronization of selected profile words

The uniform profile theorem gives one positive-mass, unit-safe rounded
profile at every vertex and color.  Here colors are `Fin n`, so these choices
form a word at each vertex.  Rotating a word preserves positivity, safety,
and every one-vertex statistic sum.  The local cyclic-shift theorem can then
synchronize the words across all graph edges.

The final theorem keeps the one remaining probabilistic input explicit: a
conditional scalar tail bound at one vertex.  It does not claim to derive
that tail estimate merely from bounded pair costs.
-/

universe u

variable (G : WeightedSimpleGraph.{u})
variable {n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}

/-- The type of concrete selected rounded-profile words indexed by `Fin n`. -/
abbrev SelectedProfileWord
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr) :=
  ∀ v (c : Fin n), {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr}

/-- Every selected profile has positive mass. -/
def SelectedProfilePositive
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (selected : G.SelectedProfileWord R0) : Prop :=
  ∀ v c, 0 < G.roundedProfileMass (R0 v).law hβ hr (selected v c).1

/-- Every selected profile is a safe unit bin. -/
def SelectedProfileSafe
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (selected : G.SelectedProfileWord R0) : Prop :=
  ∀ v c, G.roundedProfileLoad (R0 v).law (selected v c).1 ≤ 1

/-- The simultaneous one-vertex balancing property supplied by the uniform
selected-profile theorem. -/
def SelectedProfileBalanced
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (c0 : Fin n) (selected : G.SelectedProfileWord R0) : Prop :=
  ∀ v
    (f : Fin (profileStateBound β q r) → ℝ) (B : ℝ),
    (∀ a, 0 ≤ f a) → (∀ a, f a ≤ B) →
    |(∑ c : Fin n, f (G.profileStateCode
        (proposal := G.colorIndependentProposal (Color := Fin n)
          (fun _e : G.E ↦ (1 : ℝ) / n))
        (R := G.colorIndependentRealization
          (Color := Fin n) (fun _e : G.E ↦ (1 : ℝ) / n) R0)
        v c (selected v c))) -
      (n : ℝ) *
        (∑ a : Fin (profileStateBound β q r),
          G.paddedProfileProbability
            (proposal := G.colorIndependentProposal (Color := Fin n)
              (fun _e : G.E ↦ (1 : ℝ) / n))
            (R := G.colorIndependentRealization
              (Color := Fin n) (fun _e : G.E ↦ (1 : ℝ) / n) R0)
            (v, c0) a * f a)| ≤
      profileStateBound β q r * B

/-- A canonical balanced concrete profile word, obtained by choice from
`exists_balanced_selectedProfile_family`. -/
def canonicalSelectedProfileWord
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (c0 : Fin n) : G.SelectedProfileWord R0 :=
  Classical.choose
    (G.exists_balanced_selectedProfile_family
      (Color := Fin n) (fun _e : G.E ↦ (1 : ℝ) / n) R0 c0)

theorem canonicalSelectedProfileWord_positive
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (c0 : Fin n) :
    G.SelectedProfilePositive R0 (G.canonicalSelectedProfileWord R0 c0) := by
  exact (Classical.choose_spec
    (G.exists_balanced_selectedProfile_family
      (Color := Fin n) (fun _e : G.E ↦ (1 : ℝ) / n) R0 c0)).1

theorem canonicalSelectedProfileWord_safe
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (c0 : Fin n) :
    G.SelectedProfileSafe R0 (G.canonicalSelectedProfileWord R0 c0) := by
  exact (Classical.choose_spec
    (G.exists_balanced_selectedProfile_family
      (Color := Fin n) (fun _e : G.E ↦ (1 : ℝ) / n) R0 c0)).2.1

theorem canonicalSelectedProfileWord_balanced
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (c0 : Fin n) :
    G.SelectedProfileBalanced R0 c0 (G.canonicalSelectedProfileWord R0 c0) := by
  unfold SelectedProfileBalanced canonicalSelectedProfileWord
  simpa only [Fintype.card_fin] using
    (Classical.choose_spec
      (G.exists_balanced_selectedProfile_family
        (Color := Fin n) (fun _e : G.E ↦ (1 : ℝ) / n) R0 c0)).2.2

/-- Rotate the selected word at every vertex by its assigned cyclic shift. -/
def rotateSelectedProfileWord
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (selected : G.SelectedProfileWord R0) (shift : G.V → Fin n) :
    G.SelectedProfileWord R0 :=
  fun v c ↦ selected v (c + shift v)

theorem rotateSelectedProfileWord_positive
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (selected : G.SelectedProfileWord R0)
    (hpos : G.SelectedProfilePositive R0 selected) (shift : G.V → Fin n) :
    G.SelectedProfilePositive R0 (G.rotateSelectedProfileWord R0 selected shift) := by
  intro v c
  exact hpos v (c + shift v)

theorem rotateSelectedProfileWord_safe
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (selected : G.SelectedProfileWord R0)
    (hsafe : G.SelectedProfileSafe R0 selected) (shift : G.V → Fin n) :
    G.SelectedProfileSafe R0 (G.rotateSelectedProfileWord R0 selected shift) := by
  intro v c
  exact hsafe v (c + shift v)

/-- With the reused color-independent realization, the code of a concrete
profile does not depend on the color label. -/
theorem profileStateCode_colorIndependent_fin
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (v : G.V) (c d : Fin n)
    (P : {P // P ∈ G.roundedProfileMenu (R0 v).law hβ hr}) :
    G.profileStateCode
        (proposal := G.colorIndependentProposal (Color := Fin n)
          (fun _e : G.E ↦ (1 : ℝ) / n))
        (R := G.colorIndependentRealization
          (Color := Fin n) (fun _e : G.E ↦ (1 : ℝ) / n) R0)
        v c P =
      G.profileStateCode
        (proposal := G.colorIndependentProposal (Color := Fin n)
          (fun _e : G.E ↦ (1 : ℝ) / n))
        (R := G.colorIndependentRealization
          (Color := Fin n) (fun _e : G.E ↦ (1 : ℝ) / n) R0)
        v d P := by
  rfl

/-- Rotating the colors only permutes every one-vertex statistic sum. -/
theorem rotateSelectedProfileWord_balanced
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (c0 : Fin n) (selected : G.SelectedProfileWord R0)
    (hbalanced : G.SelectedProfileBalanced R0 c0 selected)
    (shift : G.V → Fin n) :
    G.SelectedProfileBalanced R0 c0
      (G.rotateSelectedProfileWord R0 selected shift) := by
  intro v f B hf0 hfB
  have hsum :
      (∑ c : Fin n, f (G.profileStateCode
        (proposal := G.colorIndependentProposal (Color := Fin n)
          (fun _e : G.E ↦ (1 : ℝ) / n))
        (R := G.colorIndependentRealization
          (Color := Fin n) (fun _e : G.E ↦ (1 : ℝ) / n) R0)
        v c (G.rotateSelectedProfileWord R0 selected shift v c))) =
      ∑ c : Fin n, f (G.profileStateCode
        (proposal := G.colorIndependentProposal (Color := Fin n)
          (fun _e : G.E ↦ (1 : ℝ) / n))
        (R := G.colorIndependentRealization
          (Color := Fin n) (fun _e : G.E ↦ (1 : ℝ) / n) R0)
        v c (selected v c)) := by
    let g : Fin n → ℝ := fun c ↦ f (G.profileStateCode
      (proposal := G.colorIndependentProposal (Color := Fin n)
        (fun _e : G.E ↦ (1 : ℝ) / n))
      (R := G.colorIndependentRealization
        (Color := Fin n) (fun _e : G.E ↦ (1 : ℝ) / n) R0)
      v c (selected v c))
    calc
      (∑ c : Fin n, f (G.profileStateCode
          (proposal := G.colorIndependentProposal (Color := Fin n)
            (fun _e : G.E ↦ (1 : ℝ) / n))
          (R := G.colorIndependentRealization
            (Color := Fin n) (fun _e : G.E ↦ (1 : ℝ) / n) R0)
          v c (G.rotateSelectedProfileWord R0 selected shift v c))) =
          ∑ c : Fin n, g (c + shift v) := by
        apply Finset.sum_congr rfl
        intro c _hc
        unfold g rotateSelectedProfileWord
        rw [G.profileStateCode_colorIndependent_fin R0 v c (c + shift v)]
      _ = ∑ c : Fin n, g c := by
        simpa [add_comm] using WeightedEdgeColoring.sum_cyclic_add_left (shift v) g
      _ = ∑ c : Fin n, f (G.profileStateCode
          (proposal := G.colorIndependentProposal (Color := Fin n)
            (fun _e : G.E ↦ (1 : ℝ) / n))
          (R := G.colorIndependentRealization
            (Color := Fin n) (fun _e : G.E ↦ (1 : ℝ) / n) R0)
          v c (selected v c)) := by rfl
  rw [hsum]
  exact hbalanced v f B hf0 hfB

/-- A pair cost may compare profiles from the two different endpoint menus
of an edge. -/
abbrev SelectedProfilePairCost
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr) :=
  ∀ e : G.E,
    {P // P ∈ G.roundedProfileMenu (R0 (G.fst e)).law hβ hr} →
    {P // P ∈ G.roundedProfileMenu (R0 (G.snd e)).law hβ hr} → ℝ

/-- The normalized cost of pairing the two endpoint words with relative
shift `t`.  Normalization by `n` makes this the cost per color. -/
def selectedProfileEdgeCyclicCost
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (selected : G.SelectedProfileWord R0)
    (pairCost : G.SelectedProfilePairCost R0)
    (e : G.E) (t : Fin n) : ℝ :=
  WeightedEdgeColoring.cyclicPairCost
      (selected (G.fst e)) (selected (G.snd e)) (pairCost e) t /
    (n : ℝ)

theorem selectedProfileEdgeCyclicCost_nonneg
    (hn : 0 < n)
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (selected : G.SelectedProfileWord R0)
    (pairCost : G.SelectedProfilePairCost R0)
    (hpair0 : ∀ e P Q, 0 ≤ pairCost e P Q) :
    ∀ e t, 0 ≤ G.selectedProfileEdgeCyclicCost R0 selected pairCost e t := by
  intro e t
  unfold selectedProfileEdgeCyclicCost WeightedEdgeColoring.cyclicPairCost
  exact div_nonneg (Finset.sum_nonneg fun c _hc ↦ hpair0 e _ _)
    (by positivity)

theorem selectedProfileEdgeCyclicCost_le
    (hn : 0 < n)
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (selected : G.SelectedProfileWord R0)
    (pairCost : G.SelectedProfilePairCost R0) (B : ℝ)
    (hpairB : ∀ e P Q, pairCost e P Q ≤ B) :
    ∀ e t, G.selectedProfileEdgeCyclicCost R0 selected pairCost e t ≤ B := by
  intro e t
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold selectedProfileEdgeCyclicCost WeightedEdgeColoring.cyclicPairCost
  calc
    (∑ c : Fin n,
        pairCost e (selected (G.fst e) c)
          (selected (G.snd e) (c + t))) / (n : ℝ) ≤
        (∑ _c : Fin n, B) / (n : ℝ) := by
      exact div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun c _hc ↦ hpairB e _ _)
        (by positivity)
    _ = B := by simp [hnR]

/-- Average pair cost on the edges incident with `x`, after all selected
profile words have been rotated. -/
def rotatedSelectedIncidentPairCost
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (selected : G.SelectedProfileWord R0)
    (pairCost : G.SelectedProfilePairCost R0)
    (shift : G.V → Fin n) (x : G.V) : ℝ :=
  ∑ e ∈ WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.incidentSet G.fst G.snd x,
    (∑ c : Fin n,
      pairCost e
        (G.rotateSelectedProfileWord R0 selected shift (G.fst e) c)
        (G.rotateSelectedProfileWord R0 selected shift (G.snd e) c)) /
      (n : ℝ)

/-- The shifted-pair identity with different state types at the two
endpoints. -/
theorem shifted_pair_sum_eq_cyclicPairCost_heterogeneous
    {A B : Type*} (hn : 0 < n)
    (a : Fin n → A) (b : Fin n → B) (f : A → B → ℝ)
    (sa sb : Fin n) :
    (∑ c : Fin n, f (a (c + sa)) (b (c + sb))) =
      WeightedEdgeColoring.cyclicPairCost a b f (sb - sa) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hind (c : Fin n) :
      (sa + c) + (sb - sa) = c + sb := by
    calc
      (sa + c) + (sb - sa) = c + ((sb - sa) + sa) := by ac_rfl
      _ = c + sb := by rw [sub_add_cancel]
  calc
    (∑ c : Fin n, f (a (c + sa)) (b (c + sb))) =
        ∑ c : Fin n,
          f (a (sa + c)) (b ((sa + c) + (sb - sa))) := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [add_comm c sa, hind]
    _ = ∑ d : Fin n, f (a d) (b (d + (sb - sa))) :=
      WeightedEdgeColoring.sum_cyclic_add_left sa
        (fun d ↦ f (a d) (b (d + (sb - sa))))
    _ = WeightedEdgeColoring.cyclicPairCost a b f (sb - sa) := by rfl

/-- Literal rotated selected-profile cost is exactly the incident
relative-shift cost used by `GlobalCyclicProfileShiftLocal`. -/
theorem rotatedSelectedIncidentPairCost_eq_vertexIncidentCost
    (hn : 0 < n)
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (selected : G.SelectedProfileWord R0)
    (pairCost : G.SelectedProfilePairCost R0)
    (shift : G.V → Fin n) (x : G.V) :
    G.rotatedSelectedIncidentPairCost R0 selected pairCost shift x =
      WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.vertexIncidentCost G.fst G.snd
        (G.selectedProfileEdgeCyclicCost R0 selected pairCost) x shift := by
  classical
  unfold rotatedSelectedIncidentPairCost
    WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.vertexIncidentCost
    WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.shiftedEdgeCost
    selectedProfileEdgeCyclicCost rotateSelectedProfileWord
  apply Finset.sum_congr rfl
  intro e _he
  congr 1
  exact shifted_pair_sum_eq_cyclicPairCost_heterogeneous hn
    (selected (G.fst e)) (selected (G.snd e)) (pairCost e)
    (shift (G.fst e)) (shift (G.snd e))

/-- The remaining scalar probability input for local synchronization.
The centre shift is fixed, while all other vertex shifts remain independent
and uniform. -/
def SelectedProfileConditionalTail
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (selected : G.SelectedProfileWord R0)
    (pairCost : G.SelectedProfilePairCost R0)
    (tau p : ℝ) : Prop :=
  ∀ (x : G.V)
    (center : WeightedEdgeColoring.FiniteCategoricalSupportSplit.Inside
      ({x} : Finset G.V) → Fin n),
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
      (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
        (WeightedEdgeColoring.FiniteCategoricalSupportSplit.outsideProb
          (WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.uniformShiftProb
            (V := G.V) (n := n)) ({x} : Finset G.V)))
      (WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.conditionalBadVertex
        G.fst G.snd
        (G.selectedProfileEdgeCyclicCost R0 selected pairCost)
        tau x center) ≤ p

/-- Local cyclic synchronization for one already chosen balanced selected
profile word. Boundedness packages the normalized edge costs in `[0,B]`;
the conditional scalar tail remains an explicit hypothesis. -/
theorem exists_rotation_for_selectedProfile_of_conditional_tail
    (hn : 0 < n)
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (c0 : Fin n) (selected : G.SelectedProfileWord R0)
    (pairCost : G.SelectedProfilePairCost R0)
    (B tau p lllWeight : ℝ) (D : ℕ)
    (hpos : G.SelectedProfilePositive R0 selected)
    (hsafe : G.SelectedProfileSafe R0 selected)
    (hbalanced : G.SelectedProfileBalanced R0 c0 selected)
    (hpair0 : ∀ e P Q, 0 ≤ pairCost e P Q)
    (hpairB : ∀ e P Q, pairCost e P Q ≤ B)
    (hdegree : ∀ x,
      (WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.neighborSet
        G.fst G.snd x).card ≤ D)
    (hweight0 : 0 ≤ lllWeight) (hweight1 : lllWeight < 1)
    (hnumeric : p ≤ lllWeight *
      (1 - lllWeight) ^ ((D + 1) * (D + 1)))
    (htail : G.SelectedProfileConditionalTail R0 selected pairCost tau p) :
    ∃ shift : G.V → Fin n,
      G.SelectedProfilePositive R0
          (G.rotateSelectedProfileWord R0 selected shift) ∧
      G.SelectedProfileSafe R0
          (G.rotateSelectedProfileWord R0 selected shift) ∧
      G.SelectedProfileBalanced R0 c0
          (G.rotateSelectedProfileWord R0 selected shift) ∧
      (∀ e t,
        0 ≤ G.selectedProfileEdgeCyclicCost R0 selected pairCost e t) ∧
      (∀ e t,
        G.selectedProfileEdgeCyclicCost R0 selected pairCost e t ≤ B) ∧
      ∀ x,
        G.rotatedSelectedIncidentPairCost R0 selected pairCost shift x ≤
          WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.vertexCyclicAverage
            G.fst G.snd
            (G.selectedProfileEdgeCyclicCost R0 selected pairCost) x + tau := by
  have hedge0 := G.selectedProfileEdgeCyclicCost_nonneg hn R0 selected
    pairCost hpair0
  have hedgeB := G.selectedProfileEdgeCyclicCost_le hn R0 selected
    pairCost B hpairB
  obtain ⟨shift, hshift⟩ :=
    WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.exists_shift_all_vertexIncidentCost_le
      hn G.fst G.snd
      (G.selectedProfileEdgeCyclicCost R0 selected pairCost)
      tau p lllWeight D hdegree hweight0 hweight1 hnumeric htail
  refine ⟨shift,
    G.rotateSelectedProfileWord_positive R0 selected hpos shift,
    G.rotateSelectedProfileWord_safe R0 selected hsafe shift,
    G.rotateSelectedProfileWord_balanced R0 c0 selected hbalanced shift,
    hedge0, hedgeB, ?_⟩
  intro x
  rw [G.rotatedSelectedIncidentPairCost_eq_vertexIncidentCost hn]
  exact hshift x

/-- Bridge from `exists_balanced_selectedProfile_family` to one global
rotation satisfying all local incident-cost bounds. The concrete selected
word is the canonical witness supplied by that theorem. -/
theorem exists_synchronized_balanced_selectedProfile_family_of_conditional_tail
    (hn : 0 < n)
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (c0 : Fin n)
    (pairCost : G.SelectedProfilePairCost R0)
    (B tau p lllWeight : ℝ) (D : ℕ)
    (hpair0 : ∀ e P Q, 0 ≤ pairCost e P Q)
    (hpairB : ∀ e P Q, pairCost e P Q ≤ B)
    (hdegree : ∀ x,
      (WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.neighborSet
        G.fst G.snd x).card ≤ D)
    (hweight0 : 0 ≤ lllWeight) (hweight1 : lllWeight < 1)
    (hnumeric : p ≤ lllWeight *
      (1 - lllWeight) ^ ((D + 1) * (D + 1)))
    (htail : G.SelectedProfileConditionalTail R0
      (G.canonicalSelectedProfileWord R0 c0) pairCost tau p) :
    ∃ shift : G.V → Fin n,
      G.SelectedProfilePositive R0
        (G.rotateSelectedProfileWord R0
          (G.canonicalSelectedProfileWord R0 c0) shift) ∧
      G.SelectedProfileSafe R0
        (G.rotateSelectedProfileWord R0
          (G.canonicalSelectedProfileWord R0 c0) shift) ∧
      G.SelectedProfileBalanced R0 c0
        (G.rotateSelectedProfileWord R0
          (G.canonicalSelectedProfileWord R0 c0) shift) ∧
      (∀ e t, 0 ≤ G.selectedProfileEdgeCyclicCost R0
        (G.canonicalSelectedProfileWord R0 c0) pairCost e t) ∧
      (∀ e t, G.selectedProfileEdgeCyclicCost R0
        (G.canonicalSelectedProfileWord R0 c0) pairCost e t ≤ B) ∧
      ∀ x,
        G.rotatedSelectedIncidentPairCost R0
            (G.canonicalSelectedProfileWord R0 c0) pairCost shift x ≤
          WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.vertexCyclicAverage
            G.fst G.snd
            (G.selectedProfileEdgeCyclicCost R0
              (G.canonicalSelectedProfileWord R0 c0) pairCost) x + tau := by
  exact G.exists_rotation_for_selectedProfile_of_conditional_tail hn R0 c0
    (G.canonicalSelectedProfileWord R0 c0) pairCost B tau p lllWeight D
    (G.canonicalSelectedProfileWord_positive R0 c0)
    (G.canonicalSelectedProfileWord_safe R0 c0)
    (G.canonicalSelectedProfileWord_balanced R0 c0)
    hpair0 hpairB hdegree hweight0 hweight1 hnumeric htail

/-- Square-root-error form of the bridge. This theorem assumes, rather
than derives, the conditional exponential tail `exp (-L)`. Supplying that
one scalar estimate yields the simultaneous bound at every vertex. -/
theorem exists_synchronized_balanced_selectedProfile_family_of_conditional_exponential_tail
    (hn : 0 < n)
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (c0 : Fin n)
    (pairCost : G.SelectedProfilePairCost R0)
    (B L lllWeight : ℝ) (D : ℕ)
    (hpair0 : ∀ e P Q, 0 ≤ pairCost e P Q)
    (hpairB : ∀ e P Q, pairCost e P Q ≤ B)
    (hdegree : ∀ x,
      (WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.neighborSet
        G.fst G.snd x).card ≤ D)
    (hweight0 : 0 ≤ lllWeight) (hweight1 : lllWeight < 1)
    (hnumeric : Real.exp (-L) ≤ lllWeight *
      (1 - lllWeight) ^ ((D + 1) * (D + 1)))
    (htail : G.SelectedProfileConditionalTail R0
      (G.canonicalSelectedProfileWord R0 c0) pairCost
      (B * Real.sqrt ((D : ℝ) * L / 2))
      (Real.exp (-L))) :
    ∃ shift : G.V → Fin n,
      G.SelectedProfilePositive R0
        (G.rotateSelectedProfileWord R0
          (G.canonicalSelectedProfileWord R0 c0) shift) ∧
      G.SelectedProfileSafe R0
        (G.rotateSelectedProfileWord R0
          (G.canonicalSelectedProfileWord R0 c0) shift) ∧
      G.SelectedProfileBalanced R0 c0
        (G.rotateSelectedProfileWord R0
          (G.canonicalSelectedProfileWord R0 c0) shift) ∧
      (∀ e t, 0 ≤ G.selectedProfileEdgeCyclicCost R0
        (G.canonicalSelectedProfileWord R0 c0) pairCost e t) ∧
      (∀ e t, G.selectedProfileEdgeCyclicCost R0
        (G.canonicalSelectedProfileWord R0 c0) pairCost e t ≤ B) ∧
      ∀ x,
        G.rotatedSelectedIncidentPairCost R0
            (G.canonicalSelectedProfileWord R0 c0) pairCost shift x ≤
          WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.vertexCyclicAverage
            G.fst G.snd
            (G.selectedProfileEdgeCyclicCost R0
              (G.canonicalSelectedProfileWord R0 c0) pairCost) x +
          B * Real.sqrt ((D : ℝ) * L / 2) := by
  exact
    G.exists_synchronized_balanced_selectedProfile_family_of_conditional_tail
      hn R0 c0 pairCost B
      (B * Real.sqrt ((D : ℝ) * L / 2))
      (Real.exp (-L)) lllWeight D hpair0 hpairB hdegree hweight0
      hweight1 hnumeric htail

/-- The conditional exponential tail required by cyclic synchronization is
automatic for the bounded pair costs of a simple graph.  The elementary
finite categorical proof gives additive error `2 B sqrt(D L)`. -/
theorem selectedProfileConditionalTail_exp_proved
    (hn : 0 < n)
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (selected : G.SelectedProfileWord R0)
    (pairCost : G.SelectedProfilePairCost R0)
    (B L : ℝ) (D : ℕ)
    (hB : 0 < B) (hD : 0 < D) (hL0 : 0 ≤ L) (hLD : L ≤ D)
    (hpair0 : ∀ e P Q, 0 ≤ pairCost e P Q)
    (hpairB : ∀ e P Q, pairCost e P Q ≤ B)
    (hdegree : ∀ x,
      (WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.neighborSet
        G.fst G.snd x).card ≤ D) :
    G.SelectedProfileConditionalTail R0 selected pairCost
      (B * (2 * Real.sqrt ((D : ℝ) * L))) (Real.exp (-L)) := by
  have hsimple : ∀ e f,
      ((G.fst e = G.fst f ∧ G.snd e = G.snd f) ∨
       (G.fst e = G.snd f ∧ G.snd e = G.fst f)) → e = f := by
    intro e f hef
    exact G.endpoints_injective ((Sym2.eq_iff).2 hef)
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
  have hmul0 : 0 ≤ (D : ℝ) * L := mul_nonneg hDreal.le hL0
  have hsqrtSq : (Real.sqrt ((D : ℝ) * L)) ^ 2 = (D : ℝ) * L :=
    Real.sq_sqrt hmul0
  have hsqrtLe : Real.sqrt ((D : ℝ) * L) ≤ (D : ℝ) := by
    have hDL : (D : ℝ) * L ≤ (D : ℝ) * D :=
      mul_le_mul_of_nonneg_left hLD hDreal.le
    nlinarith [Real.sqrt_nonneg ((D : ℝ) * L)]
  have ht0 : 0 ≤ (2 : ℝ) * Real.sqrt ((D : ℝ) * L) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have htD : (2 : ℝ) * Real.sqrt ((D : ℝ) * L) ≤ 2 * D := by
    nlinarith
  intro x center
  have htail :=
    WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.conditionalBadVertex_mass_le_exp_sq
      hn G.fst G.snd G.noLoop hsimple
      (G.selectedProfileEdgeCyclicCost R0 selected pairCost)
      B hB
      (G.selectedProfileEdgeCyclicCost_nonneg hn R0 selected pairCost hpair0)
      (G.selectedProfileEdgeCyclicCost_le hn R0 selected pairCost B hpairB)
      D hD hdegree
      (2 * Real.sqrt ((D : ℝ) * L)) ht0 htD x center
  have htSq :
      ((2 : ℝ) * Real.sqrt ((D : ℝ) * L)) ^ 2 =
        4 * ((D : ℝ) * L) := by
    nlinarith
  have hexponent :
      -(((2 : ℝ) * Real.sqrt ((D : ℝ) * L)) ^ 2) / (4 * D) = -L := by
    rw [htSq]
    field_simp [ne_of_gt hDreal]
  rw [hexponent] at htail
  exact htail

/-- Fully proved square-root synchronization theorem.  This invokes the
finite local lemma after discharging its conditional tail input by
`selectedProfileConditionalTail_exp_proved`. -/
theorem exists_synchronized_balanced_selectedProfile_family_exp_proved
    (hn : 0 < n)
    (R0 : ∀ v, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)
    (c0 : Fin n)
    (pairCost : G.SelectedProfilePairCost R0)
    (B L lllWeight : ℝ) (D : ℕ)
    (hB : 0 < B) (hD : 0 < D) (hL0 : 0 ≤ L) (hLD : L ≤ D)
    (hpair0 : ∀ e P Q, 0 ≤ pairCost e P Q)
    (hpairB : ∀ e P Q, pairCost e P Q ≤ B)
    (hdegree : ∀ x,
      (WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.neighborSet
        G.fst G.snd x).card ≤ D)
    (hweight0 : 0 ≤ lllWeight) (hweight1 : lllWeight < 1)
    (hnumeric : Real.exp (-L) ≤ lllWeight *
      (1 - lllWeight) ^ ((D + 1) * (D + 1))) :
    ∃ shift : G.V → Fin n,
      G.SelectedProfilePositive R0
        (G.rotateSelectedProfileWord R0
          (G.canonicalSelectedProfileWord R0 c0) shift) ∧
      G.SelectedProfileSafe R0
        (G.rotateSelectedProfileWord R0
          (G.canonicalSelectedProfileWord R0 c0) shift) ∧
      G.SelectedProfileBalanced R0 c0
        (G.rotateSelectedProfileWord R0
          (G.canonicalSelectedProfileWord R0 c0) shift) ∧
      (∀ e t, 0 ≤ G.selectedProfileEdgeCyclicCost R0
        (G.canonicalSelectedProfileWord R0 c0) pairCost e t) ∧
      (∀ e t, G.selectedProfileEdgeCyclicCost R0
        (G.canonicalSelectedProfileWord R0 c0) pairCost e t ≤ B) ∧
      ∀ x,
        G.rotatedSelectedIncidentPairCost R0
            (G.canonicalSelectedProfileWord R0 c0) pairCost shift x ≤
          WeightedEdgeColoring.GlobalCyclicProfileShiftLocal.vertexCyclicAverage
            G.fst G.snd
            (G.selectedProfileEdgeCyclicCost R0
              (G.canonicalSelectedProfileWord R0 c0) pairCost) x +
          B * (2 * Real.sqrt ((D : ℝ) * L)) := by
  exact
    G.exists_synchronized_balanced_selectedProfile_family_of_conditional_tail
      hn R0 c0 pairCost B (B * (2 * Real.sqrt ((D : ℝ) * L)))
      (Real.exp (-L)) lllWeight D hpair0 hpairB hdegree hweight0 hweight1
      hnumeric
      (G.selectedProfileConditionalTail_exp_proved hn R0
        (G.canonicalSelectedProfileWord R0 c0) pairCost B L D hB hD hL0 hLD
        hpair0 hpairB hdegree)

end WeightedSimpleGraph

end

end WeightedEdgeColoring
