import WeightedEdgeColoring.TwoConstraintChoice
import WeightedEdgeColoring.HarmonicBinCharge
import WeightedEdgeColoring.GreedySkeleton

/-!
# Simultaneous selection of compatible weight modes

Each edge chooses one selected mode or the residual mode.  A selected mode
uses the two endpoint constraints for its weight class; the residual option
uses the two endpoint harmonic-charge constraints.  Thus the two-constraint
rounding theorem chooses whole edges and loses only an additive constant in
every row.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u v

variable (G : WeightedMultigraph.{u})
variable {Mode : Type v} [Fintype Mode] [DecidableEq Mode]

/-- Fractional probability with which edge `e` proposes mode `m`.  Heavy
membership has priority; applications use disjoint heavy and light ranges. -/
def compatibleModeProbability
    (H S : Mode → Finset G.E) (heavyProb lightProb : Mode → ℝ)
    (e : G.E) (m : Mode) : ℝ :=
  if e ∈ H m then heavyProb m else if e ∈ S m then lightProb m else 0

/-- Probability left for the residual label. -/
def compatibleModeRemainderProbability
    (H S : Mode → Finset G.E) (heavyProb lightProb : Mode → ℝ)
    (e : G.E) : ℝ :=
  1 - ∑ m, G.compatibleModeProbability H S heavyProb lightProb e m

/-- One option for each selected mode, plus `none` for the residual label. -/
def compatibleModeOptionMass
    (H S : Mode → Finset G.E) (heavyProb lightProb : Mode → ℝ)
    (o : G.E × Option Mode) : ℝ :=
  match o.2 with
  | some m => G.compatibleModeProbability H S heavyProb lightProb o.1 m
  | none => G.compatibleModeRemainderProbability H S heavyProb lightProb o.1

/-- A selected mode has a heavy and a light row at every vertex.  The right
summand is the residual harmonic-charge row. -/
abbrev CompatibleModeConstraint (G : WeightedMultigraph.{u}) (Mode : Type v) :=
  Sum (Mode × Bool × G.V) G.V

/-- Resource use of one mode option.  `true` is the heavy row and `false` is
the light row. -/
noncomputable def compatibleModeUse
    (H S : Mode → Finset G.E)
    (o : G.E × Option Mode) (r : G.CompatibleModeConstraint Mode) : ℝ :=
  match o.2, r with
  | some m, Sum.inl (m', heavy, vertex) =>
      if m = m' ∧ G.Inc vertex o.1 ∧
          (if heavy then o.1 ∈ H m else o.1 ∉ H m ∧ o.1 ∈ S m)
      then 1 else 0
  | none, Sum.inr vertex =>
      if G.Inc vertex o.1 then harmonicCharge (G.weight o.1) else 0
  | _, _ => 0

/-- Edges assigned to the heavy part of mode `m`. -/
def selectedModeHeavyEdges (label : G.E → Option Mode)
    (H : Mode → Finset G.E) (m : Mode) : Finset G.E :=
  Finset.univ.filter fun e ↦ label e = some m ∧ e ∈ H m

/-- All edges carrying one selected mode label. -/
def selectedModeEdges (label : G.E → Option Mode) (m : Mode) : Finset G.E :=
  Finset.univ.filter fun e ↦ label e = some m

/-- Edges assigned to the light part of mode `m`. -/
def selectedModeLightEdges (label : G.E → Option Mode)
    (H S : Mode → Finset G.E) (m : Mode) : Finset G.E :=
  Finset.univ.filter fun e ↦ label e = some m ∧ e ∉ H m ∧ e ∈ S m

/-- Edges assigned to the residual label. -/
def selectedModeResidualEdges (label : G.E → Option Mode) : Finset G.E :=
  Finset.univ.filter fun e ↦ label e = none

theorem selectedModeEdges_eq_heavy_union_light
    (label : G.E → Option Mode) (H S : Mode → Finset G.E)
    (heligible : ∀ e m, label e = some m → e ∈ H m ∨ e ∈ S m)
    (m : Mode) :
    G.selectedModeEdges label m =
      G.selectedModeHeavyEdges label H m ∪
        G.selectedModeLightEdges label H S m := by
  classical
  ext e
  constructor
  · intro he
    have hlabel : label e = some m := by
      simpa [selectedModeEdges] using he
    rcases heligible e m hlabel with hH | hS
    · exact Finset.mem_union_left _ (by
        simp [selectedModeHeavyEdges, hlabel, hH])
    · by_cases hH : e ∈ H m
      · exact Finset.mem_union_left _ (by
          simp [selectedModeHeavyEdges, hlabel, hH])
      · exact Finset.mem_union_right _ (by
          simp [selectedModeLightEdges, hlabel, hH, hS])
  · intro he
    rcases Finset.mem_union.mp he with heH | heS
    · simpa [selectedModeEdges] using
        (Finset.mem_filter.mp heH).2.1
    · simpa [selectedModeEdges] using
        (Finset.mem_filter.mp heS).2.1

theorem selectedModeHeavy_light_disjoint
    (label : G.E → Option Mode) (H S : Mode → Finset G.E) (m : Mode) :
    Disjoint (G.selectedModeHeavyEdges label H m)
      (G.selectedModeLightEdges label H S m) := by
  rw [Finset.disjoint_left]
  intro e heH heS
  exact (Finset.mem_filter.mp heS).2.2.1
    (Finset.mem_filter.mp heH).2.2

theorem selectedModeEdges_pairwise_disjoint
    (label : G.E → Option Mode) {m j : Mode} (hmj : m ≠ j) :
    Disjoint (G.selectedModeEdges label m) (G.selectedModeEdges label j) := by
  rw [Finset.disjoint_left]
  intro e hem hej
  have hm : label e = some m := (Finset.mem_filter.mp hem).2
  have hj : label e = some j := (Finset.mem_filter.mp hej).2
  exact hmj (Option.some.inj (hm.symm.trans hj))

theorem selectedModeEdges_residual_disjoint
    (label : G.E → Option Mode) (m : Mode) :
    Disjoint (G.selectedModeEdges label m)
      (G.selectedModeResidualEdges label) := by
  rw [Finset.disjoint_left]
  intro e hem her
  have hm : label e = some m := (Finset.mem_filter.mp hem).2
  have hr : label e = none := (Finset.mem_filter.mp her).2
  simp [hr] at hm

theorem selectedModes_cover_univ (label : G.E → Option Mode) :
    (Finset.univ.biUnion (G.selectedModeEdges label)) ∪
        G.selectedModeResidualEdges label = Finset.univ := by
  classical
  ext e
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
    true_and, selectedModeEdges, selectedModeResidualEdges,
    Finset.mem_filter]
  cases h : label e <;> simp [h]

private theorem compatibleModeProbability_nonneg
    (H S : Mode → Finset G.E) (heavyProb lightProb : Mode → ℝ)
    (hheavy : ∀ m, 0 ≤ heavyProb m) (hlight : ∀ m, 0 ≤ lightProb m)
    (e : G.E) (m : Mode) :
    0 ≤ G.compatibleModeProbability H S heavyProb lightProb e m := by
  unfold compatibleModeProbability
  split_ifs
  · exact hheavy m
  · exact hlight m
  · exact le_rfl

private theorem compatibleModeUse_nonneg
    (H S : Mode → Finset G.E) (o : G.E × Option Mode)
    (r : G.CompatibleModeConstraint Mode) :
    0 ≤ G.compatibleModeUse H S o r := by
  cases o with
  | mk e choice =>
      cases choice with
      | none =>
          cases r with
          | inl z => simp [compatibleModeUse]
          | inr vertex =>
              simp only [compatibleModeUse]
              split_ifs
              · exact harmonicCharge_nonneg _
              · exact le_rfl
      | some m =>
          cases r with
          | inr vertex => simp [compatibleModeUse]
          | inl data =>
              simp only [compatibleModeUse]
              split_ifs <;> norm_num

private theorem compatibleModeUse_le_one
    (H S : Mode → Finset G.E) (o : G.E × Option Mode)
    (r : G.CompatibleModeConstraint Mode) :
    G.compatibleModeUse H S o r ≤ 1 := by
  cases o with
  | mk e choice =>
      cases choice with
      | none =>
          cases r with
          | inl z => simp [compatibleModeUse]
          | inr vertex =>
              by_cases hinc : G.Inc vertex e
              · simp only [compatibleModeUse, hinc, if_true]
                exact harmonicCharge_le_one (G.weight_pos e) (G.weight_le_one e)
              · simp [compatibleModeUse, hinc]
      | some m =>
          cases r with
          | inl data =>
              simp only [compatibleModeUse]
              split_ifs <;> norm_num
          | inr vertex => simp [compatibleModeUse]

private theorem compatibleModeUse_sparse
    (H S : Mode → Finset G.E) (o : G.E × Option Mode) :
    (Finset.univ.filter fun r : G.CompatibleModeConstraint Mode ↦
      G.compatibleModeUse H S o r ≠ 0).card ≤ 2 := by
  classical
  rcases o with ⟨e, choice⟩
  cases choice with
  | none =>
      let endpoints : Finset (G.CompatibleModeConstraint Mode) :=
        {Sum.inr (G.fst e), Sum.inr (G.snd e)}
      apply (Finset.card_le_card ?_).trans
        (show endpoints.card ≤ 2 by
          calc
            endpoints.card ≤
                ({Sum.inr (G.snd e)} :
                  Finset (G.CompatibleModeConstraint Mode)).card + 1 := by
              exact Finset.card_insert_le _ _
            _ = 2 := by simp)
      intro r hr
      have hne : G.compatibleModeUse H S (e, none) r ≠ 0 :=
        (Finset.mem_filter.mp hr).2
      cases r with
      | inl z => simp [compatibleModeUse] at hne
      | inr vertex =>
          have hinc : G.Inc vertex e := by
            by_contra h
            simp [compatibleModeUse, h] at hne
          rcases hinc with hv | hv
          · subst vertex
            simp [endpoints]
          · subst vertex
            simp [endpoints]
  | some m =>
      by_cases hH : e ∈ H m
      · let endpoints : Finset (G.CompatibleModeConstraint Mode) :=
          {Sum.inl (m, true, G.fst e), Sum.inl (m, true, G.snd e)}
        apply (Finset.card_le_card ?_).trans
          (show endpoints.card ≤ 2 by
            calc
              endpoints.card ≤
                  ({Sum.inl (m, true, G.snd e)} :
                    Finset (G.CompatibleModeConstraint Mode)).card + 1 := by
                exact Finset.card_insert_le _ _
              _ = 2 := by simp)
        intro r hr
        have hne : G.compatibleModeUse H S (e, some m) r ≠ 0 :=
          (Finset.mem_filter.mp hr).2
        cases r with
        | inr vertex => simp [compatibleModeUse] at hne
        | inl data =>
            rcases data with ⟨m', heavy, vertex⟩
            have hcond : m = m' ∧ G.Inc vertex e ∧
                (if heavy then e ∈ H m else e ∉ H m ∧ e ∈ S m) := by
              by_contra h
              simp [compatibleModeUse, h] at hne
            rcases hcond with ⟨rfl, hinc, hclass⟩
            have hheavy : heavy = true := by
              cases heavy
              · simp [hH] at hclass
              · rfl
            subst heavy
            rcases hinc with hv | hv
            · subst vertex
              simp [endpoints]
            · subst vertex
              simp [endpoints]
      · by_cases hS : e ∈ S m
        · let endpoints : Finset (G.CompatibleModeConstraint Mode) :=
            {Sum.inl (m, false, G.fst e), Sum.inl (m, false, G.snd e)}
          apply (Finset.card_le_card ?_).trans
            (show endpoints.card ≤ 2 by
              calc
                endpoints.card ≤
                    ({Sum.inl (m, false, G.snd e)} :
                      Finset (G.CompatibleModeConstraint Mode)).card + 1 := by
                  exact Finset.card_insert_le _ _
                _ = 2 := by simp)
          intro r hr
          have hne : G.compatibleModeUse H S (e, some m) r ≠ 0 :=
            (Finset.mem_filter.mp hr).2
          cases r with
          | inr vertex => simp [compatibleModeUse] at hne
          | inl data =>
              rcases data with ⟨m', heavy, vertex⟩
              have hcond : m = m' ∧ G.Inc vertex e ∧
                  (if heavy then e ∈ H m else e ∉ H m ∧ e ∈ S m) := by
                by_contra h
                simp [compatibleModeUse, h] at hne
              rcases hcond with ⟨rfl, hinc, hclass⟩
              have hheavy : heavy = false := by
                cases heavy
                · rfl
                · simp [hH] at hclass
              subst heavy
              rcases hinc with hv | hv
              · subst vertex
                simp [endpoints]
              · subst vertex
                simp [endpoints]
        · have hempty :
            (Finset.univ.filter fun r : G.CompatibleModeConstraint Mode ↦
              G.compatibleModeUse H S (e, some m) r ≠ 0) = ∅ := by
            ext r
            cases r with
            | inr vertex => simp [compatibleModeUse]
            | inl data =>
                rcases data with ⟨m', heavy, vertex⟩
                cases heavy <;> simp [compatibleModeUse, hH, hS]
          rw [hempty]
          simp

private theorem compatibleMode_jobMass
    (H S : Mode → Finset G.E) (heavyProb lightProb : Mode → ℝ)
    (e : G.E) :
    optionJobMass Prod.fst
      (G.compatibleModeOptionMass H S heavyProb lightProb) e = 1 := by
  rw [optionJobMass, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single e]
  · rw [Fintype.sum_option]
    simp only [Prod.fst, if_true, compatibleModeOptionMass]
    change G.compatibleModeRemainderProbability H S heavyProb lightProb e +
      (∑ m, G.compatibleModeProbability H S heavyProb lightProb e m) = 1
    simp [compatibleModeRemainderProbability]
  · intro f _hf hfe
    simp [hfe]
  · simp

private theorem compatibleMode_optionLoad_heavy
    (H S : Mode → Finset G.E) (heavyProb lightProb : Mode → ℝ)
    (m : Mode) (v : G.V) :
    optionLoad (G.compatibleModeUse H S)
        (G.compatibleModeOptionMass H S heavyProb lightProb)
        (Sum.inl (m, true, v)) =
      heavyProb m * (G.degreeOn (H m) v : ℝ) := by
  classical
  rw [optionLoad, Fintype.sum_prod_type]
  calc
    (∑ e : G.E, ∑ choice : Option Mode,
        G.compatibleModeOptionMass H S heavyProb lightProb (e, choice) *
          G.compatibleModeUse H S (e, choice) (Sum.inl (m, true, v))) =
        ∑ e : G.E,
          if e ∈ H m ∧ G.Inc v e then heavyProb m else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [Fintype.sum_option]
      simp only [compatibleModeUse, compatibleModeOptionMass, mul_zero, zero_add]
      rw [Finset.sum_eq_single m]
      · by_cases hH : e ∈ H m <;> by_cases hinc : G.Inc v e <;>
          simp [compatibleModeProbability, hH, hinc]
      · intro j _hj hjm
        simp [hjm]
      · simp
    _ = heavyProb m * (G.degreeOn (H m) v : ℝ) := by
      calc
        (∑ e : G.E, if e ∈ H m ∧ G.Inc v e then heavyProb m else 0) =
            heavyProb m *
              (∑ e : G.E, if e ∈ H m ∧ G.Inc v e then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _he
          by_cases h : e ∈ H m ∧ G.Inc v e <;> simp [h]
        _ = heavyProb m *
            ((Finset.univ.filter fun e : G.E =>
              e ∈ H m ∧ G.Inc v e).card : ℝ) := by
          rw [Finset.sum_boole]
        _ = heavyProb m * (G.degreeOn (H m) v : ℝ) := by
          congr 2
          rw [degreeOn]
          congr 1
          ext e
          simp [and_comm]

private theorem compatibleMode_optionLoad_light
    (H S : Mode → Finset G.E) (heavyProb lightProb : Mode → ℝ)
    (m : Mode) (v : G.V) :
    optionLoad (G.compatibleModeUse H S)
        (G.compatibleModeOptionMass H S heavyProb lightProb)
        (Sum.inl (m, false, v)) =
      lightProb m * (G.degreeOn (S m \ H m) v : ℝ) := by
  classical
  rw [optionLoad, Fintype.sum_prod_type]
  calc
    (∑ e : G.E, ∑ choice : Option Mode,
        G.compatibleModeOptionMass H S heavyProb lightProb (e, choice) *
          G.compatibleModeUse H S (e, choice) (Sum.inl (m, false, v))) =
        ∑ e : G.E,
          if e ∉ H m ∧ e ∈ S m ∧ G.Inc v e then lightProb m else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [Fintype.sum_option]
      simp only [compatibleModeUse, compatibleModeOptionMass, mul_zero, zero_add]
      rw [Finset.sum_eq_single m]
      · by_cases hH : e ∈ H m <;> by_cases hS : e ∈ S m <;>
          by_cases hinc : G.Inc v e <;>
          simp [compatibleModeProbability, hH, hS, hinc]
      · intro j _hj hjm
        simp [hjm]
      · simp
    _ = lightProb m * (G.degreeOn (S m \ H m) v : ℝ) := by
      calc
        (∑ e : G.E, if e ∉ H m ∧ e ∈ S m ∧ G.Inc v e then lightProb m else 0) =
            lightProb m *
              (∑ e : G.E,
                if e ∉ H m ∧ e ∈ S m ∧ G.Inc v e then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _he
          by_cases h : e ∉ H m ∧ e ∈ S m ∧ G.Inc v e <;> simp [h]
        _ = lightProb m *
            ((Finset.univ.filter fun e : G.E =>
              e ∉ H m ∧ e ∈ S m ∧ G.Inc v e).card : ℝ) := by
          rw [Finset.sum_boole]
        _ = lightProb m * (G.degreeOn (S m \ H m) v : ℝ) := by
          congr 2
          rw [degreeOn]
          congr 1
          ext e
          simp [and_assoc, and_left_comm, and_comm]

private theorem compatibleMode_optionLoad_residual
    (H S : Mode → Finset G.E) (heavyProb lightProb : Mode → ℝ)
    (v : G.V) :
    optionLoad (G.compatibleModeUse H S)
        (G.compatibleModeOptionMass H S heavyProb lightProb) (Sum.inr v) =
      ∑ e : G.E, if G.Inc v e then
        G.compatibleModeRemainderProbability H S heavyProb lightProb e *
          harmonicCharge (G.weight e) else 0 := by
  classical
  rw [optionLoad, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _he
  rw [Fintype.sum_option]
  by_cases hinc : G.Inc v e
  · simp [compatibleModeUse, compatibleModeOptionMass, hinc]
  · simp [compatibleModeUse, compatibleModeOptionMass, hinc]

private theorem compatibleMode_selectedHeavyUse
    (H S : Mode → Finset G.E) (label : G.E → Option Mode)
    (m : Mode) (v : G.V) :
    (∑ e : G.E,
      G.compatibleModeUse H S (e, label e) (Sum.inl (m, true, v))) =
      (G.degreeOn (G.selectedModeHeavyEdges label H m) v : ℝ) := by
  classical
  rw [degreeOn]
  have hset :
      (G.selectedModeHeavyEdges label H m).filter (G.Inc v) =
        Finset.univ.filter fun e ↦
          label e = some m ∧ e ∈ H m ∧ G.Inc v e := by
    ext e
    simp [selectedModeHeavyEdges, and_assoc, and_left_comm, and_comm]
  rw [hset]
  symm
  rw [Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro e _he
  cases hchoice : label e with
  | none => simp [compatibleModeUse, hchoice]
  | some j =>
      by_cases hjm : j = m
      · subst j
        simp [compatibleModeUse, hchoice, and_assoc, and_left_comm, and_comm]
      · simp [compatibleModeUse, hchoice, hjm]

private theorem compatibleMode_selectedLightUse
    (H S : Mode → Finset G.E) (label : G.E → Option Mode)
    (m : Mode) (v : G.V) :
    (∑ e : G.E,
      G.compatibleModeUse H S (e, label e) (Sum.inl (m, false, v))) =
      (G.degreeOn (G.selectedModeLightEdges label H S m) v : ℝ) := by
  classical
  rw [degreeOn]
  have hset :
      (G.selectedModeLightEdges label H S m).filter (G.Inc v) =
        Finset.univ.filter fun e ↦
          label e = some m ∧ e ∉ H m ∧ e ∈ S m ∧ G.Inc v e := by
    ext e
    simp [selectedModeLightEdges, and_assoc, and_left_comm, and_comm]
  rw [hset]
  symm
  rw [Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro e _he
  cases hchoice : label e with
  | none => simp [compatibleModeUse, hchoice]
  | some j =>
      by_cases hjm : j = m
      · subst j
        simp [compatibleModeUse, hchoice, and_assoc, and_left_comm, and_comm]
      · simp [compatibleModeUse, hchoice, hjm]

private theorem compatibleMode_selectedResidualUse
    (H S : Mode → Finset G.E) (label : G.E → Option Mode) (v : G.V) :
    (∑ e : G.E,
      G.compatibleModeUse H S (e, label e) (Sum.inr v)) =
      ∑ e : G.E,
        if label e = none ∧ G.Inc v e then harmonicCharge (G.weight e) else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro e _he
  cases hchoice : label e <;> simp [compatibleModeUse, hchoice]

/-- Simultaneously choose all compatible modes.  Every selected heavy and
light degree is within an additive two of its fractional upper bound, and
the residual harmonic charge is within two of its fractional value. -/
theorem exists_compatible_mode_selection
    (H S : Mode → Finset G.E) (heavyProb lightProb : Mode → ℝ)
    (hheavy : ∀ m, 0 ≤ heavyProb m) (hlight : ∀ m, 0 ≤ lightProb m)
    (hsum : ∀ e, (∑ m,
      G.compatibleModeProbability H S heavyProb lightProb e m) ≤ 1) :
    ∃ label : G.E → Option Mode,
      (∀ e m, label e = some m → e ∈ H m ∨ e ∈ S m) ∧
      (∀ m v, (G.degreeOn (G.selectedModeHeavyEdges label H m) v : ℝ) ≤
        heavyProb m * (G.degreeOn (H m) v : ℝ) + 2) ∧
      (∀ m v, (G.degreeOn (G.selectedModeLightEdges label H S m) v : ℝ) ≤
        lightProb m * (G.degreeOn (S m \ H m) v : ℝ) + 2) ∧
      (∀ v, (∑ e : G.E,
          if label e = none ∧ G.Inc v e then harmonicCharge (G.weight e) else 0) ≤
        (∑ e : G.E, if G.Inc v e then
          G.compatibleModeRemainderProbability H S heavyProb lightProb e *
            harmonicCharge (G.weight e) else 0) + 2) := by
  classical
  let job : (G.E × Option Mode) → G.E := Prod.fst
  let x : (G.E × Option Mode) → ℝ :=
    G.compatibleModeOptionMass H S heavyProb lightProb
  let use : (G.E × Option Mode) → G.CompatibleModeConstraint Mode → ℝ :=
    G.compatibleModeUse H S
  have hp0 : ∀ e m,
      0 ≤ G.compatibleModeProbability H S heavyProb lightProb e m :=
    fun e m ↦ G.compatibleModeProbability_nonneg H S heavyProb lightProb
      hheavy hlight e m
  have hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1 := by
    rintro ⟨e, choice⟩
    cases choice with
    | none =>
        have hsum0 : 0 ≤ ∑ m,
            G.compatibleModeProbability H S heavyProb lightProb e m :=
          Finset.sum_nonneg fun m _hm ↦ hp0 e m
        constructor
        · simpa [x, compatibleModeOptionMass,
            compatibleModeRemainderProbability] using sub_nonneg.mpr (hsum e)
        · simp only [x, compatibleModeOptionMass,
            compatibleModeRemainderProbability]
          linarith
    | some m =>
        have hsingle :
            G.compatibleModeProbability H S heavyProb lightProb e m ≤
              ∑ j, G.compatibleModeProbability H S heavyProb lightProb e j := by
          exact Finset.single_le_sum (fun j _hj ↦ hp0 e j) (Finset.mem_univ m)
        constructor
        · simpa [x, compatibleModeOptionMass] using hp0 e m
        · simpa [x, compatibleModeOptionMass] using hsingle.trans (hsum e)
  have hjob : ∀ e, optionJobMass job x e = 1 := by
    intro e
    exact G.compatibleMode_jobMass H S heavyProb lightProb e
  obtain ⟨selected, howner, hsupport, hload⟩ :=
    choose_one_option_per_job_support job use 1 x zero_lt_one hx hjob
      (fun o r ↦ G.compatibleModeUse_nonneg H S o r)
      (fun o r ↦ G.compatibleModeUse_le_one H S o r)
      (fun o ↦ G.compatibleModeUse_sparse H S o)
  let label : G.E → Option Mode := fun e ↦ (selected e).2
  have hselected (e : G.E) : selected e = (e, label e) := by
    apply Prod.ext
    · exact howner e
    · rfl
  refine ⟨label, ?_, ?_, ?_, ?_⟩
  · intro e m hem
    have hpos := hsupport e
    rw [hselected e] at hpos
    by_contra hnot
    have hnH : e ∉ H m := fun h ↦ hnot (Or.inl h)
    have hnS : e ∉ S m := fun h ↦ hnot (Or.inr h)
    simp [label, hem, x, compatibleModeOptionMass,
      compatibleModeProbability, hnH, hnS] at hpos
  · intro m v
    have h := hload (Sum.inl (m, true, v))
    simp only [use, x] at h
    simp_rw [hselected] at h
    rw [G.compatibleMode_selectedHeavyUse H S label m v,
      G.compatibleMode_optionLoad_heavy H S heavyProb lightProb m v] at h
    simpa using h
  · intro m v
    have h := hload (Sum.inl (m, false, v))
    simp only [use, x] at h
    simp_rw [hselected] at h
    rw [G.compatibleMode_selectedLightUse H S label m v,
      G.compatibleMode_optionLoad_light H S heavyProb lightProb m v] at h
    simpa using h
  · intro v
    have h := hload (Sum.inr v)
    simp only [use, x] at h
    simp_rw [hselected] at h
    rw [G.compatibleMode_selectedResidualUse H S label v,
      G.compatibleMode_optionLoad_residual H S heavyProb lightProb v] at h
    simpa using h

end WeightedMultigraph
end WeightedEdgeColoring
