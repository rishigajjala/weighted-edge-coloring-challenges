import WeightedEdgeColoring.ColumnMassSelection

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# Balancing one color-independent profile law

For the uniform proposal used in the simple-graph theorem, the profile law
at a fixed vertex is the same for every color.  This elementary observation
allows one useful part of profile synchronization to be made deterministic.

Given a probability law `p` on a finite state space and any finite set of
colors, we choose one state for every color so that no state is used more
than one time above its fractional count.  The same choice then
simultaneously approximates *every* bounded statistic of the state.  The
error is at most `|State|` times the range of the statistic; in particular it
does not depend on the graph, on the number of rows one later tests, or on
the number of colors.

The construction is an application of the already proved finite
column-mass selector to the state-indicator rows.  It does not control a row
whose summand couples profile choices at two different vertices; those are
the genuinely remaining synchronization rows.
-/

noncomputable section

universe u v w

variable {Color : Type u} {State : Type v} {Vertex : Type w}
variable [Fintype Color] [DecidableEq Color]
variable [Fintype State] [DecidableEq State]
variable [Fintype Vertex] [DecidableEq Vertex]

/-- Indicator that a color was assigned a specified state. -/
def stateIndicatorUse (_c : Color) (a r : State) : ℝ :=
  if a = r then 1 else 0

theorem stateIndicatorUse_nonneg (c : Color) (a r : State) :
    0 ≤ stateIndicatorUse c a r := by
  unfold stateIndicatorUse
  split <;> norm_num

theorem sum_stateIndicatorUse (c : Color) (a : State) :
    ∑ r, stateIndicatorUse c a r = 1 := by
  simp [stateIndicatorUse]

theorem stateIndicator_rowMean (p : State → ℝ) (r : State) :
    profileRowMean (fun _c : Color ↦ p) stateIndicatorUse r =
      (Fintype.card Color : ℝ) * p r := by
  unfold profileRowMean stateIndicatorUse
  simp [mul_comm]

/-- A single color-independent probability law has a deterministic word of
states whose count in every state is at most the fractional count plus one.

This is the basic uniform-proposal balancing lemma. -/
theorem exists_choice_stateCount_le
    (p : State → ℝ)
    (hp0 : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) :
    ∃ choice : Color → State, ∀ a,
      (((Finset.univ : Finset Color).filter
          (fun c ↦ choice c = a)).card : ℝ) ≤
        (Fintype.card Color : ℝ) * p a + 1 := by
  classical
  obtain ⟨selected, hselected, hload⟩ :=
    exists_columnMass_profile_selection
      (fun _c : Color ↦ p) stateIndicatorUse 1 zero_lt_one
      (fun _c a ↦ hp0 a) (fun _c ↦ hpsum)
      stateIndicatorUse_nonneg
      (fun c a ↦ by simpa using (sum_stateIndicatorUse c a).le)
  let choice : Color → State := fun c ↦ Classical.choose (hselected c)
  have hchoice_mem (c : Color) : (c, choice c) ∈ selected := by
    exact (Classical.choose_spec (hselected c)).1
  have hchoice_unique (c : Color) (a : State)
      (ha : (c, a) ∈ selected) : a = choice c := by
    exact (Classical.choose_spec (hselected c)).2 a ha
  have hselected_eq :
      selected = (Finset.univ : Finset Color).image (fun c ↦ (c, choice c)) := by
    ext o
    constructor
    · intro ho
      have heq : o.2 = choice o.1 := hchoice_unique o.1 o.2 ho
      apply Finset.mem_image.mpr
      exact ⟨o.1, Finset.mem_univ _, by ext <;> simp [heq]⟩
    · intro ho
      rcases Finset.mem_image.mp ho with ⟨c, _hc, hc⟩
      rw [← hc]
      exact hchoice_mem c
  refine ⟨choice, ?_⟩
  intro a
  have hrow := hload a
  rw [hselected_eq] at hrow
  have hinj : Set.InjOn (fun c : Color ↦ (c, choice c))
      (Finset.univ : Finset Color) := by
    intro c _ d _ hcd
    exact congrArg Prod.fst hcd
  rw [Finset.sum_image hinj] at hrow
  rw [stateIndicator_rowMean] at hrow
  have hcount :
      (((Finset.univ : Finset Color).filter
          (fun c ↦ choice c = a)).card : ℝ) =
        ∑ c : Color, stateIndicatorUse c (choice c) a := by
    calc
      (((Finset.univ : Finset Color).filter
          (fun c ↦ choice c = a)).card : ℝ) =
          ∑ c ∈ (Finset.univ : Finset Color).filter
            (fun c ↦ choice c = a), (1 : ℝ) := by simp
      _ = ∑ c : Color, if choice c = a then 1 else 0 := by
        rw [Finset.sum_filter]
      _ = ∑ c : Color, stateIndicatorUse c (choice c) a := by
        rfl
  rw [hcount]
  simpa using hrow

/-- Support-preserving form of state-count balancing.  States of probability
zero are removed before rounding, so every chosen state has positive law
mass.  This is the form needed to decode a padded state back to an actual
profile. -/
theorem exists_supported_choice_stateCount_le
    (p : State → ℝ)
    (hp0 : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) :
    ∃ choice : Color → State,
      (∀ c, 0 < p (choice c)) ∧
      ∀ a,
        (((Finset.univ : Finset Color).filter
          (fun c ↦ choice c = a)).card : ℝ) ≤
          (Fintype.card Color : ℝ) * p a + 1 := by
  classical
  let Support := {a : State // 0 < p a}
  have hsumSupport : ∑ a : Support, p a.1 = 1 := by
    calc
      (∑ a : Support, p a.1) =
          ∑ a ∈ (Finset.univ : Finset State).filter (fun a ↦ 0 < p a),
            p a := by
        symm
        exact Finset.sum_subtype
          ((Finset.univ : Finset State).filter (fun a ↦ 0 < p a))
          (by intro a; simp) p
      _ = ∑ a : State, p a := by
        apply Finset.sum_subset (fun _ _ ↦ Finset.mem_univ _)
        intro a _ha haSupport
        have hnot : ¬0 < p a := by simpa using haSupport
        have hz : p a = 0 := le_antisymm (le_of_not_gt hnot) (hp0 a)
        simp [hz]
      _ = 1 := hpsum
  obtain ⟨choiceS, hcountS⟩ :=
    exists_choice_stateCount_le (Color := Color)
      (State := Support) (fun a ↦ p a.1)
      (fun a ↦ (hp0 a.1)) hsumSupport
  let choice : Color → State := fun c ↦ (choiceS c).1
  refine ⟨choice, (fun c ↦ (choiceS c).2), ?_⟩
  intro a
  by_cases ha : 0 < p a
  · let aS : Support := ⟨a, ha⟩
    have hcount := hcountS aS
    have hfilter :
        (Finset.univ : Finset Color).filter (fun c ↦ choice c = a) =
          (Finset.univ : Finset Color).filter (fun c ↦ choiceS c = aS) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change ((choiceS c).1 = aS.1) ↔ choiceS c = aS
      exact Subtype.ext_iff.symm
    rw [hfilter]
    simpa [aS] using hcount
  · have hempty :
        (Finset.univ : Finset Color).filter (fun c ↦ choice c = a) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c hc
      have hca : choice c = a := by simpa using hc
      exact ha (hca ▸ (choiceS c).2)
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hpa : p a = 0 := le_antisymm (le_of_not_gt ha) (hp0 a)
    rw [hpa]
    norm_num

/-- Fiber-counting identity for a state word. -/
theorem sum_over_choice_fibers (choice : Color → State) (f : State → ℝ) :
    (∑ c, f (choice c)) =
      ∑ a,
        (((Finset.univ : Finset Color).filter
          (fun c ↦ choice c = a)).card : ℝ) * f a := by
  classical
  calc
    (∑ c, f (choice c)) =
        ∑ c, ∑ a, if choice c = a then f a else 0 := by
      apply Finset.sum_congr rfl
      intro c _hc
      simp
    _ = ∑ a, ∑ c, if choice c = a then f a else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ a,
        (((Finset.univ : Finset Color).filter
          (fun c ↦ choice c = a)).card : ℝ) * f a := by
      apply Finset.sum_congr rfl
      intro a _ha
      calc
        (∑ c : Color, if choice c = a then f a else 0) =
            ∑ c ∈ (Finset.univ : Finset Color).filter
              (fun c ↦ choice c = a), f a := by
          rw [Finset.sum_filter]
        _ = (((Finset.univ : Finset Color).filter
              (fun c ↦ choice c = a)).card : ℝ) * f a := by
          simp

/-- Upper error for every nonnegative statistic, from the same balanced
state word. -/
theorem weighted_sum_le_of_stateCount_le
    (p : State → ℝ) (choice : Color → State)
    (hcount : ∀ a,
      (((Finset.univ : Finset Color).filter
          (fun c ↦ choice c = a)).card : ℝ) ≤
        (Fintype.card Color : ℝ) * p a + 1)
    (f : State → ℝ) (hf0 : ∀ a, 0 ≤ f a) :
    (∑ c, f (choice c)) ≤
      (Fintype.card Color : ℝ) * (∑ a, p a * f a) + ∑ a, f a := by
  rw [sum_over_choice_fibers choice f]
  calc
    (∑ a,
        (((Finset.univ : Finset Color).filter
          (fun c ↦ choice c = a)).card : ℝ) * f a) ≤
        ∑ a, ((Fintype.card Color : ℝ) * p a + 1) * f a := by
      apply Finset.sum_le_sum
      intro a _ha
      exact mul_le_mul_of_nonneg_right (hcount a) (hf0 a)
    _ = (Fintype.card Color : ℝ) * (∑ a, p a * f a) +
        ∑ a, f a := by
      calc
        (∑ a, ((Fintype.card Color : ℝ) * p a + 1) * f a) =
            ∑ a, ((Fintype.card Color : ℝ) * (p a * f a) + f a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          ring
        _ = (∑ a, (Fintype.card Color : ℝ) * (p a * f a)) +
            ∑ a, f a := Finset.sum_add_distrib
        _ = (Fintype.card Color : ℝ) * (∑ a, p a * f a) +
            ∑ a, f a := by rw [Finset.mul_sum]

/-- Lower error for a statistic in `[0,B]`.  It follows by applying the
upper estimate to the complementary statistic `B-f`. -/
theorem weighted_sum_ge_of_stateCount_le
    (p : State → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1)
    (choice : Color → State)
    (hcount : ∀ a,
      (((Finset.univ : Finset Color).filter
          (fun c ↦ choice c = a)).card : ℝ) ≤
        (Fintype.card Color : ℝ) * p a + 1)
    (f : State → ℝ) (B : ℝ)
    (hf0 : ∀ a, 0 ≤ f a) (hfB : ∀ a, f a ≤ B) :
    (Fintype.card Color : ℝ) * (∑ a, p a * f a) -
        Fintype.card State * B ≤
      ∑ c, f (choice c) := by
  let g : State → ℝ := fun a ↦ B - f a
  have hg0 : ∀ a, 0 ≤ g a := fun a ↦ sub_nonneg.mpr (hfB a)
  have hupper := weighted_sum_le_of_stateCount_le p choice hcount g hg0
  have hpB : (∑ a, p a * B) = B := by
    rw [← Finset.sum_mul, hpsum, one_mul]
  have hstateB : (∑ _a : State, B) = Fintype.card State * B := by
    simp
  have hcolorB : (∑ _c : Color, B) = Fintype.card Color * B := by
    simp
  dsimp [g] at hupper
  rw [Finset.sum_sub_distrib, hcolorB] at hupper
  have hmean : (∑ a, p a * (B - f a)) =
      B - ∑ a, p a * f a := by
    calc
      (∑ a, p a * (B - f a)) =
          (∑ a, p a * B) - ∑ a, p a * f a := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
      _ = B - ∑ a, p a * f a := by rw [hpB]
  rw [hmean, Finset.sum_sub_distrib, hstateB] at hupper
  have hfSum_nonneg : 0 ≤ ∑ a, f a :=
    Finset.sum_nonneg fun a _ ↦ hf0 a
  have hsum_le : (∑ a, f a) ≤ Fintype.card State * B := by
    calc
      (∑ a, f a) ≤ ∑ _a : State, B :=
        Finset.sum_le_sum fun a _ ↦ hfB a
      _ = Fintype.card State * B := hstateB
  linarith

/-- One balanced word simultaneously approximates every statistic valued in
`[0,B]`, with error at most `|State| B`.  The quantified statistic is chosen
after the word, so this is a uniform statement over arbitrarily many later
load/loss tests. -/
theorem exists_choice_all_bounded_statistics
    (p : State → ℝ)
    (hp0 : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) :
    ∃ choice : Color → State,
      ∀ (f : State → ℝ) (B : ℝ),
        (∀ a, 0 ≤ f a) → (∀ a, f a ≤ B) →
        |(∑ c, f (choice c)) -
          (Fintype.card Color : ℝ) * (∑ a, p a * f a)| ≤
            Fintype.card State * B := by
  obtain ⟨choice, hcount⟩ :=
    exists_choice_stateCount_le (Color := Color) p hp0 hpsum
  refine ⟨choice, ?_⟩
  intro f B hf0 hfB
  have hu := weighted_sum_le_of_stateCount_le p choice hcount f hf0
  have hl := weighted_sum_ge_of_stateCount_le p hp0 hpsum choice hcount
    f B hf0 hfB
  have hsum_le : (∑ a, f a) ≤ Fintype.card State * B := by
    calc
      (∑ a, f a) ≤ ∑ _a : State, B :=
        Finset.sum_le_sum fun a _ ↦ hfB a
      _ = Fintype.card State * B := by simp
  rw [abs_le]
  constructor <;> linarith

/-- Support-preserving version of simultaneous bounded-statistic balancing.
Besides the same uniform error, it records that every chosen state has
strictly positive probability. -/
theorem exists_supported_choice_all_bounded_statistics
    (p : State → ℝ)
    (hp0 : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) :
    ∃ choice : Color → State,
      (∀ c, 0 < p (choice c)) ∧
      ∀ (f : State → ℝ) (B : ℝ),
        (∀ a, 0 ≤ f a) → (∀ a, f a ≤ B) →
        |(∑ c, f (choice c)) -
          (Fintype.card Color : ℝ) * (∑ a, p a * f a)| ≤
            Fintype.card State * B := by
  obtain ⟨choice, hsupport, hcount⟩ :=
    exists_supported_choice_stateCount_le (Color := Color) p hp0 hpsum
  refine ⟨choice, hsupport, ?_⟩
  intro f B hf0 hfB
  have hu := weighted_sum_le_of_stateCount_le p choice hcount f hf0
  have hl := weighted_sum_ge_of_stateCount_le p hp0 hpsum choice hcount
    f B hf0 hfB
  have hsum_le : (∑ a, f a) ≤ Fintype.card State * B := by
    calc
      (∑ a, f a) ≤ ∑ _a : State, B :=
        Finset.sum_le_sum fun a _ ↦ hfB a
      _ = Fintype.card State * B := by simp
  rw [abs_le]
  constructor <;> linarith

/-- Averaged form for `n` colors.  The additive error of the balanced word
is `O(1/n)` with a constant depending only on the finite state space. -/
theorem exists_fin_choice_all_bounded_statistics_average
    {n : ℕ} (hn : 0 < n)
    (p : State → ℝ)
    (hp0 : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) :
    ∃ choice : Fin n → State,
      ∀ (f : State → ℝ) (B : ℝ),
        (∀ a, 0 ≤ f a) → (∀ a, f a ≤ B) →
        |(∑ c, f (choice c)) / (n : ℝ) - (∑ a, p a * f a)| ≤
          Fintype.card State * B / n := by
  obtain ⟨choice, hchoice⟩ :=
    exists_choice_all_bounded_statistics (Color := Fin n) p hp0 hpsum
  refine ⟨choice, ?_⟩
  intro f B hf0 hfB
  have hbase := hchoice f B hf0 hfB
  have hbase' :
      |(∑ c, f (choice c)) -
        (n : ℝ) * (∑ a, p a * f a)| ≤ Fintype.card State * B := by
    simpa using hbase
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heq :
      (∑ c, f (choice c)) / (n : ℝ) - (∑ a, p a * f a) =
        ((∑ c, f (choice c)) -
          (n : ℝ) * (∑ a, p a * f a)) / (n : ℝ) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hnR]
  exact div_le_div_of_nonneg_right hbase' hnR.le

/-- Vertexwise version.  Each vertex may have a different law, but the law
is still common to all colors at that vertex.  Every vertex receives one
balanced word, and all bounded state statistics are controlled
simultaneously. -/
theorem exists_vertexwise_choice_all_bounded_statistics
    (p : Vertex → State → ℝ)
    (hp0 : ∀ v a, 0 ≤ p v a)
    (hpsum : ∀ v, ∑ a, p v a = 1) :
    ∃ choice : Vertex → Color → State,
      ∀ v (f : State → ℝ) (B : ℝ),
        (∀ a, 0 ≤ f a) → (∀ a, f a ≤ B) →
        |(∑ c, f (choice v c)) -
          (Fintype.card Color : ℝ) * (∑ a, p v a * f a)| ≤
            Fintype.card State * B := by
  classical
  have hv : ∀ v : Vertex,
      ∃ choice : Color → State,
        ∀ (f : State → ℝ) (B : ℝ),
          (∀ a, 0 ≤ f a) → (∀ a, f a ≤ B) →
          |(∑ c, f (choice c)) -
            (Fintype.card Color : ℝ) * (∑ a, p v a * f a)| ≤
              Fintype.card State * B := by
    intro v
    exact exists_choice_all_bounded_statistics (Color := Color)
      (p v) (hp0 v) (hpsum v)
  let choice : Vertex → Color → State := fun v ↦ Classical.choose (hv v)
  refine ⟨choice, ?_⟩
  intro v
  exact Classical.choose_spec (hv v)

/-- Vertexwise support-preserving form. -/
theorem exists_vertexwise_supported_choice_all_bounded_statistics
    (p : Vertex → State → ℝ)
    (hp0 : ∀ v a, 0 ≤ p v a)
    (hpsum : ∀ v, ∑ a, p v a = 1) :
    ∃ choice : Vertex → Color → State,
      (∀ v c, 0 < p v (choice v c)) ∧
      ∀ v (f : State → ℝ) (B : ℝ),
        (∀ a, 0 ≤ f a) → (∀ a, f a ≤ B) →
        |(∑ c, f (choice v c)) -
          (Fintype.card Color : ℝ) * (∑ a, p v a * f a)| ≤
            Fintype.card State * B := by
  classical
  have hv : ∀ v : Vertex,
      ∃ choice : Color → State,
        (∀ c, 0 < p v (choice c)) ∧
        ∀ (f : State → ℝ) (B : ℝ),
          (∀ a, 0 ≤ f a) → (∀ a, f a ≤ B) →
          |(∑ c, f (choice c)) -
            (Fintype.card Color : ℝ) * (∑ a, p v a * f a)| ≤
              Fintype.card State * B := by
    intro v
    exact exists_supported_choice_all_bounded_statistics (Color := Color)
      (p v) (hp0 v) (hpsum v)
  let choice : Vertex → Color → State := fun v ↦ Classical.choose (hv v)
  refine ⟨choice, ?_, ?_⟩
  · intro v c
    exact (Classical.choose_spec (hv v)).1 c
  · intro v
    exact (Classical.choose_spec (hv v)).2

end

end WeightedEdgeColoring
