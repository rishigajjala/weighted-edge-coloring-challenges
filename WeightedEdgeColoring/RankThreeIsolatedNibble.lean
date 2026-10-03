import WeightedEdgeColoring.RankThreeBernoulliThinning

/-!
# One-round isolated nibble

Retain every option independently, then keep only retained options having no
retained conflict.  The resulting set is always a partial matching.  This
file proves the exact finite expectation algebra and a union-bound survival
estimate in terms of the total retention probability in one option's
conflict neighbourhood.
-/

namespace WeightedEdgeColoring

open scoped BigOperators
open FiniteBernoulliChernoff
open FiniteBernoulliThinning

namespace FiniteBernoulliThinning

variable {I : Type*} [Fintype I] [DecidableEq I]

private def massOn (indices : Finset I) (q : I → ℝ) (S : Finset I) : ℝ :=
  (∏ i ∈ S, q i) * ∏ i ∈ indices \ S, (1 - q i)

omit [Fintype I] in
private theorem sum_massOn (indices : Finset I) (q : I → ℝ) :
    ∑ S ∈ indices.powerset, massOn indices q S = 1 := by
  calc
    (∑ S ∈ indices.powerset, massOn indices q S) =
        ∏ i ∈ indices, (q i + (1 - q i)) := by
      simpa [massOn] using
        (Finset.prod_add q (fun i ↦ 1 - q i) indices).symm
    _ = 1 := by simp

/-- Exact two-coordinate moment of the finite Bernoulli product. -/
theorem sum_bernoulliMass_indicator_pair (q : I → ℝ) {i j : I}
    (hij : i ≠ j) :
    (∑ S : Finset I, if i ∈ S ∧ j ∈ S then bernoulliMass q S else 0) =
      q i * q j := by
  classical
  let rest : Finset I := ((Finset.univ : Finset I).erase i).erase j
  let add : Finset I → Finset I := fun T ↦ insert i (insert j T)
  have hiRest : i ∉ rest := by simp [rest]
  have hjRest : j ∉ rest := by simp [rest]
  have hfilter :
      (Finset.univ : Finset (Finset I)).filter (fun S ↦ i ∈ S ∧ j ∈ S) =
        rest.powerset.image add := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_powerset]
    constructor
    · rintro ⟨hiS, hjS⟩
      refine ⟨(S.erase i).erase j, ?_, ?_⟩
      · intro x hx
        have hx' := Finset.mem_erase.mp hx
        have hx'' := Finset.mem_erase.mp hx'.2
        simp [rest, hx'.1, hx''.1]
      · unfold add
        ext x
        by_cases hxi : x = i
        · subst x; simp [hiS]
        · by_cases hxj : x = j
          · subst x; simp [hjS]
          · simp [hxi, hxj]
    · rintro ⟨T, hT, rfl⟩
      simp [add]
  rw [← Finset.sum_filter, hfilter, Finset.sum_image]
  · have hfactor : ∀ T ∈ rest.powerset,
        bernoulliMass q (add T) = q i * q j * massOn rest q T := by
      intro T hT
      have hTi : i ∉ T := fun h ↦ hiRest (Finset.mem_powerset.mp hT h)
      have hTj : j ∉ T := fun h ↦ hjRest (Finset.mem_powerset.mp hT h)
      have hdiff : (Finset.univ : Finset I) \ add T = rest \ T := by
        ext x
        simp [add, rest, and_assoc, and_comm]
      simp [bernoulliMass, massOn, add, hTi, hTj, hij, hdiff]
      ring
    calc
      (∑ T ∈ rest.powerset, bernoulliMass q (add T)) =
          ∑ T ∈ rest.powerset, q i * q j * massOn rest q T := by
        exact Finset.sum_congr rfl fun T hT ↦ hfactor T hT
      _ = (q i * q j) * (∑ T ∈ rest.powerset, massOn rest q T) := by
        rw [Finset.mul_sum]
      _ = q i * q j := by rw [sum_massOn, mul_one]
  · intro A hA B hB hab
    have hAi : i ∉ A := fun h ↦ hiRest (Finset.mem_powerset.mp hA h)
    have hAj : j ∉ A := fun h ↦ hjRest (Finset.mem_powerset.mp hA h)
    have hBi : i ∉ B := fun h ↦ hiRest (Finset.mem_powerset.mp hB h)
    have hBj : j ∉ B := fun h ↦ hjRest (Finset.mem_powerset.mp hB h)
    have herase := congrArg (fun S : Finset I ↦ (S.erase i).erase j) hab
    simpa [add, hAi, hAj, hBi, hBj, hij] using herase

end FiniteBernoulliThinning

namespace RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Other options that compete with `o` either for its owner or for a slot. -/
def conflictNeighbors (o : Option) : Finset Option :=
  ((Finset.univ : Finset Option).erase o).filter fun p ↦
    H.owner p = H.owner o ∨ ¬ H.Compatible o p

@[simp] theorem mem_conflictNeighbors {o p : Option} :
    p ∈ H.conflictNeighbors o ↔
      p ≠ o ∧ (H.owner p = H.owner o ∨ ¬ H.Compatible o p) := by
  simp [conflictNeighbors]

/-- Retained options with no other retained conflicting option. -/
def isolatedOptions (S : Finset Option) : Finset Option :=
  S.filter fun o ↦ Disjoint S (H.conflictNeighbors o)

@[simp] theorem mem_isolatedOptions {S : Finset Option} {o : Option} :
    o ∈ H.isolatedOptions S ↔
      o ∈ S ∧ Disjoint S (H.conflictNeighbors o) := by
  simp [isolatedOptions]

/-- Isolation removes every owner and slot collision. -/
theorem isolatedOptions_isPartialMatching (S : Finset Option) :
    H.IsPartialMatching (H.isolatedOptions S) := by
  constructor
  · intro o ho p hp hop
    have ho' := (H.mem_isolatedOptions.mp ho).2
    have hpS := (H.mem_isolatedOptions.mp hp).1
    by_contra hbad
    have hpne : p ≠ o := fun h ↦ hop h.symm
    have hpN : p ∈ H.conflictNeighbors o := by
      exact H.mem_conflictNeighbors.mpr ⟨hpne, Or.inr hbad⟩
    exact Finset.disjoint_left.mp ho' hpS hpN
  · intro o ho p hp howner
    by_contra hop
    have ho' := (H.mem_isolatedOptions.mp ho).2
    have hpS := (H.mem_isolatedOptions.mp hp).1
    have hpN : p ∈ H.conflictNeighbors o := by
      exact H.mem_conflictNeighbors.mpr
        ⟨(fun h ↦ hop h.symm), Or.inl howner.symm⟩
    exact Finset.disjoint_left.mp ho' hpS hpN

/-- Total retention probability in the conflict neighbourhood of `o`. -/
def conflictLoad (q : Option → ℝ) (o : Option) : ℝ :=
  ∑ p ∈ H.conflictNeighbors o, q p

/-- Total retention probability of options owned by one job. -/
def ownerLoad (q : Option → ℝ) (j : Job) : ℝ :=
  ∑ p : Option, if H.owner p = j then q p else 0

/-- Total retention probability of options using one slot. -/
def slotLoad (q : Option → ℝ) (s : Slot) : ℝ :=
  ∑ p : Option, if s ∈ H.slots p then q p else 0

/-- Conflicts are covered by the owner row and the at most two slot rows of
the option. -/
theorem conflictLoad_le_owner_add_slots (q : Option → ℝ)
    (hq0 : ∀ p, 0 ≤ q p) (o : Option) :
    H.conflictLoad q o ≤
      H.ownerLoad q (H.owner o) + ∑ s ∈ H.slots o, H.slotLoad q s := by
  classical
  unfold conflictLoad ownerLoad slotLoad
  calc
    (∑ p ∈ H.conflictNeighbors o, q p) ≤
        ∑ p ∈ H.conflictNeighbors o,
          ((if H.owner p = H.owner o then q p else 0) +
            ∑ s ∈ H.slots o, if s ∈ H.slots p then q p else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      rcases (H.mem_conflictNeighbors.mp hp).2 with howner | hslot
      · have hslots0 : 0 ≤ ∑ s ∈ H.slots o,
            if s ∈ H.slots p then q p else 0 :=
          Finset.sum_nonneg fun s _ ↦ by split <;> simp_all
        rw [if_pos howner]
        linarith
      · unfold Compatible at hslot
        rw [Finset.not_disjoint_iff] at hslot
        rcases hslot with ⟨s, hso, hsp⟩
        have hsingle : q p ≤ ∑ t ∈ H.slots o,
            if t ∈ H.slots p then q p else 0 := by
          calc
            q p = (if s ∈ H.slots p then q p else 0) := by simp [hsp]
            _ ≤ ∑ t ∈ H.slots o,
                if t ∈ H.slots p then q p else 0 := by
              exact Finset.single_le_sum
                (s := H.slots o)
                (f := fun t ↦ if t ∈ H.slots p then q p else 0)
                (fun t _ht ↦ by
                  dsimp
                  split
                  · exact hq0 p
                  · exact le_rfl)
                hso
        have howner0 : 0 ≤ if H.owner p = H.owner o then q p else 0 := by
          split
          · exact hq0 p
          · exact le_rfl
        linarith
    _ ≤ ∑ p : Option,
          ((if H.owner p = H.owner o then q p else 0) +
            ∑ s ∈ H.slots o, if s ∈ H.slots p then q p else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro p _hp _hnot
      apply add_nonneg
      · split
        · exact hq0 p
        · exact le_rfl
      · exact Finset.sum_nonneg fun s _ ↦ by split <;> simp_all
    _ = (∑ p : Option, if H.owner p = H.owner o then q p else 0) +
        ∑ s ∈ H.slots o, ∑ p : Option,
          if s ∈ H.slots p then q p else 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]

/-- Degree-form conflict bound.  Since every option uses at most two slots,
owner load at most `a` and every slot load at most `b` imply conflict load at
most `a + 2b`. -/
theorem conflictLoad_le_of_owner_slot_bounds (q : Option → ℝ)
    (hq0 : ∀ p, 0 ≤ q p) (a b : ℝ)
    (hb0 : 0 ≤ b)
    (howner : ∀ j, H.ownerLoad q j ≤ a)
    (hslot : ∀ s, H.slotLoad q s ≤ b)
    (o : Option) :
    H.conflictLoad q o ≤ a + 2 * b := by
  calc
    H.conflictLoad q o ≤
        H.ownerLoad q (H.owner o) + ∑ s ∈ H.slots o, H.slotLoad q s :=
      H.conflictLoad_le_owner_add_slots q hq0 o
    _ ≤ a + ∑ _s ∈ H.slots o, b := by
      gcongr with s hs
      · exact howner (H.owner o)
      · exact hslot s
    _ = a + (H.slots o).card * b := by simp
    _ ≤ a + 2 * b := by
      gcongr
      exact_mod_cast H.slots_card_le_two o

/-- Number of active conflicting neighbours of `o`. -/
def activeConflictCount (S : Finset Option) (o : Option) : ℕ :=
  (S ∩ H.conflictNeighbors o).card

/-- Isolation is exactly activity together with zero active conflicts. -/
theorem mem_isolatedOptions_iff_activeConflictCount_zero
    (S : Finset Option) (o : Option) :
    o ∈ H.isolatedOptions S ↔
      o ∈ S ∧ H.activeConflictCount S o = 0 := by
  rw [H.mem_isolatedOptions]
  simp [activeConflictCount, Finset.disjoint_iff_inter_eq_empty]

/-- Deterministic union-bound inequality for one outcome. -/
theorem isolated_indicator_lower (S : Finset Option) (o : Option) :
    (if o ∈ H.isolatedOptions S then (1 : ℝ) else 0) ≥
      (if o ∈ S then (1 : ℝ) - (H.activeConflictCount S o : ℝ) else 0) := by
  by_cases hoS : o ∈ S
  · by_cases hzero : H.activeConflictCount S o = 0
    · have hiso : o ∈ H.isolatedOptions S :=
        (H.mem_isolatedOptions_iff_activeConflictCount_zero S o).2 ⟨hoS, hzero⟩
      simp [hoS, hiso, hzero]
    · have hone : 1 ≤ H.activeConflictCount S o := Nat.one_le_iff_ne_zero.mpr hzero
      have hnonpos : (1 : ℝ) - (H.activeConflictCount S o : ℝ) ≤ 0 := by
        exact sub_nonpos.mpr (by exact_mod_cast hone)
      by_cases hiso : o ∈ H.isolatedOptions S
      · simp [hiso, hoS]
      · simp [hiso, hoS]
        exact_mod_cast hone
  · have hniso : o ∉ H.isolatedOptions S := fun h ↦ hoS (H.mem_isolatedOptions.mp h).1
    simp [hoS, hniso]

/-- Exact expected number of active conflict pairs incident with `o`. -/
theorem expected_active_conflicts (q : Option → ℝ) (o : Option) :
    (∑ S : Finset Option, bernoulliMass q S *
      (if o ∈ S then (H.activeConflictCount S o : ℝ) else 0)) =
      q o * H.conflictLoad q o := by
  classical
  have hcard (S : Finset Option) :
      (if o ∈ S then (H.activeConflictCount S o : ℝ) else 0) =
        ∑ p ∈ H.conflictNeighbors o,
          if o ∈ S ∧ p ∈ S then (1 : ℝ) else 0 := by
    by_cases ho : o ∈ S
    · simp only [ho, true_and, if_true]
      change (((S ∩ H.conflictNeighbors o).card : ℕ) : ℝ) = _
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      simp only [Nat.cast_one]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext p
        simp [and_comm]
      · intro p _hp
        rfl
    · simp [ho]
  simp_rw [hcard]
  simp_rw [Finset.mul_sum]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  unfold conflictLoad
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpo : p ≠ o := (H.mem_conflictNeighbors.mp hp).1
  exact sum_bernoulliMass_indicator_pair q hpo.symm

/-- Union-bound survival estimate for one option. -/
theorem expected_isolated_indicator_lower (q : Option → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1) (o : Option) :
    q o * (1 - H.conflictLoad q o) ≤
      ∑ S : Finset Option, bernoulliMass q S *
        (if o ∈ H.isolatedOptions S then (1 : ℝ) else 0) := by
  have hmass : ∀ S : Finset Option, 0 ≤ bernoulliMass q S :=
    bernoulliMass_nonneg q hq0 hq1
  have hpoint (S : Finset Option) := H.isolated_indicator_lower S o
  have hfirst :
      (∑ S : Finset Option, bernoulliMass q S *
        (if o ∈ S then (1 : ℝ) else 0)) = q o := by
    simpa [mul_ite] using sum_bernoulliMass_indicator q o
  calc
    q o * (1 - H.conflictLoad q o) =
        q o - q o * H.conflictLoad q o := by ring
    _ = (∑ S : Finset Option, bernoulliMass q S *
          (if o ∈ S then (1 : ℝ) else 0)) -
        ∑ S : Finset Option, bernoulliMass q S *
          (if o ∈ S then (H.activeConflictCount S o : ℝ) else 0) := by
      rw [hfirst, H.expected_active_conflicts q o]
    _ = ∑ S : Finset Option, bernoulliMass q S *
        (if o ∈ S then
          (1 : ℝ) - (H.activeConflictCount S o : ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro S _hS
      by_cases ho : o ∈ S <;> simp [ho]
      ring
    _ ≤ ∑ S : Finset Option, bernoulliMass q S *
        (if o ∈ H.isolatedOptions S then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro S _hS
      exact mul_le_mul_of_nonneg_left (hpoint S) (hmass S)

/-- Exact decomposition of the expected isolated-set size into individual
survival probabilities. -/
theorem expected_isolated_card (q : Option → ℝ) :
    (∑ S : Finset Option, bernoulliMass q S *
      ((H.isolatedOptions S).card : ℝ)) =
      ∑ o : Option, ∑ S : Finset Option, bernoulliMass q S *
        (if o ∈ H.isolatedOptions S then (1 : ℝ) else 0) := by
  have hcard (S : Finset Option) :
      ((H.isolatedOptions S).card : ℝ) =
        ∑ o : Option, if o ∈ H.isolatedOptions S then (1 : ℝ) else 0 := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext o
      simp
    · intro o _ho
      rfl
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Constant-rate one-round estimate under a uniform conflict-load bound. -/
theorem expected_isolated_card_lower (q : Option → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (delta : ℝ) (hdelta : ∀ o, H.conflictLoad q o ≤ delta) :
    (1 - delta) * (∑ o, q o) ≤
      ∑ S : Finset Option, bernoulliMass q S *
        ((H.isolatedOptions S).card : ℝ) := by
  rw [H.expected_isolated_card q, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o _ho
  calc
    (1 - delta) * q o ≤ q o * (1 - H.conflictLoad q o) := by
      rw [mul_comm (1 - delta)]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_left (hdelta o) 1) (hq0 o)
    _ ≤ _ := H.expected_isolated_indicator_lower q hq0 hq1 o

/-- Some Bernoulli outcome attains at least the expected isolated-set size. -/
theorem exists_isolated_card_ge_expectation (q : Option → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1) :
    ∃ S : Finset Option,
      (∑ T : Finset Option, bernoulliMass q T *
        ((H.isolatedOptions T).card : ℝ)) ≤
      ((H.isolatedOptions S).card : ℝ) := by
  classical
  obtain ⟨S, _hS, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Finset Option))
      (fun T ↦ (H.isolatedOptions T).card)
      ⟨∅, Finset.mem_univ ∅⟩
  refine ⟨S, ?_⟩
  calc
    (∑ T : Finset Option, bernoulliMass q T *
        ((H.isolatedOptions T).card : ℝ)) ≤
      ∑ T : Finset Option, bernoulliMass q T *
        ((H.isolatedOptions S).card : ℝ) := by
      apply Finset.sum_le_sum
      intro T _hT
      apply mul_le_mul_of_nonneg_left _
        (bernoulliMass_nonneg q hq0 hq1 T)
      exact_mod_cast hmax T (Finset.mem_univ T)
    _ = ((H.isolatedOptions S).card : ℝ) := by
      rw [← Finset.sum_mul, sum_bernoulliMass, one_mul]

/-- A one-round constant-rate partial matching.  The only quantitative input
is a uniform upper bound on each option's conflict load. -/
theorem exists_isolated_partialMatching_of_conflictLoad
    (q : Option → ℝ) (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (delta : ℝ) (hdelta : ∀ o, H.conflictLoad q o ≤ delta) :
    ∃ M : Finset Option,
      H.IsPartialMatching M ∧
      (1 - delta) * (∑ o, q o) ≤ (M.card : ℝ) := by
  rcases H.exists_isolated_card_ge_expectation q hq0 hq1 with ⟨S, hS⟩
  refine ⟨H.isolatedOptions S, H.isolatedOptions_isPartialMatching S, ?_⟩
  exact (H.expected_isolated_card_lower q hq0 hq1 delta hdelta).trans hS

/-- Degree-form one-round nibble: bounded owner and slot loads give a
partial matching containing a constant fraction of the total proposed mass. -/
theorem exists_isolated_partialMatching_of_owner_slot_bounds
    (q : Option → ℝ) (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (a b : ℝ) (hb0 : 0 ≤ b)
    (howner : ∀ j, H.ownerLoad q j ≤ a)
    (hslot : ∀ s, H.slotLoad q s ≤ b) :
    ∃ M : Finset Option,
      H.IsPartialMatching M ∧
      (1 - (a + 2 * b)) * (∑ o, q o) ≤ (M.card : ℝ) := by
  apply H.exists_isolated_partialMatching_of_conflictLoad
    q hq0 hq1 (a + 2 * b)
  intro o
  exact H.conflictLoad_le_of_owner_slot_bounds q hq0 a b hb0 howner hslot o

end RankThreeOptionSystem

end WeightedEdgeColoring
