import Mathlib

/-!
# A finite asymmetric lopsided Lovász local lemma

This file gives a self-contained weighted finite-space version of the
asymmetric lopsided Lovász local lemma.  Events are finsets of outcomes and
probabilities are computed from a nonnegative mass function of total mass one.
The lopsided hypothesis only conditions on complements of non-neighbours.
-/

namespace WeightedEdgeColoring.FiniteLocalLemma

open scoped BigOperators

variable {Omega I : Type*}

/-- The mass of an event in a finite weighted sample space. -/
def eventMass [Fintype Omega] [DecidableEq Omega]
    (mass : Omega → ℝ) (event : Finset Omega) : ℝ :=
  ∑ omega ∈ event, mass omega

/-- Outcomes which avoid all bad events indexed by `S`. -/
def avoid [Fintype Omega] [DecidableEq Omega] [DecidableEq I]
    (bad : I → Finset Omega) (S : Finset I) : Finset Omega :=
  Finset.univ.filter fun omega ↦ ∀ i ∈ S, omega ∉ bad i

section Elementary

variable [Fintype Omega] [DecidableEq Omega] [DecidableEq I]
variable {mass : Omega → ℝ} {bad : I → Finset Omega}

@[simp] theorem avoid_empty : avoid bad ∅ = Finset.univ := by
  ext omega
  simp [avoid]

theorem avoid_anti {S T : Finset I} (hST : S ⊆ T) : avoid bad T ⊆ avoid bad S := by
  intro omega homega
  simp only [avoid, Finset.mem_filter, Finset.mem_univ, true_and] at homega ⊢
  intro i hi
  exact homega i (hST hi)

@[simp] theorem avoid_insert (i : I) (S : Finset I) :
    avoid bad (insert i S) = avoid bad S \ bad i := by
  ext omega
  simp [avoid, and_comm]

theorem eventMass_nonneg (hmass : ∀ omega, 0 ≤ mass omega) (E : Finset Omega) :
    0 ≤ eventMass mass E := by
  exact Finset.sum_nonneg fun omega _ ↦ hmass omega

theorem eventMass_mono (hmass : ∀ omega, 0 ≤ mass omega)
    {E F : Finset Omega} (hEF : E ⊆ F) :
    eventMass mass E ≤ eventMass mass F := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hEF fun omega _ _ ↦ hmass omega

/-- Finite union bound for two events. -/
theorem eventMass_union_le (hmass : ∀ omega, 0 ≤ mass omega)
    (E F : Finset Omega) :
    eventMass mass (E ∪ F) ≤ eventMass mass E + eventMass mass F := by
  have hdisj : Disjoint E (F \ E) := by
    rw [Finset.disjoint_left]
    intro omega homega hdiff
    exact (Finset.mem_sdiff.mp hdiff).2 homega
  calc
    eventMass mass (E ∪ F) = eventMass mass (E ∪ (F \ E)) := by
      congr 1
      ext omega
      simp
    _ = eventMass mass E + eventMass mass (F \ E) := by
      unfold eventMass
      rw [Finset.sum_union hdisj]
    _ ≤ eventMass mass E + eventMass mass F := by
      exact add_le_add_right (eventMass_mono hmass Finset.sdiff_subset) _

/-- Union bound for a finite family of events. -/
theorem eventMass_biUnion_le (hmass : ∀ omega, 0 ≤ mass omega)
    (events : I → Finset Omega) (S : Finset I) :
    eventMass mass (S.biUnion events) ≤
      ∑ i ∈ S, eventMass mass (events i) := by
  induction S using Finset.induction_on with
  | empty => simp [eventMass]
  | @insert i S hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      exact (eventMass_union_le hmass _ _).trans (add_le_add_right ih _)

/-- If the sum of the masses of finitely many bad events is below one, some
outcome avoids all of them. -/
theorem exists_avoids_of_sum_eventMass_lt_one
    [Fintype I]
    (hmass : ∀ omega, 0 ≤ mass omega)
    (hmass_one : ∑ omega, mass omega = 1)
    (events : I → Finset Omega)
    (hsmall : (∑ i, eventMass mass (events i)) < 1) :
    ∃ omega, ∀ i, omega ∉ events i := by
  by_contra hnone
  push Not at hnone
  have hunion : (Finset.univ.biUnion events : Finset Omega) = Finset.univ := by
    ext omega
    simp [hnone omega]
  have hbound := eventMass_biUnion_le (mass := mass) hmass events Finset.univ
  rw [hunion] at hbound
  have htotal : eventMass mass (Finset.univ : Finset Omega) = 1 := by
    simpa [eventMass] using hmass_one
  rw [htotal] at hbound
  simpa using (not_lt_of_ge hbound hsmall)

/-- Union-bound existence criterion with a separate numerical upper bound for
each bad event. -/
theorem exists_avoids_of_sum_bounds_lt_one
    [Fintype I]
    (hmass : ∀ omega, 0 ≤ mass omega)
    (hmass_one : ∑ omega, mass omega = 1)
    (events : I → Finset Omega) (bound : I → ℝ)
    (hevent : ∀ i, eventMass mass (events i) ≤ bound i)
    (hsmall : (∑ i, bound i) < 1) :
    ∃ omega, ∀ i, omega ∉ events i := by
  apply exists_avoids_of_sum_eventMass_lt_one hmass hmass_one events
  exact lt_of_le_of_lt (Finset.sum_le_sum fun i _ ↦ hevent i) hsmall

theorem eventMass_avoid_insert_add (i : I) (S : Finset I) :
    eventMass mass (avoid bad (insert i S)) +
        eventMass mass (bad i ∩ avoid bad S) =
      eventMass mass (avoid bad S) := by
  rw [avoid_insert]
  simpa [eventMass, Finset.inter_comm] using
    (Finset.sum_sdiff
      (s₁ := avoid bad S ∩ bad i) (s₂ := avoid bad S)
      (f := mass) Finset.inter_subset_left)

end Elementary

section ProductEvents

variable {Omega₁ Omega₂ : Type*}
variable [Fintype Omega₁] [DecidableEq Omega₁]
variable [Fintype Omega₂] [DecidableEq Omega₂]

/--
Mass factorization for a rectangular event in a product sample space.

This is the basic finite-sum calculation used when independent random
coordinates are split into the coordinates seen by an event and all remaining
coordinates.  It can be iterated to factor cylinder events in larger products.
-/
theorem eventMass_product (mass₁ : Omega₁ → ℝ) (mass₂ : Omega₂ → ℝ)
    (event₁ : Finset Omega₁) (event₂ : Finset Omega₂) :
    eventMass (fun omega : Omega₁ × Omega₂ ↦ mass₁ omega.1 * mass₂ omega.2)
        (event₁.product event₂) =
      eventMass mass₁ event₁ * eventMass mass₂ event₂ := by
  unfold eventMass
  change (∑ omega ∈ event₁.product event₂, mass₁ omega.1 * mass₂ omega.2) = _
  calc
    (∑ omega ∈ event₁.product event₂, mass₁ omega.1 * mass₂ omega.2) =
        ∑ a ∈ event₁, ∑ b ∈ event₂, mass₁ a * mass₂ b := by
          exact Finset.sum_product event₁ event₂
            (fun omega ↦ mass₁ omega.1 * mass₂ omega.2)
    _ =
        ∑ a ∈ event₁, mass₁ a * (∑ b ∈ event₂, mass₂ b) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
    _ = (∑ a ∈ event₁, mass₁ a) * (∑ b ∈ event₂, mass₂ b) := by
      rw [Finset.sum_mul]

end ProductEvents

section LocalLemma

variable [Fintype Omega] [DecidableEq Omega]
variable [Fintype I] [DecidableEq I]

/--
Finite asymmetric lopsided Lovász local lemma.

`neighbor i` need not be symmetric.  In the condition below, `i` itself is
excluded separately, so the theorem does not impose a convention about
self-neighbours.  The hypothesis `hlop` is the division-free form of

`P(bad i | all events in S are avoided)
  ≤ x i * ∏ j ∈ neighbor i, (1 - x j)`

for every set `S` of non-neighbours of `i`.  The conclusion supplies the
usual quantitative lower bound, and in particular says that all bad events
can simultaneously be avoided with positive mass.
-/
theorem asymmetric_lopsided_local_lemma
    (mass : Omega → ℝ)
    (bad : I → Finset Omega)
    (neighbor : I → Finset I)
    (x : I → ℝ)
    (hmass : ∀ omega, 0 ≤ mass omega)
    (hmass_one : ∑ omega, mass omega = 1)
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_lt_one : ∀ i, x i < 1)
    (hlop : ∀ (i : I) (S : Finset I),
      S ⊆ Finset.univ \ insert i (neighbor i) →
      eventMass mass (bad i ∩ avoid bad S) ≤
        (x i * ∏ j ∈ neighbor i, (1 - x j)) * eventMass mass (avoid bad S)) :
    (∏ i, (1 - x i)) ≤ eventMass mass (avoid bad Finset.univ) ∧
      0 < eventMass mass (avoid bad Finset.univ) := by
  have hone_nonneg : ∀ i, 0 ≤ 1 - x i := fun i ↦ sub_nonneg.mpr (le_of_lt (hx_lt_one i))
  have hone_pos : ∀ i, 0 < 1 - x i := fun i ↦ sub_pos.mpr (hx_lt_one i)
  have hconditioned : ∀ (S : Finset I) (i : I), i ∉ S →
      eventMass mass (bad i ∩ avoid bad S) ≤
        x i * eventMass mass (avoid bad S) := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
        intro i hiS
        let T : Finset I := S ∩ neighbor i
        let U : Finset I := S \ neighbor i
        have hU_subset : U ⊆ Finset.univ \ insert i (neighbor i) := by
          intro j hj
          have hjS : j ∈ S := (Finset.mem_sdiff.mp hj).1
          have hjN : j ∉ neighbor i := (Finset.mem_sdiff.mp hj).2
          have hji : j ≠ i := by
            intro hji
            subst j
            exact hiS hjS
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, by
            simp [hji, hjN]⟩
        have hbase := hlop i U hU_subset
        have havoid_subset : avoid bad S ⊆ avoid bad U :=
          avoid_anti (bad := bad) Finset.sdiff_subset
        have hnum : eventMass mass (bad i ∩ avoid bad S) ≤
            eventMass mass (bad i ∩ avoid bad U) := by
          apply eventMass_mono hmass
          exact Finset.inter_subset_inter (fun _ h ↦ h) havoid_subset
        have hchain : ∀ (R : Finset I), R ⊆ T →
            (∏ j ∈ R, (1 - x j)) * eventMass mass (avoid bad U) ≤
              eventMass mass (avoid bad (U ∪ R)) := by
          intro R hRT
          induction R using Finset.induction_on with
          | empty => simp
          | @insert j R hjR hR =>
              have hjT : j ∈ T := hRT (Finset.mem_insert_self j R)
              have hRT' : R ⊆ T := fun k hk ↦ hRT (Finset.mem_insert_of_mem hk)
              have hRbound := hR hRT'
              have hjS : j ∈ S := (Finset.mem_inter.mp hjT).1
              have hjN : j ∈ neighbor i := (Finset.mem_inter.mp hjT).2
              have hjU : j ∉ U := by
                simp only [U, Finset.mem_sdiff]
                exact fun h ↦ h.2 hjN
              have hjUR : j ∉ U ∪ R := by simp [hjU, hjR]
              have hURsub : U ∪ R ⊆ S := by
                exact Finset.union_subset Finset.sdiff_subset
                  (hRT'.trans Finset.inter_subset_left)
              have hURne : U ∪ R ≠ S := by
                intro heq
                exact hjUR (heq.symm ▸ hjS)
              have hURssub : U ∪ R ⊂ S :=
                Finset.ssubset_iff_subset_ne.mpr ⟨hURsub, hURne⟩
              have hcond := ih (U ∪ R) hURssub j hjUR
              have hpartition := eventMass_avoid_insert_add
                (mass := mass) (bad := bad) j (U ∪ R)
              have hstep : (1 - x j) * eventMass mass (avoid bad (U ∪ R)) ≤
                  eventMass mass (avoid bad (insert j (U ∪ R))) := by
                nlinarith
              calc
                (∏ k ∈ insert j R, (1 - x k)) * eventMass mass (avoid bad U) =
                    (1 - x j) *
                      ((∏ k ∈ R, (1 - x k)) * eventMass mass (avoid bad U)) := by
                        rw [Finset.prod_insert hjR]
                        ring
                _ ≤ (1 - x j) * eventMass mass (avoid bad (U ∪ R)) :=
                  mul_le_mul_of_nonneg_left hRbound (hone_nonneg j)
                _ ≤ eventMass mass (avoid bad (insert j (U ∪ R))) := hstep
                _ = eventMass mass (avoid bad (U ∪ insert j R)) := by
                  congr 2
                  ext k
                  simp [or_comm]
        have hUT : U ∪ T = S := by
          ext j
          simp only [U, T, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
          tauto
        have hTbound : (∏ j ∈ T, (1 - x j)) * eventMass mass (avoid bad U) ≤
            eventMass mass (avoid bad S) := by
          simpa [hUT] using hchain T (fun _ h ↦ h)
        have hTsub : T ⊆ neighbor i := Finset.inter_subset_right
        have hprod_compl : (∏ j ∈ neighbor i \ T, (1 - x j)) ≤ 1 := by
          exact Finset.prod_le_one (fun j _ ↦ hone_nonneg j)
            (fun j _ ↦ sub_le_self 1 (hx_nonneg j))
        have hprodT_nonneg : 0 ≤ ∏ j ∈ T, (1 - x j) :=
          Finset.prod_nonneg fun j _ ↦ hone_nonneg j
        have hprod_split :
            (∏ j ∈ T, (1 - x j)) * (∏ j ∈ neighbor i \ T, (1 - x j)) =
              ∏ j ∈ neighbor i, (1 - x j) := by
          have hdisj : Disjoint T (neighbor i \ T) := by
            rw [Finset.disjoint_left]
            intro j hjT hjdiff
            exact (Finset.mem_sdiff.mp hjdiff).2 hjT
          rw [← Finset.prod_union hdisj]
          congr 1
          exact Finset.union_sdiff_of_subset hTsub
        have hprod_le : (∏ j ∈ neighbor i, (1 - x j)) ≤
            ∏ j ∈ T, (1 - x j) := by
          rw [← hprod_split]
          simpa using mul_le_mul_of_nonneg_left hprod_compl hprodT_nonneg
        have hmassU_nonneg : 0 ≤ eventMass mass (avoid bad U) :=
          eventMass_nonneg hmass _
        have hscaled :
            (∏ j ∈ neighbor i, (1 - x j)) * eventMass mass (avoid bad U) ≤
              eventMass mass (avoid bad S) :=
          (mul_le_mul_of_nonneg_right hprod_le hmassU_nonneg).trans hTbound
        calc
          eventMass mass (bad i ∩ avoid bad S) ≤
              eventMass mass (bad i ∩ avoid bad U) := hnum
          _ ≤ (x i * ∏ j ∈ neighbor i, (1 - x j)) *
                eventMass mass (avoid bad U) := hbase
          _ = x i * ((∏ j ∈ neighbor i, (1 - x j)) *
                eventMass mass (avoid bad U)) := by ring
          _ ≤ x i * eventMass mass (avoid bad S) :=
            mul_le_mul_of_nonneg_left hscaled (hx_nonneg i)
  have havoid_lower : ∀ S : Finset I,
      (∏ i ∈ S, (1 - x i)) ≤ eventMass mass (avoid bad S) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        simp [eventMass, hmass_one]
    | @insert i S hiS hS =>
        have hcond := hconditioned S i hiS
        have hpartition := eventMass_avoid_insert_add
          (mass := mass) (bad := bad) i S
        have hstep : (1 - x i) * eventMass mass (avoid bad S) ≤
            eventMass mass (avoid bad (insert i S)) := by
          nlinarith
        calc
          (∏ j ∈ insert i S, (1 - x j)) =
              (1 - x i) * ∏ j ∈ S, (1 - x j) := by
                rw [Finset.prod_insert hiS]
          _ ≤ (1 - x i) * eventMass mass (avoid bad S) :=
            mul_le_mul_of_nonneg_left hS (hone_nonneg i)
          _ ≤ eventMass mass (avoid bad (insert i S)) := hstep
  refine ⟨?_, ?_⟩
  · simpa using havoid_lower (Finset.univ : Finset I)
  · exact lt_of_lt_of_le (Finset.prod_pos fun i _ ↦ hone_pos i)
      (by simpa using havoid_lower (Finset.univ : Finset I))

/-- Powers of a number in `[0,1]` decrease as the exponent increases. -/
private theorem pow_antitone_of_mem_unitInterval {a : ℝ}
    (ha_nonneg : 0 ≤ a) (ha_le_one : a ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    a ^ n ≤ a ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hpow_le_one : ∀ r : ℕ, a ^ r ≤ 1 := by
    intro r
    induction r with
    | zero => simp
    | succ r hr =>
        rw [pow_succ]
        simpa only [one_mul] using
          mul_le_mul hr ha_le_one ha_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  rw [pow_add]
  simpa using mul_le_mul_of_nonneg_left (hpow_le_one k) (pow_nonneg ha_nonneg m)

/--
Symmetric lopsided local lemma with an explicit witness `x`.

Every bad event has at most `d` neighbours and, after conditioning on any
collection of non-neighbour complements, has conditional probability at most
`p`.  The numerical condition `p ≤ x * (1 - x)^d` then gives positive mass
to the outcome set avoiding every bad event.
-/
theorem symmetric_lopsided_local_lemma
    (mass : Omega → ℝ)
    (bad : I → Finset Omega)
    (neighbor : I → Finset I)
    (p x : ℝ) (d : ℕ)
    (hmass : ∀ omega, 0 ≤ mass omega)
    (hmass_one : ∑ omega, mass omega = 1)
    (hdegree : ∀ i, (neighbor i).card ≤ d)
    (hx_nonneg : 0 ≤ x)
    (hx_lt_one : x < 1)
    (hnumeric : p ≤ x * (1 - x) ^ d)
    (hlop : ∀ (i : I) (S : Finset I),
      S ⊆ Finset.univ \ insert i (neighbor i) →
      eventMass mass (bad i ∩ avoid bad S) ≤ p * eventMass mass (avoid bad S)) :
    0 < eventMass mass (avoid bad Finset.univ) := by
  have hone_nonneg : 0 ≤ 1 - x := sub_nonneg.mpr (le_of_lt hx_lt_one)
  have hone_le_one : 1 - x ≤ 1 := sub_le_self 1 hx_nonneg
  have hlop' : ∀ (i : I) (S : Finset I),
      S ⊆ Finset.univ \ insert i (neighbor i) →
      eventMass mass (bad i ∩ avoid bad S) ≤
        (x * ∏ j ∈ neighbor i, (1 - x)) * eventMass mass (avoid bad S) := by
    intro i S hS
    have havoid_nonneg : 0 ≤ eventMass mass (avoid bad S) :=
      eventMass_nonneg hmass _
    have hpower : (1 - x) ^ d ≤ (1 - x) ^ (neighbor i).card :=
      pow_antitone_of_mem_unitInterval hone_nonneg hone_le_one (hdegree i)
    calc
      eventMass mass (bad i ∩ avoid bad S) ≤
          p * eventMass mass (avoid bad S) := hlop i S hS
      _ ≤ (x * (1 - x) ^ d) * eventMass mass (avoid bad S) :=
        mul_le_mul_of_nonneg_right hnumeric havoid_nonneg
      _ ≤ (x * (1 - x) ^ (neighbor i).card) *
          eventMass mass (avoid bad S) := by
        apply mul_le_mul_of_nonneg_right _ havoid_nonneg
        exact mul_le_mul_of_nonneg_left hpower hx_nonneg
      _ = (x * ∏ j ∈ neighbor i, (1 - x)) *
          eventMass mass (avoid bad S) := by simp
  exact (asymmetric_lopsided_local_lemma mass bad neighbor (fun _ ↦ x)
    hmass hmass_one (fun _ ↦ hx_nonneg) (fun _ ↦ hx_lt_one) hlop').2

/--
The standard symmetric choice `x = 1 / (d + 1)`.  The assumption `0 < d`
ensures that this witness is strictly below one.
-/
theorem symmetric_lopsided_local_lemma_one_div
    (mass : Omega → ℝ)
    (bad : I → Finset Omega)
    (neighbor : I → Finset I)
    (p : ℝ) (d : ℕ)
    (hmass : ∀ omega, 0 ≤ mass omega)
    (hmass_one : ∑ omega, mass omega = 1)
    (hdegree : ∀ i, (neighbor i).card ≤ d)
    (hd : 0 < d)
    (hnumeric : p ≤ (1 / (d + 1 : ℝ)) * (1 - 1 / (d + 1 : ℝ)) ^ d)
    (hlop : ∀ (i : I) (S : Finset I),
      S ⊆ Finset.univ \ insert i (neighbor i) →
      eventMass mass (bad i ∩ avoid bad S) ≤ p * eventMass mass (avoid bad S)) :
    0 < eventMass mass (avoid bad Finset.univ) := by
  apply symmetric_lopsided_local_lemma mass bad neighbor p (1 / (d + 1 : ℝ)) d
    hmass hmass_one hdegree
  · positivity
  · have hdreal : (1 : ℝ) < d + 1 := by exact_mod_cast (Nat.succ_lt_succ hd)
    exact (div_lt_one (by positivity : (0 : ℝ) < d + 1)).mpr hdreal
  · exact hnumeric
  · exact hlop

end LocalLemma

end WeightedEdgeColoring.FiniteLocalLemma
