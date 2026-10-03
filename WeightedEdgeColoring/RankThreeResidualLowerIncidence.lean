import WeightedEdgeColoring.RankThreeResidualSharpMean

/-!
# Lower incidence bounds for residual job rows

A job option using a slot of large degree has many external blockers: all
options on that slot except the options owned by the same job.  This module
double-counts that observation to lower-bound the normalized job-deletion row.
The nonempty-slot hypothesis is explicit because a rank-three option is
allowed to use no slots.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Options externally blocking `o` in the row of job `j`. -/
def externalBlockersOf (j : Job) (o : Option) : Finset Option :=
  (Finset.univ : Finset Option).filter fun p ↦
    o ∈ H.externalBlockedBy j p

/-- A job option using a slot of degree at least `d` has at least `d-lambda`
external blockers when its own job contributes at most `lambda` options to
that slot. -/
theorem externalBlockersOf_card_ge_sub
    (j : Job) (o : Option) (s : Slot) (d lambda : ℕ)
    (hoj : o ∈ H.fiber j) (hos : s ∈ H.slots o)
    (hdegree : d ≤ H.slotDegree s)
    (hcodegree : H.jobSlotCodegree j s ≤ lambda) :
    d - lambda ≤ (H.externalBlockersOf j o).card := by
  let A : Finset Option :=
    (Finset.univ : Finset Option).filter fun p ↦ s ∈ H.slots p
  let J : Finset Option :=
    (H.fiber j).filter fun p ↦ s ∈ H.slots p
  have hJA : J ⊆ A := by
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ p, (Finset.mem_filter.mp hp).2⟩
  have hsub : A \ J ⊆ H.externalBlockersOf j o := by
    intro p hp
    have hpA := (Finset.mem_sdiff.mp hp).1
    have hpJ := (Finset.mem_sdiff.mp hp).2
    have hps : s ∈ H.slots p := (Finset.mem_filter.mp hpA).2
    have hpowner : H.owner p ≠ j := by
      intro hpj
      apply hpJ
      exact Finset.mem_filter.mpr ⟨H.mem_fiber.mpr hpj, hps⟩
    have hnotcompat : ¬ H.Compatible o p := by
      rw [Compatible, Finset.not_disjoint_iff]
      exact ⟨s, hos, hps⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ p, ?_⟩
    simp [externalBlockedBy, hpowner, H.mem_blockedBy,
      (H.mem_fiber.mp hoj), hnotcompat]
  have hAcard : A.card = H.slotDegree s := rfl
  have hJcard : J.card = H.jobSlotCodegree j s := rfl
  calc
    d - lambda ≤ H.slotDegree s - lambda :=
      Nat.sub_le_sub_right hdegree lambda
    _ ≤ H.slotDegree s - H.jobSlotCodegree j s :=
      Nat.sub_le_sub_left hcodegree (H.slotDegree s)
    _ = (A \ J).card := by
      rw [Finset.card_sdiff_of_subset hJA, hAcard, hJcard]
    _ ≤ (H.externalBlockersOf j o).card :=
      Finset.card_le_card hsub

/-- The reverse-incidence multiplicity has the same lower bound. -/
theorem externalBlockerMultiplicity_ge_sub
    (j : Job) (o : Option) (s : Slot) (d lambda : ℕ)
    (hoj : o ∈ H.fiber j) (hos : s ∈ H.slots o)
    (hdegree : d ≤ H.slotDegree s)
    (hcodegree : H.jobSlotCodegree j s ≤ lambda) :
    d - lambda ≤ blockerMultiplicity (Finset.univ : Finset Option)
      (H.externalBlockedBy j) o := by
  simpa [blockerMultiplicity, externalBlockersOf] using
    H.externalBlockersOf_card_ge_sub j o s d lambda
      hoj hos hdegree hcodegree

/-- Double counting: if every option of `j` uses some slot of degree at least
`d`, and every job-slot codegree is at most `lambda`, total external incidence
is at least `|fiber j| * (d-lambda)`. -/
theorem sum_externalBlockedBy_card_ge_fiber_mul_sub
    (j : Job) (d lambda : ℕ)
    (hnonempty : ∀ o ∈ H.fiber j, (H.slots o).Nonempty)
    (hslotDegree : ∀ o ∈ H.fiber j, ∀ s ∈ H.slots o,
      d ≤ H.slotDegree s)
    (hjobSlot : ∀ s, H.jobSlotCodegree j s ≤ lambda) :
    (H.fiber j).card * (d - lambda) ≤
      ∑ p : Option, (H.externalBlockedBy j p).card := by
  by_cases hdl : d ≤ lambda
  · have : d - lambda = 0 := Nat.sub_eq_zero_of_le hdl
    simp [this]
  · have hpos : 0 < d - lambda := Nat.sub_pos_of_lt (lt_of_not_ge hdl)
    rw [WeightedEdgeColoring.sum_card_eq_sum_blockerMultiplicity]
    have hfiberSub : H.fiber j ⊆
        (Finset.univ : Finset Option).biUnion (H.externalBlockedBy j) := by
      intro o ho
      obtain ⟨s, hs⟩ := hnonempty o ho
      have hlower := H.externalBlockerMultiplicity_ge_sub
        j o s d lambda ho hs (hslotDegree o ho s hs) (hjobSlot s)
      have hmultPos : 0 < blockerMultiplicity (Finset.univ : Finset Option)
          (H.externalBlockedBy j) o := hpos.trans_le hlower
      rw [Finset.mem_biUnion]
      by_contra hout
      push Not at hout
      unfold blockerMultiplicity at hmultPos
      simp [hout] at hmultPos
    calc
      (H.fiber j).card * (d - lambda) =
          ∑ _o ∈ H.fiber j, (d - lambda) := by simp
      _ ≤ ∑ o ∈ H.fiber j,
          blockerMultiplicity (Finset.univ : Finset Option)
            (H.externalBlockedBy j) o := by
        apply Finset.sum_le_sum
        intro o ho
        obtain ⟨s, hs⟩ := hnonempty o ho
        exact H.externalBlockerMultiplicity_ge_sub
          j o s d lambda ho hs (hslotDegree o ho s hs) (hjobSlot s)
      _ ≤ ∑ o ∈ (Finset.univ : Finset Option).biUnion
          (H.externalBlockedBy j),
          blockerMultiplicity (Finset.univ : Finset Option)
            (H.externalBlockedBy j) o := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hfiberSub
          (fun _ _ _ ↦ Nat.zero_le _)

/-- Lower bound for the total normalized job-deletion row. -/
theorem sum_residualDeleteWeight_job_ge
    (j : Job) (d lambda : ℕ) (hlambda : 0 < lambda)
    (hnonempty : ∀ o ∈ H.fiber j, (H.slots o).Nonempty)
    (hslotDegree : ∀ o ∈ H.fiber j, ∀ s ∈ H.slots o,
      d ≤ H.slotDegree s)
    (hjobSlot : ∀ s, H.jobSlotCodegree j s ≤ lambda) :
    (((H.fiber j).card * (d - lambda) : ℕ) : ℝ) /
        ((2 * lambda : ℕ) : ℝ) ≤
      ∑ p : Option, H.residualDeleteWeight lambda (Sum.inl j) p := by
  simp only [residualDeleteWeight, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast H.sum_externalBlockedBy_card_ge_fiber_mul_sub
      j d lambda hnonempty hslotDegree hjobSlot
  · positivity

/-- Under uniform Bernoulli retention, the normalized job-row mean inherits
the same incidence lower bound. -/
theorem residualDeleteWeight_job_mean_ge
    (rho : ℝ) (j : Job) (d lambda : ℕ) (hlambda : 0 < lambda)
    (hrho : 0 ≤ rho)
    (hnonempty : ∀ o ∈ H.fiber j, (H.slots o).Nonempty)
    (hslotDegree : ∀ o ∈ H.fiber j, ∀ s ∈ H.slots o,
      d ≤ H.slotDegree s)
    (hjobSlot : ∀ s, H.jobSlotCodegree j s ≤ lambda) :
    rho * ((((H.fiber j).card * (d - lambda) : ℕ) : ℝ) /
        ((2 * lambda : ℕ) : ℝ)) ≤
      linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inl j) := by
  rw [linearRowMean_uniform_eq_rho_mul_sum]
  exact mul_le_mul_of_nonneg_left
    (H.sum_residualDeleteWeight_job_ge
      j d lambda hlambda hnonempty hslotDegree hjobSlot) hrho

end WeightedEdgeColoring.RankThreeOptionSystem
