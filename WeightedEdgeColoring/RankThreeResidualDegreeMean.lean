import WeightedEdgeColoring.RankThreeResidualSharpMean

/-!
# Degree-sensitive residual-deletion means

The uniform `D^2/lambda` estimate can retain the current degree of the row.
For a job of degree `d`, reverse double counting gives `2 d D` incidences;
for a slot of degree `d`, it gives `3 d D`.  After the normalization in the
residual row, both means are at most `rho * d * D / lambda`.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Local external-blocker incidence with the target job's actual degree. -/
theorem sum_externalBlockedBy_card_le_fiber_mul_two_mul
    (j : Job) (D : ℕ) (hslotDegree : ∀ s, H.slotDegree s ≤ D) :
    (∑ p : Option, (H.externalBlockedBy j p).card) ≤
      (H.fiber j).card * (2 * D) := by
  rw [WeightedEdgeColoring.sum_card_eq_sum_blockerMultiplicity]
  calc
    (∑ o ∈ (Finset.univ : Finset Option).biUnion
        (H.externalBlockedBy j),
        WeightedEdgeColoring.blockerMultiplicity (Finset.univ : Finset Option)
          (H.externalBlockedBy j) o) ≤
        ∑ _o ∈ (Finset.univ : Finset Option).biUnion
          (H.externalBlockedBy j), 2 * D := by
      exact Finset.sum_le_sum fun o _ ↦
        H.externalBlockerMultiplicity_univ_le_two_mul
          j o D hslotDegree
    _ = ((Finset.univ : Finset Option).biUnion
          (H.externalBlockedBy j)).card * (2 * D) := by simp
    _ ≤ (H.fiber j).card * (2 * D) :=
      Nat.mul_le_mul_right (2 * D)
        (Finset.card_le_card (H.biUnion_externalBlockedBy_subset_fiber j))

/-- Local slot-blocker incidence with the target slot's actual degree. -/
theorem sum_slotBlockedBy_card_le_slotDegree_mul_three_mul
    (s : Slot) (D : ℕ)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ t, H.slotDegree t ≤ D) :
    (∑ p : Option, (H.slotBlockedBy s p).card) ≤
      H.slotDegree s * (3 * D) := by
  rw [WeightedEdgeColoring.sum_card_eq_sum_blockerMultiplicity]
  calc
    (∑ o ∈ (Finset.univ : Finset Option).biUnion (H.slotBlockedBy s),
        WeightedEdgeColoring.blockerMultiplicity (Finset.univ : Finset Option)
          (H.slotBlockedBy s) o) ≤
        ∑ _o ∈ (Finset.univ : Finset Option).biUnion
          (H.slotBlockedBy s), 3 * D := by
      exact Finset.sum_le_sum fun o _ ↦
        H.slotBlockerMultiplicity_univ_le_three_mul
          s o D hjobDegree hslotDegree
    _ = ((Finset.univ : Finset Option).biUnion
          (H.slotBlockedBy s)).card * (3 * D) := by simp
    _ ≤ (H.slotOptionFiber s).card * (3 * D) :=
      Nat.mul_le_mul_right (3 * D)
        (Finset.card_le_card
          (H.biUnion_slotBlockedBy_subset_slotOptionFiber s))
    _ = H.slotDegree s * (3 * D) := by
      rw [H.slotOptionFiber_card]

/-! ## Separate job and slot scales

The Delcourt--Postle round keeps the maximum job degree and maximum slot
degree separate.  The two contributions to a blocker of a target option are
then visibly different: there are at most `J` blockers with the same owner
and at most `2 * S` blockers meeting one of its two slots. -/

/-- With job degrees at most `J` and slot degrees at most `S`, a target
option belongs to at most `J + 2*S` slot-blocker sets. -/
theorem slotBlockerMultiplicity_univ_le_job_slot
    (s : Slot) (o : Option) (J S : ℕ)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ t, H.slotDegree t ≤ S) :
    WeightedEdgeColoring.blockerMultiplicity (Finset.univ : Finset Option)
      (H.slotBlockedBy s) o ≤ J + 2 * S := by
  unfold WeightedEdgeColoring.blockerMultiplicity
  let B := (Finset.univ : Finset Option).filter fun p ↦
    o ∈ H.slotBlockedBy s p
  have hsub : B ⊆ H.fiber (H.owner o) ∪
      H.optionsTouchingSlots (H.slots o) := by
    intro p hp
    have hop := (Finset.mem_filter.mp hp).2
    have hbad := (Finset.mem_filter.mp hop).2
    rcases hbad with howner | hincompat
    · exact Finset.mem_union_left _ (H.mem_fiber.mpr howner.symm)
    · apply Finset.mem_union_right
      rw [Compatible, Finset.not_disjoint_iff] at hincompat
      rcases hincompat with ⟨t, hto, htp⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ p,
        ⟨t, Finset.mem_inter.mpr ⟨htp, hto⟩⟩⟩
  change B.card ≤ J + 2 * S
  calc
    B.card ≤ (H.fiber (H.owner o) ∪
        H.optionsTouchingSlots (H.slots o)).card := Finset.card_le_card hsub
    _ ≤ (H.fiber (H.owner o)).card +
        (H.optionsTouchingSlots (H.slots o)).card := Finset.card_union_le _ _
    _ ≤ J + (H.slots o).card * S := by
      exact Nat.add_le_add (hjobDegree (H.owner o))
        (H.card_optionsTouchingSlots_le (H.slots o) S
          (fun t _ ↦ hslotDegree t))
    _ ≤ J + 2 * S := by
      gcongr
      exact H.slots_card_le_two o

/-- The total raw slot-deletion load has the sharp separate-scale bound
`degree(s) * (J + 2*S)`. -/
theorem sum_slotBlockedBy_card_le_slotDegree_mul_add
    (s : Slot) (J S : ℕ)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ t, H.slotDegree t ≤ S) :
    (∑ p : Option, (H.slotBlockedBy s p).card) ≤
      H.slotDegree s * (J + 2 * S) := by
  rw [WeightedEdgeColoring.sum_card_eq_sum_blockerMultiplicity]
  calc
    (∑ o ∈ (Finset.univ : Finset Option).biUnion (H.slotBlockedBy s),
        WeightedEdgeColoring.blockerMultiplicity (Finset.univ : Finset Option)
          (H.slotBlockedBy s) o) ≤
        ∑ _o ∈ (Finset.univ : Finset Option).biUnion
          (H.slotBlockedBy s), (J + 2 * S) := by
      apply Finset.sum_le_sum
      intro o _ho
      exact H.slotBlockerMultiplicity_univ_le_job_slot
        s o J S hjobDegree hslotDegree
    _ = ((Finset.univ : Finset Option).biUnion
          (H.slotBlockedBy s)).card * (J + 2 * S) := by simp
    _ ≤ (H.slotOptionFiber s).card * (J + 2 * S) :=
      Nat.mul_le_mul_right (J + 2 * S)
        (Finset.card_le_card
          (H.biUnion_slotBlockedBy_subset_slotOptionFiber s))
    _ = H.slotDegree s * (J + 2 * S) := by
      rw [H.slotOptionFiber_card]

/-- After normalization, the sharp separate-scale slot-row coefficient sum
is `degree(s) * (J + 2*S) / (3*lambda)`. -/
theorem sum_residualDeleteWeight_slot_le_job_slot
    (lambda J S : ℕ) (hlambda : 0 < lambda) (s : Slot)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ t, H.slotDegree t ≤ S) :
    (∑ p : Option, H.residualDeleteWeight lambda (Sum.inr s) p) ≤
      (H.slotDegree s : ℝ) * ((J + 2 * S : ℕ) : ℝ) /
        ((3 * lambda : ℕ) : ℝ) := by
  calc
    (∑ p : Option, H.residualDeleteWeight lambda (Sum.inr s) p) ≤
        ∑ p : Option, ((H.slotBlockedBy s p).card : ℝ) /
          ((3 * lambda : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hsp : s ∈ H.slots p
      · simp [residualDeleteWeight, hsp]
        positivity
      · simp [residualDeleteWeight, hsp]
    _ = (∑ p : Option, ((H.slotBlockedBy s p).card : ℝ)) /
        ((3 * lambda : ℕ) : ℝ) := by rw [Finset.sum_div]
    _ ≤ (((H.slotDegree s * (J + 2 * S) : ℕ) : ℝ)) /
        ((3 * lambda : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast H.sum_slotBlockedBy_card_le_slotDegree_mul_add
          s J S hjobDegree hslotDegree
      · positivity
    _ = (H.slotDegree s : ℝ) * ((J + 2 * S : ℕ) : ℝ) /
        ((3 * lambda : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul, Nat.cast_add]

/-- Uniform Bernoulli mean for the sharp separate-scale slot row. -/
theorem residualDeleteWeight_slot_mean_le_job_slot
    (rho : ℝ) (lambda J S : ℕ) (hlambda : 0 < lambda)
    (hrho0 : 0 ≤ rho) (s : Slot)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ t, H.slotDegree t ≤ S) :
    linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inr s) ≤
      rho * ((H.slotDegree s : ℝ) * ((J + 2 * S : ℕ) : ℝ) /
        ((3 * lambda : ℕ) : ℝ)) := by
  rw [linearRowMean_uniform_eq_rho_mul_sum]
  exact mul_le_mul_of_nonneg_left
    (H.sum_residualDeleteWeight_slot_le_job_slot
      lambda J S hlambda s hjobDegree hslotDegree) hrho0

/-- A normalized job-deletion row has coefficient sum at most
`degree(j) * D / lambda`. -/
theorem sum_residualDeleteWeight_job_le_degree
    (lambda D : ℕ) (hlambda : 0 < lambda) (j : Job)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) :
    (∑ p : Option, H.residualDeleteWeight lambda (Sum.inl j) p) ≤
      ((H.fiber j).card : ℝ) * (D : ℝ) / (lambda : ℝ) := by
  simp only [residualDeleteWeight]
  rw [← Finset.sum_div]
  simp_rw [← Nat.cast_sum]
  calc
    _ ≤ (((H.fiber j).card * (2 * D) : ℕ) : ℝ) /
          ((2 * lambda : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast H.sum_externalBlockedBy_card_le_fiber_mul_two_mul
          j D hslotDegree
      · positivity
    _ = ((H.fiber j).card : ℝ) * (D : ℝ) / (lambda : ℝ) := by
      push_cast
      field_simp

/-- A normalized slot-deletion row has coefficient sum at most
`degree(s) * D / lambda`. -/
theorem sum_residualDeleteWeight_slot_le_degree
    (lambda D : ℕ) (hlambda : 0 < lambda) (s : Slot)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ t, H.slotDegree t ≤ D) :
    (∑ p : Option, H.residualDeleteWeight lambda (Sum.inr s) p) ≤
      (H.slotDegree s : ℝ) * (D : ℝ) / (lambda : ℝ) := by
  calc
    (∑ p : Option, H.residualDeleteWeight lambda (Sum.inr s) p) ≤
        ∑ p : Option, ((H.slotBlockedBy s p).card : ℝ) /
          ((3 * lambda : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hsp : s ∈ H.slots p
      · simp [residualDeleteWeight, hsp]
        positivity
      · simp [residualDeleteWeight, hsp]
    _ = (∑ p : Option, ((H.slotBlockedBy s p).card : ℝ)) /
        ((3 * lambda : ℕ) : ℝ) := by rw [Finset.sum_div]
    _ ≤ (((H.slotDegree s) * (3 * D) : ℕ) : ℝ) /
        ((3 * lambda : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast H.sum_slotBlockedBy_card_le_slotDegree_mul_three_mul
          s D hjobDegree hslotDegree
      · positivity
    _ = (H.slotDegree s : ℝ) * (D : ℝ) / (lambda : ℝ) := by
      push_cast
      field_simp

/-- Uniform Bernoulli mean for a job row, retaining its actual degree. -/
theorem residualDeleteWeight_job_mean_le_degree
    (rho : ℝ) (lambda D : ℕ) (hlambda : 0 < lambda)
    (hrho0 : 0 ≤ rho) (j : Job)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) :
    linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inl j) ≤
      rho * (((H.fiber j).card : ℝ) * (D : ℝ) / (lambda : ℝ)) := by
  rw [linearRowMean_uniform_eq_rho_mul_sum]
  exact mul_le_mul_of_nonneg_left
    (H.sum_residualDeleteWeight_job_le_degree
      lambda D hlambda j hslotDegree) hrho0

/-- Uniform Bernoulli mean for a slot row, retaining its actual degree. -/
theorem residualDeleteWeight_slot_mean_le_degree
    (rho : ℝ) (lambda D : ℕ) (hlambda : 0 < lambda)
    (hrho0 : 0 ≤ rho) (s : Slot)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ t, H.slotDegree t ≤ D) :
    linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inr s) ≤
      rho * ((H.slotDegree s : ℝ) * (D : ℝ) / (lambda : ℝ)) := by
  rw [linearRowMean_uniform_eq_rho_mul_sum]
  exact mul_le_mul_of_nonneg_left
    (H.sum_residualDeleteWeight_slot_le_degree
      lambda D hlambda s hjobDegree hslotDegree) hrho0

/-- The current degree naturally attached to a residual-deletion row. -/
def residualDeleteRowDegree : ResidualDeleteRow Job Slot → ℕ
  | Sum.inl j => (H.fiber j).card
  | Sum.inr s => H.slotDegree s

/-- Both row kinds have mean at most `rho * currentDegree * D / lambda`. -/
theorem residualDeleteWeight_mean_le_degree
    (rho : ℝ) (lambda D : ℕ) (hlambda : 0 < lambda)
    (hrho0 : 0 ≤ rho)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) :
    ∀ r : ResidualDeleteRow Job Slot,
      linearRowMean (fun _ : Option ↦ rho)
          (H.residualDeleteWeight lambda) r ≤
        rho * ((H.residualDeleteRowDegree r : ℝ) * (D : ℝ) /
          (lambda : ℝ)) := by
  intro r
  rcases r with j | s
  · exact H.residualDeleteWeight_job_mean_le_degree
      rho lambda D hlambda hrho0 j hslotDegree
  · exact H.residualDeleteWeight_slot_mean_le_degree
      rho lambda D hlambda hrho0 s hjobDegree hslotDegree

/-- The support of a job-deletion row keeps the target job's current
degree.  Each of its options meets at most `2D` other options. -/
theorem externalJobRowCover_card_le_degree
    (D : ℕ) (hslotDegree : ∀ s, H.slotDegree s ≤ D) (j : Job) :
    (H.externalJobRowCover j).card ≤ (H.fiber j).card * (2 * D) := by
  calc
    (H.externalJobRowCover j).card ≤
        ∑ o ∈ H.fiber j, (H.optionsMeeting o).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _o ∈ H.fiber j, 2 * D :=
      Finset.sum_le_sum fun o _ ↦
        H.optionsMeeting_card_le_two_mul D hslotDegree o
    _ = (H.fiber j).card * (2 * D) := by simp

/-- The support of a slot-deletion row keeps the target slot's current
degree. -/
theorem slotDeleteRowCover_card_le_degree
    (D : ℕ) (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) (s : Slot) :
    (H.slotDeleteRowCover s).card ≤ H.slotDegree s * (3 * D) := by
  calc
    (H.slotDeleteRowCover s).card ≤
        ∑ o ∈ H.slotOptionFiber s,
          (H.fiber (H.owner o) ∪ H.optionsMeeting o).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ o ∈ H.slotOptionFiber s,
        ((H.fiber (H.owner o)).card + (H.optionsMeeting o).card) := by
      exact Finset.sum_le_sum fun o _ ↦ Finset.card_union_le _ _
    _ ≤ ∑ _o ∈ H.slotOptionFiber s, (D + 2 * D) := by
      apply Finset.sum_le_sum
      intro o _
      exact Nat.add_le_add (hjobDegree (H.owner o))
        (H.optionsMeeting_card_le_two_mul D hslotDegree o)
    _ = (H.slotOptionFiber s).card * (D + 2 * D) := by simp
    _ = H.slotDegree s * (3 * D) := by
      rw [H.slotOptionFiber_card]
      ring

/-- Every residual-deletion support is bounded by three times its current
row degree times the ambient maximum degree. -/
theorem residualDeleteWeight_support_card_le_degree
    (lambda D : ℕ) (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) :
    ∀ r : ResidualDeleteRow Job Slot,
      (linearRowSupport (H.residualDeleteWeight lambda) r).card ≤
        3 * H.residualDeleteRowDegree r * D := by
  intro r
  rcases r with j | s
  · calc
      _ ≤ (H.externalJobRowCover j).card := Finset.card_le_card
        (H.residualDeleteWeight_job_support_subset lambda j)
      _ ≤ (H.fiber j).card * (2 * D) :=
        H.externalJobRowCover_card_le_degree D hslotDegree j
      _ ≤ (H.fiber j).card * (3 * D) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (H.fiber j).card * D := by ring
  · calc
      _ ≤ (H.slotDeleteRowCover s).card := Finset.card_le_card
        (H.residualDeleteWeight_slot_support_subset lambda s)
      _ ≤ H.slotDegree s * (3 * D) :=
        H.slotDeleteRowCover_card_le_degree D hjobDegree hslotDegree s
      _ = 3 * H.slotDegree s * D := by ring

end WeightedEdgeColoring.RankThreeOptionSystem
