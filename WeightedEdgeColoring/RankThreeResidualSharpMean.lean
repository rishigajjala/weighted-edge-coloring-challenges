import WeightedEdgeColoring.RankThreeResidualHarrisExplicit
import WeightedEdgeColoring.RankThreeResidualCollisionBounds

/-!
# Sharp means for normalized residual-deletion rows

The coarse estimate treats every nonzero normalized blocker coefficient as
one.  Here we sum the coefficients before applying the probability `rho`.
Double counting localizes the targets to one job fibre or one slot fibre,
so the normalizing factor `lambda` remains visible.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Every target of an external blocker for `j` belongs to the fibre of
`j`. -/
theorem biUnion_externalBlockedBy_subset_fiber (j : Job) :
    (Finset.univ : Finset Option).biUnion (H.externalBlockedBy j) ⊆
      H.fiber j := by
  intro o ho
  rcases Finset.mem_biUnion.mp ho with ⟨p, _hp, hop⟩
  by_cases hpj : H.owner p = j
  · simp [externalBlockedBy, hpj] at hop
  · have : o ∈ H.blockedBy j p := by
      simpa [externalBlockedBy, hpj] using hop
    exact (Finset.mem_filter.mp this).1

/-- Reverse double counting gives the local bound `2D²`, without any bound
on the total number of options. -/
theorem sum_externalBlockedBy_card_le_two_mul_sq_local
    (j : Job) (D : ℕ)
    (hjobDegree : ∀ k, (H.fiber k).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) :
    (∑ p : Option, (H.externalBlockedBy j p).card) ≤ 2 * D ^ 2 := by
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
    _ ≤ D * (2 * D) :=
      Nat.mul_le_mul_right (2 * D) (hjobDegree j)
    _ = 2 * D ^ 2 := by ring

/-- Every target of a slot-blocker row uses the row's slot. -/
theorem biUnion_slotBlockedBy_subset_slotOptionFiber (s : Slot) :
    (Finset.univ : Finset Option).biUnion (H.slotBlockedBy s) ⊆
      H.slotOptionFiber s := by
  intro o ho
  rcases Finset.mem_biUnion.mp ho with ⟨p, _hp, hop⟩
  have houter := (Finset.mem_filter.mp hop).1
  exact H.mem_slotOptionFiber.mpr (Finset.mem_filter.mp houter).2

/-- Reverse double counting gives the local slot-row bound `3D²`, again
without a global bound on the option type. -/
theorem sum_slotBlockedBy_card_le_three_mul_sq_local
    (s : Slot) (D : ℕ)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ t, H.slotDegree t ≤ D) :
    (∑ p : Option, (H.slotBlockedBy s p).card) ≤ 3 * D ^ 2 := by
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
    _ ≤ D * (3 * D) := by
      apply Nat.mul_le_mul_right
      rw [H.slotOptionFiber_card]
      exact hslotDegree s
    _ = 3 * D ^ 2 := by ring

/-- Exact sum of the normalized external-job coefficients. -/
theorem sum_residualDeleteWeight_job_le_precise
    (lambda D : ℕ) (j : Job)
    (hjobDegree : ∀ k, (H.fiber k).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) :
    (∑ p : Option,
      H.residualDeleteWeight lambda (Sum.inl j) p) ≤
        (((2 * D ^ 2 : ℕ) : ℝ) / ((2 * lambda : ℕ) : ℝ)) := by
  simp only [residualDeleteWeight]
  rw [← Finset.sum_div]
  simp_rw [← Nat.cast_sum]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast H.sum_externalBlockedBy_card_le_two_mul_sq_local
      j D hjobDegree hslotDegree
  · exact Nat.cast_nonneg _

/-- Exact sum of the normalized slot coefficients.  The definition zeros
options already using `s`; discarding that restriction only increases the
sum. -/
theorem sum_residualDeleteWeight_slot_le_precise
    (lambda D : ℕ) (s : Slot)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ t, H.slotDegree t ≤ D) :
    (∑ p : Option,
      H.residualDeleteWeight lambda (Sum.inr s) p) ≤
        (((3 * D ^ 2 : ℕ) : ℝ) / ((3 * lambda : ℕ) : ℝ)) := by
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
    _ ≤ (((3 * D ^ 2 : ℕ) : ℝ) / ((3 * lambda : ℕ) : ℝ)) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast H.sum_slotBlockedBy_card_le_three_mul_sq_local
          s D hjobDegree hslotDegree
      · exact Nat.cast_nonneg _

/-- After cancelling the common factor two, a job row has total normalized
coefficient at most `D²/lambda`. -/
theorem sum_residualDeleteWeight_job_le
    (lambda D : ℕ) (hlambda : 0 < lambda) (j : Job)
    (hjobDegree : ∀ k, (H.fiber k).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) :
    (∑ p : Option,
      H.residualDeleteWeight lambda (Sum.inl j) p) ≤
        (D : ℝ) ^ 2 / (lambda : ℝ) := by
  calc
    _ ≤ (((2 * D ^ 2 : ℕ) : ℝ) / ((2 * lambda : ℕ) : ℝ)) :=
      H.sum_residualDeleteWeight_job_le_precise
        lambda D j hjobDegree hslotDegree
    _ = (D : ℝ) ^ 2 / (lambda : ℝ) := by
      push_cast
      field_simp

/-- After cancelling the common factor three, a slot row has the same
`D²/lambda` coefficient-sum bound. -/
theorem sum_residualDeleteWeight_slot_le
    (lambda D : ℕ) (hlambda : 0 < lambda) (s : Slot)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ t, H.slotDegree t ≤ D) :
    (∑ p : Option,
      H.residualDeleteWeight lambda (Sum.inr s) p) ≤
        (D : ℝ) ^ 2 / (lambda : ℝ) := by
  calc
    _ ≤ (((3 * D ^ 2 : ℕ) : ℝ) / ((3 * lambda : ℕ) : ℝ)) :=
      H.sum_residualDeleteWeight_slot_le_precise
        lambda D s hjobDegree hslotDegree
    _ = (D : ℝ) ^ 2 / (lambda : ℝ) := by
      push_cast
      field_simp

/-- With uniform retention probability, a linear-row mean is `rho` times
the total coefficient sum, including coefficients outside its declared
support (which are zero). -/
theorem linearRowMean_uniform_eq_rho_mul_sum
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    (rho : ℝ) (a : Row → Option → ℝ) (r : Row) :
    linearRowMean (fun _ : Option ↦ rho) a r =
      rho * ∑ o : Option, a r o := by
  rw [linearRowMean]
  unfold mean
  simp only [insideParameter]
  rw [← Finset.mul_sum]
  congr 1
  calc
    (∑ i : Inside (linearRowSupport a r), a r i) =
        ∑ o ∈ linearRowSupport a r, a r o := by
      rw [Finset.sum_subtype (linearRowSupport a r)]
      intro o
      simp
    _ = ∑ o : Option, a r o := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro o _ho hnot
      by_contra hzero
      apply hnot
      simp [linearRowSupport, hzero]

/-- Sharp uniform mean for a normalized job-deletion row. -/
theorem residualDeleteWeight_job_mean_le
    (rho : ℝ) (lambda D : ℕ) (hlambda : 0 < lambda)
    (hrho0 : 0 ≤ rho) (j : Job)
    (hjobDegree : ∀ k, (H.fiber k).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) :
    linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inl j) ≤
      rho * ((D : ℝ) ^ 2 / (lambda : ℝ)) := by
  rw [linearRowMean_uniform_eq_rho_mul_sum]
  exact mul_le_mul_of_nonneg_left
    (H.sum_residualDeleteWeight_job_le
      lambda D hlambda j hjobDegree hslotDegree) hrho0

/-- Sharp uniform mean for a normalized slot-deletion row. -/
theorem residualDeleteWeight_slot_mean_le
    (rho : ℝ) (lambda D : ℕ) (hlambda : 0 < lambda)
    (hrho0 : 0 ≤ rho) (s : Slot)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ t, H.slotDegree t ≤ D) :
    linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inr s) ≤
      rho * ((D : ℝ) ^ 2 / (lambda : ℝ)) := by
  rw [linearRowMean_uniform_eq_rho_mul_sum]
  exact mul_le_mul_of_nonneg_left
    (H.sum_residualDeleteWeight_slot_le
      lambda D hlambda s hjobDegree hslotDegree) hrho0

/-- Both residual-deletion row kinds obey the same sharp uniform mean bound. -/
theorem residualDeleteWeight_mean_le_sharp
    (rho : ℝ) (lambda D : ℕ) (hlambda : 0 < lambda)
    (hrho0 : 0 ≤ rho)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) :
    ∀ r : ResidualDeleteRow Job Slot,
      linearRowMean (fun _ : Option ↦ rho)
          (H.residualDeleteWeight lambda) r ≤
        rho * ((D : ℝ) ^ 2 / (lambda : ℝ)) := by
  intro r
  rcases r with j | s
  · exact H.residualDeleteWeight_job_mean_le
      rho lambda D hlambda hrho0 j hjobDegree hslotDegree
  · exact H.residualDeleteWeight_slot_mean_le
      rho lambda D hlambda hrho0 s hjobDegree hslotDegree

universe x

variable {Group : Type x} [Fintype Group] [DecidableEq Group]

/-- A half-product Harris round using the sharp common upper mean
`rho * D²/lambda`.  This is still a one-round statement: it does not claim
that the same hypotheses automatically persist after iteration. -/
theorem exists_oneRound_residual_harris_uniform_sharp_mean
    (rho : ℝ) (members : Group → Finset Job)
    (lambda : ℕ) (hlambda : 0 < lambda)
    (jobBudget : Job → ℕ) (slotBudget : Slot → ℕ)
    (D R K m : ℕ) (pairX rowX cap : ℝ)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hmembers : ∀ g, (members g).card ≤ K)
    (hgroupSupportLower : ∀ g,
      m ≤ (linearRowSupport
        (H.jobGroupCoverageWeight members) g).card)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (hpairX0 : 0 ≤ pairX) (hrowX0 : 0 ≤ rowX)
    (hpairXcap : pairX ≤ cap) (hrowXcap : rowX ≤ cap)
    (hcap1 : cap < 1)
    (hpairTail : rho * rho ≤ pairX / 2)
    (hlowerTail :
      Real.exp (-(1 / 8 : ℝ) * (rho * (m : ℝ))) ≤ rowX / 2)
    (hthreshold : ∀ r : ResidualDeleteRow Job Slot,
      4 * (rho * ((D : ℝ) ^ 2 / (lambda : ℝ))) ≤
        residualDeleteThreshold lambda jobBudget slotBudget r)
    (hupperTail :
      Real.exp (-2 * (rho * ((D : ℝ) ^ 2 / (lambda : ℝ)))) ≤
        rowX / 2)
    (hpairCost : rowX * (2 * R : ℕ) ≤ 1 / 2)
    (hlowerCost : cap * (((K * D) * (14 * D) : ℕ) : ℝ) ≤ 1 / 2)
    (hupperCost : rowX * (((3 * D * D) * R : ℕ) : ℝ) ≤ 1 / 2) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ g, (1 / 2 : ℝ) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.jobGroupCoverageWeight members) g <
        ∑ o ∈ S, H.jobGroupCoverageWeight members g o) ∧
      (∀ j, ¬ H.Covers S j →
        H.residualJobDegree ∅ j ≤ H.residualJobDegree S j + jobBudget j) ∧
      (∀ s, (∀ p ∈ S, s ∉ H.slots p) →
        H.residualSlotDegree ∅ s ≤
          H.residualSlotDegree S s + slotBudget s) := by
  let muUpper : ℝ := rho * ((D : ℝ) ^ 2 / (lambda : ℝ))
  have hlambda0 : 0 ≤ (lambda : ℝ) := Nat.cast_nonneg lambda
  have hmuUpper0 : 0 ≤ muUpper := by
    dsimp [muUpper]
    exact mul_nonneg hrho0 (div_nonneg (sq_nonneg _) hlambda0)
  have hcap0 : 0 ≤ cap := hpairX0.trans hpairXcap
  have hcap1' : cap ≤ 1 := hcap1.le
  have hrowX1 : rowX ≤ 1 := hrowXcap.trans hcap1'
  have hpairPow : (1 / 2 : ℝ) ≤ (1 - rowX) ^ (2 * R) := by
    apply half_le_one_sub_pow_of_mul_le_half rowX (2 * R)
      hrowX0 hrowX1
    exact_mod_cast hpairCost
  have hlowerPowMax : (1 / 2 : ℝ) ≤
      (1 - cap) ^ ((K * D) * (14 * D)) := by
    exact half_le_one_sub_pow_of_mul_le_half cap ((K * D) * (14 * D))
      hcap0 hcap1' hlowerCost
  have hupperPowMax : (1 / 2 : ℝ) ≤
      (1 - rowX) ^ ((3 * D * D) * R) := by
    exact half_le_one_sub_pow_of_mul_le_half rowX ((3 * D * D) * R)
      hrowX0 hrowX1 hupperCost
  have hresult := H.exists_oneRound_residual_harris
    (fun _ : Option ↦ rho) members lambda hlambda jobBudget slotBudget
    (fun _ ↦ 1) D R pairX rowX cap (1 / 2 : ℝ) (rho * (m : ℝ))
    (fun _ ↦ hrho0) (fun _ ↦ hrho1)
    hjobDegree hslotDegree hjobSlot hslotPair hgroupIncidence
    (by norm_num) half_lowerTail_coefficient_nonpos
    (fun g ↦ by
      rw [H.linearRowMean_jobGroupCoverageWeight_uniform]
      apply mul_le_mul_of_nonneg_left _ hrho0
      exact_mod_cast hgroupSupportLower g)
    (fun _ ↦ by norm_num)
    hpairX0 hrowX0 hpairXcap hrowXcap hcap1
    (fun _ ↦ hpairTail.trans (by
      calc
        pairX / 2 = pairX * (1 / 2) := by ring
        _ ≤ pairX * (1 - rowX) ^ (2 * R) :=
          mul_le_mul_of_nonneg_left hpairPow hpairX0))
    (fun g ↦ by
      have hs := H.jobGroupCoverage_support_card_le members K D
        hmembers hjobDegree g
      have hdegree :
          (linearRowSupport
              (H.jobGroupCoverageWeight members) g).card *
                (6 * D + 8 * D) ≤ (K * D) * (14 * D) := by
        calc
          _ ≤ (K * D) * (6 * D + 8 * D) :=
            Nat.mul_le_mul_right (6 * D + 8 * D) hs
          _ = (K * D) * (14 * D) := by ring
      have hpow : (1 / 2 : ℝ) ≤
          (1 - cap) ^
            ((linearRowSupport
              (H.jobGroupCoverageWeight members) g).card *
                (6 * D + 8 * D)) :=
        hlowerPowMax.trans
          (pow_le_pow_of_le_one (sub_nonneg.mpr hcap1')
            (sub_le_self 1 hcap0) hdegree)
      calc
        Real.exp
            (((1 / 2 : ℝ) * (1 - 1 / 2) +
              (Real.exp (-(1 / 2 : ℝ)) - 1)) *
                (rho * (m : ℝ))) ≤
            Real.exp (-(1 / 8 : ℝ) * (rho * (m : ℝ))) :=
          half_lowerTail_exp_le _
            (mul_nonneg hrho0 (Nat.cast_nonneg m))
        _ ≤ rowX / 2 := hlowerTail
        _ = rowX * (1 / 2) := by ring
        _ ≤ rowX * (1 - cap) ^
            ((linearRowSupport
              (H.jobGroupCoverageWeight members) g).card *
                (6 * D + 8 * D)) :=
          mul_le_mul_of_nonneg_left hpow hrowX0)
    (fun r ↦ by
      have hmean : linearRowMean (fun _ : Option ↦ rho)
          (H.residualDeleteWeight lambda) r ≤ muUpper := by
        simpa [muUpper] using H.residualDeleteWeight_mean_le_sharp
          rho lambda D hlambda hrho0 hjobDegree hslotDegree r
      have hcoef : 0 ≤ Real.exp (1 : ℝ) - 1 :=
        sub_nonneg.mpr (Real.one_le_exp (by norm_num))
      have hfirst :
          Real.exp (-(1 : ℝ) *
              residualDeleteThreshold lambda jobBudget slotBudget r +
            (Real.exp (1 : ℝ) - 1) *
              linearRowMean (fun _ : Option ↦ rho)
                (H.residualDeleteWeight lambda) r) ≤
            Real.exp (-residualDeleteThreshold lambda jobBudget slotBudget r +
              (Real.exp 1 - 1) * muUpper) := by
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_left hmean hcoef
        norm_num
        linarith
      have htail :
          Real.exp (-residualDeleteThreshold lambda jobBudget slotBudget r +
              (Real.exp 1 - 1) * muUpper) ≤ Real.exp (-2 * muUpper) :=
        upperTail_lambda_one_exp_le muUpper
          (residualDeleteThreshold lambda jobBudget slotBudget r)
          hmuUpper0 (by simpa [muUpper] using hthreshold r)
      have hsupport :=
        H.residualDeleteWeight_support_card_le_three_mul_sq
          lambda D hjobDegree hslotDegree r
      have hdegree :
          (linearRowSupport (H.residualDeleteWeight lambda) r).card * R ≤
            (3 * D * D) * R := Nat.mul_le_mul_right R hsupport
      have hpow : (1 / 2 : ℝ) ≤
          (1 - rowX) ^
            ((linearRowSupport
              (H.residualDeleteWeight lambda) r).card * R) :=
        hupperPowMax.trans
          (pow_le_pow_of_le_one (sub_nonneg.mpr hrowX1)
            (sub_le_self 1 hrowX0) hdegree)
      calc
        _ ≤ Real.exp (-2 * muUpper) := hfirst.trans htail
        _ ≤ rowX / 2 := by simpa [muUpper] using hupperTail
        _ = rowX * (1 / 2) := by ring
        _ ≤ rowX * (1 - rowX) ^
            ((linearRowSupport
              (H.residualDeleteWeight lambda) r).card * R) :=
          mul_le_mul_of_nonneg_left hpow hrowX0)
  norm_num at hresult ⊢
  exact hresult

end WeightedEdgeColoring.RankThreeOptionSystem
