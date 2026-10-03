import WeightedEdgeColoring.RankThreeResidualSlotLowerIncidence

/-!
# A common lower mean for all residual-deletion rows

The job-row lower incidence theorem has denominator `2 * lambda`; the
slot-row theorem has denominator `3 * lambda`.  If every job fibre and every
slot fibre has size at least `d`, both therefore have the common lower bound
`rho * d * (d - lambda) / (3 * lambda)`.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Every job-deletion row has the common lower mean.  The job-row incidence
bound itself has the stronger denominator `2 * lambda`; this theorem weakens
it to the denominator shared with slot rows. -/
theorem residualDeleteWeight_job_mean_ge_uniform
    (rho : ℝ) (j : Job) (d lambda : ℕ) (hlambda : 0 < lambda)
    (hrho : 0 ≤ rho)
    (hjobDegree : ∀ k, d ≤ (H.fiber k).card)
    (hslotDegree : ∀ s, d ≤ H.slotDegree s)
    (hnonempty : ∀ o, (H.slots o).Nonempty)
    (hjobSlot : ∀ k s, H.jobSlotCodegree k s ≤ lambda) :
    rho * ((((d * (d - lambda) : ℕ) : ℝ) /
        ((3 * lambda : ℕ) : ℝ))) ≤
      linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inl j) := by
  have hbase := H.residualDeleteWeight_job_mean_ge
    rho j d lambda hlambda hrho
    (fun o _ho ↦ hnonempty o)
    (fun o _ho s _hs ↦ hslotDegree s)
    (fun s ↦ hjobSlot j s)
  apply le_trans ?_ hbase
  apply mul_le_mul_of_nonneg_left ?_ hrho
  apply div_le_div₀
  · positivity
  · exact_mod_cast Nat.mul_le_mul_right (d - lambda) (hjobDegree j)
  · positivity
  · exact_mod_cast (show 2 * lambda ≤ 3 * lambda by omega)

/-- Every slot-deletion row has the common lower mean. -/
theorem residualDeleteWeight_slot_mean_ge_uniform
    (rho : ℝ) (s : Slot) (d lambda : ℕ) (hlambda : 0 < lambda)
    (hrho : 0 ≤ rho)
    (hjobDegree : ∀ k, d ≤ (H.fiber k).card)
    (hslotDegree : ∀ t, d ≤ H.slotDegree t)
    (hjobSlot : ∀ k t, H.jobSlotCodegree k t ≤ lambda) :
    rho * ((((d * (d - lambda) : ℕ) : ℝ) /
        ((3 * lambda : ℕ) : ℝ))) ≤
      linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) (Sum.inr s) := by
  have hbase := H.residualDeleteWeight_slot_mean_ge
    rho s d lambda hlambda hrho hjobDegree (fun k ↦ hjobSlot k s)
  apply le_trans ?_ hbase
  apply mul_le_mul_of_nonneg_left ?_ hrho
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Nat.mul_le_mul_right (d - lambda) (hslotDegree s)
  · positivity

/-- Uniform lower bound for every residual-deletion row. -/
theorem residualDeleteWeight_mean_ge_uniform
    (rho : ℝ) (d lambda : ℕ) (hlambda : 0 < lambda)
    (hrho : 0 ≤ rho)
    (hjobDegree : ∀ j, d ≤ (H.fiber j).card)
    (hslotDegree : ∀ s, d ≤ H.slotDegree s)
    (hnonempty : ∀ o, (H.slots o).Nonempty)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda) :
    ∀ r : ResidualDeleteRow Job Slot,
      rho * ((((d * (d - lambda) : ℕ) : ℝ) /
          ((3 * lambda : ℕ) : ℝ))) ≤
        linearRowMean (fun _ : Option ↦ rho)
          (H.residualDeleteWeight lambda) r := by
  intro r
  rcases r with j | s
  · exact H.residualDeleteWeight_job_mean_ge_uniform
      rho j d lambda hlambda hrho hjobDegree hslotDegree
        hnonempty hjobSlot
  · exact H.residualDeleteWeight_slot_mean_ge_uniform
      rho s d lambda hlambda hrho hjobDegree hslotDegree hjobSlot

end WeightedEdgeColoring.RankThreeOptionSystem
