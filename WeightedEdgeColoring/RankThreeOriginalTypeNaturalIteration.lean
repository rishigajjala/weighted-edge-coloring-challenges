import WeightedEdgeColoring.RankThreeOriginalTypeSharpStep

/-!
# Fixed-parameter natural iteration on original option types

The job scale is rounded down after every sharp round.  The slot cap is also
rounded down: the one-round conclusion already bounds an integer slot degree
by the unrounded real cap, so the natural floor is valid and saves one unit
of rounding loss.  A single explicit margin preserves the fixed slot/job
gap.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  {Group : Type x} [Fintype Group] [DecidableEq Group]
  {H : RankThreeOptionSystem Job Slot Option}

namespace OriginalIterationState

noncomputable def naturalSharpJobScale
    (d0 : ℕ) (a gamma etaJob : ℝ) : ℕ → ℕ
  | 0 => d0
  | n + 1 => ⌊(WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) *
      naturalSharpJobScale d0 a gamma etaJob n⌋₊

noncomputable def naturalSharpSlotCap
    (S0 d0 : ℕ)
    (a gamma etaJob etaLoad etaCollision : ℝ) : ℕ → ℕ
  | 0 => S0
  | n + 1 =>
      ⌊(WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
          etaLoad + etaCollision) *
        naturalSharpJobScale d0 a gamma etaJob n⌋₊

/-- Slot degree to which cyclic regularization pads in a round.  It is the
largest integer below the maintained real slot/job envelope, rather than the
tighter cap inherited from the previous round. -/
noncomputable def fixedSlackPaddedSlotTarget (gamma : ℝ) (d : ℕ) : ℕ :=
  ⌊(1 - gamma) * d⌋₊

theorem fixedSlackPaddedSlotTarget_le
    (gamma : ℝ) (d : ℕ) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1) :
    fixedSlackPaddedSlotTarget gamma d ≤ d := by
  have hfactor : 0 ≤ 1 - gamma := by linarith
  have harg : 0 ≤ (1 - gamma) * (d : ℝ) :=
    mul_nonneg hfactor (Nat.cast_nonneg d)
  have hfloor : ((fixedSlackPaddedSlotTarget gamma d : ℕ) : ℝ) ≤
      (1 - gamma) * d := Nat.floor_le harg
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hreal : ((fixedSlackPaddedSlotTarget gamma d : ℕ) : ℝ) ≤ d := by
    nlinarith
  exact_mod_cast hreal

theorem nat_le_fixedSlackPaddedSlotTarget
    (gamma : ℝ) (d x : ℕ)
    (hgamma1 : gamma ≤ 1)
    (hx : (x : ℝ) ≤ (1 - gamma) * d) :
    x ≤ fixedSlackPaddedSlotTarget gamma d := by
  have hfactor : 0 ≤ 1 - gamma := by linarith
  have harg : 0 ≤ (1 - gamma) * (d : ℝ) :=
    mul_nonneg hfactor (Nat.cast_nonneg d)
  exact (Nat.le_floor_iff harg).mpr hx

/-- The padded target loses less than one slot from the real envelope. -/
theorem fixedSlackPaddedSlotTarget_lower
    (gamma : ℝ) (d : ℕ) :
    (1 - gamma) * d - 1 < fixedSlackPaddedSlotTarget gamma d := by
  have h := Nat.lt_floor_add_one ((1 - gamma) * d)
  dsimp [fixedSlackPaddedSlotTarget]
  linarith

@[simp] theorem naturalSharpJobScale_zero
    (d0 : ℕ) (a gamma etaJob : ℝ) :
    naturalSharpJobScale d0 a gamma etaJob 0 = d0 := rfl

@[simp] theorem naturalSharpJobScale_succ
    (d0 n : ℕ) (a gamma etaJob : ℝ) :
    naturalSharpJobScale d0 a gamma etaJob (n + 1) =
      ⌊(WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) *
        naturalSharpJobScale d0 a gamma etaJob n⌋₊ := rfl

@[simp] theorem naturalSharpSlotCap_zero
    (S0 d0 : ℕ) (a gamma etaJob etaLoad etaCollision : ℝ) :
    naturalSharpSlotCap S0 d0 a gamma etaJob etaLoad etaCollision 0 = S0 := rfl

@[simp] theorem naturalSharpSlotCap_succ
    (S0 d0 n : ℕ) (a gamma etaJob etaLoad etaCollision : ℝ) :
    naturalSharpSlotCap S0 d0 a gamma etaJob etaLoad etaCollision (n + 1) =
      ⌊(WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
          etaLoad + etaCollision) *
        naturalSharpJobScale d0 a gamma etaJob n⌋₊ := rfl

/-- One unit of floor loss is absorbed if the real gap surplus times the
current job scale is at least `1-gamma`. -/
theorem naturalSharp_rounding_preserves_gap
    (d : ℕ) (a gamma etaJob etaLoad etaCollision : ℝ)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hjobRate0 : 0 ≤ WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob)
    (hslotRate0 : 0 ≤
      WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
        etaLoad + etaCollision)
    (hmargin : 1 - gamma ≤
      (a * gamma * (1 - gamma) -
        ((1 - gamma) * etaJob + etaLoad + etaCollision)) * d) :
    (⌊(WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
          etaLoad + etaCollision) * d⌋₊ : ℝ) ≤
      (1 - gamma) *
        ⌊(WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d⌋₊ := by
  let rJ := WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob
  let rS := WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
    etaLoad + etaCollision
  have hfactor : 0 ≤ 1 - gamma := by linarith
  have hJarg : 0 ≤ rJ * d := mul_nonneg hjobRate0 (Nat.cast_nonneg d)
  have hSarg : 0 ≤ rS * d := mul_nonneg hslotRate0 (Nat.cast_nonneg d)
  have hfloorS : ((⌊rS * d⌋₊ : ℕ) : ℝ) ≤ rS * d := Nat.floor_le hSarg
  have hfloorJ : rJ * d < (⌊rJ * d⌋₊ : ℕ) + 1 :=
    Nat.lt_floor_add_one _
  have hgap := sharpFixedSlack_separated_exact_gap
    a gamma etaJob etaLoad etaCollision
  dsimp [rJ, rS] at hfloorS hfloorJ ⊢
  nlinarith [hgap]

/-- The rounded natural sequences preserve the same fixed gap at every
round for which the explicit rounding margin holds. -/
theorem naturalSharpSlotCap_le_gap
    (S0 d0 : ℕ) (a gamma etaJob etaLoad etaCollision : ℝ)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hjobRate0 : 0 ≤ WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob)
    (hslotRate0 : 0 ≤
      WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
        etaLoad + etaCollision)
    (hgap0 : (S0 : ℝ) ≤ (1 - gamma) * d0)
    (hmargin : ∀ n, 1 - gamma ≤
      (a * gamma * (1 - gamma) -
        ((1 - gamma) * etaJob + etaLoad + etaCollision)) *
          naturalSharpJobScale d0 a gamma etaJob n) :
    ∀ n,
      (naturalSharpSlotCap S0 d0 a gamma etaJob etaLoad etaCollision n : ℝ) ≤
        (1 - gamma) * naturalSharpJobScale d0 a gamma etaJob n := by
  intro n
  cases n with
  | zero => exact hgap0
  | succ n =>
      exact naturalSharp_rounding_preserves_gap
        (naturalSharpJobScale d0 a gamma etaJob n)
        a gamma etaJob etaLoad etaCollision hgamma0 hgamma1
        hjobRate0 hslotRate0 (hmargin n)

theorem naturalSharpSlotCap_le_jobScale
    (S0 d0 : ℕ) (a gamma etaJob etaLoad etaCollision : ℝ)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hjobRate0 : 0 ≤ WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob)
    (hslotRate0 : 0 ≤
      WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
        etaLoad + etaCollision)
    (hgap0 : (S0 : ℝ) ≤ (1 - gamma) * d0)
    (hmargin : ∀ n, 1 - gamma ≤
      (a * gamma * (1 - gamma) -
        ((1 - gamma) * etaJob + etaLoad + etaCollision)) *
          naturalSharpJobScale d0 a gamma etaJob n) :
    ∀ n,
      naturalSharpSlotCap S0 d0 a gamma etaJob etaLoad etaCollision n ≤
        naturalSharpJobScale d0 a gamma etaJob n := by
  intro n
  have hgap := naturalSharpSlotCap_le_gap S0 d0 a gamma etaJob etaLoad
    etaCollision hgamma0 hgamma1 hjobRate0 hslotRate0 hgap0 hmargin n
  have hreal :
      (naturalSharpSlotCap S0 d0 a gamma etaJob etaLoad etaCollision n : ℝ) ≤
        naturalSharpJobScale d0 a gamma etaJob n := by
    have hd0 : (0 : ℝ) ≤ naturalSharpJobScale d0 a gamma etaJob n :=
      Nat.cast_nonneg _
    nlinarith
  exact_mod_cast hreal

/-- Concrete trace.  Each successor stores the actual sharp round and its
group, degree, slot, and same-gap conclusions; hence endpoint-group coverage
is available by pattern matching on any round of the trace. -/
inductive NaturalSharpTrace
    (members : ∀ n (X : OriginalIterationState H),
      Group → Finset (ActiveJob X.activeJobs))
    (m : ℕ → ℕ) (d0 : ℕ)
    (a gamma etaJob etaLoad etaCollision delta : ℝ) :
    ℕ → OriginalIterationState H → OriginalIterationState H → Prop
  | zero (X) : NaturalSharpTrace members m d0 a gamma etaJob etaLoad
      etaCollision delta 0 X X
  | succ {n X Y Z}
      (hprev : NaturalSharpTrace members m d0 a gamma etaJob etaLoad
        etaCollision delta n X Y)
      (W : ActiveRegularizedProjectedRound Y
        (naturalSharpJobScale d0 a gamma etaJob n))
      (hgood : SharpActiveRoundGood (members n Y) (m n)
        (naturalSharpJobScale d0 a gamma etaJob n)
        a gamma etaJob etaLoad etaCollision delta W)
      (hZ : Z = W.result) :
      NaturalSharpTrace members m d0 a gamma etaJob etaLoad
        etaCollision delta (n + 1) X Z

/-- A round's original selection is contained in its accumulated result. -/
theorem ActiveRegularizedProjectedRound.originalSelection_subset_result
    {X : OriginalIterationState H} {d : ℕ}
    (W : ActiveRegularizedProjectedRound X d) :
    W.originalSelection ⊆ W.result.matching := by
  intro o ho
  exact Finset.mem_union_right _ ho

/-- The matching component grows monotonically along the concrete trace. -/
theorem NaturalSharpTrace.matching_subset
    {members : ∀ n (X : OriginalIterationState H),
      Group → Finset (ActiveJob X.activeJobs)}
    {m : ℕ → ℕ} {d0 : ℕ}
    {a gamma etaJob etaLoad etaCollision delta : ℝ}
    {n : ℕ} {X Y : OriginalIterationState H}
    (T : NaturalSharpTrace members m d0 a gamma etaJob etaLoad
      etaCollision delta n X Y) :
    X.matching ⊆ Y.matching := by
  induction T with
  | zero X => exact Finset.Subset.rfl
  | succ hprev W hgood hZ ih =>
      rw [hZ]
      exact ih.trans Finset.subset_union_left

/-- All data that can vary with the current active-job type, but contains no
abstract round-existence assumption.  Its `numeric` field is precisely the
explicit scalar package consumed by the concrete one-step theorem. -/
structure NaturalSharpStepData
    (X : OriginalIterationState H) (d S lambda R K m k : ℕ)
    (rho a gamma etaJob etaLoad etaCollision z delta : ℝ)
    (hd : 0 < d) (hSd : S ≤ d)
    (members : Group → Finset (ActiveJob X.activeJobs)) where
  members_card : ∀ g, (members g).card ≤ K
  group_size : ∀ g, m ≤ (members g).card * d
  group_incidence : ∀ j,
    ((Finset.univ : Finset Group).filter
      (fun g ↦ j ∈ members g)).card ≤ R
  numeric : ∀
    (trim : Finset (X.system.ActiveJobOption X.activeJobs))
    (htrim : ∀ j,
      ((((X.activeSystem).inducedOnOptions trim).fiber j).card) = d)
    (htwo : ∀ o : KeptOption trim,
      ((((X.activeSystem).inducedOnOptions trim).slots o).card) = 2)
    (hslot : ∀ s,
      ((X.activeSystem).inducedOnOptions trim).slotDegree s ≤ S)
    (hjobSlot : ∀ j s,
      ((X.activeSystem).inducedOnOptions trim).jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t →
      ((X.activeSystem).inducedOnOptions trim).slotPairCodegree s t ≤ lambda),
    UniformSharpScalarData
      (((X.activeSystem).inducedOnOptions trim).cyclicRegularization hSd htwo)
      ((CyclicRegularization.regularExtension hd hSd htwo htrim hslot
        hjobSlot hslotPair).liftedOldMembers members)
      (max lambda 1) d d R K m k
      rho a gamma etaJob etaLoad etaCollision z delta

/-- Fixed-parameter finite iteration.  The output retains the concrete trace,
the next nonempty-fibre lower bound, and the next slot cap, all on the
original option type. -/
theorem exists_naturalSharpIteration
    (initial : OriginalIterationState H) (steps d0 S0 lambda R K k : ℕ)
    (m : ℕ → ℕ)
    (rho : ℕ → ℝ) (a gamma etaJob etaLoad etaCollision z delta : ℝ)
    (hlambda : 0 < lambda)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hjobRate0 : 0 ≤ WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob)
    (hslotRate0 : 0 ≤
      WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
        etaLoad + etaCollision)
    (herror : (1 - gamma) * etaJob + etaLoad + etaCollision ≤
      a * gamma * (1 - gamma))
    (hgap0 : (S0 : ℝ) ≤ (1 - gamma) * d0)
    (hmargin : ∀ n, 1 - gamma ≤
      (a * gamma * (1 - gamma) -
        ((1 - gamma) * etaJob + etaLoad + etaCollision)) *
          naturalSharpJobScale d0 a gamma etaJob n)
    (hpositive : ∀ n < steps,
      0 < naturalSharpJobScale d0 a gamma etaJob n)
    (hSdNat : ∀ n < steps,
      naturalSharpSlotCap S0 d0 a gamma etaJob etaLoad etaCollision n ≤
        naturalSharpJobScale d0 a gamma etaJob n)
    (htwo : ∀ o, (H.slots o).card = 2)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hdegree0 : ∀ j, (initial.system.fiber j).Nonempty →
      d0 ≤ (initial.system.fiber j).card)
    (hslot0 : ∀ s, initial.system.slotDegree s ≤ S0)
    (members : ∀ n (X : OriginalIterationState H),
      Group → Finset (ActiveJob X.activeJobs))
    (data : ∀ n (hn : n < steps) X,
      NaturalSharpStepData X
        (naturalSharpJobScale d0 a gamma etaJob n)
        (naturalSharpSlotCap S0 d0 a gamma etaJob etaLoad etaCollision n)
        lambda R K (m n) k (rho n) a gamma etaJob etaLoad etaCollision z delta
        (hpositive n hn) (hSdNat n hn) (members n X)) :
    ∃ final : OriginalIterationState H,
      NaturalSharpTrace members m d0 a gamma etaJob etaLoad etaCollision
        delta steps initial final ∧
      (∀ j, (final.system.fiber j).Nonempty →
        naturalSharpJobScale d0 a gamma etaJob steps ≤
          (final.system.fiber j).card) ∧
      (∀ s, final.system.slotDegree s ≤
        naturalSharpSlotCap S0 d0 a gamma etaJob etaLoad etaCollision steps) := by
  let d : ℕ → ℕ := naturalSharpJobScale d0 a gamma etaJob
  let cap : ℕ → ℕ :=
    naturalSharpSlotCap S0 d0 a gamma etaJob etaLoad etaCollision
  have hgap : ∀ n, (cap n : ℝ) ≤ (1 - gamma) * d n := by
    exact naturalSharpSlotCap_le_gap S0 d0 a gamma etaJob etaLoad
      etaCollision hgamma0 hgamma1 hjobRate0 hslotRate0 hgap0 hmargin
  have hiter : ∀ n, n ≤ steps →
      ∃ X : OriginalIterationState H,
        NaturalSharpTrace members m d0 a gamma etaJob etaLoad etaCollision
          delta n initial X ∧
        (∀ j, (X.system.fiber j).Nonempty → d n ≤ (X.system.fiber j).card) ∧
        (∀ s, X.system.slotDegree s ≤ cap n) := by
    intro n hn
    induction n with
    | zero =>
        exact ⟨initial, NaturalSharpTrace.zero initial, hdegree0, hslot0⟩
    | succ n ih =>
        have hnlt : n < steps := Nat.lt_of_succ_le hn
        rcases ih (Nat.le_of_succ_le hn) with ⟨X, htrace, hdegX, hslotX⟩
        let stepData := data n hnlt X
        have htwoX : ∀ o : KeptOption X.keep,
            (X.system.slots o).card = 2 := by
          intro o
          exact htwo o.1
        have hjobSlotX : ∀ j s, X.system.jobSlotCodegree j s ≤ lambda := by
          intro j s
          exact (H.inducedOnOptions_jobSlotCodegree_le X.keep j s).trans
            (hjobSlot j s)
        have hslotPairX : ∀ s t, s ≠ t →
            X.system.slotPairCodegree s t ≤ lambda := by
          intro s t hst
          exact (H.inducedOnOptions_slotPairCodegree_le X.keep s t).trans
            (hslotPair s t hst)
        have hcap0 : 0 ≤
            (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
              etaLoad + etaCollision) * d n :=
          mul_nonneg hslotRate0 (Nat.cast_nonneg _)
        rcases exists_activeSharpRound X (d n) (cap n) lambda R K (m n) k
            (rho n) a gamma etaJob etaLoad etaCollision z delta
            (hpositive n hnlt) hlambda (hSdNat n hnlt) hdegX htwoX hslotX
            hjobSlotX hslotPairX (hgap n) hgamma1 herror hcap0
            (members n X) stepData.members_card stepData.group_size
            stepData.group_incidence stepData.numeric with
          ⟨W, hgood⟩
        let Y := W.result
        have hdegY : ∀ j, (Y.system.fiber j).Nonempty →
            d (n + 1) ≤ (Y.system.fiber j).card := by
          intro j hj
          have hlower := hgood.originalKeep_nonempty_fiber_lower j (by
            simpa [Y, OriginalIterationState.system] using hj)
          have harg : 0 ≤
              (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d n :=
            mul_nonneg hjobRate0 (Nat.cast_nonneg _)
          have hfloor := Nat.floor_le harg
          have hreal : ((d (n + 1) : ℕ) : ℝ) ≤
              ((H.inducedOnOptions W.originalKeep).fiber j).card := by
            exact hfloor.trans hlower
          have hnatDegree : d (n + 1) ≤
              ((H.inducedOnOptions W.originalKeep).fiber j).card := by
            exact_mod_cast hreal
          simpa [Y, OriginalIterationState.system] using hnatDegree
        have hslotY : ∀ s, Y.system.slotDegree s ≤ cap (n + 1) := by
          intro s
          have hreal := hgood.originalKeep_slotDegree s
          have harg : 0 ≤
              (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
                etaLoad + etaCollision) * d n :=
            mul_nonneg hslotRate0 (Nat.cast_nonneg _)
          have hnat :
              (H.inducedOnOptions W.originalKeep).slotDegree s ≤
                ⌊(WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
                    etaLoad + etaCollision) * d n⌋₊ :=
            (Nat.le_floor_iff harg).mpr hreal
          simpa [Y, OriginalIterationState.system, cap, d,
            naturalSharpSlotCap] using hnat
        refine ⟨Y, NaturalSharpTrace.succ htrace W hgood rfl, hdegY, hslotY⟩
  rcases hiter steps le_rfl with ⟨final, htrace, hdeg, hslot⟩
  exact ⟨final, htrace, hdeg, hslot⟩

end OriginalIterationState

end WeightedEdgeColoring.RankThreeOptionSystem
