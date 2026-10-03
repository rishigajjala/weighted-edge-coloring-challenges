import WeightedEdgeColoring.SubtwoFiniteTinySingleLabel
import WeightedEdgeColoring.SubtwoDiffuseLabelLawFactory
import WeightedEdgeColoring.BPGeneralPacketCompletion

/-! A finite/tiny label law directly on a colored packet base of an arbitrary
quotient graph. The finite/tiny split is supplied as data, so this module
does not require the quotient graph to be a threshold packetization. -/

namespace WeightedEdgeColoring.WeightedMultigraph

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

universe u
variable {G : WeightedMultigraph.{u}} {K : ℕ}

namespace GeneralColoredPacketBase

variable (C : G.GeneralColoredPacketBase K)

def quotientSplitCharge (finite : Finset C.residualGraph.E)
    (tau : ℝ) (e : C.residualGraph.E) : ℝ :=
  if e ∈ finite then harmonicCharge (C.residualGraph.weight e)
  else C.residualGraph.weight e / (1 - tau)

theorem quotientSplitChargeLoad_eq_classes
    {T : ℕ} (finite : Finset C.residualGraph.E)
    (classOf : C.residualGraph.E → Fin T) (tau : ℝ)
    {v : G.V} (x : C.residualGraph.StarEdge v → ℝ)
    (hcharge : ∀ e ∈ finite,
      harmonicCharge (C.residualGraph.weight e) =
        (1 : ℝ) / finiteClassSize (classOf e)) :
    (∑ e : C.residualGraph.StarEdge v,
      C.quotientSplitCharge finite tau e.1 * x e) =
      (∑ e : {e : C.residualGraph.StarEdge v // e.1 ∈ finite},
        x e.1 / (finiteClassSize (classOf e.1.1) : ℝ)) +
      (∑ e : {e : C.residualGraph.StarEdge v // e.1 ∉ finite},
        C.residualGraph.weight e.1.1 * x e.1) / (1 - tau) := by
  classical
  let A := (Finset.univ : Finset (C.residualGraph.StarEdge v)).filter
    (fun e => e.1 ∈ finite)
  let B := (Finset.univ : Finset (C.residualGraph.StarEdge v)).filter
    (fun e => e.1 ∉ finite)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    exact (Finset.mem_filter.mp heB).2 (Finset.mem_filter.mp heA).2
  have hunion : A ∪ B = Finset.univ := by
    ext e
    by_cases he : e.1 ∈ finite <;> simp [A, B, he]
  calc
    (∑ e : C.residualGraph.StarEdge v,
        C.quotientSplitCharge finite tau e.1 * x e) =
      (∑ e ∈ A, C.quotientSplitCharge finite tau e.1 * x e) +
        ∑ e ∈ B, C.quotientSplitCharge finite tau e.1 * x e := by
      rw [← Finset.sum_union hdisj, hunion]
    _ = (∑ e : {e : C.residualGraph.StarEdge v // e.1 ∈ finite},
          C.quotientSplitCharge finite tau e.1.1 * x e.1) +
        ∑ e : {e : C.residualGraph.StarEdge v // e.1 ∉ finite},
          C.quotientSplitCharge finite tau e.1.1 * x e.1 := by
      exact congrArg₂ (fun a b : ℝ => a + b)
        (Finset.sum_subtype A (by simp [A])
          (fun e => C.quotientSplitCharge finite tau e.1 * x e))
        (Finset.sum_subtype B (by simp [B])
          (fun e => C.quotientSplitCharge finite tau e.1 * x e))
    _ = (∑ e : {e : C.residualGraph.StarEdge v // e.1 ∈ finite},
          x e.1 / (finiteClassSize (classOf e.1.1) : ℝ)) +
        ∑ e : {e : C.residualGraph.StarEdge v // e.1 ∉ finite},
          (C.residualGraph.weight e.1.1 / (1 - tau)) * x e.1 := by
      apply congrArg₂ (fun a b : ℝ => a + b)
      · apply Finset.sum_congr rfl
        intro e _
        rw [quotientSplitCharge, if_pos e.2, hcharge e.1.1 e.2]
        ring
      · apply Finset.sum_congr rfl
        intro e _
        rw [quotientSplitCharge, if_neg e.2]
    _ = _ := by
      apply congrArg (fun z : ℝ =>
        (∑ e : {e : C.residualGraph.StarEdge v // e.1 ∈ finite},
          x e.1 / (finiteClassSize (classOf e.1.1) : ℝ)) + z)
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e _
      ring

/-- A quotient packet base may use an inherited finite/tiny split.  The
single-label local law depends only on that split and its charge row, not on
any uncontracted pair-simplicity property. -/
theorem exists_quotientSplitSingleLabelLaw
    {T : ℕ} (hT : 0 < T)
    (finite : Finset C.residualGraph.E)
    (classOf : C.residualGraph.E → Fin T) (tau M : ℝ)
    {Label Color : Type*}
    [Fintype Label] [DecidableEq Label]
    [Fintype Color] [DecidableEq Color]
    (edgeLabel : ∀ v : G.V, C.residualGraph.StarEdge v → Label)
    (x : C.residualGraph.E → Color → ℝ)
    (hM : 0 < M) (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (hfiniteWeight : ∀ e ∈ finite,
      C.residualGraph.weight e ≤
        (1 : ℝ) / finiteClassSize (classOf e))
    (htinyWeight : ∀ e ∉ finite, C.residualGraph.weight e ≤ tau)
    (hcharge : ∀ e ∈ finite,
      harmonicCharge (C.residualGraph.weight e) =
        (1 : ℝ) / finiteClassSize (classOf e))
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hxM : ∀ e c, x e c ≤ M)
    (hbudget : ∀ v c,
      (∑ e : C.residualGraph.StarEdge v,
        C.quotientSplitCharge finite tau e.1 * x e.1 c) +
          (Fintype.card Label : ℝ) * (T + 1 : ℝ) * M ≤ 1) :
    ∃ qLaw : ∀ v : G.V, Color →
        Finset (C.residualGraph.StarEdge v) → ℝ,
      (∀ v c S, 0 ≤ qLaw v c S) ∧
      (∀ v c, ∑ S, qLaw v c S = 1) ∧
      (∀ v c S, qLaw v c S ≠ 0 →
        C.residualGraph.StarFeasible v S) ∧
      (∀ v c (f : C.residualGraph.StarEdge v),
        (∑ S, if f ∈ S then qLaw v c S else 0) = x f.1 c) ∧
      (∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
        ∃ l : Label, ∀ f ∈ S, edgeLabel v f = l) ∧
      (∀ v c l, subsetLabelMass (edgeLabel v) (qLaw v c) l ≤
        (∑ e : {e : C.residualGraph.StarEdge v // e.1 ∈ finite},
          if edgeLabel v e.1 = l then
            x e.1.1 c / (finiteClassSize (classOf e.1.1) : ℝ) else 0) +
        (∑ e : {e : C.residualGraph.StarEdge v // e.1 ∉ finite},
          if edgeLabel v e.1 = l then
            C.residualGraph.weight e.1.1 * x e.1.1 c else 0) / (1 - tau) +
          (T + 1 : ℝ) * M) := by
  classical
  letI : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
  have hlocal (v : G.V) (c : Color) :
      ∃ q : Finset (C.residualGraph.StarEdge v) → ℝ,
        (∀ S, 0 ≤ q S) ∧ (∑ S, q S = 1) ∧
        (∀ S, q S ≠ 0 → C.residualGraph.StarFeasible v S) ∧
        (∀ f, (∑ S, if f ∈ S then q S else 0) = x f.1 c) ∧
        (∀ S, q S ≠ 0 → S ≠ ∅ →
          ∃ l : Label, ∀ f ∈ S, edgeLabel v f = l) ∧
        (∀ l, subsetLabelMass (edgeLabel v) q l ≤
          (∑ e : {e : C.residualGraph.StarEdge v // e.1 ∈ finite},
            if edgeLabel v e.1 = l then
              x e.1.1 c / (finiteClassSize (classOf e.1.1) : ℝ) else 0) +
          (∑ e : {e : C.residualGraph.StarEdge v // e.1 ∉ finite},
            if edgeLabel v e.1 = l then
              C.residualGraph.weight e.1.1 * x e.1.1 c else 0) / (1 - tau) +
            (T + 1 : ℝ) * M) := by
    obtain ⟨q, hq0, hqsum, hqfeas, hqmarg, hqsingle, hqlabel⟩ :=
      C.residualGraph.finiteTiny_singleLabelDistribution_of_charge
      (edgeLabel v) (fun e => e.1 ∈ finite)
      (fun a : Fin T => finiteClassSize a)
      (fun a : Fin T => by simp [finiteClassSize])
      (fun e => classOf e.1.1)
      (fun e => x e.1 c) M tau hM htau0 htau1
      (by intro e; exact hfiniteWeight e.1.1 e.2)
      (by intro e; exact htinyWeight e.1.1 e.2)
      (by intro e; exact hx0 e.1 c)
      (by intro e; exact hxM e.1 c)
      (by
        have heq := C.quotientSplitChargeLoad_eq_classes
          finite classOf tau (fun f : C.residualGraph.StarEdge v => x f.1 c)
          hcharge
        have hb := hbudget v c
        rw [heq] at hb
        simpa only [Fintype.card_fin] using hb)
    exact ⟨q, hq0, hqsum, hqfeas, hqmarg, hqsingle,
      by intro l; simpa only [Fintype.card_fin] using hqlabel l⟩
  let qLaw : ∀ v : G.V, Color →
      Finset (C.residualGraph.StarEdge v) → ℝ :=
    fun v c => Classical.choose (hlocal v c)
  refine ⟨qLaw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v c S; exact (Classical.choose_spec (hlocal v c)).1 S
  · intro v c; exact (Classical.choose_spec (hlocal v c)).2.1
  · intro v c S hS; exact (Classical.choose_spec (hlocal v c)).2.2.1 S hS
  · intro v c f; exact (Classical.choose_spec (hlocal v c)).2.2.2.1 f
  · intro v c S hS hSne
    exact (Classical.choose_spec (hlocal v c)).2.2.2.2.1 S hS hSne
  · intro v c l
    exact (Classical.choose_spec (hlocal v c)).2.2.2.2.2 l

/-- The generic quotient label law has all conditional endpoint realizations
needed by the mixed decoder. No small-pair simplicity is used here. -/
theorem exists_quotientSplitSingleLabelLawAndRealizations
    {T : ℕ} (hT : 0 < T)
    (finite : Finset C.residualGraph.E)
    (classOf : C.residualGraph.E → Fin T) (tau M : ℝ)
    {Label Color : Type*}
    [Fintype Label] [DecidableEq Label]
    [Fintype Color] [DecidableEq Color]
    (edgeLabel : ∀ v : G.V, C.residualGraph.StarEdge v → Label)
    (x : C.residualGraph.E → Color → ℝ)
    (hM : 0 < M) (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (hfiniteWeight : ∀ e ∈ finite,
      C.residualGraph.weight e ≤
        (1 : ℝ) / finiteClassSize (classOf e))
    (htinyWeight : ∀ e ∉ finite, C.residualGraph.weight e ≤ tau)
    (hcharge : ∀ e ∈ finite,
      harmonicCharge (C.residualGraph.weight e) =
        (1 : ℝ) / finiteClassSize (classOf e))
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hxM : ∀ e c, x e c ≤ M)
    (hbudget : ∀ v c,
      (∑ e : C.residualGraph.StarEdge v,
        C.quotientSplitCharge finite tau e.1 * x e.1 c) +
          (Fintype.card Label : ℝ) * (T + 1 : ℝ) * M ≤ 1)
    {s β qstep r : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hqstep : 0 < qstep) (hr : 0 < r) :
    ∃ (qLaw : ∀ v : G.V, Color →
        Finset (C.residualGraph.StarEdge v) → ℝ)
      (R : ∀ v c label,
        C.residualGraph.BoundedProfileRealization
          (C.residualGraph.conditionalEndpointProposal
            (edgeLabel v)
            (fun f : C.residualGraph.StarEdge v => x f.1 c)
            (qLaw v c) label) s β qstep r hβ hr),
      (∀ v c S, 0 ≤ qLaw v c S) ∧
      (∀ v c, ∑ S, qLaw v c S = 1) ∧
      (∀ v c S, qLaw v c S ≠ 0 →
        C.residualGraph.StarFeasible v S) ∧
      (∀ v c (f : C.residualGraph.StarEdge v),
        (∑ S, if f ∈ S then qLaw v c S else 0) = x f.1 c) ∧
      (∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
        ∃ l : Label, ∀ f ∈ S, edgeLabel v f = l) ∧
      (∀ v c l, subsetLabelMass (edgeLabel v) (qLaw v c) l ≤
        (∑ e : {e : C.residualGraph.StarEdge v // e.1 ∈ finite},
          if edgeLabel v e.1 = l then
            x e.1.1 c / (finiteClassSize (classOf e.1.1) : ℝ) else 0) +
        (∑ e : {e : C.residualGraph.StarEdge v // e.1 ∉ finite},
          if edgeLabel v e.1 = l then
            C.residualGraph.weight e.1.1 * x e.1.1 c else 0) / (1 - tau) +
          (T + 1 : ℝ) * M) ∧
      (∀ v c label (f : C.residualGraph.StarEdge v) j,
        0 < (R v c label).largeAssign f j → edgeLabel v f = label) ∧
      (∀ v c label (f : C.residualGraph.StarEdge v) P,
        0 < (R v c label).tinyAssign f P → edgeLabel v f = label) ∧
      (∀ v c (f : C.residualGraph.StarEdge v),
        (∑ label : Label,
          subsetLabelMass (edgeLabel v) (qLaw v c) label *
            (∑ j : C.residualGraph.ExplicitLargeSlot
              (R v c label).law hβ hr,
              (R v c label).largeAssign f j)) +
        (∑ label : Label,
          subsetLabelMass (edgeLabel v) (qLaw v c) label *
            (∑ P : C.residualGraph.RoundedProfileIndex
              (R v c label).law hβ hr,
              (R v c label).tinyAssign f P)) = s * x f.1 c) := by
  obtain ⟨qLaw, hq0, hqsum, hqfeas, hqmarg, hqsingle, hqlabel⟩ :=
    C.exists_quotientSplitSingleLabelLaw hT finite classOf tau M edgeLabel x
      hM htau0 htau1 hfiniteWeight htinyWeight hcharge hx0 hxM hbudget
  obtain ⟨R, hlarge, htiny, hsum⟩ :=
    C.residualGraph.exists_allDiffuseLabelEndpointRealizations
      x edgeLabel qLaw hq0 hqfeas hqmarg hqsingle
      hs hs1 hβ hqstep hr
  exact ⟨qLaw, R, hq0, hqsum, hqfeas, hqmarg, hqsingle, hqlabel,
    hlarge, htiny, hsum⟩

end GeneralColoredPacketBase
end
end WeightedEdgeColoring.WeightedMultigraph
