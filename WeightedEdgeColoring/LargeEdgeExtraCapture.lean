import WeightedEdgeColoring.GraphExtraSlotBudget
import WeightedEdgeColoring.LargeEdgeMatchingExtraction

/-!
# Capacity of selected leave-uncolored options

A leave-uncolored option uses one private extra slot at each endpoint.  Thus
a partial matching can select at most `B v h` such options incident with a
fixed vertex `v` in a fixed class `h`.  This file records that elementary
capacity fact and its weighted consequence.  The statement is deliberately
independent of the probabilistic construction that produced the matching.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace RankThreeOptionSystem

universe u v v₁ v₂ w₁ w₂

variable {Job : Type u} {Slot : Type v} {Slot₁ : Type v₁} {Slot₂ : Type v₂}
  {Option₁ : Type w₁} {Option₂ : Type w₂}
  [Fintype Job] [Fintype Slot] [Fintype Slot₁] [Fintype Slot₂]
  [Fintype Option₁] [Fintype Option₂]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Slot₁] [DecidableEq Slot₂]
  [DecidableEq Option₁] [DecidableEq Option₂]

/-- Keep just the right options in a finite set of sum options. -/
def rightOptionSet (M : Finset (Option₁ ⊕ Option₂)) : Finset Option₂ :=
  M.biUnion fun z ↦ match z with
    | Sum.inl _ => ∅
    | Sum.inr p => {p}

@[simp] theorem mem_rightOptionSet_iff
    (M : Finset (Option₁ ⊕ Option₂)) (p : Option₂) :
    p ∈ rightOptionSet M ↔ Sum.inr p ∈ M := by
  constructor
  · intro hp
    rcases Finset.mem_biUnion.mp hp with ⟨z, hzM, hzp⟩
    cases z with
    | inl o => simp at hzp
    | inr q =>
        simp only [Finset.mem_singleton] at hzp
        subst q
        exact hzM
  · intro hp
    apply Finset.mem_biUnion.mpr
    exact ⟨Sum.inr p, hp, by simp⟩

/-- Restricting a matching in a separated sum to the right summand
preserves a partial matching. -/
theorem separatedSum_rightOptionSet_isPartialMatching
    (H : RankThreeOptionSystem Job Slot₁ Option₁)
    (K : RankThreeOptionSystem Job Slot₂ Option₂)
    (M : Finset (Option₁ ⊕ Option₂))
    (hM : (H.separatedSum K).IsPartialMatching M) :
    K.IsPartialMatching (rightOptionSet M) := by
  constructor
  · intro p hp q hq hpq
    have hdis := hM.1
      ((mem_rightOptionSet_iff M p).mp hp)
      ((mem_rightOptionSet_iff M q).mp hq)
      (fun h ↦ hpq (Sum.inr.inj h))
    rw [Compatible, Finset.disjoint_left]
    intro s hsp hsq
    exact Finset.disjoint_left.mp hdis
      ((K.mem_liftSlotsRight_inr p s).mpr hsp)
      ((K.mem_liftSlotsRight_inr q s).mpr hsq)
  · intro p hp q hq howner
    exact Sum.inr.inj (hM.2
      ((mem_rightOptionSet_iff M p).mp hp)
      ((mem_rightOptionSet_iff M q).mp hq) howner)

end RankThreeOptionSystem

namespace WeightedSimpleGraph

universe u w₁ w₂

variable (G : WeightedSimpleGraph.{u})
variable {Color : Type w₁} {Class : Type w₂}
  [Fintype Color] [DecidableEq Color]
  [Fintype Class] [DecidableEq Class]

/-- Extra base options represented by the selected quantized copies. -/
def selectedExtraBaseOptions
    (K N : ℕ) (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K bucket B x residual))) :
    Finset (ExtraSlotChoice G.E G.V Class G.fst G.snd bucket B) :=
  RankThreeOptionSystem.rightOptionSet
    (RankThreeOptionSystem.baseOptionSet N
      (G.largeEdgeMass K bucket B x residual) M)

@[simp] theorem mem_selectedExtraBaseOptions_iff
    (K N : ℕ) (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K bucket B x residual)))
    (p : ExtraSlotChoice G.E G.V Class G.fst G.snd bucket B) :
    p ∈ G.selectedExtraBaseOptions K N bucket B x residual M ↔
      Sum.inr p ∈ RankThreeOptionSystem.baseOptionSet N
        (G.largeEdgeMass K bucket B x residual) M := by
  exact RankThreeOptionSystem.mem_rightOptionSet_iff _ _

/-- The selected leave-uncolored base options form a partial matching in the
extra-slot system. -/
theorem selectedExtraBaseOptions_isPartialMatching
    (K N : ℕ) (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K bucket B x residual)))
    (hM : ((G.largeEdgeOptionSystem K bucket B).quantized N
      (G.largeEdgeMass K bucket B x residual)).IsPartialMatching M) :
    (ExtraSlotChoice.system G.fst G.snd bucket B).IsPartialMatching
      (G.selectedExtraBaseOptions K N bucket B x residual M) := by
  let Hord : RankThreeOptionSystem G.E (OrdinarySlot G.V Color K)
      (OrdinarySlotChoice G.E Color K) :=
    OrdinarySlotChoice.system G.fst G.snd K
  let Hextra : RankThreeOptionSystem G.E (ExtraSlot G.V Class B)
      (ExtraSlotChoice G.E G.V Class G.fst G.snd bucket B) :=
    ExtraSlotChoice.system G.fst G.snd bucket B
  let mass := G.largeEdgeMass K bucket B x residual
  let base := RankThreeOptionSystem.baseOptionSet N mass M
  have hbase : (Hord.separatedSum Hextra).IsPartialMatching base :=
    (Hord.separatedSum Hextra).baseOptionSet_isPartialMatching N mass M hM
  exact Hord.separatedSum_rightOptionSet_isPartialMatching Hextra base hbase

/-- The selected leave-uncolored jobs, with duplicate option labels forgotten. -/
def selectedExtraEdges
    (K N : ℕ) (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K bucket B x residual))) :
    Finset G.E :=
  (G.selectedExtraBaseOptions K N bucket B x residual M).image Sigma.fst

/-- The endpoint slot used by an extra option at `v`.  The right slot is
returned off the left endpoint; later lemmas use this only when `v` is
incident with the option's job. -/
def extraSlotAt
    (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (v : G.V)
    (p : ExtraSlotChoice G.E G.V Class G.fst G.snd bucket B) :
    ExtraSlot G.V Class B :=
  if G.fst p.1 = v then
    ExtraSlotChoice.leftSlot G.fst G.snd bucket B p
  else
    ExtraSlotChoice.rightSlot G.fst G.snd bucket B p

theorem extraSlotAt_mem_slots
    (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (v : G.V)
    (p : ExtraSlotChoice G.E G.V Class G.fst G.snd bucket B)
    (hinc : G.Inc v p.1) :
    G.extraSlotAt bucket B v p ∈
      (ExtraSlotChoice.system G.fst G.snd bucket B).slots p := by
  rcases hinc with hleft | hright
  · simp [extraSlotAt, hleft.symm, ExtraSlotChoice.system]
  · have hne : G.fst p.1 ≠ v := by
      intro h
      exact G.noLoop p.1 (h.trans hright.symm)
    simp [extraSlotAt, hne, ExtraSlotChoice.system]

theorem extraSlotAt_fst
    (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (v : G.V)
    (p : ExtraSlotChoice G.E G.V Class G.fst G.snd bucket B)
    (hinc : G.Inc v p.1) :
    (G.extraSlotAt bucket B v p).1 = (v, bucket p.1) := by
  rcases hinc with hleft | hright
  · simp [extraSlotAt, hleft.symm, ExtraSlotChoice.leftSlot]
  · have hne : G.fst p.1 ≠ v := by
      intro h
      exact G.noLoop p.1 (h.trans hright.symm)
    simp [extraSlotAt, hne, hright, ExtraSlotChoice.rightSlot]

/-- All concrete extra slots at one vertex and class. -/
def extraSlotsAt (B : G.V → Class → ℕ) (v : G.V) (h : Class) :
    Finset (ExtraSlot G.V Class B) :=
  Finset.univ.filter fun s ↦ s.1 = (v, h)

@[simp] theorem card_extraSlotsAt
    (B : G.V → Class → ℕ) (v : G.V) (h : Class) :
    (G.extraSlotsAt B v h).card = B v h := by
  classical
  unfold extraSlotsAt
  rw [Finset.card_filter, Fintype.sum_sigma]
  rw [Fintype.sum_eq_single (v, h)]
  · simp
  · intro x hx
    simp [hx]

/-- A partial matching uses at most `B v h` leave-uncolored options incident
with `v` and belonging to class `h`. -/
theorem extraMatching_card_inc_bucket_le
    (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (X : Finset (ExtraSlotChoice G.E G.V Class G.fst G.snd bucket B))
    (hX : (ExtraSlotChoice.system G.fst G.snd bucket B).IsPartialMatching X)
    (v : G.V) (h : Class) :
    (X.filter fun p ↦ G.Inc v p.1 ∧ bucket p.1 = h).card ≤ B v h := by
  classical
  let f := G.extraSlotAt bucket B v
  have hcard :
      (X.filter fun p ↦ G.Inc v p.1 ∧ bucket p.1 = h).card ≤
        (G.extraSlotsAt B v h).card := by
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [G.extraSlotAt_fst bucket B v p hp'.2.1, hp'.2.2]
    · intro p hp q hq hpq
      by_contra hne
      have hp' := Finset.mem_filter.mp hp
      have hq' := Finset.mem_filter.mp hq
      have hdis := hX.1 hp'.1 hq'.1 hne
      change G.extraSlotAt bucket B v p =
        G.extraSlotAt bucket B v q at hpq
      have hqmem := G.extraSlotAt_mem_slots bucket B v q hq'.2.1
      rw [← hpq] at hqmem
      exact Finset.disjoint_left.mp hdis
        (G.extraSlotAt_mem_slots bucket B v p hp'.2.1)
        hqmem
  simpa using hcard

/-- Weighted form of the extra-slot capacity bound for one class. -/
theorem extraMatching_weight_inc_bucket_le
    (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (X : Finset (ExtraSlotChoice G.E G.V Class G.fst G.snd bucket B))
    (hX : (ExtraSlotChoice.system G.fst G.snd bucket B).IsPartialMatching X)
    (upper : Class → ℝ) (hupper0 : ∀ h, 0 ≤ upper h)
    (hweight : ∀ e, G.weight e ≤ upper (bucket e))
    (v : G.V) (h : Class) :
    (∑ p ∈ X.filter (fun p ↦ G.Inc v p.1 ∧ bucket p.1 = h),
      G.weight p.1) ≤ (B v h : ℕ) * upper h := by
  calc
    _ ≤ ∑ _p ∈ X.filter (fun p ↦ G.Inc v p.1 ∧ bucket p.1 = h),
        upper h := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := (Finset.mem_filter.mp hp).2.2
      simpa [hh] using hweight p.1
    _ = ((X.filter fun p ↦ G.Inc v p.1 ∧ bucket p.1 = h).card : ℝ) *
        upper h := by simp
    _ ≤ (B v h : ℕ) * upper h := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast G.extraMatching_card_inc_bucket_le bucket B X hX v h
      · exact hupper0 h

/-- Summing the classwise capacities bounds all selected leave-uncolored
weight at one vertex. -/
theorem extraMatching_starWeight_le
    (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (X : Finset (ExtraSlotChoice G.E G.V Class G.fst G.snd bucket B))
    (hX : (ExtraSlotChoice.system G.fst G.snd bucket B).IsPartialMatching X)
    (upper : Class → ℝ) (hupper0 : ∀ h, 0 ≤ upper h)
    (hweight : ∀ e, G.weight e ≤ upper (bucket e))
    (v : G.V) :
    (∑ p ∈ X.filter (fun p ↦ G.Inc v p.1), G.weight p.1) ≤
      ∑ h, (B v h : ℕ) * upper h := by
  classical
  have hsplit :
      (∑ p ∈ X.filter (fun p ↦ G.Inc v p.1), G.weight p.1) =
        ∑ h, ∑ p ∈ X.filter
          (fun p ↦ G.Inc v p.1 ∧ bucket p.1 = h), G.weight p.1 := by
    calc
      _ = ∑ p ∈ X, if G.Inc v p.1 then G.weight p.1 else 0 := by
        rw [Finset.sum_filter]
      _ = ∑ p ∈ X, ∑ h,
          if G.Inc v p.1 ∧ bucket p.1 = h then G.weight p.1 else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hinc : G.Inc v p.1
        · simp [hinc]
        · simp [hinc]
      _ = ∑ h, ∑ p ∈ X,
          if G.Inc v p.1 ∧ bucket p.1 = h then G.weight p.1 else 0 := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [← Finset.sum_filter]
  rw [hsplit]
  exact Finset.sum_le_sum fun h _ ↦
    G.extraMatching_weight_inc_bucket_le bucket B X hX upper hupper0
      hweight v h

/-- Capacity bound for the actual extra options extracted from a combined
quantized matching. -/
theorem selectedExtra_starWeight_le
    (K N : ℕ) (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K bucket B x residual)))
    (hM : ((G.largeEdgeOptionSystem K bucket B).quantized N
      (G.largeEdgeMass K bucket B x residual)).IsPartialMatching M)
    (upper : Class → ℝ) (hupper0 : ∀ h, 0 ≤ upper h)
    (hweight : ∀ e, G.weight e ≤ upper (bucket e))
    (v : G.V) :
    (∑ p ∈ (G.selectedExtraBaseOptions K N bucket B x residual M).filter
        (fun p ↦ G.Inc v p.1), G.weight p.1) ≤
      ∑ h, (B v h : ℕ) * upper h := by
  exact G.extraMatching_starWeight_le bucket B
    (G.selectedExtraBaseOptions K N bucket B x residual M)
    (G.selectedExtraBaseOptions_isPartialMatching K N bucket B x residual M hM)
    upper hupper0 hweight v

/-- The option-level sum above is exactly the weight of the corresponding
set of selected leave-uncolored jobs. Owner injectivity removes duplicate
option labels. -/
theorem selectedExtraEdges_starWeight_eq
    (K N : ℕ) (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K bucket B x residual)))
    (hM : ((G.largeEdgeOptionSystem K bucket B).quantized N
      (G.largeEdgeMass K bucket B x residual)).IsPartialMatching M)
    (v : G.V) :
    (∑ e ∈ (G.selectedExtraEdges K N bucket B x residual M).filter
        (G.Inc v), G.weight e) =
      ∑ p ∈ (G.selectedExtraBaseOptions K N bucket B x residual M).filter
        (fun p ↦ G.Inc v p.1), G.weight p.1 := by
  classical
  let X := G.selectedExtraBaseOptions K N bucket B x residual M
  have hX := G.selectedExtraBaseOptions_isPartialMatching
    K N bucket B x residual M hM
  have hset :
      (G.selectedExtraEdges K N bucket B x residual M).filter (G.Inc v) =
        (X.filter fun p ↦ G.Inc v p.1).image
          (fun p : ExtraSlotChoice G.E G.V Class G.fst G.snd bucket B ↦ p.1) := by
    ext e
    simp [selectedExtraEdges, X]
  have hinj : Set.InjOn
      (fun p : ExtraSlotChoice G.E G.V Class G.fst G.snd bucket B ↦ p.1)
      ((X.filter fun p ↦ G.Inc v p.1 : Finset _) : Set _) := by
    intro p hp q hq hpq
    exact hX.2 (Finset.mem_filter.mp hp).1
      (Finset.mem_filter.mp hq).1 hpq
  rw [hset, Finset.sum_image hinj]

/-- Weighted star bound stated directly for the selected leave-uncolored
edge set. -/
theorem selectedExtraEdges_starWeight_le
    (K N : ℕ) (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K bucket B x residual)))
    (hM : ((G.largeEdgeOptionSystem K bucket B).quantized N
      (G.largeEdgeMass K bucket B x residual)).IsPartialMatching M)
    (upper : Class → ℝ) (hupper0 : ∀ h, 0 ≤ upper h)
    (hweight : ∀ e, G.weight e ≤ upper (bucket e))
    (v : G.V) :
    (∑ e ∈ (G.selectedExtraEdges K N bucket B x residual M).filter
        (G.Inc v), G.weight e) ≤
      ∑ h, (B v h : ℕ) * upper h := by
  rw [G.selectedExtraEdges_starWeight_eq K N bucket B x residual M hM v]
  exact G.selectedExtra_starWeight_le K N bucket B x residual M hM
    upper hupper0 hweight v

/-- With the graph residual budget, the selected leave-uncolored star weight
is bounded by the fractional residual quotient plus the explicit ceiling and
reserve terms. -/
theorem selectedExtraEdges_starWeight_le_graphBudget
    (K N : ℕ) (bucket : G.E → Class)
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (gamma : ℝ) (t : ℕ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K bucket
      (G.graphExtraSlotCount bucket residual gamma t) x residual)))
    (hM : ((G.largeEdgeOptionSystem K bucket
      (G.graphExtraSlotCount bucket residual gamma t)).quantized N
      (G.largeEdgeMass K bucket
        (G.graphExtraSlotCount bucket residual gamma t) x residual)).IsPartialMatching M)
    (hr0 : ∀ e, 0 ≤ residual e) (hgamma1 : gamma < 1)
    (upper : Class → ℝ) (hupper0 : ∀ h, 0 ≤ upper h)
    (hweight : ∀ e, G.weight e ≤ upper (bucket e))
    (v : G.V) :
    (∑ e ∈ (G.selectedExtraEdges K N bucket
        (G.graphExtraSlotCount bucket residual gamma t) x residual M).filter
        (G.Inc v), G.weight e) ≤
      ∑ h, upper h *
        (G.classResidual bucket residual v h / (1 - gamma) + 1 + t) := by
  have hcapacity := G.selectedExtraEdges_starWeight_le K N bucket
    (G.graphExtraSlotCount bucket residual gamma t) x residual M hM
    upper hupper0 hweight v
  refine hcapacity.trans (Finset.sum_le_sum fun h _ ↦ ?_)
  have hcount := extraSlotCount_cast_le
    (G.classResidual bucket residual v h) gamma t
    (G.classResidual_nonneg bucket residual hr0 v h) hgamma1
  have hu := hupper0 h
  calc
    ((G.graphExtraSlotCount bucket residual gamma t v h : ℕ) : ℝ) * upper h =
        upper h * (G.graphExtraSlotCount bucket residual gamma t v h : ℕ) := by
          ring
    _ ≤ upper h *
        (G.classResidual bucket residual v h / (1 - gamma) + 1 + t) :=
      mul_le_mul_of_nonneg_left hcount hu

/-- Fractional residual weight in one vertex star. -/
def weightedResidualStar (residual : G.E → ℝ) (v : G.V) : ℝ :=
  ∑ e, if G.Inc v e then residual e * G.weight e else 0

/-- Class residuals weighted by class upper bounds are exactly the
corresponding endpoint sum. -/
theorem sum_upper_mul_classResidual_eq
    (bucket : G.E → Class) (residual : G.E → ℝ) (upper : Class → ℝ)
    (v : G.V) :
    (∑ h, upper h * G.classResidual bucket residual v h) =
      ∑ e, if G.Inc v e then residual e * upper (bucket e) else 0 := by
  classical
  unfold classResidual
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hl : G.fst e = v
  · have hs : G.snd e ≠ v := by
      intro hs
      exact G.noLoop e (hl.trans hs.symm)
    simp [Inc, hl, hs, mul_comm]
  · by_cases hs : G.snd e = v
    · simp [Inc, hl, hs, mul_comm]
    · simp [Inc, hl, hs]

/-- If a class upper bound is at most `ratio` times every weight in that
class, then the upper-bound-weighted residual is at most `ratio` times the
true fractional residual weight. -/
theorem sum_upper_mul_classResidual_le_weightedResidualStar
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (hr0 : ∀ e, 0 ≤ residual e)
    (upper : Class → ℝ) (ratio : ℝ)
    (hratio : ∀ e, upper (bucket e) ≤ ratio * G.weight e)
    (v : G.V) :
    (∑ h, upper h * G.classResidual bucket residual v h) ≤
      ratio * G.weightedResidualStar residual v := by
  rw [G.sum_upper_mul_classResidual_eq bucket residual upper v]
  unfold weightedResidualStar
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  by_cases hinc : G.Inc v e
  · simp only [if_pos hinc]
    calc
      residual e * upper (bucket e) ≤
          residual e * (ratio * G.weight e) :=
        mul_le_mul_of_nonneg_left (hratio e) (hr0 e)
      _ = ratio * (residual e * G.weight e) := by ring
  · simp [hinc]

/-- The useful dyadic form of extra capture.  Besides the fractional
residual term, the only loss is the explicit `1+t` slots per class. -/
theorem selectedExtraEdges_starWeight_le_weightedResidual
    (K N : ℕ) (bucket : G.E → Class)
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (gamma ratio : ℝ) (t : ℕ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K bucket
      (G.graphExtraSlotCount bucket residual gamma t) x residual)))
    (hM : ((G.largeEdgeOptionSystem K bucket
      (G.graphExtraSlotCount bucket residual gamma t)).quantized N
      (G.largeEdgeMass K bucket
        (G.graphExtraSlotCount bucket residual gamma t) x residual)).IsPartialMatching M)
    (hr0 : ∀ e, 0 ≤ residual e) (hgamma1 : gamma < 1)
    (upper : Class → ℝ) (hupper0 : ∀ h, 0 ≤ upper h)
    (hweight : ∀ e, G.weight e ≤ upper (bucket e))
    (hratio : ∀ e, upper (bucket e) ≤ ratio * G.weight e)
    (v : G.V) :
    (∑ e ∈ (G.selectedExtraEdges K N bucket
        (G.graphExtraSlotCount bucket residual gamma t) x residual M).filter
        (G.Inc v), G.weight e) ≤
      ratio * G.weightedResidualStar residual v / (1 - gamma) +
        (1 + (t : ℝ)) * ∑ h, upper h := by
  have hbudget := G.selectedExtraEdges_starWeight_le_graphBudget
    K N bucket x residual gamma t M hM hr0 hgamma1
    upper hupper0 hweight v
  have hgap : 0 < 1 - gamma := sub_pos.mpr hgamma1
  have hres := G.sum_upper_mul_classResidual_le_weightedResidualStar
    bucket residual hr0 upper ratio hratio v
  have hdecomp :
      (∑ h, upper h *
        (G.classResidual bucket residual v h / (1 - gamma) + 1 + t)) =
      (∑ h, upper h * G.classResidual bucket residual v h) /
          (1 - gamma) +
        (1 + (t : ℝ)) * ∑ h, upper h := by
    have hterm : ∀ h : Class,
        upper h *
            (G.classResidual bucket residual v h / (1 - gamma) + 1 + t) =
          (upper h * G.classResidual bucket residual v h) / (1 - gamma) +
            (1 + (t : ℝ)) * upper h := by
      intro h
      ring
    simp_rw [hterm, Finset.sum_add_distrib]
    rw [Finset.sum_div, Finset.mul_sum]
  rw [hdecomp] at hbudget
  exact hbudget.trans (add_le_add
    (div_le_div_of_nonneg_right hres hgap.le) le_rfl)

end WeightedSimpleGraph

end

end WeightedEdgeColoring
