import WeightedEdgeColoring.MultigraphExtendedProfileSelectedQuantizedBridge
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeOptionBounds
import WeightedEdgeColoring.BoundedMultiplicityDyadicExtraSlotBudget
import WeightedEdgeColoring.BoundedMultiplicityLargeEdgeRestriction
import WeightedEdgeColoring.MultigraphPackingBounds
import WeightedEdgeColoring.RankThreeActiveJobs

/-!
# Initial bounds for the local-dyadic endpoint iteration

This file packages the selected-profile estimates after restricting the job
type to the `beta`-large graph edges.  It is the direct deterministic input
to `exists_endpointVariableSlackIsolatedIteration`.
-/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]
variable {B k N reserve C S0 lambda : ℕ}
variable {s β q r gamma : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- Only large jobs enter the endpoint iteration.  Masking the residual
before defining local extra-slot counts prevents arbitrarily many tiny edges
from inflating those counts. -/
def selectedBlockLargeResidual
    (omega rho : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) : ℝ :=
  if β ≤ G.weight e then
    G.selectedBlockResidualOptionMass R0 rho omega choice e else 0

theorem selectedBlockLargeResidual_eq_of_large
    (omega rho : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    {e : G.E} (he : β ≤ G.weight e) :
    G.selectedBlockLargeResidual R0 omega rho choice e =
      G.selectedBlockResidualOptionMass R0 rho omega choice e := by
  simp [selectedBlockLargeResidual, he]

theorem selectedBlockLargeResidual_nonneg
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r) :
    ∀ e, 0 ≤ G.selectedBlockLargeResidual R0 omega rho choice e := by
  intro e
  by_cases he : β ≤ G.weight e
  · simp [selectedBlockLargeResidual, he,
      G.selectedBlockResidualOptionMass_nonneg R0 rho omega choice e]
  · simp [selectedBlockLargeResidual, he]

theorem selectedBlockLargeResidual_le_one
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r) :
    ∀ e, G.selectedBlockLargeResidual R0 omega rho choice e ≤ 1 := by
  intro e
  by_cases he : β ≤ G.weight e
  · rw [G.selectedBlockLargeResidual_eq_of_large R0 omega rho choice he]
    unfold selectedBlockResidualOptionMass
    exact sub_le_self _ (le_min zero_le_one
      (G.selectedBlockAllOptionMass_nonneg R0 hn hs hq hr0 hleft
        homega0 homega1 hrho choice e))
  · simp [selectedBlockLargeResidual, he]

theorem boundedClassResidual_selectedBlockLargeResidual_mul_beta_le_starWeight
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (v : G.V) (h : Class) :
    G.boundedClassResidual bucket (G.selectedBlockLargeResidual R0 omega rho choice)
        v h * β ≤ G.starWeight v := by
  have hres1 := G.selectedBlockLargeResidual_le_one R0 hn hs hq hr0
    hleft omega homega0 homega1 rho hrho choice
  unfold boundedClassResidual
  rw [Finset.sum_mul]
  calc
    (∑ e,
      ((if (G.fst e, bucket e) = (v, h) then
          G.selectedBlockLargeResidual R0 omega rho choice e else 0) +
        (if (G.snd e, bucket e) = (v, h) then
          G.selectedBlockLargeResidual R0 omega rho choice e else 0)) * β) ≤
      ∑ e, if G.Inc v e then G.weight e else 0 := by
        apply Finset.sum_le_sum
        intro e _
        have hedge :
            G.selectedBlockLargeResidual R0 omega rho choice e * β ≤
              G.weight e := by
          by_cases he : β ≤ G.weight e
          · have hmul :
                G.selectedBlockLargeResidual R0 omega rho choice e * β ≤ β := by
              simpa using mul_le_mul_of_nonneg_right (hres1 e) hβ.le
            exact hmul.trans he
          · simp [selectedBlockLargeResidual, he, G.weight_nonneg]
        by_cases hf : (G.fst e, bucket e) = (v, h)
        · have hfv : G.fst e = v := congrArg Prod.fst hf
          have hsnd : (G.snd e, bucket e) ≠ (v, h) := by
            intro heq
            exact G.noLoop e (hfv.trans (congrArg Prod.fst heq).symm)
          have hinc : G.Inc v e := Or.inl hfv
          rw [if_pos hf, if_neg hsnd, add_zero, if_pos hinc]
          exact hedge
        · by_cases hsnd : (G.snd e, bucket e) = (v, h)
          · have hsv : G.snd e = v := congrArg Prod.fst hsnd
            have hinc : G.Inc v e := Or.inr hsv
            rw [if_neg hf, if_pos hsnd, zero_add, if_pos hinc]
            exact hedge
          · by_cases hinc : G.Inc v e
            · simp [hf, hsnd, hinc, G.weight_nonneg]
            · simp [hf, hsnd, hinc]
    _ = ∑ e ∈ Finset.univ.filter (G.Inc v), G.weight e := by
      rw [Finset.sum_filter]
    _ = G.starWeight v := by
      unfold starWeight
      exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
        (by intro e; simp) (fun e ↦ G.weight e)

theorem boundedClassResidual_selectedBlockLargeResidual_le_palette_div_beta
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (hpack : G.LocallyPacksInto (B * k))
    (v : G.V) (h : Class) :
    G.boundedClassResidual bucket (G.selectedBlockLargeResidual R0 omega rho choice)
        v h ≤ (B * k : ℕ) / β := by
  apply (le_div_iff₀ hβ).2
  exact (G.boundedClassResidual_selectedBlockLargeResidual_mul_beta_le_starWeight R0
    hn hs hq hr0 hleft omega homega0 homega1 rho hrho choice bucket v h).trans
      (G.starWeight_le_of_locallyPacksInto hpack v)

/-- Uniform count bound used in the floor-loss estimate. -/
theorem graphDyadicLargeResidual_supportCount_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (hpack : G.LocallyPacksInto (B * k))
    (hreserve : 0 < reserve) (hgamma1 : gamma < 1)
    (E : ℕ)
    (hE : 2 * (((B * k : ℕ) : ℝ) / β / (1 - gamma) +
      1 + reserve) ≤ E) (e : G.E) :
    DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
      (G.boundedDyadicExtraSlotCount bucket
        (G.selectedBlockLargeResidual R0 omega rho choice) gamma reserve) e ≤
      E := by
  have count_le (v : G.V) (h : Class) :
      G.boundedDyadicExtraSlotCount bucket
          (G.selectedBlockLargeResidual R0 omega rho choice) gamma reserve v h ≤
        E := by
    have hc := G.boundedDyadicExtraSlotCount_cast_le bucket
      (G.selectedBlockLargeResidual R0 omega rho choice)
      (G.selectedBlockLargeResidual_nonneg R0 hn hs hq hr0 hleft
        omega homega0 homega1 rho hrho choice)
      gamma hreserve hgamma1 v h
    have hR := G.boundedClassResidual_selectedBlockLargeResidual_le_palette_div_beta
      R0 hn hs hq hr0 hleft omega homega0 homega1 rho hrho choice bucket
      hpack v h
    have hgap : 0 < 1 - gamma := sub_pos.mpr hgamma1
    have hdiv := div_le_div_of_nonneg_right hR hgap.le
    have hinter :
        G.boundedClassResidual bucket
              (G.selectedBlockLargeResidual R0 omega rho choice) v h /
              (1 - gamma) + 1 + (reserve : ℝ) ≤
          ((B * k : ℕ) : ℝ) / β / (1 - gamma) + 1 + reserve := by
      linarith
    have hreal :
        (G.boundedDyadicExtraSlotCount bucket
          (G.selectedBlockLargeResidual R0 omega rho choice) gamma reserve v h :
            ℝ) ≤ E :=
      hc.trans ((mul_le_mul_of_nonneg_left hinter (by norm_num)).trans hE)
    exact_mod_cast hreal
  unfold DivisibleLocalExtraChoice.supportCount
  exact max_le (count_le _ _) (count_le _ _)

abbrev selectedBlockDyadicQuantizedSystem
    (omega rho : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) :=
  (G.dyadicLargeEdgeOptionSystem
    (Color := Fin (B * k)) (explicitLargeSlotBound β q r) bucket gamma reserve
    (G.selectedBlockLargeResidual R0 omega rho choice)).quantized N
  (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma reserve
    (G.selectedBlockLargeResidual R0 omega rho choice)
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice))

theorem selectedBlockDyadicLarge_slots_card_eq_two
    (omega rho : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class)
    (o : (G.selectedBlockDyadicQuantizedSystem (N := N) (reserve := reserve)
      (gamma := gamma) R0 omega rho choice bucket).ActiveJobOption
      (G.largeEdgeJobs β)) :
    (((G.largeEdgeJobSystem
      (G.selectedBlockDyadicQuantizedSystem (N := N) (reserve := reserve)
        (gamma := gamma) R0 omega rho choice bucket) β).slots o).card) = 2 := by
  exact G.quantized_dyadicLargeEdgeOptionSystem_slots_card_eq_two
    (explicitLargeSlotBound β q r) bucket gamma reserve
    (G.selectedBlockLargeResidual R0 omega rho choice)
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) N o.1

theorem selectedBlockDyadicLarge_jobDegree_lower
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (hCN : C ≤ N)
    (hchoices : ∀ e,
      (B * k) * explicitLargeSlotBound β q r *
          explicitLargeSlotBound β q r +
        DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
          (G.boundedDyadicExtraSlotCount bucket
            (G.selectedBlockLargeResidual R0 omega rho choice)
            gamma reserve) e ≤ C)
    (e : (G.largeEdgeRestriction β).E) :
    N - C ≤
      ((G.largeEdgeJobSystem
        (G.selectedBlockDyadicQuantizedSystem (N := N) (reserve := reserve)
          (gamma := gamma) R0 omega rho choice bucket) β).fiber e).card := by
  rw [RankThreeOptionSystem.inducedOnJobs_fiber_card]
  have hbase := G.dyadicLargeEdge_quantizedJobDegree_lower
    (explicitLargeSlotBound β q r) bucket gamma reserve
    (G.selectedBlockLargeResidual R0 omega rho choice)
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) N e.1
  have heLarge : β ≤ G.weight e.1 := G.mem_largeEdgeJobs.mp e.2
  have hmass := G.sum_selectedBlockNormalizedLarge_add_residual_of_large R0
    hn hs hq hr0 hleft homega0 homega1 hrho choice e.1 heLarge
  rw [G.selectedBlockLargeResidual_eq_of_large R0 omega rho choice heLarge,
    hmass, mul_one] at hbase
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul] at hbase
  have hchoiceR :
      (((B * k) * explicitLargeSlotBound β q r *
          explicitLargeSlotBound β q r +
        DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
          (G.boundedDyadicExtraSlotCount bucket
            (G.selectedBlockLargeResidual R0 omega rho choice)
            gamma reserve) e.1 : ℕ) : ℝ) ≤ C := by
    exact_mod_cast hchoices e.1
  push_cast at hchoiceR
  have hreal : ((N - C : ℕ) : ℝ) ≤
      ((G.selectedBlockDyadicQuantizedSystem (N := N) (reserve := reserve)
        (gamma := gamma) R0 omega rho choice bucket).fiber e.1).card := by
    rw [(G.dyadicLargeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r) bucket gamma reserve
      (G.selectedBlockLargeResidual R0 omega rho choice)).quantized_fiber_card
        N (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
          reserve (G.selectedBlockLargeResidual R0 omega rho choice)
          (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)) e.1]
    rw [Nat.cast_sub hCN]
    exact (sub_le_sub_left hchoiceR N).trans hbase
  exact_mod_cast hreal

/-- A positive trimmed lower degree makes every large job active in the
initial restricted system. -/
theorem selectedBlockDyadicLarge_mem_activeJobs
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (hCN : C ≤ N) (hNC : 0 < N - C)
    (hchoices : ∀ e,
      (B * k) * explicitLargeSlotBound β q r *
          explicitLargeSlotBound β q r +
        DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
          (G.boundedDyadicExtraSlotCount bucket
            (G.selectedBlockLargeResidual R0 omega rho choice)
            gamma reserve) e ≤ C)
    (e : (G.largeEdgeRestriction β).E) :
    e ∈ (G.largeEdgeJobSystem
      (G.selectedBlockDyadicQuantizedSystem (N := N) (reserve := reserve)
        (gamma := gamma) R0 omega rho choice bucket) β).activeJobs := by
  rw [RankThreeOptionSystem.mem_activeJobs]
  apply Finset.card_pos.mp
  exact hNC.trans_le
    (G.selectedBlockDyadicLarge_jobDegree_lower R0 hn hs hq hr0 hleft
      omega homega0 homega1 rho hrho choice bucket hCN hchoices e)

theorem selectedBlockDyadicLarge_slotDegree_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r) (hN : 0 < N)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (D ordinaryRate : ℝ)
    (hcapacity : ∀ row : G.ExtendedProfileLargeRow
        (n := B * k) (β := β) (q := q) (r := r),
      G.selectedBlockCapacityLoad R0 rho omega choice (Sum.inl row) /
          extendedProfileCandidateCapacityScale rho s omega β q r <
        ((B * k : ℕ) : ℝ) * rho /
            (extendedProfileCandidateCapacityScale rho s omega β q r *
              extendedProfileSmoothingKappa omega β q r) + D)
    (hordinaryRate :
      rho / extendedProfileSmoothingKappa omega β q r +
          extendedProfileCandidateCapacityScale rho s omega β q r /
            ((B * k : ℕ) : ℝ) * D ≤ ordinaryRate)
    (hordinaryCap : (N : ℝ) * ordinaryRate ≤ S0)
    (hreserve : 0 < reserve) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma < 1) (hextraCap : (1 - gamma) * N ≤ S0)
    (slot : G.DyadicLargeEdgeSlot
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r) bucket gamma
      reserve (G.selectedBlockLargeResidual R0 omega rho choice)) :
    (G.largeEdgeJobSystem
      (G.selectedBlockDyadicQuantizedSystem (N := N) (reserve := reserve)
        (gamma := gamma) R0 omega rho choice bucket) β).slotDegree slot ≤ S0 := by
  apply (G.largeEdgeJobSystem_slotDegree_le
    (G.selectedBlockDyadicQuantizedSystem (N := N) (reserve := reserve)
      (gamma := gamma) R0 omega rho choice bucket) β slot).trans
  cases slot with
  | inl slot =>
      have hx0 := G.selectedBlockNormalizedLargeOptionMass_nonneg R0 hn hs hq
        hr0 hleft homega0 homega1 hrho.le choice
      have hdeg := G.dyadicLargeEdge_quantized_slotDegree_inl_le
        (explicitLargeSlotBound β q r) bucket gamma reserve
        (G.selectedBlockLargeResidual R0 omega rho choice)
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        hx0 N slot
      have hload := G.selectedBlockNormalizedLargeSlotLoad_lt_ratio_add R0
        hn hs hspos hq hr0 hleft omega homega0 homega1 rho hrho choice D
        hcapacity (slot.vertex, slot.color, slot.place)
      have hdeg' := hdeg.trans_lt
        (mul_lt_mul_of_pos_left hload (by exact_mod_cast hN))
      have hreal :
          (((G.selectedBlockDyadicQuantizedSystem (N := N) (reserve := reserve)
            (gamma := gamma) R0 omega rho choice bucket).slotDegree
            (Sum.inl slot) : ℕ) : ℝ) ≤ S0 :=
        hdeg'.le.trans ((mul_le_mul_of_nonneg_left hordinaryRate
          (Nat.cast_nonneg N)).trans hordinaryCap)
      exact_mod_cast hreal
  | inr slot =>
      have hres0 := G.selectedBlockLargeResidual_nonneg R0 hn hs hq hr0
        hleft omega homega0 homega1 rho hrho.le choice
      have hdeg := G.dyadicLargeEdge_quantized_slotDegree_inr_le
        (explicitLargeSlotBound β q r) bucket gamma reserve
        (G.selectedBlockLargeResidual R0 omega rho choice)
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        hres0 hreserve hgamma0 hgamma1 N slot
      exact_mod_cast hdeg.trans hextraCap

theorem selectedBlockDyadicLarge_jobSlotCodegree_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (hreserve : 0 < reserve)
    (hordinary : (N : ℝ) *
      ((explicitLargeSlotBound β q r : ℝ) *
        extendedProfileCandidateCapacityScale rho s omega β q r /
          (B * k : ℕ)) ≤ lambda)
    (hextra : (N : ℝ) / reserve ≤ lambda)
    (e : (G.largeEdgeRestriction β).E)
    (slot : G.DyadicLargeEdgeSlot
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r) bucket gamma
      reserve (G.selectedBlockLargeResidual R0 omega rho choice)) :
    (G.largeEdgeJobSystem
      (G.selectedBlockDyadicQuantizedSystem (N := N) (reserve := reserve)
        (gamma := gamma) R0 omega rho choice bucket) β).jobSlotCodegree
        e slot ≤ lambda := by
  rw [G.largeEdgeJobSystem_jobSlotCodegree
    (G.selectedBlockDyadicQuantizedSystem (N := N) (reserve := reserve)
      (gamma := gamma) R0 omega rho choice bucket) β e slot]
  cases slot with
  | inl slot =>
      have hx0 := G.selectedBlockNormalizedLargeOptionMass_nonneg R0 hn hs hq
        hr0 hleft homega0 homega1 hrho choice
      have hbase := G.dyadicLargeEdge_quantized_jobSlotCodegree_inl_le
        (explicitLargeSlotBound β q r) bucket gamma reserve
        (G.selectedBlockLargeResidual R0 omega rho choice)
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        hx0 N e.1 slot
      have hmass := G.n_mul_sum_selectedBlockNormalizedLargeOptionMass_color_le
        R0 hn hs hq hr0 hleft omega homega0 homega1 rho hrho choice
        e.1 slot.color
      have hnR : (0 : ℝ) < (B * k : ℕ) := by exact_mod_cast hn
      have hdeg := hbase.trans (mul_le_mul_of_nonneg_left
        ((le_div_iff₀ hnR).2 (by
          convert hmass using 1 <;> push_cast <;> ring))
        (Nat.cast_nonneg N))
      exact_mod_cast hdeg.trans hordinary
  | inr slot =>
      have hres0 := G.selectedBlockLargeResidual_nonneg R0 hn hs hq hr0
        hleft omega homega0 homega1 rho hrho choice
      have hres1 := G.selectedBlockLargeResidual_le_one R0 hn hs hq hr0
        hleft omega homega0 homega1 rho hrho choice
      have hdeg := G.dyadicLargeEdge_quantized_jobSlotCodegree_inr_le
        (explicitLargeSlotBound β q r) bucket gamma reserve
        (G.selectedBlockLargeResidual R0 omega rho choice)
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        hres0 hres1 hreserve N e.1 slot
      exact_mod_cast hdeg.trans hextra

theorem selectedBlockDyadicLarge_slotPairCodegree_le
    {mult : ℕ} (hmult : G.PairMultiplicityAtMost mult)
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (hreserve : 0 < reserve)
    (hordinary :
      extendedProfileCandidateCapacityScale rho s omega β q r /
          (B * k : ℕ) ≤ 1 / (reserve : ℝ))
    (hcap : (mult : ℝ) * (N : ℝ) / reserve ≤ lambda)
    (left right : G.DyadicLargeEdgeSlot
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r) bucket gamma
      reserve (G.selectedBlockLargeResidual R0 omega rho choice))
    (hne : left ≠ right) :
    (G.largeEdgeJobSystem
      (G.selectedBlockDyadicQuantizedSystem (N := N) (reserve := reserve)
        (gamma := gamma) R0 omega rho choice bucket) β).slotPairCodegree
        left right ≤ lambda := by
  apply (G.largeEdgeJobSystem_slotPairCodegree_le
    (G.selectedBlockDyadicQuantizedSystem (N := N) (reserve := reserve)
      (gamma := gamma) R0 omega rho choice bucket) β
    left right).trans
  have hx0 := G.selectedBlockNormalizedLargeOptionMass_nonneg R0 hn hs hq
    hr0 hleft homega0 homega1 hrho choice
  have hx : ∀ e c i j,
      G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice e c i j ≤
        1 / (reserve : ℝ) := by
    intro e c i j
    exact (G.selectedBlockNormalizedLargeOptionMass_le_scale_div R0 hn hs hq
      hr0 hleft omega homega0 homega1 rho hrho choice e c i j).trans hordinary
  have hres0 := G.selectedBlockLargeResidual_nonneg R0 hn hs hq hr0
    hleft omega homega0 homega1 rho hrho choice
  have hres1 := G.selectedBlockLargeResidual_le_one R0 hn hs hq hr0
    hleft omega homega0 homega1 rho hrho choice
  have hdeg := G.dyadicLargeEdge_quantized_slotPairCodegree_le
    (explicitLargeSlotBound β q r) bucket gamma reserve
    (G.selectedBlockLargeResidual R0 omega rho choice) hmult
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
    hx0 hx hres0 hres1 hreserve N hne
  exact_mod_cast hdeg.trans hcap

/- obsolete tail removed -/
end WeightedMultigraph

end

end WeightedEdgeColoring
