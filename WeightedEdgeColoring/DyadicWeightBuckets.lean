import WeightedEdgeColoring.FiniteGeometricWeightGrouping

open scoped BigOperators
open Finset

namespace WeightedEdgeColoring

/-! # Finite dyadic weight buckets -/

/-- The upper scale of dyadic bucket `i`. -/
def dyadicScale (β : ℝ) (i : ℕ) : ℝ := β * (2 : ℝ) ^ i

/-- Every positive base scale reaches one after finitely many
doublings. -/
theorem exists_dyadic_scale_ge_one (β : ℝ) (hβ : 0 < β) :
    ∃ L, 1 ≤ dyadicScale β L := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / β)
  have hpowNat : ∀ m : ℕ, m + 1 ≤ 2 ^ m := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
        rw [pow_succ]
        omega
  have hnpow : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (le_trans (Nat.le_succ n) (hpowNat n))
  have hnβ : 1 < β * (n : ℝ) := by
    have := (div_lt_iff₀ hβ).mp hn
    nlinarith
  refine ⟨n, ?_⟩
  unfold dyadicScale
  have hmul := mul_le_mul_of_nonneg_left hnpow hβ.le
  nlinarith

/-- The least index at which an item's weight is below the dyadic scale.
If no such index through `L` exists, the total function uses bucket zero; the
main lemmas rule out this fallback from the stated cover assumptions. -/
noncomputable def dyadicBucket {α : Type*} (β : ℝ) (L : ℕ)
    (w : α → ℝ) (a : α) : Fin (L + 1) := by
  classical
  by_cases h : ∃ i : ℕ, i ≤ L ∧ w a ≤ dyadicScale β i
  · exact ⟨Nat.find h, Nat.lt_succ_of_le (Nat.find_spec h).1⟩
  · exact ⟨0, Nat.succ_pos L⟩

theorem dyadicBucket_spec {α : Type*} (β : ℝ) (L : ℕ)
    (w : α → ℝ) (a : α)
    (h : ∃ i : ℕ, i ≤ L ∧ w a ≤ dyadicScale β i) :
    w a ≤ dyadicScale β (dyadicBucket β L w a).val := by
  classical
  unfold dyadicBucket
  simp only [dif_pos h]
  exact (Nat.find_spec h).2

theorem dyadicScale_lt_of_lt_bucket {α : Type*} (β : ℝ) (L : ℕ)
    (w : α → ℝ) (a : α)
    (h : ∃ i : ℕ, i ≤ L ∧ w a ≤ dyadicScale β i)
    {j : ℕ} (hj : j < (dyadicBucket β L w a).val) :
    dyadicScale β j < w a := by
  classical
  unfold dyadicBucket at hj
  simp only [dif_pos h] at hj
  have hnot := Nat.find_min h hj
  have hjL : j ≤ L := (Nat.le_of_lt hj).trans (Nat.find_spec h).1
  exact lt_of_not_ge (fun hle ↦ hnot ⟨hjL, hle⟩)

/-- Under the range assumptions, every item has a covered dyadic bucket. -/
theorem exists_dyadic_scale_cover {α : Type*} {S : Finset α}
    (β : ℝ) (L : ℕ) (w : α → ℝ)
    (hcover : 1 ≤ dyadicScale β L) (a : α) (ha : a ∈ S)
    (hwupper : ∀ a ∈ S, w a ≤ 1) :
    ∃ i : ℕ, i ≤ L ∧ w a ≤ dyadicScale β i := by
  exact ⟨L, le_rfl, (hwupper a ha).trans hcover⟩

/-- Two positive weights in the same least dyadic bucket differ by at most a
factor two. -/
theorem dyadicBucket_same_weight_le_two_mul {α : Type*} {S : Finset α}
    (β : ℝ) (L : ℕ) (w : α → ℝ) (hβ : 0 < β)
    (hcover : 1 ≤ dyadicScale β L)
    (hwlower : ∀ a ∈ S, β ≤ w a) (hwupper : ∀ a ∈ S, w a ≤ 1)
    {a b : α} (ha : a ∈ S) (hb : b ∈ S)
    (hab : dyadicBucket β L w a = dyadicBucket β L w b) :
    w a ≤ 2 * w b := by
  have hacover := exists_dyadic_scale_cover β L w hcover a ha hwupper
  have hbcover := exists_dyadic_scale_cover β L w hcover b hb hwupper
  have haupper := dyadicBucket_spec β L w a hacover
  by_cases hzero : (dyadicBucket β L w a).val = 0
  · rw [hzero, dyadicScale, pow_zero, mul_one] at haupper
    have hab0 : 0 ≤ w b := (hβ.le.trans (hwlower b hb)).trans' (le_refl _)
    calc
      w a ≤ β := haupper
      _ ≤ w b := hwlower b hb
      _ ≤ 2 * w b := by linarith
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hbval : (dyadicBucket β L w b).val = j + 1 := by
      rw [← hab, hj]
    have hblower : dyadicScale β j < w b := by
      apply dyadicScale_lt_of_lt_bucket β L w b hbcover
      rw [hbval]
      omega
    rw [hj, dyadicScale, pow_succ] at haupper
    rw [dyadicScale] at hblower
    calc
      w a ≤ β * ((2 : ℝ) ^ j * 2) := haupper
      _ = 2 * (β * (2 : ℝ) ^ j) := by ring
      _ ≤ 2 * w b := by linarith

/-- The least dyadic bucket map on weights in `[β,1]` is a geometric weight
classification with ratio two. Its bucket type is `Fin (L+1)`, so it uses
exactly `L+1` available bucket labels. -/
theorem dyadicBucket_isGeometricWeightClassing {α : Type*}
    [DecidableEq α] (S : Finset α) (β : ℝ) (L : ℕ) (w : α → ℝ)
    (hβ : 0 < β) (hcover : 1 ≤ dyadicScale β L)
    (hwlower : ∀ a ∈ S, β ≤ w a) (hwupper : ∀ a ∈ S, w a ≤ 1) :
    IsGeometricWeightClassing S w 2 (dyadicBucket β L w) := by
  constructor
  · intro a ha
    exact hβ.trans_le (hwlower a ha)
  · intro i a ha hai b hb hbi
    apply dyadicBucket_same_weight_le_two_mul β L w hβ hcover hwlower hwupper ha hb
    exact hai.trans hbi.symm

/-- Dyadic specialization of the generic finite geometric grouping theorem. -/
theorem exists_dyadic_block_finpartition {α : Type*} [DecidableEq α]
    (S : Finset α) (β : ℝ) (L K : ℕ) (w : α → ℝ)
    (hβ : 0 < β) (hcover : 1 ≤ dyadicScale β L)
    (hwlower : ∀ a ∈ S, β ≤ w a) (hwupper : ∀ a ∈ S, w a ≤ 1)
    (hK : 0 < K) :
    ∃ P : Finpartition S,
      ∀ T ∈ P.parts,
        ((K ≤ T.card ∧ T.card ≤ 2 * K - 1) ∨ T.card < K) ∧
        (∃ i : Fin (L + 1),
          T ⊆ weightClass S (dyadicBucket β L w) i) ∧
        (∀ a ∈ T, ∀ b ∈ T, w a ≤ 2 * w b) := by
  apply exists_geometric_block_finpartition S w 2
    (dyadicBucket β L w) K (by norm_num) hK
  exact dyadicBucket_isGeometricWeightClassing S β L w
    hβ hcover hwlower hwupper

/-- Dyadic grouping with the small-class invariant and an explicit
global bound on the sum of all small parts. Each bucket contributes at most
one such part, it has at most `K-1` items, and every item has weight at most
one. -/
theorem exists_dyadic_block_finpartition_small_weight_bound {α : Type*}
    [DecidableEq α]
    (S : Finset α) (β : ℝ) (L K : ℕ) (w : α → ℝ)
    (hβ : 0 < β) (hcover : 1 ≤ dyadicScale β L)
    (hwlower : ∀ a ∈ S, β ≤ w a) (hwupper : ∀ a ∈ S, w a ≤ 1)
    (hK : 0 < K) :
    ∃ P : Finpartition S,
      (∀ T ∈ P.parts,
        ((K ≤ T.card ∧ T.card ≤ 2 * K - 1) ∨ T.card < K) ∧
        (∃ i : Fin (L + 1),
          T ⊆ weightClass S (dyadicBucket β L w) i) ∧
        (∀ a ∈ T, ∀ b ∈ T, w a ≤ 2 * w b)) ∧
      (∀ i T, T ∈ P.parts → T.card < K →
        T ⊆ weightClass S (dyadicBucket β L w) i →
        T = weightClass S (dyadicBucket β L w) i) ∧
      (∑ T ∈ P.parts.filter (fun T ↦ T.card < K),
        ∑ a ∈ T, w a) ≤ (((L + 1) * (K - 1) : ℕ) : ℝ) := by
  classical
  have hgeom := dyadicBucket_isGeometricWeightClassing S β L w
    hβ hcover hwlower hwupper
  obtain ⟨P, hprops, hsmall⟩ :=
    exists_geometric_block_finpartition_small_eq_class
      S w 2 (dyadicBucket β L w) K (by norm_num) hK hgeom
  let smallParts := P.parts.filter fun T ↦ T.card < K
  let f : {T // T ∈ smallParts} → Fin (L + 1) := fun T ↦
    Classical.choose ((hprops T.1 (Finset.mem_filter.mp T.2).1).2.1)
  have hfsub : ∀ T : {T // T ∈ smallParts},
      T.1 ⊆ weightClass S (dyadicBucket β L w) (f T) := by
    intro T
    exact Classical.choose_spec
      ((hprops T.1 (Finset.mem_filter.mp T.2).1).2.1)
  have hfinj : Function.Injective f := by
    intro T U hTU
    apply Subtype.ext
    have hTm := Finset.mem_filter.mp T.2
    have hUm := Finset.mem_filter.mp U.2
    have hTeq := hsmall (f T) T.1 hTm.1 hTm.2 (hfsub T)
    have hUsub : U.1 ⊆ weightClass S (dyadicBucket β L w) (f T) := by
      simpa [hTU] using hfsub U
    have hUeq := hsmall (f T) U.1 hUm.1 hUm.2 hUsub
    exact hTeq.trans hUeq.symm
  have hsmallCard : smallParts.card ≤ L + 1 := by
    have hc := Fintype.card_le_of_injective f hfinj
    simpa using hc
  have hpartWeight : ∀ T ∈ smallParts,
      (∑ a ∈ T, w a) ≤ ((K - 1 : ℕ) : ℝ) := by
    intro T hT
    have hm := Finset.mem_filter.mp hT
    have hTsubS : T ⊆ S := fun a ha ↦
      P.le hm.1 ha
    calc
      (∑ a ∈ T, w a) ≤ ∑ _a ∈ T, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        exact hwupper a (hTsubS ha)
      _ = (T.card : ℝ) := by simp
      _ ≤ ((K - 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_pred_of_lt hm.2)
  refine ⟨P, hprops, hsmall, ?_⟩
  change (∑ T ∈ smallParts, ∑ a ∈ T, w a) ≤ _
  calc
    (∑ T ∈ smallParts, ∑ a ∈ T, w a) ≤
        ∑ _T ∈ smallParts, (((K - 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro T hT
      exact hpartWeight T hT
    _ = (smallParts.card : ℝ) * (K - 1 : ℕ) := by simp
    _ ≤ (((L + 1 : ℕ) : ℝ)) * (((K - 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsmallCard) (by positivity)
    _ = (((L + 1) * (K - 1) : ℕ) : ℝ) := by norm_num

/-- The dyadic construction has `L+1` bucket labels. -/
theorem dyadicBucket_count (L : ℕ) :
    Fintype.card (Fin (L + 1)) = L + 1 := by simp

end WeightedEdgeColoring
