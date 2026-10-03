import WeightedEdgeColoring.BalancedDivisibleProjection
import WeightedEdgeColoring.ExtraSlotOptions

/-!
# Sparse coupling of unequal local extra-slot marginals

For an edge with endpoint counts `B₁,B₂`, take
`T=max B₁ B₂` coupled choices.  When both counts are powers of two,
each divides `T`; a balanced projection from `Fin T` to each endpoint gives
the exact uniform marginals `1/B₁` and `1/B₂`.  Thus the fibre size is
linear in the endpoint counts rather than their product.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u v w

abbrev DivisibleLocalExtraChoice (Job : Type u) (Vertex : Type v)
    (Class : Type w) (left right : Job → Vertex) (bucket : Job → Class)
    (B : Vertex → Class → ℕ) :=
  Sigma fun j : Job ↦ Fin (max (B (left j) (bucket j))
    (B (right j) (bucket j)))

namespace DivisibleLocalExtraChoice

variable {Job : Type u} {Vertex : Type v} {Class : Type w}
  [Fintype Job] [Fintype Vertex] [Fintype Class]
  [DecidableEq Job] [DecidableEq Vertex] [DecidableEq Class]

variable (left right : Job → Vertex) (bucket : Job → Class)
  (B : Vertex → Class → ℕ)

def supportCount (j : Job) : ℕ :=
  max (B (left j) (bucket j)) (B (right j) (bucket j))

variable
  (hleftDiv : ∀ j, B (left j) (bucket j) ∣ supportCount left right bucket B j)
  (hrightDiv : ∀ j, B (right j) (bucket j) ∣ supportCount left right bucket B j)

def leftIndex (q : DivisibleLocalExtraChoice Job Vertex Class
    left right bucket B) : Fin (B (left q.1) (bucket q.1)) :=
  balancedDivisibleProjection (hleftDiv q.1) q.2

def rightIndex (q : DivisibleLocalExtraChoice Job Vertex Class
    left right bucket B) : Fin (B (right q.1) (bucket q.1)) :=
  balancedDivisibleProjection (hrightDiv q.1) q.2

def leftSlot (q : DivisibleLocalExtraChoice Job Vertex Class
    left right bucket B) : ExtraSlot Vertex Class B :=
  ⟨(left q.1, bucket q.1), leftIndex left right bucket B hleftDiv q⟩

def rightSlot (q : DivisibleLocalExtraChoice Job Vertex Class
    left right bucket B) : ExtraSlot Vertex Class B :=
  ⟨(right q.1, bucket q.1), rightIndex left right bucket B hrightDiv q⟩

def system : RankThreeOptionSystem Job (ExtraSlot Vertex Class B)
    (DivisibleLocalExtraChoice Job Vertex Class left right bucket B) where
  owner q := q.1
  slots q := {leftSlot left right bucket B hleftDiv q,
    rightSlot left right bucket B hrightDiv q}
  slots_card_le_two q := (Finset.card_insert_le _ _).trans (by simp)

def mass (residual : Job → ℝ)
    (q : DivisibleLocalExtraChoice Job Vertex Class left right bucket B) : ℝ :=
  residual q.1 / supportCount left right bucket B q.1

theorem mass_nonneg (residual : Job → ℝ) (hr : ∀ j, 0 ≤ residual j) :
    ∀ q, 0 ≤ mass left right bucket B residual q := by
  intro q
  exact div_nonneg (hr q.1) (Nat.cast_nonneg _)

theorem supportCount_pos
    (hleft : ∀ j, 0 < B (left j) (bucket j)) (j : Job) :
    0 < supportCount left right bucket B j := by
  unfold supportCount
  exact (hleft j).trans_le (Nat.le_max_left _ _)

/-- The sparse coupled fibre has total residual mass one, exactly as the
Cartesian fibre did. -/
theorem sum_mass_fiber (residual : Job → ℝ)
    (hleft : ∀ j, 0 < B (left j) (bucket j)) (j : Job) :
    (∑ q ∈ (system left right bucket B hleftDiv hrightDiv).fiber j,
      mass left right bucket B residual q) = residual j := by
  classical
  simp only [RankThreeOptionSystem.fiber, system, mass, Finset.sum_filter]
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · have hT : ((supportCount left right bucket B j : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt
        (supportCount_pos left right bucket B hleft j))
    simp only [if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [hT]
    unfold supportCount
    ring
  · intro k _hk hkj
    simp [hkj]
  · simp

/-- Exact uniform marginal on the left endpoint. -/
theorem sum_mass_leftIndex_eq (residual : Job → ℝ)
    (hleft : ∀ j, 0 < B (left j) (bucket j))
    (j : Job) (i : Fin (B (left j) (bucket j))) :
    (∑ z : Fin (supportCount left right bucket B j),
      if leftIndex left right bucket B hleftDiv ⟨j, z⟩ = i then
        residual j / supportCount left right bucket B j else 0) =
      residual j / B (left j) (bucket j) := by
  exact sum_balancedDivisibleProjection_indicator
    (hleft j) (supportCount_pos left right bucket B hleft j)
    (hleftDiv j) (residual j) i

/-- Exact uniform marginal on the right endpoint. -/
theorem sum_mass_rightIndex_eq (residual : Job → ℝ)
    (hright : ∀ j, 0 < B (right j) (bucket j))
    (j : Job) (i : Fin (B (right j) (bucket j))) :
    (∑ z : Fin (supportCount left right bucket B j),
      if rightIndex left right bucket B hrightDiv ⟨j, z⟩ = i then
        residual j / supportCount left right bucket B j else 0) =
      residual j / B (right j) (bucket j) := by
  exact sum_balancedDivisibleProjection_indicator
    (hright j)
    ((hright j).trans_le (Nat.le_max_right _ _))
    (hrightDiv j) (residual j) i

theorem sum_mass_leftSlot_eq (residual : Job → ℝ)
    (hleft : ∀ j, 0 < B (left j) (bucket j))
    (j : Job) (s : ExtraSlot Vertex Class B) :
    (∑ q ∈ (system left right bucket B hleftDiv hrightDiv).fiber j,
      if leftSlot left right bucket B hleftDiv q = s then
        mass left right bucket B residual q else 0) =
      if s.1 = (left j, bucket j) then
        residual j / B (left j) (bucket j) else 0 := by
  classical
  simp only [RankThreeOptionSystem.fiber, system, mass, Finset.sum_filter]
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · by_cases hs : s.1 = (left j, bucket j)
    · rcases s with ⟨vh, i⟩
      dsimp at hs
      subst vh
      simpa [leftSlot] using
        sum_mass_leftIndex_eq left right bucket B hleftDiv residual hleft j i
    · have hne : ∀ z : Fin (supportCount left right bucket B j),
          leftSlot left right bucket B hleftDiv ⟨j, z⟩ ≠ s := by
        intro z heq
        exact hs (congrArg Sigma.fst heq).symm
      simp [hs, hne]
  · intro k _hk hkj
    simp [hkj]
  · simp

theorem sum_mass_rightSlot_eq (residual : Job → ℝ)
    (hright : ∀ j, 0 < B (right j) (bucket j))
    (j : Job) (s : ExtraSlot Vertex Class B) :
    (∑ q ∈ (system left right bucket B hleftDiv hrightDiv).fiber j,
      if rightSlot left right bucket B hrightDiv q = s then
        mass left right bucket B residual q else 0) =
      if s.1 = (right j, bucket j) then
        residual j / B (right j) (bucket j) else 0 := by
  classical
  simp only [RankThreeOptionSystem.fiber, system, mass, Finset.sum_filter]
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · by_cases hs : s.1 = (right j, bucket j)
    · rcases s with ⟨vh, i⟩
      dsimp at hs
      subst vh
      simpa [rightSlot] using
        sum_mass_rightIndex_eq left right bucket B hrightDiv residual hright j i
    · have hne : ∀ z : Fin (supportCount left right bucket B j),
          rightSlot left right bucket B hrightDiv ⟨j, z⟩ ≠ s := by
        intro z heq
        exact hs (congrArg Sigma.fst heq).symm
      simp [hs, hne]
  · intro k _hk hkj
    simp [hkj]
  · simp

/-- One concrete slot sees at most the corresponding uniform endpoint
share of a job. -/
theorem sum_mass_using_slot_fiber_le (residual : Job → ℝ)
    (hr0 : ∀ j, 0 ≤ residual j)
    (hleft : ∀ j, 0 < B (left j) (bucket j))
    (hright : ∀ j, 0 < B (right j) (bucket j))
    (hne : ∀ j, left j ≠ right j) (j : Job)
    (s : ExtraSlot Vertex Class B) :
    (∑ q ∈ (system left right bucket B hleftDiv hrightDiv).fiber j,
      if s ∈ (system left right bucket B hleftDiv hrightDiv).slots q then
        mass left right bucket B residual q else 0) ≤
      if s.1 = (left j, bucket j) then residual j / B (left j) (bucket j)
      else if s.1 = (right j, bucket j) then
        residual j / B (right j) (bucket j) else 0 := by
  classical
  calc
    _ ≤ ∑ q ∈ (system left right bucket B hleftDiv hrightDiv).fiber j,
        ((if leftSlot left right bucket B hleftDiv q = s then
            mass left right bucket B residual q else 0) +
          if rightSlot left right bucket B hrightDiv q = s then
            mass left right bucket B residual q else 0) := by
      apply Finset.sum_le_sum
      intro q _hq
      have hm := mass_nonneg left right bucket B residual hr0 q
      simp only [system, Finset.mem_insert, Finset.mem_singleton]
      by_cases hl : leftSlot left right bucket B hleftDiv q = s
      · simp [hl]
        split_ifs <;> linarith
      · by_cases hr : rightSlot left right bucket B hrightDiv q = s
        · simp [hl, hr, hm]
        · have hls : ¬s = leftSlot left right bucket B hleftDiv q :=
            fun hs ↦ hl hs.symm
          have hrs : ¬s = rightSlot left right bucket B hrightDiv q :=
            fun hs ↦ hr hs.symm
          simp [hl, hr, hls, hrs]
    _ = (if s.1 = (left j, bucket j) then
          residual j / B (left j) (bucket j) else 0) +
        (if s.1 = (right j, bucket j) then
          residual j / B (right j) (bucket j) else 0) := by
      rw [Finset.sum_add_distrib,
        sum_mass_leftSlot_eq left right bucket B hleftDiv hrightDiv
          residual hleft j s,
        sum_mass_rightSlot_eq left right bucket B hleftDiv hrightDiv
          residual hright j s]
    _ = _ := by
      by_cases hl : s.1 = (left j, bucket j)
      · have hr : s.1 ≠ (right j, bucket j) := by
          intro hs
          exact hne j (congrArg Prod.fst (hl.symm.trans hs))
        rw [if_pos hl, if_neg hr, if_pos hl]
        simp
      · by_cases hr : s.1 = (right j, bucket j)
        · rw [if_neg hl, if_pos hr, if_neg hl]
          have hrl : right j ≠ left j := Ne.symm (hne j)
          simp [hrl]
        · rw [if_neg hl, if_neg hr, if_neg hl]
          simp

theorem quantized_jobSlotCodegree_le_reserve
    (residual : Job → ℝ) (hr0 : ∀ j, 0 ≤ residual j)
    (hr1 : ∀ j, residual j ≤ 1)
    (hleft : ∀ j, 0 < B (left j) (bucket j))
    (hright : ∀ j, 0 < B (right j) (bucket j))
    (hreserve : ∀ v h, reserve ≤ B v h) (hreserve0 : 0 < reserve)
    (hne : ∀ j, left j ≠ right j) (N : ℕ) (j : Job)
    (s : ExtraSlot Vertex Class B) :
    (((system left right bucket B hleftDiv hrightDiv).quantized N
      (mass left right bucket B residual)).jobSlotCodegree j s : ℝ) ≤
      (N : ℝ) / reserve := by
  have hquant := (system left right bucket B hleftDiv hrightDiv).quantizedJobSlotCodegree_upper N
      (mass left right bucket B residual) j s
      (fun q _ ↦ mass_nonneg left right bucket B residual hr0 q)
  have hrewrite :
      (∑ q, if (system left right bucket B hleftDiv hrightDiv).owner q = j ∧
          s ∈ (system left right bucket B hleftDiv hrightDiv).slots q then
          mass left right bucket B residual q else 0) =
        ∑ q ∈ (system left right bucket B hleftDiv hrightDiv).fiber j,
          if s ∈ (system left right bucket B hleftDiv hrightDiv).slots q then
            mass left right bucket B residual q else 0 := by
    classical
    simp only [RankThreeOptionSystem.fiber, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hj : (system left right bucket B hleftDiv hrightDiv).owner q = j <;>
      by_cases hs : s ∈ (system left right bucket B hleftDiv hrightDiv).slots q <;>
        simp [hj, hs]
  rw [hrewrite] at hquant
  have hshare :
      (if s.1 = (left j, bucket j) then residual j / B (left j) (bucket j)
      else if s.1 = (right j, bucket j) then residual j / B (right j) (bucket j)
      else 0) ≤ 1 / (reserve : ℝ) := by
    have hrpos : (0 : ℝ) < reserve := by exact_mod_cast hreserve0
    by_cases hl : s.1 = (left j, bucket j)
    · rw [if_pos hl]
      exact residual_div_count_le_inv_reserve (residual j) (hr1 j)
        hreserve0 (hreserve _ _)
    · rw [if_neg hl]
      by_cases hr : s.1 = (right j, bucket j)
      · rw [if_pos hr]
        exact residual_div_count_le_inv_reserve (residual j) (hr1 j)
          hreserve0 (hreserve _ _)
      · simp [hr, le_of_lt (one_div_pos.mpr hrpos)]
  calc
    _ ≤ (N : ℝ) *
        (if s.1 = (left j, bucket j) then residual j / B (left j) (bucket j)
        else if s.1 = (right j, bucket j) then residual j / B (right j) (bucket j)
        else 0) := hquant.trans (mul_le_mul_of_nonneg_left
          (sum_mass_using_slot_fiber_le left right bucket B hleftDiv hrightDiv
            residual hr0 hleft hright hne j s) (Nat.cast_nonneg N))
    _ ≤ (N : ℝ) * (1 / (reserve : ℝ)) :=
      mul_le_mul_of_nonneg_left hshare (Nat.cast_nonneg N)
    _ = (N : ℝ) / reserve := by ring

theorem sum_eq_sum_fiber
    (f : DivisibleLocalExtraChoice Job Vertex Class left right bucket B → ℝ) :
    (∑ q, f q) = ∑ j, ∑ q ∈
      (system left right bucket B hleftDiv hrightDiv).fiber j, f q := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  simp only [RankThreeOptionSystem.fiber, system, Finset.sum_filter]
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · simp
  · intro k _hk hkj
    simp [hkj]
  · simp

theorem quantized_slotDegree_le_endpointShares
    (residual : Job → ℝ) (hr0 : ∀ j, 0 ≤ residual j)
    (hleft : ∀ j, 0 < B (left j) (bucket j))
    (hright : ∀ j, 0 < B (right j) (bucket j))
    (hne : ∀ j, left j ≠ right j) (N : ℕ)
    (s : ExtraSlot Vertex Class B) :
    (((system left right bucket B hleftDiv hrightDiv).quantized N
      (mass left right bucket B residual)).slotDegree s : ℕ) ≤
      (N : ℝ) * ∑ j,
        (if s.1 = (left j, bucket j) then residual j / B (left j) (bucket j)
        else if s.1 = (right j, bucket j) then
          residual j / B (right j) (bucket j) else 0) := by
  have hquant := (system left right bucket B hleftDiv hrightDiv).quantizedSlotDegree_upper
    N (mass left right bucket B residual) s
      (fun q _ ↦ mass_nonneg left right bucket B residual hr0 q)
  have hfrac :
      (∑ q, if s ∈ (system left right bucket B hleftDiv hrightDiv).slots q
        then mass left right bucket B residual q else 0) ≤
      ∑ j,
        (if s.1 = (left j, bucket j) then residual j / B (left j) (bucket j)
        else if s.1 = (right j, bucket j) then
          residual j / B (right j) (bucket j) else 0) := by
    rw [sum_eq_sum_fiber left right bucket B hleftDiv hrightDiv]
    exact Finset.sum_le_sum fun j _ ↦
      sum_mass_using_slot_fiber_le left right bucket B hleftDiv hrightDiv
        residual hr0 hleft hright hne j s
  exact hquant.trans (mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg N))

theorem leftIndex_injective_of_right_le
    (hleft : ∀ j, 0 < B (left j) (bucket j)) (j : Job)
    (hle : B (right j) (bucket j) ≤ B (left j) (bucket j)) :
    Function.Injective (fun z : Fin (supportCount left right bucket B j) ↦
      show Fin (B (left j) (bucket j)) from
        leftIndex left right bucket B hleftDiv
          (⟨j, z⟩ : DivisibleLocalExtraChoice Job Vertex Class
            left right bucket B)) := by
  refine balancedDivisibleProjection_injective_of_eq
    (hleft j) ?_ (hleftDiv j)
  simpa [supportCount, Nat.max_eq_left hle]

theorem rightIndex_injective_of_left_le
    (hright : ∀ j, 0 < B (right j) (bucket j)) (j : Job)
    (hle : B (left j) (bucket j) ≤ B (right j) (bucket j)) :
    Function.Injective (fun z : Fin (supportCount left right bucket B j) ↦
      show Fin (B (right j) (bucket j)) from
        rightIndex left right bucket B hrightDiv
          (⟨j, z⟩ : DivisibleLocalExtraChoice Job Vertex Class
            left right bucket B)) := by
  refine balancedDivisibleProjection_injective_of_eq
    (hright j) ?_ (hrightDiv j)
  simpa [supportCount, Nat.max_eq_right hle]

/-- Number of sparse base options in one job fibre. -/
theorem fiber_card (j : Job) :
    ((system left right bucket B hleftDiv hrightDiv).fiber j).card =
      supportCount left right bucket B j := by
  classical
  rw [show ((system left right bucket B hleftDiv hrightDiv).fiber j).card =
      Fintype.card {q : DivisibleLocalExtraChoice Job Vertex Class
        left right bucket B //
          (system left right bucket B hleftDiv hrightDiv).owner q = j} by
    rw [Fintype.card_subtype]
    rfl]
  let E : {q : DivisibleLocalExtraChoice Job Vertex Class
      left right bucket B //
        (system left right bucket B hleftDiv hrightDiv).owner q = j} ≃
      Fin (supportCount left right bucket B j) :=
    {
      toFun := fun q ↦ by
        rcases q with ⟨⟨k, z⟩, hk⟩
        change k = j at hk
        subst k
        exact z
      invFun := fun z ↦ ⟨⟨j, z⟩, rfl⟩
      left_inv := by
        intro q
        rcases q with ⟨⟨k, z⟩, hk⟩
        change k = j at hk
        subst k
        rfl
      right_inv := by intro z; rfl
    }
  simpa using Fintype.card_congr E

/-- Floor replication loses fewer than `max(B_left,B_right)` copies. -/
theorem quantizedJobDegree_lower (residual : Job → ℝ)
    (hleft : ∀ j, 0 < B (left j) (bucket j)) (N : ℕ) (j : Job) :
    (N : ℝ) * residual j - supportCount left right bucket B j ≤
      ((system left right bucket B hleftDiv hrightDiv).quantizedJobDegree N
        (mass left right bucket B residual) j : ℝ) := by
  have h := (system left right bucket B hleftDiv hrightDiv).quantizedJobDegree_lower
    N (mass left right bucket B residual) j
  rw [sum_mass_fiber left right bucket B hleftDiv hrightDiv residual hleft j,
    fiber_card left right bucket B hleftDiv hrightDiv j] at h
  simpa using h

/-- The sparse fibre is bounded by the sum of the two endpoint counts. -/
theorem fiber_card_le_add (j : Job) :
    ((system left right bucket B hleftDiv hrightDiv).fiber j).card ≤
      B (left j) (bucket j) + B (right j) (bucket j) := by
  rw [fiber_card left right bucket B hleftDiv hrightDiv]
  exact max_le_add_of_nonneg (Nat.zero_le _) (Nat.zero_le _)

end DivisibleLocalExtraChoice

end

end WeightedEdgeColoring
