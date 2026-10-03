import WeightedEdgeColoring.OptionSystemSum

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# Cartesian extra-slot choices

For every large edge left uncoloured, the manuscript chooses one private
counting slot at each endpoint.  If endpoint `v` has `B v h` slots for its
weight class `h`, an edge in class `h` has the Cartesian product of the two
endpoint slot sets as its leave-uncoloured options.  This file builds that
finite rank-three option system explicitly.
-/

noncomputable section

universe u v w

/-- A labelled extra slot at a vertex and weight class. -/
abbrev ExtraSlot (Vertex : Type v) (Class : Type w)
    (B : Vertex → Class → ℕ) :=
  Sigma fun vh : Vertex × Class ↦ Fin (B vh.1 vh.2)

/-- One pair of endpoint extra slots for a job. -/
abbrev ExtraSlotChoice (Job : Type u) (Vertex : Type v) (Class : Type w)
    (left right : Job → Vertex) (bucket : Job → Class)
    (B : Vertex → Class → ℕ) :=
  Sigma fun j : Job ↦
    Fin (B (left j) (bucket j)) × Fin (B (right j) (bucket j))

namespace ExtraSlotChoice

variable {Job : Type u} {Vertex : Type v} {Class : Type w}
  [Fintype Job] [Fintype Vertex] [Fintype Class]
  [DecidableEq Job] [DecidableEq Vertex] [DecidableEq Class]

variable (left right : Job → Vertex) (bucket : Job → Class)
  (B : Vertex → Class → ℕ)

/-- The extra slot selected at the left endpoint. -/
def leftSlot (q : ExtraSlotChoice Job Vertex Class left right bucket B) :
    ExtraSlot Vertex Class B :=
  ⟨(left q.1, bucket q.1), q.2.1⟩

/-- The extra slot selected at the right endpoint. -/
def rightSlot (q : ExtraSlotChoice Job Vertex Class left right bucket B) :
    ExtraSlot Vertex Class B :=
  ⟨(right q.1, bucket q.1), q.2.2⟩

/-- Every leave-uncoloured choice owns its edge job and uses its two
endpoint counting slots. -/
def system : RankThreeOptionSystem Job (ExtraSlot Vertex Class B)
    (ExtraSlotChoice Job Vertex Class left right bucket B) where
  owner q := q.1
  slots q := {leftSlot left right bucket B q,
    rightSlot left right bucket B q}
  slots_card_le_two q := by
    exact (Finset.card_insert_le _ _).trans (by simp)

/-- Split the unused mass of a job uniformly over its Cartesian grid of
extra-slot pairs. -/
def mass (residual : Job → ℝ)
    (q : ExtraSlotChoice Job Vertex Class left right bucket B) : ℝ :=
  residual q.1 /
    ((B (left q.1) (bucket q.1) : ℕ) *
      B (right q.1) (bucket q.1) : ℕ)

theorem mass_nonneg (residual : Job → ℝ)
    (hresidual : ∀ j, 0 ≤ residual j) :
    ∀ q : ExtraSlotChoice Job Vertex Class left right bucket B,
      0 ≤ mass left right bucket B residual q := by
  intro q
  exact div_nonneg (hresidual q.1) (Nat.cast_nonneg _)

/-- The Cartesian extra-slot options of one job have total mass exactly its
unused fraction. -/
theorem sum_mass_fiber (residual : Job → ℝ)
    (hleft : ∀ j, 0 < B (left j) (bucket j))
    (hright : ∀ j, 0 < B (right j) (bucket j))
    (j : Job) :
    (∑ q ∈ (system left right bucket B).fiber j,
      mass left right bucket B residual q) = residual j := by
  classical
  simp only [RankThreeOptionSystem.fiber, system, mass,
    Finset.sum_filter]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true, Fintype.sum_prod_type]
    have hL : (B (left j) (bucket j) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hleft j))
    have hR : (B (right j) (bucket j) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hright j))
    simp
    field_simp [hL, hR]
  · intro k _hk hkj
    simp [hkj]
  · simp

/-- Mass of one job using a fixed left extra slot.  It is zero off the
correct vertex/class fibre and otherwise equals `residual / B_left`. -/
theorem sum_mass_leftSlot_eq (residual : Job → ℝ)
    (hright : ∀ j, 0 < B (right j) (bucket j))
    (j : Job) (s : ExtraSlot Vertex Class B) :
    (∑ q ∈ (system left right bucket B).fiber j,
      if leftSlot left right bucket B q = s then
        mass left right bucket B residual q else 0) =
      if s.1 = (left j, bucket j) then
        residual j / B (left j) (bucket j) else 0 := by
  classical
  simp only [RankThreeOptionSystem.fiber, system, leftSlot, mass,
    Finset.sum_filter]
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · simp only [ite_true, Fintype.sum_prod_type]
    by_cases hs : s.1 = (left j, bucket j)
    · rw [if_pos hs]
      rcases s with ⟨vh, i⟩
      dsimp at hs
      subst vh
      simp
      have hR : (B (right j) (bucket j) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt (hright j)
      field_simp [hR]
    · rw [if_neg hs]
      rcases s with ⟨vh, i⟩
      dsimp at hs
      have hne : ∀ x : Fin (B (left j) (bucket j)),
          (⟨(left j, bucket j), x⟩ : ExtraSlot Vertex Class B) ≠
            ⟨vh, i⟩ := by
        intro x heq
        exact hs (congrArg Sigma.fst heq).symm
      simp [hne]
  · intro k _hk hkj
    simp [hkj]
  · simp

/-- Right-end analogue of `sum_mass_leftSlot_eq`. -/
theorem sum_mass_rightSlot_eq (residual : Job → ℝ)
    (hleft : ∀ j, 0 < B (left j) (bucket j))
    (j : Job) (s : ExtraSlot Vertex Class B) :
    (∑ q ∈ (system left right bucket B).fiber j,
      if rightSlot left right bucket B q = s then
        mass left right bucket B residual q else 0) =
      if s.1 = (right j, bucket j) then
        residual j / B (right j) (bucket j) else 0 := by
  classical
  simp only [RankThreeOptionSystem.fiber, system, rightSlot, mass,
    Finset.sum_filter]
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · simp only [ite_true, Fintype.sum_prod_type]
    by_cases hs : s.1 = (right j, bucket j)
    · rw [if_pos hs]
      rcases s with ⟨vh, i⟩
      dsimp at hs
      subst vh
      simp
      have hL : (B (left j) (bucket j) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt (hleft j)
      field_simp [hL]
    · rw [if_neg hs]
      rcases s with ⟨vh, i⟩
      dsimp at hs
      have hne : ∀ x : Fin (B (right j) (bucket j)),
          (⟨(right j, bucket j), x⟩ : ExtraSlot Vertex Class B) ≠
            ⟨vh, i⟩ := by
        intro x heq
        exact hs (congrArg Sigma.fst heq).symm
      simp [hne]
  · intro k _hk hkj
    simp [hkj]
  · simp

/-- A fixed extra slot receives at most the sum of the two endpoint shares
of one job.  The inequality also covers the degenerate case in which the
two endpoint slot labels coincide. -/
theorem sum_mass_using_slot_fiber_le (residual : Job → ℝ)
    (hresidual : ∀ j, 0 ≤ residual j)
    (hleft : ∀ j, 0 < B (left j) (bucket j))
    (hright : ∀ j, 0 < B (right j) (bucket j))
    (j : Job) (s : ExtraSlot Vertex Class B) :
    (∑ q ∈ (system left right bucket B).fiber j,
      if s ∈ (system left right bucket B).slots q then
        mass left right bucket B residual q else 0) ≤
      (if s.1 = (left j, bucket j) then
          residual j / B (left j) (bucket j) else 0) +
        if s.1 = (right j, bucket j) then
          residual j / B (right j) (bucket j) else 0 := by
  classical
  calc
    (∑ q ∈ (system left right bucket B).fiber j,
        if s ∈ (system left right bucket B).slots q then
          mass left right bucket B residual q else 0) ≤
      ∑ q ∈ (system left right bucket B).fiber j,
        ((if leftSlot left right bucket B q = s then
            mass left right bucket B residual q else 0) +
          if rightSlot left right bucket B q = s then
            mass left right bucket B residual q else 0) := by
      apply Finset.sum_le_sum
      intro q _hq
      by_cases hl : s = leftSlot left right bucket B q <;>
        by_cases hr : s = rightSlot left right bucket B q
      all_goals
        have hm := mass_nonneg left right bucket B residual hresidual q
        by_cases hlr : leftSlot left right bucket B q =
            rightSlot left right bucket B q <;>
          simp [system, hl, hr, hlr, eq_comm, hm]
    _ = (∑ q ∈ (system left right bucket B).fiber j,
          if leftSlot left right bucket B q = s then
            mass left right bucket B residual q else 0) +
        ∑ q ∈ (system left right bucket B).fiber j,
          if rightSlot left right bucket B q = s then
            mass left right bucket B residual q else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (if s.1 = (left j, bucket j) then
          residual j / B (left j) (bucket j) else 0) +
        if s.1 = (right j, bucket j) then
          residual j / B (right j) (bucket j) else 0 := by
      rw [sum_mass_leftSlot_eq left right bucket B residual hright j s,
        sum_mass_rightSlot_eq left right bucket B residual hleft j s]

/-- If a job's two endpoints are distinct, one concrete extra slot can occur
at only one end.  Thus its job--slot mass is bounded by one endpoint share,
with no factor two. -/
theorem sum_mass_using_slot_fiber_le_oneEndpoint (residual : Job → ℝ)
    (hresidual : ∀ j, 0 ≤ residual j)
    (hleft : ∀ j, 0 < B (left j) (bucket j))
    (hright : ∀ j, 0 < B (right j) (bucket j))
    (hne : ∀ j, left j ≠ right j)
    (j : Job) (s : ExtraSlot Vertex Class B) :
    (∑ q ∈ (system left right bucket B).fiber j,
      if s ∈ (system left right bucket B).slots q then
        mass left right bucket B residual q else 0) ≤
      if s.1 = (left j, bucket j) then
        residual j / B (left j) (bucket j)
      else if s.1 = (right j, bucket j) then
        residual j / B (right j) (bucket j) else 0 := by
  have hbase := sum_mass_using_slot_fiber_le left right bucket B residual
    hresidual hleft hright j s
  by_cases hl : s.1 = (left j, bucket j)
  · have hr : s.1 ≠ (right j, bucket j) := by
      intro hs
      exact hne j (congrArg Prod.fst (hl.symm.trans hs))
    simpa [hl, hne j] using hbase
  · by_cases hr : s.1 = (right j, bucket j)
    · simpa [hr, (hne j).symm] using hbase
    · simpa [hl, hr] using hbase

/-- Floor replication preserves the preceding one-endpoint job--slot bound. -/
theorem quantized_jobSlotCodegree_upper_oneEndpoint (residual : Job → ℝ)
    (hresidual : ∀ j, 0 ≤ residual j)
    (hleft : ∀ j, 0 < B (left j) (bucket j))
    (hright : ∀ j, 0 < B (right j) (bucket j))
    (hne : ∀ j, left j ≠ right j)
    (N : ℕ) (j : Job) (s : ExtraSlot Vertex Class B) :
    (((system left right bucket B).quantized N
        (mass left right bucket B residual)).jobSlotCodegree j s : ℝ) ≤
      (N : ℝ) *
        (if s.1 = (left j, bucket j) then
          residual j / B (left j) (bucket j)
        else if s.1 = (right j, bucket j) then
          residual j / B (right j) (bucket j) else 0) := by
  have hquant := (system left right bucket B).quantizedJobSlotCodegree_upper
    N (mass left right bucket B residual) j s
    (fun q _ ↦ mass_nonneg left right bucket B residual hresidual q)
  have hrewrite :
      (∑ q, if (system left right bucket B).owner q = j ∧
          s ∈ (system left right bucket B).slots q then
          mass left right bucket B residual q else 0) =
        ∑ q ∈ (system left right bucket B).fiber j,
          if s ∈ (system left right bucket B).slots q then
            mass left right bucket B residual q else 0 := by
    classical
    simp only [RankThreeOptionSystem.fiber, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hj : (system left right bucket B).owner q = j <;>
      by_cases hs : s ∈ (system left right bucket B).slots q <;> simp [hj, hs]
  rw [hrewrite] at hquant
  exact hquant.trans (mul_le_mul_of_nonneg_left
    (sum_mass_using_slot_fiber_le_oneEndpoint left right bucket B residual
      hresidual hleft hright hne j s) (Nat.cast_nonneg N))

/-- A sum over all Cartesian choices can be partitioned exactly by job. -/
theorem sum_eq_sum_fiber
    (f : ExtraSlotChoice Job Vertex Class left right bucket B → ℝ) :
    (∑ q, f q) =
      ∑ j, ∑ q ∈ (system left right bucket B).fiber j, f q := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [RankThreeOptionSystem.fiber, system, Finset.sum_filter]
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · simp
  · intro k _hk hkj
    simp [hkj]
  · simp

/-- Total fractional load of an extra slot, written in the endpoint-share
form used to choose the numbers of counting slots. -/
theorem sum_mass_using_slot_le (residual : Job → ℝ)
    (hresidual : ∀ j, 0 ≤ residual j)
    (hleft : ∀ j, 0 < B (left j) (bucket j))
    (hright : ∀ j, 0 < B (right j) (bucket j))
    (s : ExtraSlot Vertex Class B) :
    (∑ q, if s ∈ (system left right bucket B).slots q then
        mass left right bucket B residual q else 0) ≤
      ∑ j,
        ((if s.1 = (left j, bucket j) then
            residual j / B (left j) (bucket j) else 0) +
          if s.1 = (right j, bucket j) then
            residual j / B (right j) (bucket j) else 0) := by
  rw [sum_eq_sum_fiber left right bucket B]
  exact Finset.sum_le_sum fun j _hj ↦
    sum_mass_using_slot_fiber_le left right bucket B residual hresidual
      hleft hright j s

/-- The same endpoint-share expression bounds the degree after integer
replication. -/
theorem quantized_slotDegree_upper (residual : Job → ℝ)
    (hresidual : ∀ j, 0 ≤ residual j)
    (hleft : ∀ j, 0 < B (left j) (bucket j))
    (hright : ∀ j, 0 < B (right j) (bucket j))
    (N : ℕ) (s : ExtraSlot Vertex Class B) :
    (((system left right bucket B).quantized N
        (mass left right bucket B residual)).slotDegree s : ℕ) ≤
      (N : ℝ) * ∑ j,
        ((if s.1 = (left j, bucket j) then
            residual j / B (left j) (bucket j) else 0) +
          if s.1 = (right j, bucket j) then
            residual j / B (right j) (bucket j) else 0) := by
  have hquant := (system left right bucket B).quantizedSlotDegree_upper N
    (mass left right bucket B residual) s
    (fun o _ho ↦ mass_nonneg left right bucket B residual hresidual o)
  have hfrac := sum_mass_using_slot_le left right bucket B residual
    hresidual hleft hright s
  exact hquant.trans (mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg N))

/-- Number of base leave-uncoloured options owned by one job. -/
theorem fiber_card
    (j : Job) :
    ((system left right bucket B).fiber j).card =
      B (left j) (bucket j) * B (right j) (bucket j) := by
  classical
  rw [show ((system left right bucket B).fiber j).card =
      Fintype.card {q : ExtraSlotChoice Job Vertex Class left right bucket B //
        (system left right bucket B).owner q = j} by
    rw [Fintype.card_subtype]
    rfl]
  let E :
      {q : ExtraSlotChoice Job Vertex Class left right bucket B //
        (system left right bucket B).owner q = j} ≃
      Fin (B (left j) (bucket j)) × Fin (B (right j) (bucket j)) :=
    {
      toFun := fun q ↦ by
        rcases q with ⟨⟨k, a, b⟩, hk⟩
        change k = j at hk
        subst k
        exact (a, b)
      invFun := fun ab ↦ ⟨⟨j, ab⟩, rfl⟩
      left_inv := by
        intro q
        rcases q with ⟨⟨k, a, b⟩, hk⟩
        change k = j at hk
        subst k
        rfl
      right_inv := by intro ab; rfl
    }
  calc
    Fintype.card {q : ExtraSlotChoice Job Vertex Class left right bucket B //
        (system left right bucket B).owner q = j} =
        Fintype.card
          (Fin (B (left j) (bucket j)) × Fin (B (right j) (bucket j))) :=
      Fintype.card_congr E
    _ = B (left j) (bucket j) * B (right j) (bucket j) := by simp

/-- Taking floors loses fewer copies than the size of the endpoint Cartesian
grid.  This is the `O(B_u B_v)` job-degree loss used in the large-edge
matching construction. -/
theorem quantizedJobDegree_lower
    (residual : Job → ℝ)
    (hleft : ∀ j, 0 < B (left j) (bucket j))
    (hright : ∀ j, 0 < B (right j) (bucket j))
    (N : ℕ) (j : Job) :
    (N : ℝ) * residual j -
        (B (left j) (bucket j) * B (right j) (bucket j) : ℕ) ≤
      ((system left right bucket B).quantizedJobDegree N
        (mass left right bucket B residual) j : ℝ) := by
  have h := (system left right bucket B).quantizedJobDegree_lower N
    (mass left right bucket B residual) j
  rw [sum_mass_fiber left right bucket B residual hleft hright j,
    fiber_card left right bucket B j] at h
  simpa using h

end ExtraSlotChoice

end

end WeightedEdgeColoring
