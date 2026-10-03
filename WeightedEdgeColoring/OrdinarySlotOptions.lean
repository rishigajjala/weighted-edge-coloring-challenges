import WeightedEdgeColoring.OptionSystemSum

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# Ordinary two-endpoint slot choices

Once one profile has been fixed at every vertex and colour, an ordinary
large-edge option consists of a colour, one numbered place at the left
endpoint, and one numbered place at the right endpoint.  Profiles are padded
to a common number `K` of places, so zero-size or otherwise inadmissible
places can simply be assigned mass zero.

This file constructs that finite option system and proves the exact fibre and
slot-load identities used before integer replication.  It is deliberately
independent of how the option masses were obtained.
-/

noncomputable section

universe u v w

/-- A numbered ordinary place in the selected profile at `(vertex, colour)`. -/
structure OrdinarySlot (Vertex : Type v) (Color : Type w) (K : ℕ) where
  vertex : Vertex
  color : Color
  place : Fin K
deriving Fintype, DecidableEq

/-- One colour and one endpoint place at each end of a job. -/
structure OrdinarySlotChoice (Job : Type u) (Color : Type w) (K : ℕ) where
  job : Job
  color : Color
  leftPlace : Fin K
  rightPlace : Fin K
deriving Fintype, DecidableEq

namespace OrdinarySlotChoice

variable {Job : Type u} {Vertex : Type v} {Color : Type w}
  [Fintype Job] [Fintype Vertex] [Fintype Color]
  [DecidableEq Job] [DecidableEq Vertex] [DecidableEq Color]

variable (left right : Job → Vertex) (K : ℕ)

/-- The concrete place used at the left endpoint. -/
def leftSlot (q : OrdinarySlotChoice Job Color K) :
    OrdinarySlot Vertex Color K :=
  ⟨left q.job, q.color, q.leftPlace⟩

/-- The concrete place used at the right endpoint. -/
def rightSlot (q : OrdinarySlotChoice Job Color K) :
    OrdinarySlot Vertex Color K :=
  ⟨right q.job, q.color, q.rightPlace⟩

/-- Ordinary choices form a rank-three option system: one job and at most two
concrete endpoint slots. -/
def system : RankThreeOptionSystem Job (OrdinarySlot Vertex Color K)
    (OrdinarySlotChoice Job Color K) where
  owner q := q.job
  slots q := {leftSlot left K q, rightSlot right K q}
  slots_card_le_two q := (Finset.card_insert_le _ _).trans (by simp)

/-- Read a four-index fractional array as a mass on ordinary choices. -/
def mass (x : Job → Color → Fin K → Fin K → ℝ)
    (q : OrdinarySlotChoice Job Color K) : ℝ :=
  x q.job q.color q.leftPlace q.rightPlace

theorem mass_nonneg (x : Job → Color → Fin K → Fin K → ℝ)
    (hx : ∀ j c i k, 0 ≤ x j c i k) :
    ∀ q : OrdinarySlotChoice Job Color K, 0 ≤ mass K x q := by
  intro q
  exact hx q.job q.color q.leftPlace q.rightPlace

/-- Summing the options in one job fibre is just summing its colour and
endpoint-place array. -/
theorem sum_mass_fiber (x : Job → Color → Fin K → Fin K → ℝ) (j : Job) :
    (∑ q ∈ (system left right K).fiber j, mass K x q) =
      ∑ c, ∑ i, ∑ k, x j c i k := by
  classical
  simp only [RankThreeOptionSystem.fiber, system, mass, Finset.sum_filter]
  rw [show (∑ q : OrdinarySlotChoice Job Color K,
      if q.job = j then x q.job q.color q.leftPlace q.rightPlace else 0) =
      ∑ a : Job × Color × Fin K × Fin K,
        if a.1 = j then x a.1 a.2.1 a.2.2.1 a.2.2.2 else 0 by
    let E : OrdinarySlotChoice Job Color K ≃ Job × Color × Fin K × Fin K :=
      { toFun := fun q ↦ (q.job, q.color, q.leftPlace, q.rightPlace)
        invFun := fun a ↦ ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩
        left_inv := by intro q; cases q; rfl
        right_inv := by intro a; rcases a with ⟨j, c, i, k⟩; rfl }
    exact Fintype.sum_equiv E _ _ (fun _ ↦ rfl)]
  simp only [Fintype.sum_prod_type]
  simp

/-- Restricting one job fibre to one colour leaves precisely the two-place
sum for that colour. -/
theorem sum_mass_fiber_color (x : Job → Color → Fin K → Fin K → ℝ)
    (j : Job) (c : Color) :
    (∑ q ∈ (system left right K).fiber j,
      if q.color = c then mass K x q else 0) =
      ∑ i, ∑ k, x j c i k := by
  classical
  simp only [RankThreeOptionSystem.fiber, system, mass, Finset.sum_filter]
  rw [show (∑ q : OrdinarySlotChoice Job Color K,
      if q.job = j then
        (if q.color = c then x q.job q.color q.leftPlace q.rightPlace else 0)
      else 0) =
      ∑ a : Job × Color × Fin K × Fin K,
        if a.1 = j then
          (if a.2.1 = c then x a.1 a.2.1 a.2.2.1 a.2.2.2 else 0)
        else 0 by
    let E : OrdinarySlotChoice Job Color K ≃ Job × Color × Fin K × Fin K :=
      { toFun := fun q ↦ (q.job, q.color, q.leftPlace, q.rightPlace)
        invFun := fun a ↦ ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩
        left_inv := by intro q; cases q; rfl
        right_inv := by intro a; rcases a with ⟨j, c, i, k⟩; rfl }
    exact Fintype.sum_equiv E _ _ (fun _ ↦ rfl)]
  simp only [Fintype.sum_prod_type]
  simp

/-- Mass of the choices of one job that use a fixed slot as their left
endpoint place. -/
theorem sum_mass_leftSlot_eq (x : Job → Color → Fin K → Fin K → ℝ)
    (j : Job) (s : OrdinarySlot Vertex Color K) :
    (∑ q ∈ (system left right K).fiber j,
      if leftSlot left K q = s then mass K x q else 0) =
      if s.vertex = left j then
        ∑ k, x j s.color s.place k else 0 := by
  classical
  rcases s with ⟨v, c, i⟩
  simp only [RankThreeOptionSystem.fiber, system, leftSlot, mass,
    Finset.sum_filter]
  rw [show (∑ q : OrdinarySlotChoice Job Color K,
      if q.job = j then
        (if (⟨left q.job, q.color, q.leftPlace⟩ :
            OrdinarySlot Vertex Color K) = ⟨v, c, i⟩ then
          x q.job q.color q.leftPlace q.rightPlace else 0)
      else 0) =
      ∑ a : Job × Color × Fin K × Fin K,
        if a.1 = j then
          (if (⟨left a.1, a.2.1, a.2.2.1⟩ :
              OrdinarySlot Vertex Color K) = ⟨v, c, i⟩ then
            x a.1 a.2.1 a.2.2.1 a.2.2.2 else 0)
        else 0 by
    let E : OrdinarySlotChoice Job Color K ≃ Job × Color × Fin K × Fin K :=
      { toFun := fun q ↦ (q.job, q.color, q.leftPlace, q.rightPlace)
        invFun := fun a ↦ ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩
        left_inv := by intro q; cases q; rfl
        right_inv := by intro a; rcases a with ⟨j, c, i, k⟩; rfl }
    exact Fintype.sum_equiv E _ _ (fun _ ↦ rfl)]
  by_cases hv : v = left j
  · subst v
    simp only [Fintype.sum_prod_type, OrdinarySlot.mk.injEq]
    simp_rw [ite_and]
    simp
  · have hv' : left j ≠ v := Ne.symm hv
    simp only [Fintype.sum_prod_type, OrdinarySlot.mk.injEq]
    simp_rw [ite_and]
    simp [hv, hv']

/-- Right-end analogue of `sum_mass_leftSlot_eq`. -/
theorem sum_mass_rightSlot_eq (x : Job → Color → Fin K → Fin K → ℝ)
    (j : Job) (s : OrdinarySlot Vertex Color K) :
    (∑ q ∈ (system left right K).fiber j,
      if rightSlot right K q = s then mass K x q else 0) =
      if s.vertex = right j then
        ∑ i, x j s.color i s.place else 0 := by
  classical
  rcases s with ⟨v, c, k⟩
  simp only [RankThreeOptionSystem.fiber, system, rightSlot, mass,
    Finset.sum_filter]
  rw [show (∑ q : OrdinarySlotChoice Job Color K,
      if q.job = j then
        (if (⟨right q.job, q.color, q.rightPlace⟩ :
            OrdinarySlot Vertex Color K) = ⟨v, c, k⟩ then
          x q.job q.color q.leftPlace q.rightPlace else 0)
      else 0) =
      ∑ a : Job × Color × Fin K × Fin K,
        if a.1 = j then
          (if (⟨right a.1, a.2.1, a.2.2.2⟩ :
              OrdinarySlot Vertex Color K) = ⟨v, c, k⟩ then
            x a.1 a.2.1 a.2.2.1 a.2.2.2 else 0)
        else 0 by
    let E : OrdinarySlotChoice Job Color K ≃ Job × Color × Fin K × Fin K :=
      { toFun := fun q ↦ (q.job, q.color, q.leftPlace, q.rightPlace)
        invFun := fun a ↦ ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩
        left_inv := by intro q; cases q; rfl
        right_inv := by intro a; rcases a with ⟨j, c, i, k⟩; rfl }
    exact Fintype.sum_equiv E _ _ (fun _ ↦ rfl)]
  by_cases hv : v = right j
  · subst v
    simp only [Fintype.sum_prod_type, OrdinarySlot.mk.injEq]
    simp_rw [ite_and]
    simp
  · have hv' : right j ≠ v := Ne.symm hv
    simp only [Fintype.sum_prod_type, OrdinarySlot.mk.injEq]
    simp_rw [ite_and]
    simp [hv, hv']

/-- A fixed concrete slot receives at most the sum of its left- and
right-end contributions from one job.  This weak form remains true even if
the two endpoint labels coincide. -/
theorem sum_mass_using_slot_fiber_le
    (x : Job → Color → Fin K → Fin K → ℝ)
    (hx : ∀ j c i k, 0 ≤ x j c i k)
    (j : Job) (s : OrdinarySlot Vertex Color K) :
    (∑ q ∈ (system left right K).fiber j,
      if s ∈ (system left right K).slots q then mass K x q else 0) ≤
      (if s.vertex = left j then ∑ k, x j s.color s.place k else 0) +
      (if s.vertex = right j then ∑ i, x j s.color i s.place else 0) := by
  classical
  calc
    (∑ q ∈ (system left right K).fiber j,
        if s ∈ (system left right K).slots q then mass K x q else 0) ≤
      ∑ q ∈ (system left right K).fiber j,
        ((if leftSlot left K q = s then mass K x q else 0) +
          if rightSlot right K q = s then mass K x q else 0) := by
      apply Finset.sum_le_sum
      intro q _hq
      have hm : 0 ≤ mass K x q := mass_nonneg K x hx q
      by_cases hl : s = leftSlot left K q <;>
        by_cases hr : s = rightSlot right K q
      all_goals
        by_cases hlr : leftSlot left K q = rightSlot right K q <;>
          simp [system, hl, hr, hlr, eq_comm, hm]
    _ = (∑ q ∈ (system left right K).fiber j,
          if leftSlot left K q = s then mass K x q else 0) +
        ∑ q ∈ (system left right K).fiber j,
          if rightSlot right K q = s then mass K x q else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (if s.vertex = left j then ∑ k, x j s.color s.place k else 0) +
        (if s.vertex = right j then ∑ i, x j s.color i s.place else 0) := by
      rw [sum_mass_leftSlot_eq left right K x j s,
        sum_mass_rightSlot_eq left right K x j s]

/-- When the two endpoint labels of every job are distinct, the mass of one
job using one concrete slot is at most that job's total mass in the slot's
colour.  This is the fractional job--slot codegree estimate. -/
theorem sum_mass_using_slot_fiber_le_colorTotal
    (x : Job → Color → Fin K → Fin K → ℝ)
    (hx : ∀ j c i k, 0 ≤ x j c i k)
    (hne : ∀ j, left j ≠ right j)
    (j : Job) (s : OrdinarySlot Vertex Color K) :
    (∑ q ∈ (system left right K).fiber j,
      if s ∈ (system left right K).slots q then mass K x q else 0) ≤
      ∑ i, ∑ k, x j s.color i k := by
  have hbase := sum_mass_using_slot_fiber_le left right K x hx j s
  have hrow : (∑ k, x j s.color s.place k) ≤
      ∑ i, ∑ k, x j s.color i k := by
    exact Finset.single_le_sum
      (fun i _ ↦ Finset.sum_nonneg fun k _ ↦ hx j s.color i k)
      (Finset.mem_univ s.place)
  have hcol : (∑ i, x j s.color i s.place) ≤
      ∑ i, ∑ k, x j s.color i k := by
    exact Finset.sum_le_sum fun i _ ↦
      Finset.single_le_sum (fun k _ ↦ hx j s.color i k)
        (Finset.mem_univ s.place)
  by_cases hl : s.vertex = left j
  · have hr : s.vertex ≠ right j := by
      intro hs
      exact hne j (hl.symm.trans hs)
    have hbase' :
        (∑ q ∈ (system left right K).fiber j,
          if s ∈ (system left right K).slots q then mass K x q else 0) ≤
          ∑ k, x j s.color s.place k := by
      simpa [hl, hne j] using hbase
    exact hbase'.trans hrow
  · by_cases hr : s.vertex = right j
    · have hbase' :
          (∑ q ∈ (system left right K).fiber j,
            if s ∈ (system left right K).slots q then mass K x q else 0) ≤
            ∑ i, x j s.color i s.place := by
        simpa [hr, (hne j).symm] using hbase
      exact hbase'.trans hcol
    · have htotal : 0 ≤ ∑ i, ∑ k, x j s.color i k :=
        Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun k _ ↦
          hx j s.color i k
      exact hbase.trans (by simpa [hl, hr] using htotal)

/-- After floor replication, the job--slot codegree is at most `N` times
the total mass of that job in the slot's colour. -/
theorem quantized_jobSlotCodegree_upper_colorTotal
    (x : Job → Color → Fin K → Fin K → ℝ)
    (hx : ∀ j c i k, 0 ≤ x j c i k)
    (hne : ∀ j, left j ≠ right j)
    (N : ℕ) (j : Job) (s : OrdinarySlot Vertex Color K) :
    (((system left right K).quantized N (mass K x)).jobSlotCodegree j s : ℝ) ≤
      (N : ℝ) * ∑ i, ∑ k, x j s.color i k := by
  have hquant := (system left right K).quantizedJobSlotCodegree_upper
    N (mass K x) j s (fun q _ ↦ mass_nonneg K x hx q)
  have hrewrite :
      (∑ q, if (system left right K).owner q = j ∧
          s ∈ (system left right K).slots q then mass K x q else 0) =
        ∑ q ∈ (system left right K).fiber j,
          if s ∈ (system left right K).slots q then mass K x q else 0 := by
    classical
    simp only [RankThreeOptionSystem.fiber, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hj : (system left right K).owner q = j <;>
      by_cases hs : s ∈ (system left right K).slots q <;> simp [hj, hs]
  rw [hrewrite] at hquant
  exact hquant.trans (mul_le_mul_of_nonneg_left
    (sum_mass_using_slot_fiber_le_colorTotal left right K x hx hne j s)
    (Nat.cast_nonneg N))

/-- A sum over all ordinary choices partitions exactly by owner. -/
theorem sum_eq_sum_fiber
    (f : OrdinarySlotChoice Job Color K → ℝ) :
    (∑ q, f q) =
      ∑ j, ∑ q ∈ (system left right K).fiber j, f q := by
  classical
  symm
  calc
    (∑ j, ∑ q ∈ (system left right K).fiber j, f q) =
        ∑ j, ∑ q, if (system left right K).owner q = j then f q else 0 := by
      simp only [RankThreeOptionSystem.fiber, Finset.sum_filter]
    _ = ∑ q, ∑ j, if (system left right K).owner q = j then f q else 0 :=
      Finset.sum_comm
    _ = ∑ q, f q := by simp

/-- Total fractional load of a concrete ordinary slot, expressed through
the endpoint arrays of the jobs incident with it. -/
theorem sum_mass_using_slot_le
    (x : Job → Color → Fin K → Fin K → ℝ)
    (hx : ∀ j c i k, 0 ≤ x j c i k)
    (s : OrdinarySlot Vertex Color K) :
    (∑ q, if s ∈ (system left right K).slots q then mass K x q else 0) ≤
      ∑ j,
        ((if s.vertex = left j then ∑ k, x j s.color s.place k else 0) +
          if s.vertex = right j then ∑ i, x j s.color i s.place else 0) := by
  rw [sum_eq_sum_fiber left right K]
  exact Finset.sum_le_sum fun j _ ↦
    sum_mass_using_slot_fiber_le left right K x hx j s

/-- The copied degree of a concrete ordinary slot is bounded by `N` times
the corresponding endpoint-array load. -/
theorem quantized_slotDegree_upper
    (x : Job → Color → Fin K → Fin K → ℝ)
    (hx : ∀ j c i k, 0 ≤ x j c i k)
    (N : ℕ) (s : OrdinarySlot Vertex Color K) :
    (((system left right K).quantized N (mass K x)).slotDegree s : ℝ) ≤
      (N : ℝ) * ∑ j,
        ((if s.vertex = left j then ∑ k, x j s.color s.place k else 0) +
          if s.vertex = right j then ∑ i, x j s.color i s.place else 0) := by
  have hquant := (system left right K).quantizedSlotDegree_upper N (mass K x) s
    (fun q _ ↦ mass_nonneg K x hx q)
  exact hquant.trans (mul_le_mul_of_nonneg_left
    (sum_mass_using_slot_le left right K x hx s) (Nat.cast_nonneg N))

/-- The number of base ordinary choices owned by one job is exactly
`|Color| * K^2`. -/
theorem fiber_card (j : Job) :
    ((system (Job := Job) (Vertex := Vertex) (Color := Color)
      left right K).fiber j).card = Fintype.card Color * K * K := by
  classical
  rw [show ((system left right K).fiber j).card =
      Fintype.card {q : OrdinarySlotChoice Job Color K //
        (system left right K).owner q = j} by
    rw [Fintype.card_subtype]
    rfl]
  let E :
      {q : OrdinarySlotChoice Job Color K //
        (system left right K).owner q = j} ≃ Color × Fin K × Fin K :=
    { toFun := fun q ↦ (q.1.color, q.1.leftPlace, q.1.rightPlace)
      invFun := fun a ↦ ⟨⟨j, a.1, a.2.1, a.2.2⟩, rfl⟩
      left_inv := by
        intro q
        rcases q with ⟨⟨k, c, i, l⟩, hk⟩
        change k = j at hk
        subst k
        rfl
      right_inv := by intro a; rcases a with ⟨c, i, k⟩; rfl }
  calc
    Fintype.card {q : OrdinarySlotChoice Job Color K //
        (system left right K).owner q = j} =
        Fintype.card (Color × Fin K × Fin K) := Fintype.card_congr E
    _ = Fintype.card Color * K * K := by simp [Nat.mul_assoc]

/-- Taking integer parts loses fewer than `|Color| * K^2` copies from one
job. -/
theorem quantizedJobDegree_lower
    (x : Job → Color → Fin K → Fin K → ℝ)
    (N : ℕ) (j : Job) :
    (N : ℝ) * (∑ c, ∑ i, ∑ k, x j c i k) -
        (Fintype.card Color * K * K : ℕ) ≤
      ((system left right K).quantizedJobDegree N (mass K x) j : ℝ) := by
  have h := (system left right K).quantizedJobDegree_lower N (mass K x) j
  rw [sum_mass_fiber left right K x j, fiber_card left right K j] at h
  simpa using h

end OrdinarySlotChoice

end

end WeightedEdgeColoring
