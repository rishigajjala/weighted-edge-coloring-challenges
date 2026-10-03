import WeightedEdgeColoring.PairUniqueOptions
import WeightedEdgeColoring.GraphExtraSlotBudget

open scoped BigOperators

namespace WeightedEdgeColoring

/-!
# Linearly many coupled extra choices

The older extra-option family independently chose one counting slot at each
endpoint.  Thus a job had `t^2` extra choices even when both endpoint
marginals were uniform on `t` slots.  Here the two choices are coupled by one
common cyclic index.  A job has only `t` extra choices, while every endpoint
slot still receives exactly a `1/t` share of its residual mass.

This is the scale needed by the isolated nibble: floor quantization loses
only `O(t)` copies from a job and both job--slot and slot--pair codegrees are
`O(N/t)`.
-/

noncomputable section

universe u v w

/-- A uniform extra slot, indexed by a vertex, a weight class, and one point
of the common cyclic set `Fin t`. -/
structure CyclicExtraSlot (Vertex : Type v) (Class : Type w) (t : ℕ) where
  vertex : Vertex
  bucket : Class
  index : Fin t
deriving Fintype, DecidableEq

/-- One coupled extra choice for each job and cyclic index. -/
abbrev CyclicExtraChoice (Job : Type u) (t : ℕ) := Job × Fin t

namespace CyclicExtraChoice

variable {Job : Type u} {Vertex : Type v} {Class : Type w}
  [Fintype Job] [Fintype Vertex] [Fintype Class]
  [DecidableEq Job] [DecidableEq Vertex] [DecidableEq Class]

variable (left right : Job → Vertex) (bucket : Job → Class) (t : ℕ)

/-- The left endpoint slot of a coupled choice. -/
def leftSlot (q : CyclicExtraChoice Job t) :
    CyclicExtraSlot Vertex Class t :=
  ⟨left q.1, bucket q.1, q.2⟩

/-- The right endpoint slot of a coupled choice.  The identity permutation
is used; replacing it by any job-dependent cyclic shift gives the same
marginals and all the same estimates. -/
def rightSlot (q : CyclicExtraChoice Job t) :
    CyclicExtraSlot Vertex Class t :=
  ⟨right q.1, bucket q.1, q.2⟩

/-- Every coupled choice owns its job and uses its two endpoint slots. -/
def system : RankThreeOptionSystem Job (CyclicExtraSlot Vertex Class t)
    (CyclicExtraChoice Job t) where
  owner q := q.1
  slots q := {leftSlot left bucket t q,
    rightSlot right bucket t q}
  slots_card_le_two q := (Finset.card_insert_le _ _).trans (by simp)

/-- Split the residual mass uniformly over the common cyclic index. -/
def mass (residual : Job → ℝ) (q : CyclicExtraChoice Job t) : ℝ :=
  residual q.1 / t

theorem mass_nonneg (residual : Job → ℝ)
    (hresidual : ∀ j, 0 ≤ residual j) :
    ∀ q : CyclicExtraChoice Job t,
      0 ≤ mass t residual q := by
  intro q
  exact div_nonneg (hresidual q.1) (Nat.cast_nonneg t)

/-- The coupled options in one fibre have exactly the prescribed residual
mass. -/
theorem sum_mass_fiber (residual : Job → ℝ) (ht : 0 < t) (j : Job) :
    (∑ q ∈ (system (left := left) (right := right) (bucket := bucket) t).fiber j,
      mass t residual q) =
      residual j := by
  classical
  simp only [RankThreeOptionSystem.fiber, system, mass, Finset.sum_filter]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
  · have htR : ((t : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt ht)
    simp only [if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [htR]
  · intro k _hk hkj
    simp [hkj]
  · simp

/-- A concrete left endpoint slot receives exactly one cyclic share from a
fixed job, when its label agrees with that endpoint. -/
theorem sum_mass_leftSlot_eq (residual : Job → ℝ) (ht : 0 < t)
    (j : Job) (s : CyclicExtraSlot Vertex Class t) :
    (∑ q ∈ (system (left := left) (right := right) (bucket := bucket) t).fiber j,
      if leftSlot left bucket t q = s then mass t residual q else 0) =
      if (s.vertex, s.bucket) = (left j, bucket j) then
        residual j / t else 0 := by
  classical
  simp only [RankThreeOptionSystem.fiber, system, mass, Finset.sum_filter]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
  · by_cases hs : (s.vertex, s.bucket) = (left j, bucket j)
    · rcases s with ⟨v, h, k⟩
      simp only at hs
      have hv : v = left j := congrArg Prod.fst hs
      have hh : h = bucket j := congrArg Prod.snd hs
      subst v
      subst h
      simp [leftSlot]
    · have hne : ∀ k : Fin t,
          leftSlot left bucket t (j, k) ≠ s := by
        intro k heq
        apply hs
        exact congrArg (fun z : CyclicExtraSlot Vertex Class t ↦
          (z.vertex, z.bucket)) heq |>.symm
      simp [hs, hne]
  · intro k _hk hkj
    simp [hkj]
  · simp

/-- Right-end analogue of `sum_mass_leftSlot_eq`. -/
theorem sum_mass_rightSlot_eq (residual : Job → ℝ) (ht : 0 < t)
    (j : Job) (s : CyclicExtraSlot Vertex Class t) :
    (∑ q ∈ (system (left := left) (right := right) (bucket := bucket) t).fiber j,
      if rightSlot right bucket t q = s then mass t residual q else 0) =
      if (s.vertex, s.bucket) = (right j, bucket j) then
        residual j / t else 0 := by
  classical
  simp only [RankThreeOptionSystem.fiber, system, mass, Finset.sum_filter]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
  · by_cases hs : (s.vertex, s.bucket) = (right j, bucket j)
    · rcases s with ⟨v, h, k⟩
      simp only at hs
      have hv : v = right j := congrArg Prod.fst hs
      have hh : h = bucket j := congrArg Prod.snd hs
      subst v
      subst h
      simp [rightSlot]
    · have hne : ∀ k : Fin t,
          rightSlot right bucket t (j, k) ≠ s := by
        intro k heq
        apply hs
        exact congrArg (fun z : CyclicExtraSlot Vertex Class t ↦
          (z.vertex, z.bucket)) heq |>.symm
      simp [hs, hne]
  · intro k _hk hkj
    simp [hkj]
  · simp

/-- With distinct endpoints, a fixed slot belongs to at most one end of a
job and therefore sees at most one mass `residual/t`. -/
theorem sum_mass_using_slot_fiber_le (residual : Job → ℝ)
    (hresidual : ∀ j, 0 ≤ residual j) (ht : 0 < t)
    (hne : ∀ j, left j ≠ right j)
    (j : Job) (s : CyclicExtraSlot Vertex Class t) :
    (∑ q ∈ (system (left := left) (right := right) (bucket := bucket) t).fiber j,
      if s ∈ (system (left := left) (right := right) (bucket := bucket) t).slots q then
        mass t residual q else 0) ≤
      if (s.vertex, s.bucket) = (left j, bucket j) then residual j / t
      else if (s.vertex, s.bucket) = (right j, bucket j) then
        residual j / t else 0 := by
  classical
  calc
    _ ≤ ∑ q ∈ (system (left := left) (right := right) (bucket := bucket) t).fiber j,
        ((if leftSlot left bucket t q = s then mass t residual q else 0) +
          if rightSlot right bucket t q = s then mass t residual q else 0) := by
      apply Finset.sum_le_sum
      intro q _hq
      have hm := mass_nonneg t residual hresidual q
      simp only [system, Finset.mem_insert, Finset.mem_singleton]
      by_cases hl : leftSlot left bucket t q = s
      · simp [hl]
        split_ifs <;> linarith
      · by_cases hr : rightSlot right bucket t q = s
        · simp [hl, hr, hm]
        · have hls : ¬s = leftSlot left bucket t q := fun hs ↦ hl hs.symm
          have hrs : ¬s = rightSlot right bucket t q := fun hs ↦ hr hs.symm
          simp [hl, hr, hls, hrs]
    _ = (if (s.vertex, s.bucket) = (left j, bucket j) then
          residual j / t else 0) +
        (if (s.vertex, s.bucket) = (right j, bucket j) then
          residual j / t else 0) := by
      rw [Finset.sum_add_distrib,
        sum_mass_leftSlot_eq (left := left) (right := right)
          (bucket := bucket) (t := t) residual ht j s,
        sum_mass_rightSlot_eq (left := left) (right := right)
          (bucket := bucket) (t := t) residual ht j s]
    _ = _ := by
      by_cases hl : (s.vertex, s.bucket) = (left j, bucket j)
      · have hr : (s.vertex, s.bucket) ≠ (right j, bucket j) := by
          intro hs
          exact hne j (congrArg Prod.fst (hl.symm.trans hs))
        rw [if_pos hl, if_neg hr, if_pos hl]
        simp
      · by_cases hr : (s.vertex, s.bucket) = (right j, bucket j)
        · rw [if_neg hl, if_pos hr, if_neg hl]
          simp
        · rw [if_neg hl, if_neg hr, if_neg hl]
          simp

/-- Quantization preserves the `N/t` job--slot estimate. -/
theorem quantized_jobSlotCodegree_le (residual : Job → ℝ)
    (hresidual : ∀ j, 0 ≤ residual j) (ht : 0 < t)
    (hresidual_one : ∀ j, residual j ≤ 1)
    (hne : ∀ j, left j ≠ right j)
    (N : ℕ) (j : Job) (s : CyclicExtraSlot Vertex Class t) :
    (((system (left := left) (right := right) (bucket := bucket) t).quantized N
      (mass t residual)).jobSlotCodegree
      j s : ℝ) ≤ (N : ℝ) / t := by
  have hquant := (system (left := left) (right := right) (bucket := bucket) t).quantizedJobSlotCodegree_upper
    N (mass t residual) j s
    (fun q _ ↦ mass_nonneg t residual hresidual q)
  have hrewrite :
      (∑ q, if (system (left := left) (right := right) (bucket := bucket) t).owner q = j ∧
          s ∈ (system (left := left) (right := right) (bucket := bucket) t).slots q then
          mass t residual q else 0) =
        ∑ q ∈ (system (left := left) (right := right) (bucket := bucket) t).fiber j,
          if s ∈ (system (left := left) (right := right) (bucket := bucket) t).slots q then
            mass t residual q else 0 := by
    classical
    simp only [RankThreeOptionSystem.fiber, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hj : (system (left := left) (right := right) (bucket := bucket) t).owner q = j <;>
      by_cases hs : s ∈ (system (left := left) (right := right) (bucket := bucket) t).slots q <;>
        simp [hj, hs]
  rw [hrewrite] at hquant
  have hshare :
      (if (s.vertex, s.bucket) = (left j, bucket j) then residual j / t
      else if (s.vertex, s.bucket) = (right j, bucket j) then
        residual j / t else 0) ≤ 1 / (t : ℝ) := by
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
    have hj := hresidual_one j
    by_cases hl : (s.vertex, s.bucket) = (left j, bucket j)
    · rw [if_pos hl]
      exact (div_le_div_iff_of_pos_right ht0).2 hj
    · by_cases hr : (s.vertex, s.bucket) = (right j, bucket j)
      · rw [if_neg hl, if_pos hr]
        exact (div_le_div_iff_of_pos_right ht0).2 hj
      · rw [if_neg hl, if_neg hr]
        exact le_of_lt (one_div_pos.mpr ht0)
  calc
    _ ≤ (N : ℝ) *
        (if (s.vertex, s.bucket) = (left j, bucket j) then residual j / t
        else if (s.vertex, s.bucket) = (right j, bucket j) then
          residual j / t else 0) :=
      hquant.trans (mul_le_mul_of_nonneg_left
        (sum_mass_using_slot_fiber_le (left := left) (right := right)
          (bucket := bucket) (t := t) residual
          hresidual ht hne j s) (Nat.cast_nonneg N))
    _ ≤ (N : ℝ) * (1 / (t : ℝ)) :=
      mul_le_mul_of_nonneg_left hshare (Nat.cast_nonneg N)
    _ = (N : ℝ) / t := by ring

/-- A total sum over cyclic choices splits into its job fibres. -/
theorem sum_eq_sum_fiber
    (f : CyclicExtraChoice Job t → ℝ) :
    (∑ q, f q) =
      ∑ j, ∑ q ∈
        (system (left := left) (right := right) (bucket := bucket) t).fiber j,
        f q := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [RankThreeOptionSystem.fiber, system, Finset.sum_filter]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
  · simp
  · intro k _hk hkj
    simp [hkj]
  · simp

/-- The load of a cyclic slot is at most the sum of the uniform endpoint
shares of the incident jobs. -/
theorem sum_mass_using_slot_le (residual : Job → ℝ)
    (hresidual : ∀ j, 0 ≤ residual j) (ht : 0 < t)
    (hne : ∀ j, left j ≠ right j)
    (s : CyclicExtraSlot Vertex Class t) :
    (∑ q, if s ∈
        (system (left := left) (right := right) (bucket := bucket) t).slots q then
        mass t residual q else 0) ≤
      ∑ j,
        (if (s.vertex, s.bucket) = (left j, bucket j) then residual j / t
        else if (s.vertex, s.bucket) = (right j, bucket j) then
          residual j / t else 0) := by
  rw [sum_eq_sum_fiber (left := left) (right := right)
    (bucket := bucket) (t := t)]
  exact Finset.sum_le_sum fun j _ ↦
    sum_mass_using_slot_fiber_le (left := left) (right := right)
      (bucket := bucket) (t := t) residual
      hresidual ht hne j s

/-- Quantized slot degree is bounded by the corresponding endpoint-share
sum. -/
theorem quantized_slotDegree_le (residual : Job → ℝ)
    (hresidual : ∀ j, 0 ≤ residual j) (ht : 0 < t)
    (hne : ∀ j, left j ≠ right j)
    (N : ℕ) (s : CyclicExtraSlot Vertex Class t) :
    (((system (left := left) (right := right) (bucket := bucket) t).quantized N
      (mass t residual)).slotDegree s : ℕ) ≤
      (N : ℝ) * ∑ j,
        (if (s.vertex, s.bucket) = (left j, bucket j) then residual j / t
        else if (s.vertex, s.bucket) = (right j, bucket j) then
          residual j / t else 0) := by
  have hquant := (system (left := left) (right := right) (bucket := bucket) t).quantizedSlotDegree_upper
    N (mass t residual) s
    (fun q _ ↦ mass_nonneg t residual hresidual q)
  exact hquant.trans (mul_le_mul_of_nonneg_left
    (sum_mass_using_slot_le (left := left) (right := right)
      (bucket := bucket) (t := t) residual hresidual ht hne s)
    (Nat.cast_nonneg N))

/-- Exactly `t` coupled base options belong to every job. -/
theorem fiber_card (j : Job) :
    ((system (left := left) (right := right) (bucket := bucket) t).fiber j).card = t := by
  classical
  rw [show ((system (left := left) (right := right) (bucket := bucket) t).fiber j).card =
      Fintype.card {q : CyclicExtraChoice Job t //
        (system (left := left) (right := right) (bucket := bucket) t).owner q = j} by
    rw [Fintype.card_subtype]
    rfl]
  let E : {q : CyclicExtraChoice Job t //
      (system (left := left) (right := right) (bucket := bucket) t).owner q = j} ≃
      Fin t :=
    {
      toFun := fun q ↦ q.1.2
      invFun := fun i ↦ ⟨(j, i), rfl⟩
      left_inv := by
        intro q
        rcases q with ⟨⟨k, i⟩, hk⟩
        change k = j at hk
        subst k
        rfl
      right_inv := by intro i; rfl
    }
  simpa using Fintype.card_congr E

/-- Integer replication loses fewer than `t` copies from the residual part
of each job. -/
theorem quantizedJobDegree_lower (residual : Job → ℝ) (ht : 0 < t)
    (N : ℕ) (j : Job) :
    (N : ℝ) * residual j - t ≤
      ((system (left := left) (right := right) (bucket := bucket) t).quantizedJobDegree
        N (mass t residual) j : ℝ) := by
  have h := (system (left := left) (right := right) (bucket := bucket) t).quantizedJobDegree_lower
    N (mass t residual) j
  rw [sum_mass_fiber (left := left) (right := right)
      (bucket := bucket) (t := t) residual ht j,
    fiber_card (left := left) (right := right)
      (bucket := bucket) (t := t) j] at h
  simpa using h

end CyclicExtraChoice

namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]

/-- With `t` uniform slots in each class, the endpoint-share sum of a
concrete cyclic slot is exactly the class residual divided by `t`. -/
theorem sum_cyclicEndpointShares_eq_classResidual_div
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (t : ℕ) (v : G.V) (h : Class) :
    (∑ e,
      (if (v, h) = (G.fst e, bucket e) then residual e / t
      else if (v, h) = (G.snd e, bucket e) then residual e / t else 0)) =
      G.classResidual bucket residual v h / t := by
  unfold classResidual
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hl : (v, h) = (G.fst e, bucket e)
  · have hl' := hl.symm
    have hr : (v, h) ≠ (G.snd e, bucket e) := by
      intro hs
      exact G.noLoop e (congrArg Prod.fst (hl.symm.trans hs))
    have hr' : (G.snd e, bucket e) ≠ (v, h) := fun hs ↦ hr hs.symm
    rw [if_pos hl, if_pos hl', if_neg hr']
    simp
  · have hl' : (G.fst e, bucket e) ≠ (v, h) := fun hs ↦ hl hs.symm
    by_cases hr : (v, h) = (G.snd e, bucket e)
    · have hr' := hr.symm
      rw [if_neg hl, if_pos hr, if_neg hl', if_pos hr']
      simp
    · have hr' : (G.snd e, bucket e) ≠ (v, h) := fun hs ↦ hr hs.symm
      rw [if_neg hl, if_neg hr, if_neg hl', if_neg hr']
      simp

/-- A class-residual cap gives the required copied cyclic-slot degree cap. -/
theorem quantized_cyclicExtraSlotDegree_le
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (hr0 : ∀ e, 0 ≤ residual e) {gamma : ℝ} {t : ℕ}
    (ht : 0 < t)
    (hclass : ∀ v h,
      G.classResidual bucket residual v h ≤ (1 - gamma) * t)
    (N : ℕ) (s : CyclicExtraSlot G.V Class t) :
    ((((CyclicExtraChoice.system (left := G.fst) (right := G.snd)
      (bucket := bucket) t).quantized N
      (CyclicExtraChoice.mass t residual)).slotDegree s : ℕ) : ℝ) ≤
      (1 - gamma) * N := by
  have hbase := CyclicExtraChoice.quantized_slotDegree_le
    (left := G.fst) (right := G.snd) (bucket := bucket) (t := t)
    residual hr0 ht G.noLoop N s
  rw [G.sum_cyclicEndpointShares_eq_classResidual_div
    bucket residual t s.vertex s.bucket] at hbase
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hratio :
      G.classResidual bucket residual s.vertex s.bucket / t ≤
        1 - gamma := by
    rw [div_le_iff₀ ht0]
    simpa [mul_comm] using hclass s.vertex s.bucket
  calc
    _ ≤ (N : ℝ) *
        (G.classResidual bucket residual s.vertex s.bucket / t) := hbase
    _ ≤ (N : ℝ) * (1 - gamma) :=
      mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg N)
    _ = (1 - gamma) * N := by ring

/-- In a simple graph, two distinct cyclic extra slots identify the edge and
the common cyclic index. -/
theorem cyclicExtraChoice_pairUnique (bucket : G.E → Class) (t : ℕ) :
    (CyclicExtraChoice.system (left := G.fst) (right := G.snd)
      (bucket := bucket) t).PairUnique := by
  intro s r hsr q p hsq hrq hsp hrp
  have orient (x : CyclicExtraChoice G.E t)
      (hsx : s ∈ (CyclicExtraChoice.system (left := G.fst) (right := G.snd)
        (bucket := bucket) t).slots x)
      (hrx : r ∈ (CyclicExtraChoice.system (left := G.fst) (right := G.snd)
        (bucket := bucket) t).slots x) :
      (s = CyclicExtraChoice.leftSlot G.fst bucket t x ∧
        r = CyclicExtraChoice.rightSlot G.snd bucket t x) ∨
      (s = CyclicExtraChoice.rightSlot G.snd bucket t x ∧
        r = CyclicExtraChoice.leftSlot G.fst bucket t x) := by
    simp only [CyclicExtraChoice.system, Finset.mem_insert,
      Finset.mem_singleton] at hsx hrx
    rcases hsx with hs | hs <;> rcases hrx with hr | hr
    · exact (hsr (hs.trans hr.symm)).elim
    · exact Or.inl ⟨hs, hr⟩
    · exact Or.inr ⟨hs, hr⟩
    · exact (hsr (hs.trans hr.symm)).elim
  rcases q with ⟨e, i⟩
  rcases p with ⟨f, k⟩
  have hq := orient (e, i) hsq hrq
  have hp := orient (f, k) hsp hrp
  rcases hq with hq | hq <;> rcases hp with hp | hp
  · have hleft := hq.1.symm.trans hp.1
    have hright := hq.2.symm.trans hp.2
    have hef : e = f := G.endpoints_injective ((Sym2.eq_iff).2 (Or.inl
      ⟨congrArg CyclicExtraSlot.vertex hleft,
        congrArg CyclicExtraSlot.vertex hright⟩))
    subst f
    have hik : i = k := Fin.ext (congrArg
      (fun z : CyclicExtraSlot G.V Class t ↦ z.index.val) hleft)
    subst k
    rfl
  · have hlr := hq.1.symm.trans hp.1
    have hrl := hq.2.symm.trans hp.2
    have hef : e = f := G.endpoints_injective ((Sym2.eq_iff).2 (Or.inr
      ⟨congrArg CyclicExtraSlot.vertex hlr,
        congrArg CyclicExtraSlot.vertex hrl⟩))
    subst f
    exact (G.noLoop e (congrArg CyclicExtraSlot.vertex hlr)).elim
  · have hrl := hq.1.symm.trans hp.1
    have hlr := hq.2.symm.trans hp.2
    have hef : e = f := G.endpoints_injective ((Sym2.eq_iff).2 (Or.inr
      ⟨congrArg CyclicExtraSlot.vertex hlr,
        congrArg CyclicExtraSlot.vertex hrl⟩))
    subst f
    exact (G.noLoop e (congrArg CyclicExtraSlot.vertex hlr)).elim
  · have hright := hq.1.symm.trans hp.1
    have hleft := hq.2.symm.trans hp.2
    have hef : e = f := G.endpoints_injective ((Sym2.eq_iff).2 (Or.inl
      ⟨congrArg CyclicExtraSlot.vertex hleft,
        congrArg CyclicExtraSlot.vertex hright⟩))
    subst f
    have hik : i = k := Fin.ext (congrArg
      (fun z : CyclicExtraSlot G.V Class t ↦ z.index.val) hleft)
    subst k
    rfl

/-- Pair uniqueness plus the point-mass bound gives the copied pair
codegree `N/t`. -/
theorem quantized_cyclicExtraSlotPairCodegree_le
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (hr0 : ∀ e, 0 ≤ residual e) (hr1 : ∀ e, residual e ≤ 1)
    {t : ℕ} (ht : 0 < t) (N : ℕ)
    {s r : CyclicExtraSlot G.V Class t} (hsr : s ≠ r) :
    ((((CyclicExtraChoice.system (left := G.fst) (right := G.snd)
      (bucket := bucket) t).quantized N
      (CyclicExtraChoice.mass t residual)).slotPairCodegree s r : ℕ) : ℝ) ≤
      (N : ℝ) / t := by
  calc
    _ ≤ (N : ℝ) * (1 / (t : ℝ)) := by
      apply (CyclicExtraChoice.system (left := G.fst) (right := G.snd)
        (bucket := bucket) t).quantized_slotPairCodegree_le
          (G.cyclicExtraChoice_pairUnique bucket t)
          N (CyclicExtraChoice.mass t residual) (1 / (t : ℝ))
      · exact le_of_lt (one_div_pos.mpr (by exact_mod_cast ht))
      · exact CyclicExtraChoice.mass_nonneg t residual hr0
      · intro q
        have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
        exact (div_le_div_iff_of_pos_right ht0).2 (hr1 q.1)
      · exact hsr
    _ = (N : ℝ) / t := by ring

end WeightedSimpleGraph

end

end WeightedEdgeColoring
