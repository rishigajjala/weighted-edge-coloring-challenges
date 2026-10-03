import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exact rational residual certificates for finite linear programs

This module verifies the algebraic step used by the dense-five LP archives.
The matrix, objective, row bounds, variable bounds, and proposed dual
multipliers are all *inputs*.  In particular, this theorem does not assert
that any archived file has been imported, that its rows are geometrically
valid, or that the archived boxes cover a price domain.

The certificate permits arbitrary residuals.  A positive residual is paid
at the variable's upper bound and a negative residual at its lower bound.
-/

namespace WeightedEdgeColoring

namespace SubtwoRationalCertificate

/-- An exactly specified, finite rational maximization problem with rows
`∑ j, A i j * x j ≤ b i` and finite variable bounds `lo j ≤ x j ≤ hi j`. -/
structure Problem (m n : ℕ) where
  A : Fin m → Fin n → ℚ
  b : Fin m → ℚ
  c : Fin n → ℚ
  lo : Fin n → ℚ
  hi : Fin n → ℚ

namespace Problem

/-- The primal feasible set of the encoded rational LP. -/
def Feasible {m n : ℕ} (P : Problem m n) (x : Fin n → ℚ) : Prop :=
  (∀ i, (∑ j, P.A i j * x j) ≤ P.b i) ∧
  (∀ j, P.lo j ≤ x j ∧ x j ≤ P.hi j)

/-- The exact rational maximization objective. -/
def objective {m n : ℕ} (P : Problem m n) (x : Fin n → ℚ) : ℚ :=
  ∑ j, P.c j * x j

/-- `c - Aᵀ α`; no exact dual feasibility is required. -/
def residual {m n : ℕ} (P : Problem m n) (α : Fin m → ℚ)
    (j : Fin n) : ℚ := P.c j - ∑ i, α i * P.A i j

/-- The maximum payment for one residual over the variable interval. -/
def payment {m n : ℕ} (P : Problem m n) (α : Fin m → ℚ)
    (j : Fin n) : ℚ :=
  if 0 ≤ P.residual α j then P.residual α j * P.hi j
  else P.residual α j * P.lo j

/-- The exact upper bound proposed by nonnegative row multipliers. -/
def certificateBound {m n : ℕ} (P : Problem m n)
    (α : Fin m → ℚ) : ℚ :=
  (∑ i, α i * P.b i) + ∑ j, P.payment α j

private theorem residual_mul_le_payment {m n : ℕ} (P : Problem m n)
    (α : Fin m → ℚ) (x : Fin n → ℚ) (j : Fin n)
    (hx : P.lo j ≤ x j ∧ x j ≤ P.hi j) :
    P.residual α j * x j ≤ P.payment α j := by
  unfold payment
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left hx.2 h
  · exact mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge h)

private theorem objective_identity {m n : ℕ} (P : Problem m n)
    (α : Fin m → ℚ) (x : Fin n → ℚ) :
    P.objective x =
      (∑ i, α i * (∑ j, P.A i j * x j)) +
        ∑ j, P.residual α j * x j := by
  unfold objective residual
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  have hswap :
      (∑ i, ∑ j, α i * (P.A i j * x j)) =
        ∑ j, ∑ i, α i * P.A i j * x j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hswap]
  have hfactor :
      (∑ j, ∑ i, α i * P.A i j * x j) =
        ∑ j, (∑ i, α i * P.A i j) * x j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_mul]
  rw [hfactor]
  ring

/-- Soundness of a finite rational dual-residual certificate.  All
arithmetic is checked by Lean's kernel; inexact proposed multipliers are
allowed because the residual is paid at a valid variable endpoint. -/
theorem objective_le_certificateBound {m n : ℕ} (P : Problem m n)
    (α : Fin m → ℚ) (hα : ∀ i, 0 ≤ α i)
    (x : Fin n → ℚ) (hx : P.Feasible x) :
    P.objective x ≤ P.certificateBound α := by
  rw [objective_identity P α x]
  unfold certificateBound
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hx.1 i) (hα i)
  · apply Finset.sum_le_sum
    intro j hj
    exact residual_mul_le_payment P α x j (hx.2 j)

/-- A decidable exact certificate check against any rational target. -/
def passes {m n : ℕ} (P : Problem m n) (α : Fin m → ℚ)
    (target : ℚ) : Bool :=
  decide (∀ i, 0 ≤ α i) && decide (P.certificateBound α < target)

/-- Passing the Boolean check proves a strict bound for every feasible
primal point of the encoded LP. -/
theorem objective_lt_of_passes {m n : ℕ} (P : Problem m n)
    (α : Fin m → ℚ) (target : ℚ) (h : P.passes α target = true)
    (x : Fin n → ℚ) (hx : P.Feasible x) :
    P.objective x < target := by
  unfold passes at h
  have hα : ∀ i, 0 ≤ α i := by
    by_contra ha
    simp [ha] at h
  have hb : P.certificateBound α < target := by
    by_contra hbound
    simp [hbound] at h
  exact (P.objective_le_certificateBound α hα x hx).trans_lt hb

/-- Feasibility of a real point for the rational rows and endpoints. This is
the form needed when LP variables arise from fractional packing data. -/
def RealFeasible {m n : ℕ} (P : Problem m n) (x : Fin n → ℝ) : Prop :=
  (∀ i, (∑ j, (P.A i j : ℝ) * x j) ≤ (P.b i : ℝ)) ∧
  (∀ j, (P.lo j : ℝ) ≤ x j ∧ x j ≤ (P.hi j : ℝ))

def realObjective {m n : ℕ} (P : Problem m n) (x : Fin n → ℝ) : ℝ :=
  ∑ j, (P.c j : ℝ) * x j

private theorem real_residual_identity {m n : ℕ} (P : Problem m n)
    (α : Fin m → ℚ) (x : Fin n → ℝ) :
    P.realObjective x =
      (∑ i, (α i : ℝ) * (∑ j, (P.A i j : ℝ) * x j)) +
        ∑ j, (P.residual α j : ℝ) * x j := by
  unfold realObjective residual
  simp only [Rat.cast_sub, Rat.cast_sum, Rat.cast_mul, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum]
  have hswap :
      (∑ i, ∑ j, (α i : ℝ) * ((P.A i j : ℝ) * x j)) =
        ∑ j, ∑ i, (α i : ℝ) * (P.A i j : ℝ) * x j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hswap]
  have hfactor :
      (∑ j, ∑ i, (α i : ℝ) * (P.A i j : ℝ) * x j) =
        ∑ j, (∑ i, (α i : ℝ) * (P.A i j : ℝ)) * x j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_mul]
  rw [hfactor]
  ring

private theorem real_residual_mul_le_cast_payment {m n : ℕ}
    (P : Problem m n) (α : Fin m → ℚ) (x : Fin n → ℝ)
    (j : Fin n) (hx : (P.lo j : ℝ) ≤ x j ∧ x j ≤ (P.hi j : ℝ)) :
    (P.residual α j : ℝ) * x j ≤ (P.payment α j : ℝ) := by
  unfold payment
  split_ifs with h
  · rw [Rat.cast_mul]
    exact mul_le_mul_of_nonneg_left hx.2 (by exact_mod_cast h)
  · rw [Rat.cast_mul]
    exact mul_le_mul_of_nonpos_left hx.1 (by exact_mod_cast (le_of_not_ge h))

/-- The same exact rational certificate bounds **real** feasible points.
Thus rational arithmetic certificates apply to fractional LP data without
assuming the primal optimum or its variables are rational. -/
theorem realObjective_le_certificateBound {m n : ℕ} (P : Problem m n)
    (α : Fin m → ℚ) (hα : ∀ i, 0 ≤ α i)
    (x : Fin n → ℝ) (hx : P.RealFeasible x) :
    P.realObjective x ≤ (P.certificateBound α : ℝ) := by
  rw [real_residual_identity P α x]
  have hrows :
      (∑ i, (α i : ℝ) * (∑ j, (P.A i j : ℝ) * x j)) ≤
        ∑ i, (α i : ℝ) * (P.b i : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hx.1 i) (by exact_mod_cast hα i)
  have hpayments :
      (∑ j, (P.residual α j : ℝ) * x j) ≤
        ∑ j, (P.payment α j : ℝ) := by
    apply Finset.sum_le_sum
    intro j hj
    exact real_residual_mul_le_cast_payment P α x j (hx.2 j)
  have hsum := add_le_add hrows hpayments
  simpa [certificateBound, Rat.cast_add, Rat.cast_sum, Rat.cast_mul] using hsum

theorem realObjective_lt_of_passes {m n : ℕ} (P : Problem m n)
    (α : Fin m → ℚ) (target : ℚ) (h : P.passes α target = true)
    (x : Fin n → ℝ) (hx : P.RealFeasible x) :
    P.realObjective x < (target : ℝ) := by
  unfold passes at h
  have hα : ∀ i, 0 ≤ α i := by
    by_contra ha
    simp [ha] at h
  have hb : P.certificateBound α < target := by
    by_contra hbound
    simp [hbound] at h
  exact (P.realObjective_le_certificateBound α hα x hx).trans_lt
    (by exact_mod_cast hb)

end Problem

/-- A column-oriented sparse encoding of the same finite LP. Each pair
`(i,a)` in `columns j` contributes `a` to coefficient `A i j`.
Repeated pairs are summed, so no uniqueness assumption is needed. -/
structure ColumnProblem (m n : ℕ) where
  columns : Fin n → List (Fin m × ℚ)
  b : Fin m → ℚ
  c : Fin n → ℚ
  lo : Fin n → ℚ
  hi : Fin n → ℚ

namespace ColumnProblem

def coefficient {m n : ℕ} (P : ColumnProblem m n)
    (i : Fin m) (j : Fin n) : ℚ :=
  ((P.columns j).map fun term => if term.1 = i then term.2 else 0).sum

/-- Dense mathematical interpretation of sparse column data. -/
def dense {m n : ℕ} (P : ColumnProblem m n) : Problem m n where
  A := P.coefficient
  b := P.b
  c := P.c
  lo := P.lo
  hi := P.hi

def residual {m n : ℕ} (P : ColumnProblem m n)
    (α : Fin m → ℚ) (j : Fin n) : ℚ :=
  P.c j - ((P.columns j).map fun term => α term.1 * term.2).sum

def payment {m n : ℕ} (P : ColumnProblem m n)
    (α : Fin m → ℚ) (j : Fin n) : ℚ :=
  if 0 ≤ P.residual α j then P.residual α j * P.hi j
  else P.residual α j * P.lo j

/-- Only the stored nonzero column entries are visited when computing the
residual; this avoids a dense `m × n` kernel reduction. -/
def certificateBound {m n : ℕ} (P : ColumnProblem m n)
    (α : Fin m → ℚ) : ℚ :=
  (∑ i, α i * P.b i) + ∑ j, P.payment α j

private theorem weighted_column_sum {m : ℕ} (α : Fin m → ℚ)
    (terms : List (Fin m × ℚ)) :
    (∑ i, α i * ((terms.map fun term =>
      if term.1 = i then term.2 else 0).sum)) =
      (terms.map fun term => α term.1 * term.2).sum := by
  induction terms with
  | nil => simp
  | cons term rest ih =>
      simp only [List.map_cons, List.sum_cons, mul_add,
        Finset.sum_add_distrib]
      have hone :
          (∑ i, α i * if term.1 = i then term.2 else 0) =
            α term.1 * term.2 := by
        simp
      rw [hone, ih]

theorem dense_residual_eq {m n : ℕ} (P : ColumnProblem m n)
    (α : Fin m → ℚ) (j : Fin n) :
    P.dense.residual α j = P.residual α j := by
  change P.c j - (∑ i, α i *
      ((P.columns j).map fun term => if term.1 = i then term.2 else 0).sum) =
    P.c j - ((P.columns j).map fun term => α term.1 * term.2).sum
  exact congrArg (P.c j - ·) (weighted_column_sum α (P.columns j))

theorem dense_certificateBound_eq {m n : ℕ} (P : ColumnProblem m n)
    (α : Fin m → ℚ) :
    P.dense.certificateBound α = P.certificateBound α := by
  unfold Problem.certificateBound certificateBound
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  unfold Problem.payment payment
  rw [P.dense_residual_eq α j]
  rfl

def passes {m n : ℕ} (P : ColumnProblem m n)
    (α : Fin m → ℚ) (target : ℚ) : Bool :=
  decide (∀ i, 0 ≤ α i) && decide (P.certificateBound α < target)

/-- Exact sparse arithmetic certifies every real feasible point of the
corresponding finite LP. -/
theorem realObjective_lt_of_passes {m n : ℕ} (P : ColumnProblem m n)
    (α : Fin m → ℚ) (target : ℚ) (h : P.passes α target = true)
    (x : Fin n → ℝ) (hx : P.dense.RealFeasible x) :
    P.dense.realObjective x < (target : ℝ) := by
  unfold passes at h
  have hα : ∀ i, 0 ≤ α i := by
    by_contra ha
    simp [ha] at h
  have hb : P.certificateBound α < target := by
    by_contra hbound
    simp [hbound] at h
  have hbound := P.dense.realObjective_le_certificateBound α hα x hx
  rw [P.dense_certificateBound_eq α] at hbound
  exact hbound.trans_lt (by exact_mod_cast hb)

end ColumnProblem

/-- A closed rational price box in `d` coordinates. -/
structure Box (d : ℕ) where
  lo : Fin d → ℚ
  hi : Fin d → ℚ

namespace Box

def Contains {d : ℕ} (B : Box d) (p : Fin d → ℚ) : Prop :=
  ∀ j, B.lo j ≤ p j ∧ p j ≤ B.hi j

/-- Membership for real price vectors in a box with rational endpoints. -/
def RealContains {d : ℕ} (B : Box d) (p : Fin d → ℝ) : Prop :=
  ∀ j, (B.lo j : ℝ) ≤ p j ∧ p j ≤ (B.hi j : ℝ)

/-- The closed left half of a split, intersected with its parent. -/
def left {d : ℕ} (B : Box d) (k : Fin d) (cut : ℚ) : Box d where
  lo := B.lo
  hi := fun j => if j = k then min (B.hi j) cut else B.hi j

/-- The closed right half of a split, intersected with its parent. -/
def right {d : ℕ} (B : Box d) (k : Fin d) (cut : ℚ) : Box d where
  lo := fun j => if j = k then max (B.lo j) cut else B.lo j
  hi := B.hi

theorem contains_left_of_le {d : ℕ} (B : Box d) (p : Fin d → ℚ)
    (k : Fin d) (cut : ℚ) (hp : B.Contains p) (h : p k ≤ cut) :
    (B.left k cut).Contains p := by
  intro j
  by_cases hj : j = k
  · subst j
    constructor
    · exact (hp k).1
    · simpa [left] using le_min (hp k).2 h
  · simpa [left, hj] using hp j

theorem contains_right_of_ge {d : ℕ} (B : Box d) (p : Fin d → ℚ)
    (k : Fin d) (cut : ℚ) (hp : B.Contains p) (h : cut ≤ p k) :
    (B.right k cut).Contains p := by
  intro j
  by_cases hj : j = k
  · subst j
    constructor
    · simpa [right] using max_le (hp k).1 h
    · exact (hp k).2
  · simpa [right, hj] using hp j

theorem real_contains_left_of_le {d : ℕ} (B : Box d) (p : Fin d → ℝ)
    (k : Fin d) (cut : ℚ) (hp : B.RealContains p)
    (h : p k ≤ (cut : ℝ)) :
    (B.left k cut).RealContains p := by
  intro j
  by_cases hj : j = k
  · subst j
    constructor
    · exact (hp k).1
    · simpa [left, Rat.cast_min] using le_min (hp k).2 h
  · simpa [left, hj] using hp j

theorem real_contains_right_of_ge {d : ℕ} (B : Box d) (p : Fin d → ℝ)
    (k : Fin d) (cut : ℚ) (hp : B.RealContains p)
    (h : (cut : ℝ) ≤ p k) :
    (B.right k cut).RealContains p := by
  intro j
  by_cases hj : j = k
  · subst j
    constructor
    · simpa [right, Rat.cast_max] using max_le (hp k).1 h
    · exact (hp k).2
  · simpa [right, hj] using hp j

end Box

/-- A finite binary partition tree. A leaf records the rational box on
which its local certificate is intended to apply. -/
inductive CoverTree (d : ℕ) where
  | leaf (box : Box d)
  | split (coordinate : Fin d) (cut : ℚ)
      (left right : CoverTree d)

namespace CoverTree

/-- Exact check that every leaf contains the corresponding portion of the
root box. Split children receive the closed intersections with their
parent, so shared boundaries are covered. -/
def checkCover {d : ℕ} (parent : Box d) : CoverTree d → Bool
  | .leaf box =>
      decide (∀ j, box.lo j ≤ parent.lo j ∧ parent.hi j ≤ box.hi j)
  | .split k cut l r =>
      checkCover (parent.left k cut) l &&
        checkCover (parent.right k cut) r

/-- An exact Boolean check of any leaf property, such as a rational LP
certificate for that leaf. -/
def allLeavesPass {d : ℕ} (good : Box d → Bool) : CoverTree d → Bool
  | .leaf box => good box
  | .split _ _ l r => allLeavesPass good l && allLeavesPass good r

/-- A price vector lies in at least one certified leaf. -/
def ReachesLeaf {d : ℕ} (tree : CoverTree d) (p : Fin d → ℚ)
    (good : Box d → Bool) : Prop :=
  match tree with
  | .leaf box => box.Contains p ∧ good box = true
  | .split _ _ l r => l.ReachesLeaf p good ∨ r.ReachesLeaf p good

/-- The same leaf-reachability assertion for real prices. -/
def RealReachesLeaf {d : ℕ} (tree : CoverTree d) (p : Fin d → ℝ)
    (good : Box d → Bool) : Prop :=
  match tree with
  | .leaf box => box.RealContains p ∧ good box = true
  | .split _ _ l r => l.RealReachesLeaf p good ∨ r.RealReachesLeaf p good

theorem reachesLeaf_of_checks {d : ℕ} (tree : CoverTree d)
    (parent : Box d) (good : Box d → Bool) (p : Fin d → ℚ)
    (hc : tree.checkCover parent = true)
    (hg : tree.allLeavesPass good = true)
    (hp : parent.Contains p) :
    tree.ReachesLeaf p good := by
  induction tree generalizing parent with
  | leaf box =>
      simp only [checkCover, decide_eq_true_eq] at hc
      simp only [allLeavesPass] at hg
      simp only [ReachesLeaf]
      constructor
      · intro j
        have h := hc j
        exact ⟨h.1.trans (hp j).1, (hp j).2.trans h.2⟩
      · exact hg
  | split k cut l r ihl ihr =>
      have hcl : l.checkCover (parent.left k cut) = true := by
        cases hval : l.checkCover (parent.left k cut) with
        | false => simp [checkCover, hval] at hc
        | true => rfl
      have hcr : r.checkCover (parent.right k cut) = true := by
        cases hval : r.checkCover (parent.right k cut) with
        | false => simp [checkCover, hval] at hc
        | true => rfl
      have hgl : l.allLeavesPass good = true := by
        cases hval : l.allLeavesPass good with
        | false => simp [allLeavesPass, hval] at hg
        | true => rfl
      have hgr : r.allLeavesPass good = true := by
        cases hval : r.allLeavesPass good with
        | false => simp [allLeavesPass, hval] at hg
        | true => rfl
      simp only [ReachesLeaf]
      by_cases hcut : p k ≤ cut
      · exact Or.inl (ihl (parent.left k cut) hcl hgl
          (parent.contains_left_of_le p k cut hp hcut))
      · exact Or.inr (ihr (parent.right k cut) hcr hgr
          (parent.contains_right_of_ge p k cut hp (le_of_lt (lt_of_not_ge hcut))))

theorem exists_good_leaf {d : ℕ} (tree : CoverTree d)
    (p : Fin d → ℚ) (good : Box d → Bool)
    (h : tree.ReachesLeaf p good) :
    ∃ box, box.Contains p ∧ good box = true := by
  induction tree with
  | leaf box => exact ⟨box, h⟩
  | split _ _ l r ihl ihr =>
      rcases h with hl | hr
      · exact ihl hl
      · exact ihr hr

theorem real_reachesLeaf_of_checks {d : ℕ} (tree : CoverTree d)
    (parent : Box d) (good : Box d → Bool) (p : Fin d → ℝ)
    (hc : tree.checkCover parent = true)
    (hg : tree.allLeavesPass good = true)
    (hp : parent.RealContains p) :
    tree.RealReachesLeaf p good := by
  induction tree generalizing parent with
  | leaf box =>
      simp only [checkCover, decide_eq_true_eq] at hc
      simp only [allLeavesPass] at hg
      simp only [RealReachesLeaf]
      constructor
      · intro j
        have h := hc j
        have hlow : (box.lo j : ℝ) ≤ (parent.lo j : ℝ) := by
          exact_mod_cast h.1
        have hhigh : (parent.hi j : ℝ) ≤ (box.hi j : ℝ) := by
          exact_mod_cast h.2
        exact ⟨hlow.trans (hp j).1, (hp j).2.trans hhigh⟩
      · exact hg
  | split k cut l r ihl ihr =>
      have hcl : l.checkCover (parent.left k cut) = true := by
        cases hval : l.checkCover (parent.left k cut) with
        | false => simp [checkCover, hval] at hc
        | true => rfl
      have hcr : r.checkCover (parent.right k cut) = true := by
        cases hval : r.checkCover (parent.right k cut) with
        | false => simp [checkCover, hval] at hc
        | true => rfl
      have hgl : l.allLeavesPass good = true := by
        cases hval : l.allLeavesPass good with
        | false => simp [allLeavesPass, hval] at hg
        | true => rfl
      have hgr : r.allLeavesPass good = true := by
        cases hval : r.allLeavesPass good with
        | false => simp [allLeavesPass, hval] at hg
        | true => rfl
      simp only [RealReachesLeaf]
      by_cases hcut : p k ≤ (cut : ℝ)
      · exact Or.inl (ihl (parent.left k cut) hcl hgl
          (parent.real_contains_left_of_le p k cut hp hcut))
      · exact Or.inr (ihr (parent.right k cut) hcr hgr
          (parent.real_contains_right_of_ge p k cut hp (le_of_lt (lt_of_not_ge hcut))))

theorem exists_good_real_leaf {d : ℕ} (tree : CoverTree d)
    (p : Fin d → ℝ) (good : Box d → Bool)
    (h : tree.RealReachesLeaf p good) :
    ∃ box, box.RealContains p ∧ good box = true := by
  induction tree with
  | leaf box => exact ⟨box, h⟩
  | split _ _ l r ihl ihr =>
      rcases h with hl | hr
      · exact ihl hl
      · exact ihr hr

/-- Combining the box check and the finite LP checker gives a certified
leaf for every rational price vector in the root box. The relationship
between that price and feasible LP variables is a separate mathematical
obligation for the application. -/
theorem exists_leaf_with_strict_lp_bound {d m n : ℕ}
    (tree : CoverTree d) (root : Box d)
    (P : Box d → Problem m n) (α : (box : Box d) → Fin m → ℚ)
    (target : ℚ) (p : Fin d → ℚ)
    (hc : tree.checkCover root = true)
    (hg : tree.allLeavesPass (fun box => (P box).passes (α box) target) = true)
    (hp : root.Contains p) :
    ∃ box, box.Contains p ∧
      ∀ x, (P box).Feasible x → (P box).objective x < target := by
  obtain ⟨box, hbox, hpass⟩ :=
    tree.exists_good_leaf p _ (tree.reachesLeaf_of_checks root _ p hc hg hp)
  exact ⟨box, hbox, fun x hx =>
    (P box).objective_lt_of_passes (α box) target hpass x hx⟩

/-- Real-valued version of the checked tree conclusion. -/
theorem exists_leaf_with_strict_real_lp_bound {d m n : ℕ}
    (tree : CoverTree d) (root : Box d)
    (P : Box d → Problem m n) (α : (box : Box d) → Fin m → ℚ)
    (target : ℚ) (p : Fin d → ℚ)
    (hc : tree.checkCover root = true)
    (hg : tree.allLeavesPass (fun box => (P box).passes (α box) target) = true)
    (hp : root.Contains p) :
    ∃ box, box.Contains p ∧
      ∀ x, (P box).RealFeasible x → (P box).realObjective x < (target : ℝ) := by
  obtain ⟨box, hbox, hpass⟩ :=
    tree.exists_good_leaf p _ (tree.reachesLeaf_of_checks root _ p hc hg hp)
  exact ⟨box, hbox, fun x hx =>
    (P box).realObjective_lt_of_passes (α box) target hpass x hx⟩

/-- Full real interface: rational box arithmetic and rational dual
arithmetic certify a bound for real price vectors and real LP points. -/
theorem exists_leaf_for_real_prices_with_strict_real_lp_bound {d m n : ℕ}
    (tree : CoverTree d) (root : Box d)
    (P : Box d → Problem m n) (α : (box : Box d) → Fin m → ℚ)
    (target : ℚ) (p : Fin d → ℝ)
    (hc : tree.checkCover root = true)
    (hg : tree.allLeavesPass (fun box => (P box).passes (α box) target) = true)
    (hp : root.RealContains p) :
    ∃ box, box.RealContains p ∧
      ∀ x, (P box).RealFeasible x → (P box).realObjective x < (target : ℝ) := by
  obtain ⟨box, hbox, hpass⟩ :=
    tree.exists_good_real_leaf p _ (tree.real_reachesLeaf_of_checks root _ p hc hg hp)
  exact ⟨box, hbox, fun x hx =>
    (P box).realObjective_lt_of_passes (α box) target hpass x hx⟩

end CoverTree

end SubtwoRationalCertificate

end WeightedEdgeColoring
