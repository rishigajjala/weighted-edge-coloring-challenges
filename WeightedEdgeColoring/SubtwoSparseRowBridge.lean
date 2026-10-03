import WeightedEdgeColoring.SubtwoRationalCertificate

/-!
# Sparse row formulas and the exact real LP checker

A row is a list of column/coefficient pairs. Repeated columns are allowed
and their coefficients are added. Thus a separately checked matrix identity
can connect the physical row formulas to any frozen certificate matrix.
-/

open scoped BigOperators
set_option autoImplicit false

namespace WeightedEdgeColoring.SubtwoRationalCertificate

def sparseRowCoefficients {n : ℕ} : List (Fin n × ℚ) → Fin n → ℚ
  | [], _ => 0
  | term :: rest, j => (if j = term.1 then term.2 else 0) + sparseRowCoefficients rest j

def realSparseRowEval {n : ℕ} (row : List (Fin n × ℚ)) (x : Fin n → ℝ) : ℝ :=
  (row.map fun term => (term.2 : ℝ) * x term.1).sum

theorem realSparseRowEval_eq_dot {n : ℕ} (row : List (Fin n × ℚ)) (x : Fin n → ℝ) :
    realSparseRowEval row x = ∑ j, (sparseRowCoefficients row j : ℝ) * x j := by
  induction row with
  | nil => simp [realSparseRowEval, sparseRowCoefficients]
  | cons term rest ih =>
    simp only [sparseRowCoefficients, Rat.cast_add, apply_ite, Rat.cast_zero,
      add_mul, Finset.sum_add_distrib]
    have h : (∑ j : Fin n, (if j = term.1 then (term.2 : ℝ) else 0) * x j) =
        (term.2 : ℝ) * x term.1 := by simp
    rw [h, ← ih]
    rfl

theorem realSparseRowEval_ofFn {a n : ℕ} (column : Fin a → Fin n)
    (coefficient : Fin a → ℚ) (x : Fin n → ℝ) :
    realSparseRowEval (List.ofFn fun i => (column i, coefficient i)) x =
      ∑ i, (coefficient i : ℝ) * x (column i) := by
  simp only [realSparseRowEval, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem realSparseRowEval_append {n : ℕ} (s t : List (Fin n × ℚ)) (x : Fin n → ℝ) :
    realSparseRowEval (s ++ t) x = realSparseRowEval s x + realSparseRowEval t x := by
  simp only [realSparseRowEval, List.map_append, List.sum_append]

theorem realSparseRowEval_scale {n : ℕ} (a : ℚ) (s : List (Fin n × ℚ)) (x : Fin n → ℝ) :
    realSparseRowEval (s.map fun term => (term.1, a * term.2)) x =
      (a : ℝ) * realSparseRowEval s x := by
  induction s with
  | nil => simp [realSparseRowEval]
  | cons term rest ih =>
    simp only [realSparseRowEval, List.map_cons, List.sum_cons, Rat.cast_mul] at ih ⊢
    rw [ih]
    ring

/-- The physical row proofs are sufficient once every frozen matrix row
has been identified with its sparse formula and its exact right-hand side. -/
theorem Problem.realFeasible_of_sparse_rows {m n : ℕ} (P : Problem m n)
    (rows : Fin m → List (Fin n × ℚ)) (x : Fin n → ℝ)
    (hmatrix : ∀ i j, P.A i j = sparseRowCoefficients (rows i) j)
    (hrows : ∀ i, realSparseRowEval (rows i) x ≤ (P.b i : ℝ))
    (hbox : ∀ j, (P.lo j : ℝ) ≤ x j ∧ x j ≤ (P.hi j : ℝ)) : P.RealFeasible x := by
  refine ⟨?_, hbox⟩
  intro i
  simp only [hmatrix]
  rw [← realSparseRowEval_eq_dot]
  exact hrows i

end WeightedEdgeColoring.SubtwoRationalCertificate
