import WeightedEdgeColoring.WeightedMultigraph
import WeightedEdgeColoring.SubtwoFractionalStarDemand
import Mathlib.Tactic

/-!
# The actual finite weighted-color patterns

A pattern contains natural-number copies of edge types and has capacity one
at every vertex. Its total weight over the whole graph need not be at most
one. These are the configurations needed by the geometric price argument.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- One feasible weighted color, allowing repeated copies of each edge type. -/
def SubtwoWeightedPattern :=
  {m : G.E → ℕ // ∀ v : G.V,
    (∑ e : G.E, if G.Inc v e then (m e : ℝ) * G.weight e else 0) ≤ 1}

namespace SubtwoWeightedPattern

theorem coordinate_load_le (p : G.SubtwoWeightedPattern) (e : G.E) :
    (p.val e : ℝ) * G.weight e ≤ 1 := by
  have hi : G.Inc (G.fst e) e := Or.inl rfl
  have hle := Finset.single_le_sum
    (s := (Finset.univ : Finset G.E))
    (f := fun f ↦ if G.Inc (G.fst e) f then (p.val f : ℝ) * G.weight f else 0)
    (fun f _ ↦ by
      dsimp only
      split
      · exact mul_nonneg (Nat.cast_nonneg _) (G.weight_pos f).le
      · rfl)
    (Finset.mem_univ e)
  have he : (p.val e : ℝ) * G.weight e ≤
      ∑ f : G.E, if G.Inc (G.fst e) f then (p.val f : ℝ) * G.weight f else 0 := by
    simpa [hi] using hle
  exact he.trans (p.property (G.fst e))

theorem multiplicity_le_floor (p : G.SubtwoWeightedPattern) (e : G.E) :
    p.val e ≤ Nat.floor (1 / G.weight e) := by
  apply Nat.le_floor
  exact (le_div_iff₀ (G.weight_pos e)).2 (p.coordinate_load_le G e)

noncomputable def finiteCode (p : G.SubtwoWeightedPattern) :
    ∀ e : G.E, Fin (Nat.floor (1 / G.weight e) + 1) :=
  fun e ↦ ⟨p.val e, Nat.lt_succ_of_le (p.multiplicity_le_floor G e)⟩

theorem finiteCode_injective : Function.Injective (finiteCode G) := by
  intro p q h
  apply Subtype.ext
  funext e
  exact congrArg Fin.val (congrFun h e)

noncomputable instance : Fintype G.SubtwoWeightedPattern :=
  Fintype.ofInjective (finiteCode G) (finiteCode_injective G)

noncomputable instance : DecidableEq G.SubtwoWeightedPattern := Classical.decEq _

def zero : G.SubtwoWeightedPattern := ⟨fun _ ↦ 0, by intro v; simp⟩

instance : Inhabited G.SubtwoWeightedPattern := ⟨zero G⟩

/-- Deleting arbitrary copies preserves every vertex capacity. -/
def ofLE (p : G.SubtwoWeightedPattern) (m : G.E → ℕ)
    (hm : ∀ e, m e ≤ p.val e) : G.SubtwoWeightedPattern := by
  refine ⟨m, ?_⟩
  intro v
  calc
    _ ≤ ∑ e : G.E, if G.Inc v e then (p.val e : ℝ) * G.weight e else 0 := by
      apply Finset.sum_le_sum
      intro e _
      split
      · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hm e)) (G.weight_pos e).le
      · rfl
    _ ≤ 1 := p.property v

/-- A color reserved for exterior use at `v` deletes its internal edges at
`v`, while keeping all edges at other vertices that do not meet `v`. -/
noncomputable def avoidVertex (p : G.SubtwoWeightedPattern) (v : G.V) :
    G.SubtwoWeightedPattern := by
  classical
  exact p.ofLE G (fun e ↦ if G.Inc v e then 0 else p.val e)
    (fun e ↦ by dsimp only; split <;> simp)

theorem avoidVertex_zero (p : G.SubtwoWeightedPattern) (v : G.V)
    (e : G.E) (he : G.Inc v e) : (p.avoidVertex G v).val e = 0 := by
  classical
  simp [avoidVertex, ofLE, he]

theorem avoidVertex_keeps (p : G.SubtwoWeightedPattern) (v : G.V)
    (e : G.E) (he : ¬G.Inc v e) : (p.avoidVertex G v).val e = p.val e := by
  classical
  simp [avoidVertex, ofLE, he]

theorem avoidVertex_fixed (p : G.SubtwoWeightedPattern) (v : G.V)
    (hp : ∀ e, G.Inc v e → p.val e = 0) : p.avoidVertex G v = p := by
  classical
  apply Subtype.ext
  funext e
  by_cases he : G.Inc v e
  · rw [p.avoidVertex_zero G v e he, hp e he]
  · exact p.avoidVertex_keeps G v e he

end SubtwoWeightedPattern

namespace SubtwoFractionalDemandColoring

variable {G}

def toWeightedPattern {demand : G.E → ℝ}
    (C : G.SubtwoFractionalDemandColoring demand) (p : C.P) :
    G.SubtwoWeightedPattern := ⟨C.pattern p, C.feasible p⟩

/-- A cap on the price of every genuine feasible color bounds the price
of a fractionally colored demand by that coloring's total mass. -/
theorem price_le_cost_mul {demand : G.E → ℝ}
    (C : G.SubtwoFractionalDemandColoring demand)
    (price : G.E → ℝ) (R : ℝ)
    (hscore : ∀ p : G.SubtwoWeightedPattern,
      (∑ e : G.E, price e * (p.val e : ℝ)) ≤ R) :
    (∑ e : G.E, price e * demand e) ≤ C.cost * R := by
  calc
    _ = ∑ e : G.E, price e * (∑ p : C.P, C.mass p * (C.pattern p e : ℝ)) := by
      simp_rw [C.covers]
    _ = ∑ p : C.P, C.mass p * (∑ e : G.E, price e * (C.pattern p e : ℝ)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ ≤ ∑ p : C.P, C.mass p * R := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_left (hscore (C.toWeightedPattern p)) (C.mass_nonneg p)
    _ = C.cost * R := by rw [cost, Finset.sum_mul]

end SubtwoFractionalDemandColoring
end WeightedEdgeColoring.WeightedMultigraph
