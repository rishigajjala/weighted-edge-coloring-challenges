import WeightedEdgeColoring.WeightedMultigraph
import Mathlib.Tactic

/-!
# Incidence accounting for dense three- and five-vertex blocks

These estimates are the bookkeeping core of the dense-set contraction
argument in Section `general-subtwo`. The edge index type allows parallel
edges; `cost` may be a packet charge rather than the original edge weight.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Total charge at one original vertex, counted by endpoint. -/
def subtwoVertexCost (cost : G.E → ℝ) (v : G.V) : ℝ :=
  ∑ e : G.E, ((if G.fst e = v then cost e else 0) +
    (if G.snd e = v then cost e else 0))

/-- Endpoint counting agrees with the existing incidence relation because
    the multigraph has no loops. -/
theorem subtwoVertexCost_eq_incidence (cost : G.E → ℝ) (v : G.V) :
    G.subtwoVertexCost cost v =
      ∑ e : G.E, if G.Inc v e then cost e else 0 := by
  classical
  unfold subtwoVertexCost Inc
  apply Finset.sum_congr rfl
  intro e _
  by_cases hf : G.fst e = v
  · have hs : G.snd e ≠ v := by
      intro h
      exact G.noLoop e (hf.trans h.symm)
    simp [hf, hs]
  · by_cases hs : G.snd e = v <;> simp [hf, hs]

/-- Charge carried by edges with both endpoints in a vertex set. -/
def subtwoInternalCost (cost : G.E → ℝ) (S : Finset G.V) : ℝ :=
  ∑ e : G.E, if G.fst e ∈ S ∧ G.snd e ∈ S then cost e else 0

/-- Charge crossing the boundary of a vertex set. -/
def subtwoBoundaryCost (cost : G.E → ℝ) (S : Finset G.V) : ℝ :=
  ∑ e : G.E, if (G.fst e ∈ S) ≠ (G.snd e ∈ S) then cost e else 0

/-- Each edge internal to `S` occurs twice in the incident-cost sum;
    each crossing edge occurs once. -/
theorem subtwo_incidence_identity (cost : G.E → ℝ) (S : Finset G.V) :
    (∑ v ∈ S, G.subtwoVertexCost cost v) =
      2 * G.subtwoInternalCost cost S + G.subtwoBoundaryCost cost S := by
  classical
  unfold subtwoVertexCost subtwoInternalCost subtwoBoundaryCost
  calc
    (∑ v ∈ S, ∑ e : G.E,
      ((if G.fst e = v then cost e else 0) +
      (if G.snd e = v then cost e else 0))) =
        ∑ e : G.E, ∑ v ∈ S,
          ((if G.fst e = v then cost e else 0) +
          (if G.snd e = v then cost e else 0)) := by rw [Finset.sum_comm]
    _ = ∑ e : G.E,
        ((if G.fst e ∈ S then cost e else 0) +
        (if G.snd e ∈ S then cost e else 0)) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.sum_add_distrib]
          by_cases hf : G.fst e ∈ S <;> by_cases hs : G.snd e ∈ S <;>
            simp [hf, hs]
    _ = ∑ e : G.E,
        (2 * (if G.fst e ∈ S ∧ G.snd e ∈ S then cost e else 0) +
        (if (G.fst e ∈ S) ≠ (G.snd e ∈ S) then cost e else 0)) := by
          apply Finset.sum_congr rfl
          intro e _
          by_cases hf : G.fst e ∈ S <;> by_cases hs : G.snd e ∈ S <;>
            simp [hf, hs]; ring
    _ = 2 * (∑ e : G.E,
          if G.fst e ∈ S ∧ G.snd e ∈ S then cost e else 0) +
        (∑ e : G.E,
          if (G.fst e ∈ S) ≠ (G.snd e ∈ S) then cost e else 0) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The exact boundary formula for an arbitrary contracted block. -/
theorem subtwo_boundary_eq_degree_sub_internal (cost : G.E → ℝ)
    (S : Finset G.V) :
    G.subtwoBoundaryCost cost S =
      (∑ v ∈ S, G.subtwoVertexCost cost v) -
        2 * G.subtwoInternalCost cost S := by
  linarith [G.subtwo_incidence_identity cost S]

/-- A dense block of size `n` has small external charge. -/
theorem subtwo_boundary_lt_of_dense (cost : G.E → ℝ)
    (S : Finset G.V) (n : ℕ) (M κ : ℝ)
    (hcard : S.card = n)
    (hdegree : ∀ v ∈ S, G.subtwoVertexCost cost v ≤ M)
    (hdense : ((n : ℝ) - 1) * κ / 2 < G.subtwoInternalCost cost S) :
    G.subtwoBoundaryCost cost S < (n : ℝ) * M - ((n : ℝ) - 1) * κ := by
  have hsum : (∑ v ∈ S, G.subtwoVertexCost cost v) ≤ (n : ℝ) * M := by
    calc
      _ ≤ ∑ _v ∈ S, M := Finset.sum_le_sum fun v hv => hdegree v hv
      _ = (n : ℝ) * M := by simp [hcard]
  rw [G.subtwo_boundary_eq_degree_sub_internal cost S]
  linarith

/-- The manuscript's boundary estimate for a dense triangle. -/
theorem subtwo_triangle_boundary_lt (cost : G.E → ℝ) (S : Finset G.V)
    (M κ : ℝ) (hcard : S.card = 3)
    (hdegree : ∀ v ∈ S, G.subtwoVertexCost cost v ≤ M)
    (hdense : κ < G.subtwoInternalCost cost S) :
    G.subtwoBoundaryCost cost S < 3 * M - 2 * κ := by
  have h := G.subtwo_boundary_lt_of_dense cost S 3 M κ hcard hdegree (by norm_num; linarith)
  norm_num at h ⊢
  linarith

/-- The manuscript's boundary estimate for a dense five-set. -/
theorem subtwo_five_boundary_lt (cost : G.E → ℝ) (S : Finset G.V)
    (M κ : ℝ) (hcard : S.card = 5)
    (hdegree : ∀ v ∈ S, G.subtwoVertexCost cost v ≤ M)
    (hdense : 2 * κ < G.subtwoInternalCost cost S) :
    G.subtwoBoundaryCost cost S < 5 * M - 4 * κ := by
  have h := G.subtwo_boundary_lt_of_dense cost S 5 M κ hcard hdegree (by norm_num; linarith)
  norm_num at h ⊢
  linarith

/-- Every set of at least seven vertices satisfies the manuscript's
    large odd-set estimate when `7 M / 6 ≤ κ`. -/
theorem subtwo_large_odd_density (cost : G.E → ℝ) (S : Finset G.V)
    (M κ : ℝ) (hcard : 7 ≤ S.card) (hM : 0 ≤ M)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v ∈ S, G.subtwoVertexCost cost v ≤ M)
    (hconstants : 7 * M ≤ 6 * κ) :
    G.subtwoInternalCost cost S ≤ κ * ((S.card : ℝ) - 1) / 2 := by
  have hsum : (∑ v ∈ S, G.subtwoVertexCost cost v) ≤ (S.card : ℝ) * M := by
    calc
      _ ≤ ∑ _v ∈ S, M := Finset.sum_le_sum fun v hv => hdegree v hv
      _ = (S.card : ℝ) * M := by simp
  have hboundary : 0 ≤ G.subtwoBoundaryCost cost S := by
    unfold subtwoBoundaryCost
    apply Finset.sum_nonneg
    intro e _
    split_ifs <;> first | exact hcost e | exact le_refl _
  have hinc := G.subtwo_incidence_identity cost S
  have hn : (7 : ℝ) ≤ S.card := by exact_mod_cast hcard
  have hgap : 0 ≤ κ - M := by linarith
  have hproduct := mul_nonneg (show 0 ≤ (S.card : ℝ) - 7 by linarith) hgap
  have hscaled : (S.card : ℝ) * M ≤ κ * ((S.card : ℝ) - 1) := by
    nlinarith
  linarith


/-- Nonnegative edge charges give a nonnegative block boundary. -/
theorem subtwo_boundary_nonneg (cost : G.E → ℝ) (S : Finset G.V)
    (hcost : ∀ e, 0 ≤ cost e) : 0 ≤ G.subtwoBoundaryCost cost S := by
  unfold subtwoBoundaryCost
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> first | exact hcost e | exact le_refl _

/-- The internal cost is at most half the total incident cost of a set. -/
theorem subtwo_internal_le_half_degree (cost : G.E → ℝ) (S : Finset G.V)
    (hcost : ∀ e, 0 ≤ cost e) :
    2 * G.subtwoInternalCost cost S ≤
      ∑ v ∈ S, G.subtwoVertexCost cost v := by
  have h := G.subtwo_incidence_identity cost S
  have hb := G.subtwo_boundary_nonneg cost S hcost
  linarith

/-- Accounting interface for an expanded quotient set. Here `a` old
    triangle blocks and `b` five-blocks increase the expanded vertex
    count by `2a+4b`. `removed` is their total internal cost. -/
theorem subtwo_expansion_cost_bound (cost : G.E → ℝ)
    (U : Finset G.V) (s a b : ℕ) (M κ removed quotientCost : ℝ)
    (hcard : U.card = s + 2 * a + 4 * b)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v ∈ U, G.subtwoVertexCost cost v ≤ M)
    (hremoved : ((a : ℝ) + 2 * b) * κ ≤ removed)
    (hquotient : quotientCost = G.subtwoInternalCost cost U - removed) :
    quotientCost ≤ (s : ℝ) * M / 2 +
      (M - κ) * ((a : ℝ) + 2 * b) := by
  have hsum : (∑ v ∈ U, G.subtwoVertexCost cost v) ≤ (U.card : ℝ) * M := by
    calc
      _ ≤ ∑ _v ∈ U, M := Finset.sum_le_sum fun v hv => hdegree v hv
      _ = (U.card : ℝ) * M := by simp
  have hi := G.subtwo_internal_le_half_degree cost U hcost
  have hc : (U.card : ℝ) = (s : ℝ) + 2 * a + 4 * b := by
    exact_mod_cast hcard
  rw [hc] at hsum
  rw [hquotient]
  nlinarith

/-- A quotient five-set containing a dense block has cost below the
    `2κ` odd-set threshold, provided the local constants satisfy the
    manuscript inequalities. -/
theorem subtwo_quotient_five_bound (cost : G.E → ℝ)
    (U : Finset G.V) (a b : ℕ) (M κ removed quotientCost : ℝ)
    (hcard : U.card = 5 + 2 * a + 4 * b)
    (hblock : 1 ≤ a + 2 * b)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v ∈ U, G.subtwoVertexCost cost v ≤ M)
    (hremoved : ((a : ℝ) + 2 * b) * κ ≤ removed)
    (hquotient : quotientCost = G.subtwoInternalCost cost U - removed)
    (hMk : M ≤ κ) (hconstants : 7 * M / 2 - κ < 2 * κ) :
    quotientCost < 2 * κ := by
  have hexpand := G.subtwo_expansion_cost_bound cost U 5 a b M κ removed quotientCost
    hcard hcost hdegree hremoved hquotient
  have hb : (1 : ℝ) ≤ (a : ℝ) + 2 * b := by exact_mod_cast hblock
  have hsign : M - κ ≤ 0 := by linarith
  have hprod := mul_nonpos_of_nonpos_of_nonneg hsign
    (show 0 ≤ (a : ℝ) + 2 * b - 1 by linarith)
  norm_num at hexpand
  nlinarith

/-- The rational constants used in the dense-set argument. -/
noncomputable def subtwoM : ℝ := 1691031 / 1000000

noncomputable def subtwoKappa : ℝ := 1999 / 1000

theorem subtwo_constant_inequalities :
    0 ≤ subtwoM ∧ subtwoM < subtwoKappa ∧
    7 * subtwoM ≤ 6 * subtwoKappa ∧
    7 * subtwoM / 2 - subtwoKappa < 2 * subtwoKappa := by
  unfold subtwoM subtwoKappa
  norm_num

/-- Numerical comparisons used to exclude overlapping dense blocks and
    quotient triangles after contraction. -/
theorem subtwo_overlap_constant_inequalities :
    2 * subtwoM < 2 * subtwoKappa ∧
    9 * subtwoM / 2 < 4 * subtwoKappa ∧
    4 * subtwoM + 1 < 4 * subtwoKappa ∧
    7 * subtwoM / 2 + subtwoKappa < 4 * subtwoKappa ∧
    (5 * subtwoM - 4 * subtwoKappa) + 1 < subtwoKappa ∧
    (2 * (3 * subtwoM - 2 * subtwoKappa) + subtwoM) / 2 < subtwoKappa := by
  unfold subtwoM subtwoKappa
  norm_num

end WeightedMultigraph
end WeightedEdgeColoring
