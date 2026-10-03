import WeightedEdgeColoring.SubtwoContraction

/-!
# Density bounds for the actual quotient graph

These results apply the exact contraction identities to fibers of size
`1+2r`. Ordinary vertices have `r=0`, three-blocks `r=1`, and five-blocks
`r=2`. The cost paid inside a fiber is at least `κr`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- A loopless graph has no internal edge in a singleton. -/
theorem subtwo_internal_singleton (cost : G.E → ℝ) (v : G.V) :
    G.subtwoInternalCost cost {v} = 0 := by
  classical
  unfold subtwoInternalCost
  apply Finset.sum_eq_zero
  intro e _
  have hn : ¬ (G.fst e = v ∧ G.snd e = v) := by
    rintro ⟨hf, hs⟩
    exact G.noLoop e (hf.trans hs.symm)
  simp [hn]

theorem subtwo_boundary_singleton (cost : G.E → ℝ) (v : G.V) :
    G.subtwoBoundaryCost cost {v} = G.subtwoVertexCost cost v := by
  have h := G.subtwo_incidence_identity cost {v}
  simpa [G.subtwo_internal_singleton] using h.symm

/-- The total cost deleted from the fibers pays for their total rank. -/
theorem subtwo_removed_cost_ge (block : G.V → Q) (cost : G.E → ℝ)
    (S : Finset Q) (rank : Q → ℕ) (κ : ℝ)
    (hdense : ∀ q ∈ S,
      (rank q : ℝ) * κ ≤ G.subtwoInternalCost cost (G.subtwoFiber block q)) :
    ((∑ q ∈ S, rank q : ℕ) : ℝ) * κ ≤
      ∑ q ∈ S, G.subtwoInternalCost cost (G.subtwoFiber block q) := by
  calc
    ((∑ q ∈ S, rank q : ℕ) : ℝ) * κ = ∑ q ∈ S, (rank q : ℝ) * κ := by
      simp [Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum hdense

/-- Expansion and subtraction for actual quotient edges, with no
assumed scalar cost identity. -/
theorem subtwo_quotient_set_cost_bound (block : G.V → Q) (cost : G.E → ℝ)
    (S : Finset Q) (rank : Q → ℕ) (M κ : ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v ∈ G.subtwoExpand block S, G.subtwoVertexCost cost v ≤ M)
    (hsize : ∀ q ∈ S, (G.subtwoFiber block q).card = 1 + 2 * rank q)
    (hdense : ∀ q ∈ S,
      (rank q : ℝ) * κ ≤ G.subtwoInternalCost cost (G.subtwoFiber block q)) :
    (G.subtwoQuotient block).subtwoInternalCost (fun e ↦ cost e.1) S ≤
      (S.card : ℝ) * M / 2 + (M - κ) * (∑ q ∈ S, rank q : ℕ) := by
  have hc := G.subtwo_expand_card_of_fiber_sizes block S rank hsize
  have hi := G.subtwo_contraction_internal_identity block cost S
  have hr := G.subtwo_removed_cost_ge block cost S rank κ hdense
  have h := G.subtwo_expansion_cost_bound cost (G.subtwoExpand block S)
    S.card (∑ q ∈ S, rank q) 0 M κ
    (∑ q ∈ S, G.subtwoInternalCost cost (G.subtwoFiber block q))
    ((G.subtwoQuotient block).subtwoInternalCost (fun e ↦ cost e.1) S)
    (by simpa using hc) hcost hdegree (by simpa using hr) (by linarith)
  simpa using h

/-- A five-set with at least one contracted block is below the density
threshold. Here the block condition is the positive total fiber rank. -/
theorem subtwo_quotient_five_with_block (block : G.V → Q) (cost : G.E → ℝ)
    (S : Finset Q) (rank : Q → ℕ) (M κ : ℝ)
    (hfive : S.card = 5) (hblock : 1 ≤ ∑ q ∈ S, rank q)
    (hcost : ∀ e, 0 ≤ cost e)
    (hdegree : ∀ v ∈ G.subtwoExpand block S, G.subtwoVertexCost cost v ≤ M)
    (hsize : ∀ q ∈ S, (G.subtwoFiber block q).card = 1 + 2 * rank q)
    (hdense : ∀ q ∈ S,
      (rank q : ℝ) * κ ≤ G.subtwoInternalCost cost (G.subtwoFiber block q))
    (hMk : M ≤ κ) (hconstants : 7 * M / 2 - κ < 2 * κ) :
    (G.subtwoQuotient block).subtwoInternalCost (fun e ↦ cost e.1) S < 2 * κ := by
  have h := G.subtwo_quotient_set_cost_bound block cost S rank M κ
    hcost hdegree hsize hdense
  have hr : (1 : ℝ) ≤ (∑ q ∈ S, rank q : ℕ) := by exact_mod_cast hblock
  have hp := mul_nonpos_of_nonpos_of_nonneg (show M - κ ≤ 0 by linarith)
    (show (0 : ℝ) ≤ (∑ q ∈ S, rank q : ℕ) - 1 by linarith)
  rw [hfive] at h
  norm_num only [Nat.cast_ofNat] at h
  nlinarith

/-- Once triangle and five-set inequalities have been checked, the
degree bound proves every remaining odd-set inequality. -/
theorem subtwo_all_odd_sets_of_small_sets (cost : G.E → ℝ) (M κ : ℝ)
    (hcost : ∀ e, 0 ≤ cost e) (hM : 0 ≤ M)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ M)
    (hconstants : 7 * M ≤ 6 * κ)
    (htri : ∀ S : Finset G.V, S.card = 3 → G.subtwoInternalCost cost S ≤ κ)
    (hfive : ∀ S : Finset G.V, S.card = 5 → G.subtwoInternalCost cost S ≤ 2 * κ) :
    ∀ S : Finset G.V, Odd S.card → 3 ≤ S.card →
      G.subtwoInternalCost cost S ≤ κ * ((S.card : ℝ) - 1) / 2 := by
  intro S hodd hcard
  by_cases hlarge : 7 ≤ S.card
  · exact G.subtwo_large_odd_density cost S M κ hlarge hM hcost
      (fun v _ ↦ hdegree v) hconstants
  · have hsmall : S.card = 3 ∨ S.card = 5 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    rcases hsmall with h3 | h5
    · have hh := htri S h3
      rw [h3]
      norm_num
      linarith
    · have hh := hfive S h5
      rw [h5]
      norm_num
      linarith

end WeightedEdgeColoring.WeightedMultigraph
