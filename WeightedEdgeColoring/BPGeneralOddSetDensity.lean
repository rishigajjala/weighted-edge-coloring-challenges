import WeightedEdgeColoring.ShannonBridge

/-!
# Odd-set bookkeeping for the general packet graph

Edmonds' fractional edge-coloring bound has one vertex-degree constraint and
one constraint for every odd vertex set.  This file proves the elementary
part of the manuscript argument.  A separate triangle bound controls odd
sets of size three.  For every odd set of size at least five, summing the
vertex degrees loses at most the factor `5/4`.

The final definition isolates the standard external input combining the
fractional matching-polytope formula with near-fractional ordinary edge
coloring.  No such external theorem is assumed in the concrete counting
lemmas.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Edges of `F` with both endpoints in `S`. -/
def internalEdges (F : Finset G.E) (S : Finset G.V) : Finset G.E :=
  F.filter fun e ↦ G.fst e ∈ S ∧ G.snd e ∈ S

/-- Number of endpoints of an edge which lie in `S`.  It is at most two,
and equals two exactly for an internal edge. -/
def endpointCountIn (S : Finset G.V) (e : G.E) : ℕ :=
  (if G.fst e ∈ S then 1 else 0) +
    (if G.snd e ∈ S then 1 else 0)

theorem sum_incidence_indicator_eq_endpointCountIn
    (S : Finset G.V) (e : G.E) :
    (∑ v ∈ S, if G.Inc v e then 1 else 0) =
      G.endpointCountIn S e := by
  classical
  unfold Inc endpointCountIn
  calc
    (∑ v ∈ S, if G.fst e = v ∨ G.snd e = v then 1 else 0) =
        ∑ v ∈ S,
          ((if G.fst e = v then 1 else 0) +
            (if G.snd e = v then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases hf : G.fst e = v <;>
        by_cases hs : G.snd e = v <;>
          simp [hf, hs]
      exact (G.noLoop e) (hf.trans hs.symm)
    _ = (∑ v ∈ S, if G.fst e = v then 1 else 0) +
          ∑ v ∈ S, if G.snd e = v then 1 else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (if G.fst e ∈ S then 1 else 0) +
          (if G.snd e ∈ S then 1 else 0) := by simp

/-- Handshake identity restricted to a vertex set. -/
theorem sum_degreeOn_eq_sum_endpointCountIn
    (F : Finset G.E) (S : Finset G.V) :
    (∑ v ∈ S, G.degreeOn F v) =
      ∑ e ∈ F, G.endpointCountIn S e := by
  classical
  unfold degreeOn
  calc
    (∑ v ∈ S, (F.filter (G.Inc v)).card) =
        ∑ v ∈ S, ∑ e ∈ F, if G.Inc v e then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _hv
      simp
    _ = ∑ e ∈ F, ∑ v ∈ S, if G.Inc v e then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ F, G.endpointCountIn S e := by
      apply Finset.sum_congr rfl
      intro e _he
      exact G.sum_incidence_indicator_eq_endpointCountIn S e

/-- Each internal edge contributes two to the restricted degree sum. -/
theorem two_mul_internalEdges_card_le_sum_degreeOn
    (F : Finset G.E) (S : Finset G.V) :
    2 * (G.internalEdges F S).card ≤
      ∑ v ∈ S, G.degreeOn F v := by
  rw [G.sum_degreeOn_eq_sum_endpointCountIn F S]
  calc
    2 * (G.internalEdges F S).card =
        ∑ _e ∈ G.internalEdges F S, 2 := by
      simp [Nat.mul_comm]
    _ = ∑ e ∈ G.internalEdges F S, G.endpointCountIn S e := by
      apply Finset.sum_congr rfl
      intro e heInternal
      have he := (Finset.mem_filter.mp heInternal).2
      simp [endpointCountIn, he.1, he.2]
    _ ≤ ∑ e ∈ F, G.endpointCountIn S e := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _e _heF _heNot ↦ Nat.zero_le _)

/-- Real-valued handshake bound under a uniform degree cap. -/
theorem two_mul_internalEdges_card_le_card_mul_degreeCap
    (F : Finset G.E) (S : Finset G.V) (A : ℝ)
    (hdegree : ∀ v, (G.degreeOn F v : ℝ) ≤ A) :
    (2 : ℝ) * (G.internalEdges F S).card ≤ (S.card : ℝ) * A := by
  have hhandshake := G.two_mul_internalEdges_card_le_sum_degreeOn F S
  have hcast :
      (2 : ℝ) * (G.internalEdges F S).card ≤
        ∑ v ∈ S, (G.degreeOn F v : ℝ) := by
    exact_mod_cast hhandshake
  calc
    (2 : ℝ) * (G.internalEdges F S).card ≤
        ∑ v ∈ S, (G.degreeOn F v : ℝ) := hcast
    _ ≤ ∑ _v ∈ S, A := by
      exact Finset.sum_le_sum fun v _hv ↦ hdegree v
    _ = (S.card : ℝ) * A := by simp

/-- The odd-set constraints in the fractional edge-coloring polytope,
written without division. -/
def OddSetDensityAtMost (F : Finset G.E) (L : ℝ) : Prop :=
  ∀ S : Finset G.V, Odd S.card → 3 ≤ S.card →
    (2 : ℝ) * (G.internalEdges F S).card ≤
      L * ((S.card : ℝ) - 1)

/-- A separate bound on every three-vertex set.  In the packet construction
the right side is `2n`. -/
def TriangleEdgeCountAtMost (F : Finset G.E) (B : ℝ) : Prop :=
  ∀ S : Finset G.V, S.card = 3 →
    ((G.internalEdges F S).card : ℝ) ≤ B

theorem odd_three_or_five_le {s : ℕ} (hodd : Odd s) (hthree : 3 ≤ s) :
    s = 3 ∨ 5 ≤ s := by
  rcases hodd with ⟨k, hk⟩
  omega

/-- Degree bounds control every odd set of size at least five with loss at
most `5/4`; the triangle hypothesis handles the only smaller odd set. -/
theorem oddSetDensityAtMost_max_two_fiveFourth
    (F : Finset G.E) (n A : ℝ)
    (hn : 0 ≤ n) (hA : 0 ≤ A)
    (hdegree : ∀ v, (G.degreeOn F v : ℝ) ≤ A)
    (htriangle : G.TriangleEdgeCountAtMost F (2 * n)) :
    G.OddSetDensityAtMost F
      (max (2 * n) ((5 / 4 : ℝ) * A)) := by
  intro S hodd hthree
  rcases odd_three_or_five_le hodd hthree with hS3 | hS5
  · have htri := htriangle S hS3
    have hmax : 2 * n ≤ max (2 * n) ((5 / 4 : ℝ) * A) :=
      le_max_left _ _
    rw [hS3]
    norm_num at htri ⊢
    nlinarith
  · have hhandshake :=
      G.two_mul_internalEdges_card_le_card_mul_degreeCap F S A hdegree
    have hs : (5 : ℝ) ≤ S.card := by exact_mod_cast hS5
    have hfactor :
        (S.card : ℝ) * A ≤
          ((5 / 4 : ℝ) * A) * ((S.card : ℝ) - 1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : (1 : ℝ) ≤ S.card)) hA]
    have hmax : (5 / 4 : ℝ) * A ≤
        max (2 * n) ((5 / 4 : ℝ) * A) := le_max_right _ _
    have hcardNonneg : 0 ≤ (S.card : ℝ) - 1 := by linarith
    calc
      (2 : ℝ) * (G.internalEdges F S).card ≤
          (S.card : ℝ) * A := hhandshake
      _ ≤ ((5 / 4 : ℝ) * A) * ((S.card : ℝ) - 1) := hfactor
      _ ≤ max (2 * n) ((5 / 4 : ℝ) * A) *
          ((S.card : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right hmax hcardNonneg

end WeightedMultigraph

universe u

/-- Uniform near-fractional coloring statement for ordinary multigraphs.

The degree and odd-set hypotheses say that the fractional chromatic index is
at most `L` by Edmonds' matching-polytope theorem.  Sanders--Steurer then
gives a proper coloring with `L + o(n)` colors, uniformly when `L = O(n)`.
This formulation keeps exactly the uniformity needed by the weighted packet
argument and no algorithmic assumption. -/
def OrdinaryMultigraphNearFractionalColoring : Prop :=
  ∀ C η : ℝ, 0 < C → 0 < η → ∃ N : ℕ,
    ∀ (G : WeightedMultigraph.{u}) (F : Finset G.E)
      (n : ℕ) (L : ℝ),
      N ≤ n →
      0 ≤ L →
      L ≤ C * n →
      (∀ v, (G.degreeOn F v : ℝ) ≤ L) →
      G.OddSetDensityAtMost F L →
      ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ L + η * n ∧
        ∃ color : G.E → Fin q, G.IsProperOn F color

end WeightedEdgeColoring
