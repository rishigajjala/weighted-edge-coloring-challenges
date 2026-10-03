import WeightedEdgeColoring.SubtwoBlockPartition
import WeightedEdgeColoring.SubtwoOrdinaryBridge

/-!
# The actual integer packet graph after the three-stage contraction

Each indexed source edge is replaced by its prescribed number of ordinary
packet edges. Integer packet counts bounded by scaled source costs inherit
the degree and odd-set bounds of the constructed final quotient.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Replace each indexed edge by finitely many distinguishable unit edges. -/
def subtwoPacketGraph (count : G.E → ℕ) : WeightedMultigraph.{u} where
  V := G.V
  E := (e : G.E) × Fin (count e)
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := inferInstance
  fst := fun p ↦ G.fst p.1
  snd := fun p ↦ G.snd p.1
  noLoop := fun p ↦ G.noLoop p.1
  weight := fun _ ↦ 1
  weight_pos := fun _ ↦ by norm_num
  weight_le_one := fun _ ↦ le_rfl

theorem subtwo_sum_packet_edges (count : G.E → ℕ) (f : G.E → ℝ) :
    (∑ p : (G.subtwoPacketGraph count).E, f p.1) =
      ∑ e : G.E, (count e : ℝ) * f e := by
  change (∑ p : ((e : G.E) × Fin (count e)), f p.1) = _
  rw [Fintype.sum_sigma]
  simp

theorem subtwo_unit_vertex_cost (v : G.V) :
    G.subtwoVertexCost (fun _ ↦ 1) v =
      (G.degreeOn Finset.univ v : ℝ) := by
  classical
  rw [G.subtwoVertexCost_eq_incidence]
  simp [degreeOn]

theorem subtwo_unit_internal_cost (S : Finset G.V) :
    G.subtwoInternalCost (fun _ ↦ 1) S =
      ((G.internalEdges Finset.univ S).card : ℝ) := by
  classical
  simp [subtwoInternalCost, internalEdges]

/-- The degree of the packet graph counts all copies of each incident edge. -/
theorem subtwo_packet_degree_eq (count : G.E → ℕ) (v : G.V) :
    ((G.subtwoPacketGraph count).degreeOn Finset.univ v : ℝ) =
      G.subtwoVertexCost (fun e ↦ (count e : ℝ)) v := by
  classical
  rw [← (G.subtwoPacketGraph count).subtwo_unit_vertex_cost]
  unfold subtwoVertexCost
  change (∑ p : (G.subtwoPacketGraph count).E,
    ((if G.fst p.1 = v then (1 : ℝ) else 0) +
      if G.snd p.1 = v then 1 else 0)) = _
  rw [G.subtwo_sum_packet_edges count (fun e ↦
    (if G.fst e = v then (1 : ℝ) else 0) +
      if G.snd e = v then 1 else 0)]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp_all <;> ring

/-- The internal edge count is the sum of packet multiplicities internally. -/
theorem subtwo_packet_internal_card_eq (count : G.E → ℕ) (S : Finset G.V) :
    (((G.subtwoPacketGraph count).internalEdges Finset.univ S).card : ℝ) =
      G.subtwoInternalCost (fun e ↦ (count e : ℝ)) S := by
  classical
  rw [← (G.subtwoPacketGraph count).subtwo_unit_internal_cost]
  unfold subtwoInternalCost
  change (∑ p : (G.subtwoPacketGraph count).E,
    if G.fst p.1 ∈ S ∧ G.snd p.1 ∈ S then (1 : ℝ) else 0) = _
  rw [G.subtwo_sum_packet_edges count (fun e ↦
    if G.fst e ∈ S ∧ G.snd e ∈ S then (1 : ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp_all

theorem subtwo_packet_degree_le_scaled_cost
    (count : G.E → ℕ) (cost : G.E → ℝ) (N : ℝ)
    (hcount : ∀ e, (count e : ℝ) ≤ N * cost e) (v : G.V) :
    ((G.subtwoPacketGraph count).degreeOn Finset.univ v : ℝ) ≤
      N * G.subtwoVertexCost cost v := by
  classical
  rw [G.subtwo_packet_degree_eq]
  rw [G.subtwoVertexCost_eq_incidence, G.subtwoVertexCost_eq_incidence,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  by_cases he : G.Inc v e
  · simpa [he] using hcount e
  · simp [he]

theorem subtwo_packet_internal_card_le_scaled_cost
    (count : G.E → ℕ) (cost : G.E → ℝ) (N : ℝ)
    (hcount : ∀ e, (count e : ℝ) ≤ N * cost e) (S : Finset G.V) :
    (((G.subtwoPacketGraph count).internalEdges Finset.univ S).card : ℝ) ≤
      N * G.subtwoInternalCost cost S := by
  classical
  rw [G.subtwo_packet_internal_card_eq]
  unfold subtwoInternalCost
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  by_cases he : G.fst e ∈ S ∧ G.snd e ∈ S
  · simpa [he] using hcount e
  · simp [he]

/-- The actual quotient packet graph: first discard internal source edges,
then retain every prescribed packet copy of a crossing edge. -/
noncomputable def subtwoFinalPacketGraph
    (cost : G.E → ℝ) (count : G.E → ℕ) : WeightedMultigraph.{u} := by
  classical
  exact (G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwoPacketGraph
    (fun e ↦ count e.1)

theorem subtwoFinalPacketGraph_degree_le
    (cost : G.E → ℝ) (count : G.E → ℕ) (N : ℝ) (hN : 0 ≤ N)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (hcount : ∀ e, (count e : ℝ) ≤ N * cost e) :
    ∀ v, ((G.subtwoFinalPacketGraph cost count).degreeOn Finset.univ v : ℝ) ≤
      subtwoM * N := by
  classical
  intro v
  have h := (G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwo_packet_degree_le_scaled_cost
    (fun e ↦ count e.1) (fun e ↦ cost e.1) N (fun e ↦ hcount e.1) v
  have hd := G.subtwoFinalQuotient_degree_le cost hcost hpair hdegree v
  change (((G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwoPacketGraph
    (fun e ↦ count e.1)).degreeOn Finset.univ v : ℝ) ≤ _
  nlinarith

theorem subtwoFinalPacketGraph_oddSetDensityAtMost
    (cost : G.E → ℝ) (count : G.E → ℕ) (N : ℝ) (hN : 0 ≤ N)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (hcount : ∀ e, (count e : ℝ) ≤ N * cost e) :
    (G.subtwoFinalPacketGraph cost count).OddSetDensityAtMost
      Finset.univ (subtwoKappa * N) := by
  classical
  intro S hodd hthree
  have h := (G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwo_packet_internal_card_le_scaled_cost
    (fun e ↦ count e.1) (fun e ↦ cost e.1) N (fun e ↦ hcount e.1) S
  have hs := G.subtwoFinalQuotient_all_odd_sets cost hcost hpair hdegree
    S hodd hthree
  change (2 : ℝ) * (((G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwoPacketGraph
    (fun e ↦ count e.1)).internalEdges Finset.univ S).card ≤ _
  nlinarith

end WeightedEdgeColoring.WeightedMultigraph
