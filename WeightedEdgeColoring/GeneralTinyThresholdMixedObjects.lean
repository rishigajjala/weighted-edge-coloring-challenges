import WeightedEdgeColoring.GeneralTinyThresholdPacketization
import WeightedEdgeColoring.GeneralTinyThresholdCharge
import WeightedEdgeColoring.BoundedMultiplicityPairCodegree

/-!
# Mixed objects at a tiny threshold, without a bipartition

Edges of weight at least `tau` remain singleton objects.  Edges below `tau`
are replaced by the endpoint-pair packets supplied by
`GeneralTinyThresholdPacketization`.  Thus every object coloring expands to
the original graph while preserving all vertex--color loads exactly.
-/

open scoped BigOperators Sym2

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable {G : WeightedMultigraph.{u}} {tau : ℝ}

namespace GeneralTinyThresholdPacketization

variable (P : G.GeneralTinyThresholdPacketization tau)

/-- Physical edges which were not sent to the tiny restriction. -/
def nonTinyEdges (G : WeightedMultigraph.{u}) (tau : ℝ) : Finset G.E :=
  Finset.univ \ G.edgesBelow tau

/-- Objects are non-tiny singleton edges or packets of tiny physical edges. -/
abbrev Object := {e : G.E // e ∈ nonTinyEdges G tau} ⊕ P.Packet

def mixedPacketOf (e : G.E) : P.Object :=
  if he : e ∈ G.edgesBelow tau then
    Sum.inr (P.packetization.packetOf ⟨e, he⟩)
  else
    Sum.inl ⟨e, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he⟩⟩

/-- The mixed singleton/packet partition of every physical edge. -/
def mixedPacketization : G.Packetization where
  Packet := P.Object
  instFintypePacket := inferInstance
  instDecidableEqPacket := inferInstance
  packetOf := P.mixedPacketOf
  tail
    | Sum.inl e => G.fst e.1
    | Sum.inr p => P.packetization.tail p
  head
    | Sum.inl e => G.snd e.1
    | Sum.inr p => P.packetization.head p
  noLoop
    | Sum.inl e => G.noLoop e.1
    | Sum.inr p => P.packetization.noLoop p
  incidence := by
    intro v e
    by_cases he : e ∈ G.edgesBelow tau
    · simp only [mixedPacketOf, he, dite_true]
      exact P.packetization.groupedGraph_inc_packetOf v ⟨e, he⟩
    · simp [mixedPacketOf, he, Inc]
  onto := by
    intro o
    rcases o with e | p
    · refine ⟨e.1, ?_⟩
      have he : e.1 ∉ G.edgesBelow tau := (Finset.mem_sdiff.mp e.2).2
      simp [mixedPacketOf, he]
    · obtain ⟨e, he⟩ := P.packetization.onto p
      refine ⟨e.1, ?_⟩
      simp [mixedPacketOf, e.2, he]
  weight_le_one := by
    intro o
    rcases o with e | p
    · change (∑ f : G.E,
        if P.mixedPacketOf f = Sum.inl e then G.weight f else 0) ≤ 1
      have he : e.1 ∉ G.edgesBelow tau := (Finset.mem_sdiff.mp e.2).2
      calc
        _ = G.weight e.1 := by
          rw [Finset.sum_eq_single e.1]
          · simp [mixedPacketOf, he]
          · intro f _hf hne
            by_cases hf : f ∈ G.edgesBelow tau
            · simp [mixedPacketOf, hf]
            · simp [mixedPacketOf, hf, Subtype.ext_iff, hne]
          · simp
        _ ≤ 1 := G.weight_le_one e.1
    · change (∑ f : G.E,
        if P.mixedPacketOf f = Sum.inr p then G.weight f else 0) ≤ 1
      calc
        _ = ∑ f : G.E, if hf : f ∈ G.edgesBelow tau then
            (if P.packetization.packetOf ⟨f, hf⟩ = p then G.weight f else 0)
          else 0 := by
            apply Finset.sum_congr rfl
            intro f _hf
            by_cases hf : f ∈ G.edgesBelow tau <;>
              simp [mixedPacketOf, hf]
        _ = ∑ e : (G.belowRestriction tau).E,
            if P.packetization.packetOf e = p then
              (G.belowRestriction tau).weight e else 0 := by
          symm
          have hs := Finset.sum_subtype
            (p := fun e : G.E => e ∈ G.edgesBelow tau)
            (F := inferInstance)
            (G.edgesBelow tau) (by simp)
            (fun f : G.E => if hf : f ∈ G.edgesBelow tau then
              (if P.packetization.packetOf ⟨f, hf⟩ = p then G.weight f else 0)
              else 0)
          have hs' :
              (∑ f ∈ G.edgesBelow tau, if hf : f ∈ G.edgesBelow tau then
                (if P.packetization.packetOf ⟨f, hf⟩ = p then G.weight f else 0)
                else 0) =
              ∑ e : (G.belowRestriction tau).E,
                if P.packetization.packetOf e = p then G.weight e.1 else 0 := by
            simpa using hs
          have hfilt :
              (∑ f : G.E, if hf : f ∈ G.edgesBelow tau then
                (if P.packetization.packetOf ⟨f, hf⟩ = p then G.weight f else 0)
                else 0) =
              ∑ f ∈ G.edgesBelow tau, if hf : f ∈ G.edgesBelow tau then
                (if P.packetization.packetOf ⟨f, hf⟩ = p then G.weight f else 0)
                else 0 := by
            symm
            apply Finset.sum_subset (Finset.subset_univ _)
            intro f _hf hfnot
            simp [hfnot]
          exact hs'.symm.trans hfilt.symm
        _ ≤ 1 := P.packetization.weight_le_one p

/-- Named incidence interface for the full mixed packetization. -/
theorem mixedObjectGraph_inc_packetOf (v : G.V) (e : G.E) :
    P.mixedPacketization.groupedGraph.Inc v
        (P.mixedPacketization.packetOf e) ↔ G.Inc v e :=
  P.mixedPacketization.groupedGraph_inc_packetOf v e

/-- Every mixed object is represented by at least one physical edge. -/
theorem mixedPacketization_surjective :
    Function.Surjective P.mixedPacketization.packetOf :=
  P.mixedPacketization.onto

@[simp] theorem mixedPacketization_packetOf_nonTiny
    (e : {e : G.E // e ∈ nonTinyEdges G tau}) :
    P.mixedPacketization.packetOf e.1 = Sum.inl e := by
  have he : e.1 ∉ G.edgesBelow tau := (Finset.mem_sdiff.mp e.2).2
  simp [mixedPacketization, mixedPacketOf, he]

@[simp] theorem mixedPacketization_packetOf_tiny
    (e : (G.belowRestriction tau).E) :
    P.mixedPacketization.packetOf e.1 =
      Sum.inr (P.packetization.packetOf e) := by
  simp [mixedPacketization, mixedPacketOf, e.2]

/-- A non-tiny singleton object has exactly its physical weight. -/
theorem mixedPacketWeight_inl
    (e : {e : G.E // e ∈ nonTinyEdges G tau}) :
    P.mixedPacketization.packetWeight (Sum.inl e) = G.weight e.1 := by
  classical
  unfold Packetization.packetWeight
  rw [Finset.sum_eq_single e.1]
  · simp
  · intro f _hf hne
    by_cases hf : f ∈ G.edgesBelow tau
    · simp [mixedPacketization, mixedPacketOf, hf]
    · simp [mixedPacketization, mixedPacketOf, hf, Subtype.ext_iff, hne]
  · simp

/-- A tiny packet object has its original packet weight. -/
theorem mixedPacketWeight_inr (p : P.Packet) :
    P.mixedPacketization.packetWeight (Sum.inr p) =
      P.packetization.packetWeight p := by
  classical
  unfold Packetization.packetWeight
  change (∑ f : G.E,
      if P.mixedPacketization.packetOf f = Sum.inr p then G.weight f else 0) =
    ∑ e : (G.belowRestriction tau).E,
      if P.packetization.packetOf e = p then G.weight e.1 else 0
  calc
    _ = ∑ f : G.E, if hf : f ∈ G.edgesBelow tau then
        (if P.packetization.packetOf ⟨f, hf⟩ = p then G.weight f else 0)
      else 0 := by
        apply Finset.sum_congr rfl
        intro f _hf
        by_cases hf : f ∈ G.edgesBelow tau <;>
          simp [mixedPacketization, mixedPacketOf, hf]
    _ = _ := by
      symm
      have hs := Finset.sum_subtype
        (p := fun e : G.E => e ∈ G.edgesBelow tau)
        (F := inferInstance)
        (G.edgesBelow tau) (by simp)
        (fun f : G.E => if hf : f ∈ G.edgesBelow tau then
          (if P.packetization.packetOf ⟨f, hf⟩ = p then G.weight f else 0)
          else 0)
      have hs' :
          (∑ f ∈ G.edgesBelow tau, if hf : f ∈ G.edgesBelow tau then
            (if P.packetization.packetOf ⟨f, hf⟩ = p then G.weight f else 0)
            else 0) =
          ∑ e : (G.belowRestriction tau).E,
            if P.packetization.packetOf e = p then G.weight e.1 else 0 := by
        simpa using hs
      have hfilt :
          (∑ f : G.E, if hf : f ∈ G.edgesBelow tau then
            (if P.packetization.packetOf ⟨f, hf⟩ = p then G.weight f else 0)
            else 0) =
          ∑ f ∈ G.edgesBelow tau, if hf : f ∈ G.edgesBelow tau then
            (if P.packetization.packetOf ⟨f, hf⟩ = p then G.weight f else 0)
            else 0 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro f _hf hfnot
        simp [hfnot]
      exact hs'.symm.trans hfilt.symm

/-- The mixed object graph. -/
abbrev mixedObjectGraph : WeightedMultigraph.{u} :=
  P.mixedPacketization.groupedGraph

/-- Full star weight is preserved exactly by the mixed construction. -/
theorem mixedObjectGraph_starWeight (v : G.V) :
    P.mixedObjectGraph.starWeight v = G.starWeight v := by
  let Q := P.mixedPacketization
  have h := Q.restrictedWeight_originalEdgesOfPackets
    (Finset.univ : Finset Q.Packet) v
  rw [Q.groupedGraph.starWeight_eq_inc_sum, G.starWeight_eq_inc_sum]
  simpa [Packetization.originalEdgesOfPackets, Q] using h.symm

/-- Every full vertex--color load is preserved exactly on expansion. -/
theorem mixedObjectGraph_colorLoad_expandColor
    {q : ℕ} (color : P.Object → Fin q) (v : G.V) (i : Fin q) :
    G.colorLoadOn Finset.univ (P.mixedPacketization.expandColor color) v i =
      P.mixedObjectGraph.colorLoadOn Finset.univ color v i := by
  simpa [Packetization.originalEdgesOfPackets] using
    P.mixedPacketization.colorLoadOn_originalEdgesOfPackets
      (Finset.univ : Finset P.Object) color v i

/-- A feasible weighted coloring of mixed objects expands to a feasible
weighted coloring of the original edges. -/
theorem isWeightedColoring_expandMixedColor
    {q : ℕ} (color : P.Object → Fin q)
    (hcolor : P.mixedObjectGraph.IsWeightedColoring color) :
    G.IsWeightedColoring (P.mixedPacketization.expandColor color) :=
  P.mixedPacketization.isWeightedColoring_expandColor color hcolor

theorem hasWeightedColoring_of_mixedObjectGraph {q : ℕ}
    (h : P.mixedObjectGraph.HasWeightedColoring q) :
    G.HasWeightedColoring q :=
  P.mixedPacketization.hasWeightedColoring_of_groupedGraph h

/-- Tiny packet objects of weight at most `tau`. -/
def smallObjects : Finset P.Object := by
  classical
  exact Finset.univ.filter fun o => match o with
    | Sum.inl _ => False
    | Sum.inr p => P.packetization.packetWeight p ≤ tau

/-- All mixed objects outside the endpoint-simple tiny remainder. -/
def coreObjects : Finset P.Object := Finset.univ \ P.smallObjects

theorem smallObject_weight_le {o : P.Object} (ho : o ∈ P.smallObjects) :
    P.mixedObjectGraph.weight o ≤ tau := by
  rcases o with e | p
  · simp [smallObjects] at ho
  · have hp : P.packetization.packetWeight p ≤ tau := by
      simpa [smallObjects] using ho
    simpa [mixedObjectGraph, Packetization.groupedGraph,
      P.mixedPacketWeight_inr p] using hp

theorem coreObject_weight_ge {o : P.Object} (ho : o ∈ P.coreObjects) :
    tau ≤ P.mixedObjectGraph.weight o := by
  have hsmall : o ∉ P.smallObjects := (Finset.mem_sdiff.mp ho).2
  rcases o with e | p
  · have he : e.1 ∉ G.edgesBelow tau := (Finset.mem_sdiff.mp e.2).2
    have hge : tau ≤ G.weight e.1 := le_of_not_gt
      (fun h => he (G.mem_edgesBelow_iff tau e.1 |>.2 h))
    simpa [mixedObjectGraph, Packetization.groupedGraph,
      P.mixedPacketWeight_inl e] using hge
  · have hp : ¬ P.packetization.packetWeight p ≤ tau := by
      simpa [smallObjects] using hsmall
    have hge := le_of_lt (lt_of_not_ge hp)
    simpa [mixedObjectGraph, Packetization.groupedGraph,
      P.mixedPacketWeight_inr p] using hge

/-- The finite-cutoff core as a weighted multigraph. -/
abbrev coreObjectGraph : WeightedMultigraph.{u} :=
  P.mixedObjectGraph.edgeRestriction P.coreObjects

theorem coreObjectGraph_weight_ge (o : P.coreObjectGraph.E) :
    tau ≤ P.coreObjectGraph.weight o :=
  P.coreObject_weight_ge o.2

/-- The small remainder contains at most one object on each unordered
endpoint pair. -/
theorem smallObjects_endpoint_injective :
    Function.Injective
      (fun o : {o : P.Object // o ∈ P.smallObjects} =>
        s(P.mixedObjectGraph.fst o.1, P.mixedObjectGraph.snd o.1)) := by
  intro x y hxy
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  rcases x with e | p
  · simp [smallObjects] at hx
  · rcases y with f | q
    · simp [smallObjects] at hy
    · apply Subtype.ext
      apply congrArg Sum.inr
      apply P.eq_of_small_of_same_endpoints
      · simpa [smallObjects] using hx
      · simpa [smallObjects] using hy
      · simpa [mixedObjectGraph, Packetization.groupedGraph,
          mixedPacketization] using hxy

/-- The small remainder, packaged as a weighted simple graph. -/
def smallObjectGraph : WeightedSimpleGraph.{u} where
  V := G.V
  E := {o : P.Object // o ∈ P.smallObjects}
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := inferInstance
  fst o := P.mixedObjectGraph.fst o.1
  snd o := P.mixedObjectGraph.snd o.1
  noLoop o := P.mixedObjectGraph.noLoop o.1
  simple := P.smallObjects_endpoint_injective
  weight o := P.mixedObjectGraph.weight o.1
  weight_pos o := P.mixedObjectGraph.weight_pos o.1
  weight_le_one o := P.mixedObjectGraph.weight_le_one o.1

theorem smallObjectGraph_weight_le (o : P.smallObjectGraph.E) :
    P.smallObjectGraph.weight o ≤ tau :=
  P.smallObject_weight_le o.2

/-- In multigraph language the small remainder has endpoint multiplicity
one. -/
theorem smallObjectGraph_pairMultiplicityAtMost :
    P.smallObjectGraph.asMultigraph.PairMultiplicityAtMost 1 :=
  pairMultiplicityAtMost_one_of_simple P.smallObjectGraph

private theorem starCharge_eq_edgeSum (H : WeightedMultigraph.{u})
    (charge : ℝ → ℝ) (v : H.V) :
    H.starCharge charge v =
      ∑ e : H.E, if H.Inc v e then charge (H.weight e) else 0 := by
  classical
  unfold starCharge
  calc
    (∑ e : H.StarEdge v, charge (H.weight e.1)) =
        ∑ e ∈ (Finset.univ : Finset H.E).filter (H.Inc v),
          charge (H.weight e) := by
      symm
      exact Finset.sum_subtype
        ((Finset.univ : Finset H.E).filter (H.Inc v)) (by simp)
        (fun e => charge (H.weight e))
    _ = _ := by rw [Finset.sum_filter]

private theorem edgeRestriction_starCharge (R : Finset G.E)
    (charge : ℝ → ℝ) (v : G.V) :
    (G.edgeRestriction R).starCharge charge v =
      ∑ e ∈ R, if G.Inc v e then charge (G.weight e) else 0 := by
  classical
  rw [starCharge_eq_edgeSum]
  symm
  exact Finset.sum_subtype (p := fun e : G.E => e ∈ R) R (by simp)
    (fun e => if G.Inc v e then charge (G.weight e) else 0)

set_option maxHeartbeats 600000
/-- The complete mixed object graph has at most the original harmonic star
charge plus `4*tau` times the original star weight. -/
theorem mixedObjectGraph_starCharge_le_add_four_mul
    (t : ℕ) (ht : 0 < t)
    (hupper : 2 * tau ≤ (1 : ℝ) / t)
    (hlower : (1 : ℝ) / t ≤ 4 * tau)
    (v : G.V) :
    P.mixedObjectGraph.starCharge harmonicCharge v ≤
      G.starCharge harmonicCharge v + 4 * tau * G.starWeight v := by
  have htiny := P.groupedGraph_starCharge_le_add_four_mul
    t ht hupper hlower v
  have hmixed :
      P.mixedObjectGraph.starCharge harmonicCharge v =
        (G.edgeRestriction (nonTinyEdges G tau)).starCharge harmonicCharge v +
          P.packetization.groupedGraph.starCharge harmonicCharge v := by
    rw [starCharge_eq_edgeSum, starCharge_eq_edgeSum,
      starCharge_eq_edgeSum]
    change (∑ o : P.Object,
      if P.mixedObjectGraph.Inc v o then
        harmonicCharge (P.mixedObjectGraph.weight o) else 0) = _
    rw [Fintype.sum_sum_type]
    congr 1
    · apply Finset.sum_congr rfl
      intro e _he
      change (if G.Inc v e.1 then
          harmonicCharge (P.mixedPacketization.packetWeight (Sum.inl e)) else 0) =
        if G.Inc v e.1 then harmonicCharge (G.weight e.1) else 0
      rw [P.mixedPacketWeight_inl e]
    · apply Finset.sum_congr rfl
      intro p _hp
      change (if P.packetization.groupedGraph.Inc v p then
          harmonicCharge (P.mixedPacketization.packetWeight (Sum.inr p)) else 0) =
        if P.packetization.groupedGraph.Inc v p then
          harmonicCharge (P.packetization.packetWeight p) else 0
      rw [P.mixedPacketWeight_inr p]
  have hpartition :
      (G.edgeRestriction (nonTinyEdges G tau)).starCharge harmonicCharge v +
          (G.belowRestriction tau).starCharge harmonicCharge v =
        G.starCharge harmonicCharge v := by
    rw [edgeRestriction_starCharge, edgeRestriction_starCharge,
      starCharge_eq_edgeSum]
    let f : G.E → ℝ := fun e =>
      if G.Inc v e then harmonicCharge (G.weight e) else 0
    change (∑ e ∈ nonTinyEdges G tau, f e) +
        (∑ e ∈ G.edgesBelow tau, f e) = ∑ e : G.E, f e
    rw [show nonTinyEdges G tau = Finset.univ \ G.edgesBelow tau from rfl]
    calc
      (∑ e ∈ Finset.univ \ G.edgesBelow tau, f e) +
          ∑ e ∈ G.edgesBelow tau, f e =
          ∑ e ∈ (Finset.univ \ G.edgesBelow tau) ∪ G.edgesBelow tau,
            f e := (Finset.sum_union Finset.sdiff_disjoint).symm
      _ = ∑ e ∈ (Finset.univ : Finset G.E), f e := by
        rw [Finset.sdiff_union_of_subset (Finset.subset_univ _)]
      _ = ∑ e : G.E, f e := by simp
  have htinyWeight :
      (G.belowRestriction tau).starWeight v ≤ G.starWeight v := by
    rw [G.edgeRestriction_starWeight, G.starWeight_eq_inc_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun e _he _hne => by
        split
        · exact G.weight_nonneg e
        · exact le_rfl)
  rw [hmixed]
  calc
    _ ≤ (G.edgeRestriction (nonTinyEdges G tau)).starCharge harmonicCharge v +
        ((G.belowRestriction tau).starCharge harmonicCharge v +
          4 * tau * (G.belowRestriction tau).starWeight v) := by
      linarith [htiny]
    _ = G.starCharge harmonicCharge v +
        4 * tau * (G.belowRestriction tau).starWeight v := by
      rw [← hpartition]
      ring
    _ ≤ G.starCharge harmonicCharge v + 4 * tau * G.starWeight v := by
      have htau : 0 ≤ tau := by
        have hinv : 0 < (1 : ℝ) / t := by positivity
        linarith [hlower]
      simpa [add_comm] using add_le_add_left
        (mul_le_mul_of_nonneg_left htinyWeight
          (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) htau))
        (G.starCharge harmonicCharge v)

end GeneralTinyThresholdPacketization

end

end WeightedMultigraph
end WeightedEdgeColoring
