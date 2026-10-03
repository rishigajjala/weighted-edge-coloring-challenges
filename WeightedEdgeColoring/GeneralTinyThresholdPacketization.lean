import WeightedEdgeColoring.TinyThresholdPacketization
import WeightedEdgeColoring.GeneralPacketization
import WeightedEdgeColoring.BinPacking

/-!
# Tiny-threshold packetization without a bipartition

This is the endpoint-pair analogue of `TinyThresholdPacketization`.  A
finite vertex code canonically orients every edge, so the minimal-label
merge argument does not need a bipartition.  Edges below `tau` are grouped
inside one oriented parallel class.  Every packet has weight at most
`2 * tau`, and at most one packet of weight at most `tau` remains on each
unordered endpoint pair.
-/

open scoped BigOperators Sym2

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- The abstract one-dimensional estimate needed to turn small packet
weights and a total-weight budget into a prescribed number of bins.  Keeping
this interface independent of graphs isolates the remaining next-fit step. -/
def SmallItemRepackingBound (delta total : ℝ) (m : ℕ) : Prop :=
  ∀ B : BinPackingInstance.{u},
    B.totalWeight ≤ total →
    (∀ x, B.weight x ≤ delta) →
    B.PacksInto m

/-- A fixed finite code used to orient endpoint pairs canonically. -/
def tinyVertexCode : G.V ≃ Fin (Fintype.card G.V) :=
  Fintype.equivFin G.V

/-- The lower-coded endpoint of an edge. -/
def tinyTail (e : G.E) : G.V :=
  if G.tinyVertexCode (G.fst e) < G.tinyVertexCode (G.snd e)
  then G.fst e else G.snd e

/-- The higher-coded endpoint of an edge. -/
def tinyHead (e : G.E) : G.V :=
  if G.tinyVertexCode (G.fst e) < G.tinyVertexCode (G.snd e)
  then G.snd e else G.fst e

theorem tinyTail_ne_tinyHead (e : G.E) :
    G.tinyTail e ≠ G.tinyHead e := by
  unfold tinyTail tinyHead
  split
  · exact G.noLoop e
  · exact (G.noLoop e).symm

theorem tinyTailCode_lt_tinyHeadCode (e : G.E) :
    G.tinyVertexCode (G.tinyTail e) <
      G.tinyVertexCode (G.tinyHead e) := by
  have hne : G.tinyVertexCode (G.fst e) ≠
      G.tinyVertexCode (G.snd e) := by
    intro h
    exact G.noLoop e (G.tinyVertexCode.injective h)
  unfold tinyTail tinyHead
  by_cases h : G.tinyVertexCode (G.fst e) <
      G.tinyVertexCode (G.snd e)
  · simp [h]
  · have hr : G.tinyVertexCode (G.snd e) <
        G.tinyVertexCode (G.fst e) := by omega
    simp [h, hr]

theorem tinyOriented_inc_iff (v : G.V) (e : G.E) :
    G.tinyTail e = v ∨ G.tinyHead e = v ↔ G.Inc v e := by
  unfold tinyTail tinyHead Inc
  split <;> simp [or_comm]

/-- A label assignment groups only canonically oriented parallel edges and
keeps every label below the threshold-packet capacity `2*tau`. -/
def IsValidTinyPacketAssignment {C : Type*} [Fintype C] [DecidableEq C]
    (tau : ℝ) (a : G.E → C) : Prop :=
  (∀ e f, a e = a f →
      G.tinyTail e = G.tinyTail f ∧ G.tinyHead e = G.tinyHead f) ∧
    ∀ c, G.packetLabelWeight a c ≤ 2 * tau

/-- Singleton labels are valid when every edge is below `tau`. -/
theorem isValidTinyPacketAssignment_equivFin
    (tau : ℝ) (htau : 0 ≤ tau)
    (hsmall : ∀ e, G.weight e < tau) :
    G.IsValidTinyPacketAssignment tau (Fintype.equivFin G.E) := by
  classical
  constructor
  · intro e f hef
    have : e = f := (Fintype.equivFin G.E).injective hef
    subst f
    exact ⟨rfl, rfl⟩
  · intro c
    let a : G.E → Fin (Fintype.card G.E) := Fintype.equivFin G.E
    let S : Finset G.E := Finset.univ.filter fun e ↦ a e = c
    have hcard : S.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro e he f hf
      apply (Fintype.equivFin G.E).injective
      exact (Finset.mem_filter.mp he).2.trans
        (Finset.mem_filter.mp hf).2.symm
    calc
      G.packetLabelWeight a c = ∑ e ∈ S, G.weight e := by
        simp [packetLabelWeight, S, Finset.sum_filter]
      _ ≤ ∑ _e ∈ S, tau := by
        exact Finset.sum_le_sum fun e _he ↦ (hsmall e).le
      _ = (S.card : ℝ) * tau := by simp
      _ ≤ 1 * tau := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) htau
      _ ≤ 2 * tau := by nlinarith

/-- Among all valid tiny assignments, choose one using the fewest labels. -/
theorem exists_minimal_validTinyPacketAssignment
    (tau : ℝ) (htau : 0 ≤ tau)
    (hsmall : ∀ e, G.weight e < tau) :
    ∃ a : G.E → Fin (Fintype.card G.E),
      G.IsValidTinyPacketAssignment tau a ∧
      ∀ a' : G.E → Fin (Fintype.card G.E),
        G.IsValidTinyPacketAssignment tau a' →
        (G.usedPacketLabels a).card ≤ (G.usedPacketLabels a').card := by
  classical
  let C := Fin (Fintype.card G.E)
  let candidates : Finset (G.E → C) :=
    Finset.univ.filter (G.IsValidTinyPacketAssignment tau)
  have hnonempty : candidates.Nonempty := by
    refine ⟨Fintype.equivFin G.E, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      G.isValidTinyPacketAssignment_equivFin tau htau hsmall⟩
  obtain ⟨a, ha, hmin⟩ := candidates.exists_min_image
    (fun x ↦ (G.usedPacketLabels x).card) hnonempty
  refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
  intro a' ha'
  exact hmin a' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha'⟩)

theorem isValidTinyPacketAssignment_merge
    {C : Type*} [Fintype C] [DecidableEq C]
    (tau : ℝ) (htau : 0 ≤ tau) (a : G.E → C)
    (ha : G.IsValidTinyPacketAssignment tau a)
    {p q : C} (hpq : p ≠ q)
    (hcross : ∀ e f, a e = p → a f = q →
      G.tinyTail e = G.tinyTail f ∧ G.tinyHead e = G.tinyHead f)
    (hpweight : G.packetLabelWeight a p ≤ tau)
    (hqweight : G.packetLabelWeight a q ≤ tau) :
    G.IsValidTinyPacketAssignment tau (G.mergePacketLabels a p q) := by
  constructor
  · intro e f hef
    by_cases heq : a e = q <;> by_cases hfq : a f = q
    · exact ha.1 e f (heq.trans hfq.symm)
    · have hfp : a f = p := by
        simpa [mergePacketLabels, heq, hfq] using hef.symm
      exact (hcross f e hfp heq).imp Eq.symm Eq.symm
    · have hep : a e = p := by
        simpa [mergePacketLabels, heq, hfq] using hef
      exact hcross e f hep hfq
    · apply ha.1 e f
      simpa [mergePacketLabels, heq, hfq] using hef
  · intro r
    by_cases hrp : r = p
    · subst r
      rw [G.packetLabelWeight_merge_self a hpq]
      linarith
    · by_cases hrq : r = q
      · subst r
        have hzero :
            G.packetLabelWeight (G.mergePacketLabels a p q) q = 0 := by
          unfold packetLabelWeight mergePacketLabels
          apply Finset.sum_eq_zero
          intro e _he
          by_cases heq : a e = q
          · simp [heq, hpq]
          · simp [heq]
        rw [hzero]
        nlinarith
      · rw [G.packetLabelWeight_merge_old a hrp hrq]
        exact ha.2 r

theorem no_mergeable_tiny_labels_of_minimal
    {C : Type*} [Fintype C] [DecidableEq C]
    (tau : ℝ) (htau : 0 ≤ tau) (a : G.E → C)
    (ha : G.IsValidTinyPacketAssignment tau a)
    (hminimal : ∀ a' : G.E → C,
      G.IsValidTinyPacketAssignment tau a' →
      (G.usedPacketLabels a).card ≤ (G.usedPacketLabels a').card)
    {p q : C} (hpq : p ≠ q)
    (hpused : p ∈ G.usedPacketLabels a)
    (hqused : q ∈ G.usedPacketLabels a)
    (hcross : ∀ e f, a e = p → a f = q →
      G.tinyTail e = G.tinyTail f ∧ G.tinyHead e = G.tinyHead f)
    (hpweight : G.packetLabelWeight a p ≤ tau)
    (hqweight : G.packetLabelWeight a q ≤ tau) : False := by
  let a' := G.mergePacketLabels a p q
  have hvalid : G.IsValidTinyPacketAssignment tau a' :=
    G.isValidTinyPacketAssignment_merge tau htau a ha hpq hcross
      hpweight hqweight
  have hle := hminimal a' hvalid
  have hlt := G.card_usedPacketLabels_merge_lt a hpq hpused hqused
  have hle' : (G.usedPacketLabels a).card ≤
      (G.usedPacketLabels (G.mergePacketLabels a p q)).card := by
    simpa [a'] using hle
  exact (not_le_of_gt hlt) hle'

/-- Tiny edges packetized along canonical endpoint pairs, with no
bipartition assumption. -/
structure GeneralTinyThresholdPacketization (tau : ℝ) where
  packetization : (G.belowRestriction tau).Packetization
  packetWeight_le_two :
    ∀ p, packetization.packetWeight p ≤ 2 * tau
  small_endpoint_injective :
    Function.Injective
      (fun p : {p : packetization.Packet //
          packetization.packetWeight p ≤ tau} ↦
        s(packetization.tail p.1, packetization.head p.1))

namespace GeneralTinyThresholdPacketization

variable {G : WeightedMultigraph.{u}} {tau : ℝ}
  (P : G.GeneralTinyThresholdPacketization tau)

abbrev Packet := P.packetization.Packet

instance : Fintype P.Packet := inferInstance
instance : DecidableEq P.Packet := inferInstance

theorem eq_of_small_of_same_endpoints {p q : P.Packet}
    (hp : P.packetization.packetWeight p ≤ tau)
    (hq : P.packetization.packetWeight q ≤ tau)
    (hends : s(P.packetization.tail p, P.packetization.head p) =
      s(P.packetization.tail q, P.packetization.head q)) :
    p = q := by
  let p' : {r : P.Packet // P.packetization.packetWeight r ≤ tau} := ⟨p, hp⟩
  let q' : {r : P.Packet // P.packetization.packetWeight r ≤ tau} := ⟨q, hq⟩
  have hpq : p' = q' := P.small_endpoint_injective (by
    simpa [p', q'] using hends)
  exact congrArg Subtype.val hpq

/-- Packet aggregation preserves the total incident weight at every vertex. -/
theorem groupedGraph_starWeight (v : G.V) :
    P.packetization.groupedGraph.starWeight v =
      (G.belowRestriction tau).starWeight v := by
  let H := G.belowRestriction tau
  let Q := P.packetization
  have h := Q.restrictedWeight_originalEdgesOfPackets
    (Finset.univ : Finset Q.Packet) v
  rw [Q.groupedGraph.starWeight_eq_inc_sum,
    H.starWeight_eq_inc_sum]
  simpa [Packetization.originalEdgesOfPackets, H, Q] using h.symm

/-- Any scalar small-item repacking bound applies vertex by vertex to the
packet graph.  The packetization supplies both hypotheses: total star weight
is preserved and every packet weighs at most `2*tau`. -/
theorem groupedGraph_locallyPacksInto_of_smallItemRepacking
    {n m : ℕ}
    (hlocal : (G.belowRestriction tau).LocallyPacksInto n)
    (hrepack : SmallItemRepackingBound.{u} (2 * tau) n m) :
    P.packetization.groupedGraph.LocallyPacksInto m := by
  intro v
  let B : BinPackingInstance.{u} := {
    Item := P.packetization.groupedGraph.StarEdge v
    instFintypeItem := inferInstance
    instDecidableEqItem := inferInstance
    weight e := P.packetization.groupedGraph.weight e.1
    weight_pos e := P.packetization.groupedGraph.weight_pos e.1
    weight_le_one e := P.packetization.groupedGraph.weight_le_one e.1
  }
  have htotal : B.totalWeight ≤ (n : ℝ) := by
    change P.packetization.groupedGraph.starWeight v ≤ (n : ℝ)
    rw [P.groupedGraph_starWeight v]
    exact (G.belowRestriction tau).starWeight_le_of_packsStarInto (hlocal v)
  have hsmall : ∀ x : B.Item, B.weight x ≤ 2 * tau := by
    intro x
    exact P.packetWeight_le_two x.1
  obtain ⟨C⟩ := hrepack B htotal hsmall
  refine ⟨C.bin, ?_⟩
  intro i
  exact C.load_le_one i

end GeneralTinyThresholdPacketization

/-- Every weighted multigraph has a fixed-threshold tiny packetization.
Only positivity and `2*tau ≤ 1` are used. -/
theorem exists_generalTinyThresholdPacketization
    (tau : ℝ) (htau : 0 < tau) (htauhalf : tau ≤ 1 / 2) :
    Nonempty (G.GeneralTinyThresholdPacketization tau) := by
  classical
  let H : WeightedMultigraph.{u} := G.belowRestriction tau
  have hsmall : ∀ e : H.E, H.weight e < tau := by
    intro e
    exact G.mem_edgesBelow_iff tau e.1 |>.mp e.2
  obtain ⟨a, ha, hminimal⟩ :=
    H.exists_minimal_validTinyPacketAssignment tau htau.le hsmall
  let U : Type u := ULift.{u}
    {c : Fin (Fintype.card H.E) // c ∈ H.usedPacketLabels a}
  have hex (p : U) : ∃ e : H.E, a e = p.down.1 := by
    rcases Finset.mem_image.mp p.down.2 with ⟨e, _he, h⟩
    exact ⟨e, h⟩
  choose repr hre using hex
  let packetOf : H.E → U := fun e ↦
    ULift.up ⟨a e, Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩⟩
  have hpacket_eq (e : H.E) (p : U) :
      packetOf e = p ↔ a e = p.down.1 := by
    constructor
    · intro h
      exact congrArg (fun z : U ↦ z.down.1) h
    · intro h
      apply ULift.ext
      apply Subtype.ext
      exact h
  let tail : U → H.V := fun p ↦ H.tinyTail (repr p)
  let head : U → H.V := fun p ↦ H.tinyHead (repr p)
  let P : H.Packetization := {
    Packet := U
    instFintypePacket := inferInstance
    instDecidableEqPacket := inferInstance
    packetOf := packetOf
    tail := tail
    head := head
    noLoop := by
      intro p
      exact H.tinyTail_ne_tinyHead (repr p)
    incidence := by
      intro v e
      have hlabel : a e = a (repr (packetOf e)) :=
        (hre (packetOf e)).symm
      have hends := ha.1 e (repr (packetOf e)) hlabel
      change tail (packetOf e) = v ∨ head (packetOf e) = v ↔ H.Inc v e
      have htail : tail (packetOf e) = H.tinyTail e := by
        simpa [tail] using hends.1.symm
      have hhead : head (packetOf e) = H.tinyHead e := by
        simpa [head] using hends.2.symm
      rw [htail, hhead]
      exact H.tinyOriented_inc_iff v e
    onto := by
      intro p
      refine ⟨repr p, ?_⟩
      apply ULift.ext
      apply Subtype.ext
      exact hre p
    weight_le_one := by
      intro p
      have htwo : 2 * tau ≤ 1 := by linarith
      calc
        (∑ e : H.E, if packetOf e = p then H.weight e else 0) =
            H.packetLabelWeight a p.down.1 := by
          unfold packetLabelWeight
          apply Finset.sum_congr rfl
          intro e _he
          by_cases h : packetOf e = p
          · have h' : a e = p.down.1 := (hpacket_eq e p).mp h
            simp [h, h']
          · have h' : a e ≠ p.down.1 := fun heq ↦
              h ((hpacket_eq e p).mpr heq)
            simp [h, h']
        _ ≤ 2 * tau := ha.2 p.down.1
        _ ≤ 1 := htwo
  }
  refine ⟨{
    packetization := P
    packetWeight_le_two := ?_
    small_endpoint_injective := ?_ }⟩
  · intro p
    change (∑ e : H.E, if packetOf e = p then H.weight e else 0) ≤ 2 * tau
    calc
      _ = H.packetLabelWeight a p.down.1 := by
        unfold packetLabelWeight
        apply Finset.sum_congr rfl
        intro e _he
        by_cases h : packetOf e = p
        · have h' : a e = p.down.1 := (hpacket_eq e p).mp h
          simp [h, h']
        · have h' : a e ≠ p.down.1 := fun heq ↦
            h ((hpacket_eq e p).mpr heq)
          simp [h, h']
      _ ≤ 2 * tau := ha.2 p.down.1
  · intro p q hpqEndpoints
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    by_contra hpqLabel
    have horiented :
        P.tail p.1 = P.tail q.1 ∧ P.head p.1 = P.head q.1 := by
      rcases Sym2.eq_iff.mp hpqEndpoints with hdirect | hswap
      · exact hdirect
      · exfalso
        have hporder := H.tinyTailCode_lt_tinyHeadCode (repr p.1)
        have hqorder := H.tinyTailCode_lt_tinyHeadCode (repr q.1)
        have hswap₁ := congrArg H.tinyVertexCode hswap.1
        have hswap₂ := congrArg H.tinyVertexCode hswap.2
        dsimp [P, tail, head] at hswap₁ hswap₂
        omega
    have hweight (r : P.Packet) :
        P.packetWeight r = H.packetLabelWeight a r.down.1 := by
      unfold Packetization.packetWeight packetLabelWeight
      apply Finset.sum_congr rfl
      intro e _he
      change (if packetOf e = r then H.weight e else 0) =
        if a e = r.down.1 then H.weight e else 0
      by_cases h : packetOf e = r
      · have h' : a e = r.down.1 := (hpacket_eq e r).mp h
        simp [h, h']
      · have h' : a e ≠ r.down.1 := fun heq ↦
          h ((hpacket_eq e r).mpr heq)
        simp [h, h']
    have hpweight : H.packetLabelWeight a p.1.down.1 ≤ tau := by
      rw [← hweight p.1]
      exact p.2
    have hqweight : H.packetLabelWeight a q.1.down.1 ≤ tau := by
      rw [← hweight q.1]
      exact q.2
    have hcross : ∀ e f, a e = p.1.down.1 → a f = q.1.down.1 →
        H.tinyTail e = H.tinyTail f ∧ H.tinyHead e = H.tinyHead f := by
      intro e f hep hfq
      have heP := ha.1 e (repr p.1) (hep.trans (hre p.1).symm)
      have hfQ := ha.1 f (repr q.1) (hfq.trans (hre q.1).symm)
      refine ⟨?_, ?_⟩
      · exact heP.1.trans (horiented.1.trans hfQ.1.symm)
      · exact heP.2.trans (horiented.2.trans hfQ.2.symm)
    exact (H.no_mergeable_tiny_labels_of_minimal tau htau.le a ha hminimal
      hpqLabel p.1.down.2 q.1.down.2 hcross hpweight hqweight).elim

end

end WeightedMultigraph
end WeightedEdgeColoring
