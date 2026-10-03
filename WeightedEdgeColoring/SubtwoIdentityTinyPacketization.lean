import WeightedEdgeColoring.SubtwoUniformTinyAllBlocks
import WeightedEdgeColoring.GeneralTinyThresholdMixedObjects

/-! Singleton tiny packets for a graph whose below-threshold edges are endpoint-simple. -/

open scoped BigOperators Sym2
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u

variable (G : WeightedMultigraph.{u}) (τ : ℝ)

/-- Each tiny edge is its own packet.  Endpoint simplicity is needed only for
`small_endpoint_injective`; it does not restrict non-tiny multiplicities. -/
def identityTinyPacketization (hτ : 0 ≤ τ)
    (hpair : Function.Injective
      (fun e : (G.belowRestriction τ).E => s(G.fst e.1, G.snd e.1))) :
    G.GeneralTinyThresholdPacketization τ := by
  let H := G.belowRestriction τ
  let Q : H.Packetization := {
    Packet := H.E
    instFintypePacket := inferInstance
    instDecidableEqPacket := inferInstance
    packetOf := id
    tail := H.fst
    head := H.snd
    noLoop := H.noLoop
    incidence := by intro v e; rfl
    onto := by intro e; exact ⟨e, rfl⟩
    weight_le_one := by
      intro p
      simpa using H.weight_le_one p }
  refine ⟨Q, ?_, ?_⟩
  · intro p
    have hp : H.weight p < τ :=
      (G.mem_edgesBelow_iff τ p.1).mp p.2
    have hweight : Q.packetWeight p = H.weight p := by
      simp [Q, Packetization.packetWeight]
    rw [hweight]
    linarith
  · intro p q hpq
    apply Subtype.ext
    exact hpair (by simpa [Q] using hpq)

variable {G τ}

/-- The mixed object index has exactly one object per original edge. -/
theorem identityTinyPacketization_mixedPacketOf_injective
    (hτ : 0 ≤ τ)
    (hpair : Function.Injective
      (fun e : (G.belowRestriction τ).E => s(G.fst e.1, G.snd e.1))) :
    Function.Injective
      (G.identityTinyPacketization τ hτ hpair).mixedPacketization.packetOf := by
  classical
  intro e f hef
  let P := G.identityTinyPacketization τ hτ hpair
  by_cases he : e ∈ G.edgesBelow τ <;> by_cases hf : f ∈ G.edgesBelow τ
  · have hsub : (⟨e, he⟩ : (G.belowRestriction τ).E) = ⟨f, hf⟩ := by
      have h := hef
      simp [GeneralTinyThresholdPacketization.mixedPacketization,
        GeneralTinyThresholdPacketization.mixedPacketOf,
        identityTinyPacketization, he, hf] at h
      exact h
    exact congrArg Subtype.val hsub
  · have h := hef
    simp [GeneralTinyThresholdPacketization.mixedPacketization,
      GeneralTinyThresholdPacketization.mixedPacketOf, he, hf] at h
  · have h := hef
    simp [GeneralTinyThresholdPacketization.mixedPacketization,
      GeneralTinyThresholdPacketization.mixedPacketOf, he, hf] at h
  · have h := hef
    simp [GeneralTinyThresholdPacketization.mixedPacketization,
      GeneralTinyThresholdPacketization.mixedPacketOf, he, hf] at h
    exact h

/-- Explicit bijection between physical edges and singleton mixed objects. -/
def identityTinyPacketization_mixedEdgeEquiv
    (hτ : 0 ≤ τ)
    (hpair : Function.Injective
      (fun e : (G.belowRestriction τ).E => s(G.fst e.1, G.snd e.1))) :
    G.E ≃ (G.identityTinyPacketization τ hτ hpair).Object :=
  Equiv.ofBijective
    (G.identityTinyPacketization τ hτ hpair).mixedPacketization.packetOf
    ⟨G.identityTinyPacketization_mixedPacketOf_injective hτ hpair,
      (G.identityTinyPacketization τ hτ hpair).mixedPacketization.onto⟩

/-- The canonical object corresponding to an edge has unchanged weight. -/
theorem identityTinyPacketization_mixedWeight
    (hτ : 0 ≤ τ)
    (hpair : Function.Injective
      (fun e : (G.belowRestriction τ).E => s(G.fst e.1, G.snd e.1)))
    (e : G.E) :
    (G.identityTinyPacketization τ hτ hpair).mixedObjectGraph.weight
      ((G.identityTinyPacketization τ hτ hpair).mixedPacketization.packetOf e) =
        G.weight e := by
  classical
  let P := G.identityTinyPacketization τ hτ hpair
  by_cases he : e ∈ G.edgesBelow τ
  · let te : (G.belowRestriction τ).E := ⟨e, he⟩
    have hp : P.mixedPacketization.packetOf e = Sum.inr te := by
      simp [P, GeneralTinyThresholdPacketization.mixedPacketization,
        GeneralTinyThresholdPacketization.mixedPacketOf,
        identityTinyPacketization, he, te]
    rw [hp]
    change P.mixedPacketization.packetWeight (Sum.inr te) = G.weight e
    rw [P.mixedPacketWeight_inr]
    simp [P, identityTinyPacketization, Packetization.packetWeight, te]
  · let ne : {e : G.E // e ∈
        GeneralTinyThresholdPacketization.nonTinyEdges G τ} :=
      ⟨e, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he⟩⟩
    have hp : P.mixedPacketization.packetOf e = Sum.inl ne := by
      exact P.mixedPacketization_packetOf_nonTiny ne
    rw [hp]
    change P.mixedPacketization.packetWeight (Sum.inl ne) = G.weight e
    exact P.mixedPacketWeight_inl ne

/-- The floor pair key of a singleton object is its original edge key. -/
theorem identityTinyPacketization_floorKey
    (hτ : 0 ≤ τ)
    (hpair : Function.Injective
      (fun e : (G.belowRestriction τ).E => s(G.fst e.1, G.snd e.1)))
    (e : G.E) :
    (G.identityTinyPacketization τ hτ hpair).mixedObjectGraph.floorKey
      ((G.identityTinyPacketization τ hτ hpair).mixedPacketization.packetOf e) =
        G.floorKey e := by
  classical
  let P := G.identityTinyPacketization τ hτ hpair
  by_cases he : e ∈ G.edgesBelow τ
  · simp [P, GeneralTinyThresholdPacketization.mixedObjectGraph,
      GeneralTinyThresholdPacketization.mixedPacketization,
      GeneralTinyThresholdPacketization.mixedPacketOf,
      Packetization.groupedGraph, identityTinyPacketization,
      floorKey, floorTail, floorHead, floorVertexCode, he]
  · simp [P, GeneralTinyThresholdPacketization.mixedObjectGraph,
      GeneralTinyThresholdPacketization.mixedPacketization,
      GeneralTinyThresholdPacketization.mixedPacketOf,
      Packetization.groupedGraph, identityTinyPacketization,
      floorKey, floorTail, floorHead, floorVertexCode, he]

/-- Both physical endpoints are retained by the singleton mixed object. -/
theorem identityTinyPacketization_mixedEndpoints
    (hτ : 0 ≤ τ)
    (hpair : Function.Injective
      (fun e : (G.belowRestriction τ).E => s(G.fst e.1, G.snd e.1)))
    (e : G.E) :
    s((G.identityTinyPacketization τ hτ hpair).mixedObjectGraph.fst
        ((G.identityTinyPacketization τ hτ hpair).mixedPacketization.packetOf e),
      (G.identityTinyPacketization τ hτ hpair).mixedObjectGraph.snd
        ((G.identityTinyPacketization τ hτ hpair).mixedPacketization.packetOf e)) =
      s(G.fst e, G.snd e) := by
  classical
  by_cases he : e ∈ G.edgesBelow τ
  · simp [GeneralTinyThresholdPacketization.mixedPacketization,
      GeneralTinyThresholdPacketization.mixedPacketOf,
      Packetization.groupedGraph, identityTinyPacketization, he]
  · simp [GeneralTinyThresholdPacketization.mixedPacketization,
      GeneralTinyThresholdPacketization.mixedPacketOf,
      Packetization.groupedGraph, identityTinyPacketization, he]

/-- Singleton packetization preserves local bin feasibility exactly. -/
theorem identityTinyPacketization_mixedObjectGraph_locallyPacksInto
    (hτ : 0 ≤ τ)
    (hpair : Function.Injective
      (fun e : (G.belowRestriction τ).E => s(G.fst e.1, G.snd e.1)))
    {n : ℕ} (hlocal : G.LocallyPacksInto n) :
    (G.identityTinyPacketization τ hτ hpair).mixedObjectGraph.LocallyPacksInto n := by
  classical
  let P := G.identityTinyPacketization τ hτ hpair
  let H := P.mixedObjectGraph
  let eqv : G.E ≃ P.Object := Equiv.ofBijective
    P.mixedPacketization.packetOf
    ⟨G.identityTinyPacketization_mixedPacketOf_injective hτ hpair,
      P.mixedPacketization.onto⟩
  intro v
  obtain ⟨bin, hbin⟩ := hlocal v
  let starEqv : G.StarEdge v ≃ H.StarEdge v := {
    toFun := fun e => ⟨eqv e.1,
      (P.mixedPacketization.incidence v e.1).2 e.2⟩
    invFun := fun p => ⟨eqv.symm p.1, by
      apply (P.mixedPacketization.incidence v (eqv.symm p.1)).1
      change H.Inc v (eqv (eqv.symm p.1))
      rw [eqv.apply_symm_apply]
      exact p.2⟩
    left_inv := by intro e; apply Subtype.ext; exact eqv.symm_apply_apply e.1
    right_inv := by intro p; apply Subtype.ext; exact eqv.apply_symm_apply p.1 }
  let mixedBin : H.StarEdge v → Fin n := fun p => bin (starEqv.symm p)
  refine ⟨mixedBin, ?_⟩
  intro i
  have hsum :
      H.starBinLoad mixedBin i = G.starBinLoad bin i := by
    unfold WeightedMultigraph.starBinLoad
    apply Eq.symm
    apply Fintype.sum_equiv starEqv
    intro e
    have hweight : H.weight (starEqv e).1 = G.weight e.1 := by
      exact G.identityTinyPacketization_mixedWeight hτ hpair e.1
    simp [mixedBin, hweight]
  rw [hsum]
  exact hbin i

end
end WeightedEdgeColoring.WeightedMultigraph
