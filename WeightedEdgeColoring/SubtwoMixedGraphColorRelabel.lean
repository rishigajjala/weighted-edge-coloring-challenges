import WeightedEdgeColoring.SubtwoMixedGraphMaskedScalarBridge
import WeightedEdgeColoring.SubtwoMixedGraphJointRoundingDecoder

/-!
# Relabel selected ordinary options from abstract colors to the physical palette
-/

namespace WeightedEdgeColoring

noncomputable section

universe u v w z

namespace OrdinarySlot

def colorEquiv {Vertex : Type v} {Color : Type w} {D : Type z}
    {K : ℕ} (e : Color ≃ D) :
    OrdinarySlot Vertex Color K ≃ OrdinarySlot Vertex D K where
  toFun s := ⟨s.vertex, e s.color, s.place⟩
  invFun s := ⟨s.vertex, e.symm s.color, s.place⟩
  left_inv := by intro s; cases s; simp
  right_inv := by intro s; cases s; simp

end OrdinarySlot

namespace OrdinarySlotChoice

def colorEquiv {Job : Type u} {Color : Type w} {D : Type z}
    {K : ℕ} (e : Color ≃ D) :
    OrdinarySlotChoice Job Color K ≃ OrdinarySlotChoice Job D K where
  toFun o := ⟨o.job, e o.color, o.leftPlace, o.rightPlace⟩
  invFun o := ⟨o.job, e.symm o.color, o.leftPlace, o.rightPlace⟩
  left_inv := by intro o; cases o; simp
  right_inv := by intro o; cases o; simp

end OrdinarySlotChoice

theorem ordinarySlotChoice_colorEquiv_isPartialMatching
    {Job : Type u} {Vertex : Type v} {Color : Type w} {D : Type z}
    [Fintype Job] [DecidableEq Job] [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Color] [DecidableEq Color] [Fintype D] [DecidableEq D]
    (left right : Job → Vertex) (K : ℕ) (e : Color ≃ D)
    (M : Finset (OrdinarySlotChoice Job Color K))
    (hM : (OrdinarySlotChoice.system left right K).IsPartialMatching M) :
    (OrdinarySlotChoice.system left right K).IsPartialMatching
      (M.map (OrdinarySlotChoice.colorEquiv e).toEmbedding) := by
  let eo := OrdinarySlotChoice.colorEquiv (Job := Job) (K := K) e
  let es := OrdinarySlot.colorEquiv (Vertex := Vertex) (K := K) e
  have hslots (o : OrdinarySlotChoice Job Color K) :
      (OrdinarySlotChoice.system left right K).slots (eo o) =
        ((OrdinarySlotChoice.system left right K).slots o).map
          es.toEmbedding := by
    simp [OrdinarySlotChoice.system, OrdinarySlotChoice.leftSlot,
      OrdinarySlotChoice.rightSlot, eo, es,
      OrdinarySlotChoice.colorEquiv, OrdinarySlot.colorEquiv]
  constructor
  · intro o ho p hp hne
    rcases Finset.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    rcases Finset.mem_map.mp hp with ⟨p0, hp0, rfl⟩
    have hne0 : o0 ≠ p0 := by
      intro heq
      exact hne (congrArg eo heq)
    have hcompat := hM.1 ho0 hp0 hne0
    unfold RankThreeOptionSystem.Compatible at hcompat ⊢
    change Disjoint
      ((OrdinarySlotChoice.system left right K).slots (eo o0))
      ((OrdinarySlotChoice.system left right K).slots (eo p0))
    rw [hslots o0, hslots p0]
    exact (Finset.disjoint_map es.toEmbedding).2 hcompat
  · intro o ho p hp heq
    rcases Finset.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    rcases Finset.mem_map.mp hp with ⟨p0, hp0, rfl⟩
    have hjob : o0.job = p0.job := heq
    exact congrArg eo (hM.2 ho0 hp0 hjob)

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {Color Class : Type*} [Fintype Color] [DecidableEq Color]
  [Fintype Class] [DecidableEq Class]

def selectedDyadicOrdinaryBaseOptionsAny
    (K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))) :
    Finset (OrdinarySlotChoice G.E Color K) :=
  RankThreeOptionSystem.leftOptionSet
    (RankThreeOptionSystem.baseOptionSet N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M)

theorem selectedDyadicOrdinaryBaseOptionsAny_isPartialMatching
    (K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (hM : ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).IsPartialMatching M) :
    (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching
      (G.selectedDyadicOrdinaryBaseOptionsAny K N bucket gamma reserve
        residual x M) := by
  let Hord : RankThreeOptionSystem G.E (OrdinarySlot G.V Color K)
      (OrdinarySlotChoice G.E Color K) :=
    OrdinarySlotChoice.system G.fst G.snd K
  let Hextra : RankThreeOptionSystem G.E
      (ExtraSlot G.V Class
        (G.boundedDyadicExtraSlotCount bucket residual gamma reserve))
      (DivisibleLocalExtraChoice G.E G.V Class G.fst G.snd bucket
        (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)) :=
    DivisibleLocalExtraChoice.system G.fst G.snd bucket
      (G.boundedDyadicExtraSlotCount bucket residual gamma reserve)
      (G.boundedDyadic_left_dvd_support bucket residual gamma reserve)
      (G.boundedDyadic_right_dvd_support bucket residual gamma reserve)
  let mass := G.dyadicLargeEdgeMass K bucket gamma reserve residual x
  let base := RankThreeOptionSystem.baseOptionSet N mass M
  have hbase : (Hord.separatedSum Hextra).IsPartialMatching base :=
    (Hord.separatedSum Hextra).baseOptionSet_isPartialMatching N mass M hM
  exact Hord.separatedSum_leftOptionSet_isPartialMatching Hextra base hbase

theorem selectedDyadicOrdinaryBaseOptionsAny_mass_pos
    (K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    {o : OrdinarySlotChoice G.E Color K}
    (ho : o ∈ G.selectedDyadicOrdinaryBaseOptionsAny
      K N bucket gamma reserve residual x M) :
    0 < x o.job o.color o.leftPlace o.rightPlace := by
  have hinl : Sum.inl o ∈ RankThreeOptionSystem.baseOptionSet N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M :=
    (RankThreeOptionSystem.mem_leftOptionSet_iff _ o).mp ho
  exact RankThreeOptionSystem.baseOptionSet_mass_pos N
    (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M hinl

end WeightedMultigraph

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {Color Label : Type*} [Fintype Color] [DecidableEq Color]
  [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → Color → ℝ)
variable (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
variable (qLaw : ∀ v : G.V, Color → Finset (G.StarEdge v) → ℝ)
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : ∀ v c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel v)
      (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
    s β qstep r hβ hr)

theorem selectedMixedAnyMatching_load_le_concreteSlotSum
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (gamma : ℝ) (reserve N : ℕ)
    (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual
        (G.selectedMixedNormalizedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice))))
    (hM : ((G.dyadicLargeEdgeOptionSystem
        (Color := Color) (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual
        (G.selectedMixedNormalizedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice))).IsPartialMatching M)
    (v : G.V) (d : Fin (Fintype.card Color)) :
    let x := G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice
    let O := G.selectedDyadicOrdinaryBaseOptionsAny
      (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual x M
    let OFin := O.map
      (OrdinarySlotChoice.colorEquiv (Fintype.equivFin Color)).toEmbedding
    let hO := G.selectedDyadicOrdinaryBaseOptionsAny_isPartialMatching
      (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual x M hM
    let hOFin := ordinarySlotChoice_colorEquiv_isPartialMatching
      G.fst G.snd (explicitLargeSlotBound β qstep r)
      (Fintype.equivFin Color) O hO
    G.selectedOrdinaryIntegralColorLoad OFin hOFin v d ≤
      ∑ i, G.encodedSelectedMixedConcreteSlotSize
        proposal edgeLabel qLaw R choice v d i := by
  dsimp only
  let x := G.selectedMixedNormalizedLargeOptionMass
    proposal edgeLabel qLaw R rho omega choice
  let O := G.selectedDyadicOrdinaryBaseOptionsAny
    (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual x M
  let OFin := O.map
    (OrdinarySlotChoice.colorEquiv (Fintype.equivFin Color)).toEmbedding
  let hO := G.selectedDyadicOrdinaryBaseOptionsAny_isPartialMatching
    (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual x M hM
  let hOFin := ordinarySlotChoice_colorEquiv_isPartialMatching
    G.fst G.snd (explicitLargeSlotBound β qstep r)
    (Fintype.equivFin Color) O hO
  apply G.selectedOrdinaryIntegralColorLoad_le_slotSum hOFin
    (G.encodedSelectedMixedConcreteSlotSize
      proposal edgeLabel qLaw R choice)
  · intro v d i
    exact G.selectedMixedConcreteSlotSize_nonneg
      proposal edgeLabel qLaw R choice v
      ((Fintype.equivFin Color).symm d) i
  · intro o ho
    rcases Finset.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    have hpos := G.selectedDyadicOrdinaryBaseOptionsAny_mass_pos
      (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual
      x M ho0
    have hfit := G.weight_le_selectedMixedConcreteSlots_of_large_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice o0.job o0.color
      o0.leftPlace o0.rightPlace hpos
    simpa [encodedSelectedMixedConcreteSlotSize,
      OrdinarySlotChoice.colorEquiv] using hfit.1
  · intro o ho
    rcases Finset.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    have hpos := G.selectedDyadicOrdinaryBaseOptionsAny_mass_pos
      (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual
      x M ho0
    have hfit := G.weight_le_selectedMixedConcreteSlots_of_large_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice o0.job o0.color
      o0.leftPlace o0.rightPlace hpos
    simpa [encodedSelectedMixedConcreteSlotSize,
      OrdinarySlotChoice.colorEquiv] using hfit.2

theorem exists_selectedMixedAnyJointPhysicalColor
    (hColor : 0 < Fintype.card Color)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (gamma : ℝ) (reserve N : ℕ)
    (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual
        (G.selectedMixedNormalizedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice))))
    (hM : ((G.dyadicLargeEdgeOptionSystem
        (Color := Color) (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual
        (G.selectedMixedNormalizedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice))).IsPartialMatching M) :
    let T := G.selectedMixedTinyEdges (β := β)
    let x := G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice
    let O := G.selectedDyadicOrdinaryBaseOptionsAny
      (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual x M
    let OFin := O.map
      (OrdinarySlotChoice.colorEquiv (Fintype.equivFin Color)).toEmbedding
    let hO := G.selectedDyadicOrdinaryBaseOptionsAny_isPartialMatching
      (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual x M hM
    let hOFin := ordinarySlotChoice_colorEquiv_isPartialMatching
      G.fst G.snd (explicitLargeSlotBound β qstep r)
      (Fintype.equivFin Color) O hO
    ∃ decision : {e : G.E // e ∈ T} →
        Option (Fin (Fintype.card Color)),
      (∀ v d,
        G.colorLoadOn
          (G.ordinarySelectedEdges OFin ∪ G.tinyDecisionColoredEdges T decision)
          (G.ordinaryTinyJointColor hColor OFin hOFin T decision) v d ≤
          (∑ i, G.encodedSelectedMixedConcreteSlotSize
            proposal edgeLabel qLaw R choice v d i) +
          G.selectedMixedNormalizedTinyReservoirLoad
            proposal edgeLabel qLaw R rho omega choice v
              ((Fintype.equivFin Color).symm d) + 2 * β) ∧
      ∀ v,
        G.tinyResidualIntegralLossLoad decision v ≤
          G.tinyResidualLossLoad T
            (fun e ↦ G.selectedMixedResidualOptionMass
              proposal edgeLabel qLaw R rho omega choice e.1) v + 2 * β := by
  classical
  obtain ⟨decision, _hpositive, _hresidual, htiny, hloss⟩ :=
    G.exists_selectedMixedTinyColorDecision
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice
  let T := G.selectedMixedTinyEdges (β := β)
  let x := G.selectedMixedNormalizedLargeOptionMass
    proposal edgeLabel qLaw R rho omega choice
  let O := G.selectedDyadicOrdinaryBaseOptionsAny
    (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual x M
  let OFin := O.map
    (OrdinarySlotChoice.colorEquiv (Fintype.equivFin Color)).toEmbedding
  let hO := G.selectedDyadicOrdinaryBaseOptionsAny_isPartialMatching
    (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual x M hM
  let hOFin := ordinarySlotChoice_colorEquiv_isPartialMatching
    G.fst G.snd (explicitLargeSlotBound β qstep r)
    (Fintype.equivFin Color) O hO
  have hdisj : Disjoint (G.ordinarySelectedEdges OFin) T := by
    rw [Finset.disjoint_left]
    intro e heOrd heTiny
    rcases (G.mem_ordinarySelectedEdges_iff OFin e).mp heOrd with
      ⟨oFin, hoFin, rfl⟩
    rcases Finset.mem_map.mp hoFin with ⟨o, ho, rfl⟩
    have hpos := G.selectedDyadicOrdinaryBaseOptionsAny_mass_pos
      (explicitLargeSlotBound β qstep r) N bucket gamma reserve residual
      x M ho
    have hzero := G.selectedMixedNormalizedLargeOptionMass_eq_zero_of_tiny
      proposal edgeLabel qLaw R rho omega choice o.job o.color
      o.leftPlace o.rightPlace (G.mem_selectedMixedTinyEdges.mp heTiny)
    exact (ne_of_gt hpos) hzero
  refine ⟨decision, ?_, hloss⟩
  intro v d
  rw [G.colorLoadOn_ordinaryTinyJoint_eq hColor OFin hOFin T decision hdisj v d]
  have hlarge := G.selectedMixedAnyMatching_load_le_concreteSlotSum
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
    hleft homega0 homega1 hrho hproposal0 choice
    bucket gamma reserve N residual M hM v d
  have htiny' := htiny v ((Fintype.equivFin Color).symm d)
  have hcolor : (Fintype.equivFin Color)
      ((Fintype.equivFin Color).symm d) = d :=
    Equiv.apply_symm_apply _ _
  rw [hcolor] at htiny'
  dsimp only [O, OFin, hO, hOFin] at hlarge ⊢
  linarith

end WeightedMultigraph

end

end WeightedEdgeColoring
