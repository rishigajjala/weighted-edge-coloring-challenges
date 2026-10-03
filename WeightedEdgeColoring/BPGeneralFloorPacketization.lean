import WeightedEdgeColoring.BPGraphExactDemandBundlePacking
import WeightedEdgeColoring.GeneralPacketization
import WeightedEdgeColoring.FiniteExactDemandHarmonicMinimum

/-!
# Global packetization from coefficient floors

Every unordered parallel bundle is oriented by a fixed finite vertex code.
For that bundle we choose a reduced minimum exact-demand cover, retain the
integer part of every pattern coefficient, and assign its labelled item
occurrences injectively to physical edges of the corresponding weight.
Unassigned physical edges become singleton residual packets.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

def floorVertexCode : G.V ≃ Fin (Fintype.card G.V) :=
  Fintype.equivFin G.V

def floorTail (e : G.E) : G.V :=
  if G.floorVertexCode (G.fst e) < G.floorVertexCode (G.snd e)
  then G.fst e else G.snd e

def floorHead (e : G.E) : G.V :=
  if G.floorVertexCode (G.fst e) < G.floorVertexCode (G.snd e)
  then G.snd e else G.fst e

def floorKey (e : G.E) : G.V × G.V :=
  (G.floorTail e, G.floorHead e)

def floorPairKey (u v : G.V) : G.V × G.V :=
  if G.floorVertexCode u < G.floorVertexCode v then (u, v) else (v, u)

@[simp] theorem floorKey_eq_floorPairKey (e : G.E) :
    G.floorKey e = G.floorPairKey (G.fst e) (G.snd e) := by
  unfold floorKey floorPairKey floorTail floorHead
  split <;> rfl

@[simp] theorem floorPairKey_floorTail_floorHead (e : G.E) :
    G.floorPairKey (G.floorTail e) (G.floorHead e) = G.floorKey e := by
  have hcode : G.floorVertexCode (G.fst e) ≠
      G.floorVertexCode (G.snd e) := by
    intro h
    exact G.noLoop e (G.floorVertexCode.injective h)
  unfold floorPairKey floorKey floorTail floorHead
  by_cases h : G.floorVertexCode (G.fst e) < G.floorVertexCode (G.snd e)
  · simp [h]
  · have hr : G.floorVertexCode (G.snd e) < G.floorVertexCode (G.fst e) := by
      omega
    simp [h, hr]

def floorBundle (k : G.V × G.V) : Finset G.E :=
  Finset.univ.filter fun e ↦ G.floorKey e = k

@[simp] theorem mem_floorBundle_floorKey (e : G.E) :
    e ∈ G.floorBundle (G.floorKey e) := by
  simp [floorBundle]

theorem floorTail_ne_floorHead (e : G.E) :
    G.floorTail e ≠ G.floorHead e := by
  unfold floorTail floorHead
  split
  · exact G.noLoop e
  · exact (G.noLoop e).symm

theorem floorTail_inc (e : G.E) : G.Inc (G.floorTail e) e := by
  unfold floorTail Inc
  split <;> simp

theorem floorHead_inc (e : G.E) : G.Inc (G.floorHead e) e := by
  unfold floorHead Inc
  split <;> simp

theorem floorKey_eq_of_mem_floorBundle {k : G.V × G.V} {e : G.E}
    (he : e ∈ G.floorBundle k) : G.floorKey e = k :=
  (Finset.mem_filter.mp he).2

/-- A reduced minimum exact-demand cover chosen independently in every
oriented parallel bundle. -/
noncomputable def floorBundleCover (k : G.V × G.V) :
    G.EdgeSetExactDemandCover (G.floorBundle k) :=
  Classical.choose
    (BinPackingInstance.ExactDemandPatternCover.exists_reducedMinimumCost
      (G.edgeSetWeightBinPackingInstance (G.floorBundle k))
      (G.edgeSetWeightDemand (G.floorBundle k)))

theorem floorBundleCover_minimum (k : G.V × G.V) :
    (G.floorBundleCover k).IsMinimumCost :=
  (Classical.choose_spec
    (BinPackingInstance.ExactDemandPatternCover.exists_reducedMinimumCost
      (G.edgeSetWeightBinPackingInstance (G.floorBundle k))
      (G.edgeSetWeightDemand (G.floorBundle k)))).1

theorem floorBundleCover_empty_coeff (k : G.V × G.V)
    (p : (G.edgeSetWeightBinPackingInstance (G.floorBundle k)).Pattern)
    (hp : ¬ BinPackingInstance.ExactDemandPatternCover.PatternNonempty p) :
    (G.floorBundleCover k).coeff p = 0 :=
  (Classical.choose_spec
    (BinPackingInstance.ExactDemandPatternCover.exists_reducedMinimumCost
      (G.edgeSetWeightBinPackingInstance (G.floorBundle k))
      (G.edgeSetWeightDemand (G.floorBundle k)))).2 p hp

/-- All labelled full packets across all parallel bundles. -/
abbrev GlobalFloorPacket :=
  Σ k : G.V × G.V, (G.floorBundleCover k).FloorPacket

/-- All physical item occurrences requested by all full packets. -/
abbrev GlobalFloorOccurrence :=
  Σ k : G.V × G.V,
    Σ x : G.EdgeSetWeightType (G.floorBundle k),
      (G.floorBundleCover k).FloorOccurrence x

/-- Assign a global floor occurrence to its concrete physical edge. -/
noncomputable def floorOccurrenceEdge (o : G.GlobalFloorOccurrence) : G.E :=
  (G.floorOccurrenceEmbedding (G.floorBundle o.1)
    (G.floorBundleCover o.1) o.2.1 o.2.2).1

theorem floorOccurrenceEdge_mem_bundle (o : G.GlobalFloorOccurrence) :
    G.floorOccurrenceEdge o ∈ G.floorBundle o.1 :=
  (G.floorOccurrenceEmbedding (G.floorBundle o.1)
    (G.floorBundleCover o.1) o.2.1 o.2.2).2.1

theorem floorOccurrenceEdge_weight (o : G.GlobalFloorOccurrence) :
    G.weight (G.floorOccurrenceEdge o) = o.2.1.1 :=
  (G.floorOccurrenceEmbedding (G.floorBundle o.1)
    (G.floorBundleCover o.1) o.2.1 o.2.2).2.2

theorem floorOccurrenceEdge_injective :
    Function.Injective G.floorOccurrenceEdge := by
  rintro ⟨k₁, x₁, o₁⟩ ⟨k₂, x₂, o₂⟩ h
  have hk : k₁ = k₂ := by
    have hkey₁ := G.floorKey_eq_of_mem_floorBundle
      (G.floorOccurrenceEdge_mem_bundle ⟨k₁, x₁, o₁⟩)
    have hkey₂ := G.floorKey_eq_of_mem_floorBundle
      (G.floorOccurrenceEdge_mem_bundle ⟨k₂, x₂, o₂⟩)
    rw [h] at hkey₁
    exact hkey₁.symm.trans hkey₂
  subst k₂
  have hx : x₁ = x₂ := by
    apply Subtype.ext
    rw [← G.floorOccurrenceEdge_weight ⟨k₁, x₁, o₁⟩,
      ← G.floorOccurrenceEdge_weight ⟨k₁, x₂, o₂⟩, h]
  subst x₂
  have ho : o₁ = o₂ := by
    apply (G.floorOccurrenceEmbedding (G.floorBundle k₁)
      (G.floorBundleCover k₁) x₁).injective
    apply Subtype.ext
    exact h
  subst o₂
  rfl

/-- Physical edges used by the full coefficient-floor packets. -/
def IsFloorAssigned (e : G.E) : Prop :=
  ∃ o : G.GlobalFloorOccurrence, G.floorOccurrenceEdge o = e

instance (e : G.E) : Decidable (G.IsFloorAssigned e) := Classical.dec _

abbrev GlobalResidualEdge := {e : G.E // ¬ G.IsFloorAssigned e}

/-- Full packets together with singleton residual packets. -/
abbrev GlobalFloorPacketLabel :=
  G.GlobalFloorPacket ⊕ G.GlobalResidualEdge

theorem floorPacket_pattern_nonempty (q : G.GlobalFloorPacket) :
    BinPackingInstance.ExactDemandPatternCover.PatternNonempty q.2.1 := by
  by_contra h
  have hz := G.floorBundleCover_empty_coeff q.1 q.2.1 h
  have hpos : 0 < Nat.floor ((G.floorBundleCover q.1).coeff q.2.1) :=
    by
      have hlt := q.2.2.isLt
      omega
  rw [hz] at hpos
  simp at hpos

/-- Every full packet owns at least one assigned occurrence. -/
noncomputable def representativeOccurrence (q : G.GlobalFloorPacket) :
    G.GlobalFloorOccurrence := by
  let x := Classical.choose (G.floorPacket_pattern_nonempty q)
  have hx := Classical.choose_spec (G.floorPacket_pattern_nonempty q)
  exact ⟨q.1, x, q.2, ⟨0, hx⟩⟩

theorem floorPairKey_packet_key (q : G.GlobalFloorPacket) :
    G.floorPairKey q.1.1 q.1.2 = q.1 := by
  let o := G.representativeOccurrence q
  have hkey := G.floorKey_eq_of_mem_floorBundle
    (G.floorOccurrenceEdge_mem_bundle o)
  have hcanon := G.floorPairKey_floorTail_floorHead
    (G.floorOccurrenceEdge o)
  change G.floorPairKey o.1.1 o.1.2 = o.1
  rw [← hkey]
  exact hcanon

/-- Recover the unique global occurrence whose assigned edge is `e`. -/
noncomputable def occurrenceOfAssigned (e : G.E)
    (h : G.IsFloorAssigned e) : G.GlobalFloorOccurrence :=
  Classical.choose h

theorem occurrenceOfAssigned_edge (e : G.E) (h : G.IsFloorAssigned e) :
    G.floorOccurrenceEdge (G.occurrenceOfAssigned e h) = e :=
  Classical.choose_spec h

def globalFloorPacketOf (e : G.E) : G.GlobalFloorPacketLabel :=
  if h : G.IsFloorAssigned e then
    Sum.inl ⟨(G.occurrenceOfAssigned e h).1,
      (G.occurrenceOfAssigned e h).2.2.1⟩
  else Sum.inr ⟨e, h⟩

def globalFloorTail : G.GlobalFloorPacketLabel → G.V
  | Sum.inl q => q.1.1
  | Sum.inr e => G.floorTail e.1

def globalFloorHead : G.GlobalFloorPacketLabel → G.V
  | Sum.inl q => q.1.2
  | Sum.inr e => G.floorHead e.1

theorem globalFloorPacketOf_occurrence (o : G.GlobalFloorOccurrence) :
    G.globalFloorPacketOf (G.floorOccurrenceEdge o) =
      Sum.inl ⟨o.1, o.2.2.1⟩ := by
  have ha : G.IsFloorAssigned (G.floorOccurrenceEdge o) := ⟨o, rfl⟩
  simp only [globalFloorPacketOf, dif_pos ha]
  have hu : G.occurrenceOfAssigned (G.floorOccurrenceEdge o) ha = o := by
    apply G.floorOccurrenceEdge_injective
    exact G.occurrenceOfAssigned_edge _ ha
  rw [hu]

theorem globalFloorPacketOf_residual (e : G.GlobalResidualEdge) :
    G.globalFloorPacketOf e.1 = Sum.inr e := by
  simp [globalFloorPacketOf, e.2]

/-- Occurrences belonging to one fixed full packet. -/
abbrev FloorOccurrencesInPacket (q : G.GlobalFloorPacket) :=
  Σ x : G.EdgeSetWeightType (G.floorBundle q.1),
    Fin (q.2.1.multiplicity x)

/-- Physical edges whose global packet label is one fixed full packet. -/
abbrev PhysicalEdgesInFloorPacket (q : G.GlobalFloorPacket) :=
  {e : G.E // G.globalFloorPacketOf e = Sum.inl q}

def globalOccurrenceOfPacket (q : G.GlobalFloorPacket)
    (z : G.FloorOccurrencesInPacket q) : G.GlobalFloorOccurrence :=
  ⟨q.1, z.1, q.2, z.2⟩

theorem globalOccurrenceOfPacket_cast
    {q₀ q : G.GlobalFloorPacket} (h : q₀ = q)
    (z : G.FloorOccurrencesInPacket q₀) :
    G.globalOccurrenceOfPacket q
        (cast (congrArg G.FloorOccurrencesInPacket h) z) =
      G.globalOccurrenceOfPacket q₀ z := by
  subst q
  rfl

noncomputable def floorOccurrencesInPacketEquiv
    (q : G.GlobalFloorPacket) :
    G.FloorOccurrencesInPacket q ≃ G.PhysicalEdgesInFloorPacket q := by
  let toFun : G.FloorOccurrencesInPacket q →
      G.PhysicalEdgesInFloorPacket q := fun z ↦
    ⟨G.floorOccurrenceEdge (G.globalOccurrenceOfPacket q z), by
      exact G.globalFloorPacketOf_occurrence
        (G.globalOccurrenceOfPacket q z)⟩
  apply Equiv.ofBijective toFun
  constructor
  · intro z₁ z₂ h
    have hedge : G.floorOccurrenceEdge (G.globalOccurrenceOfPacket q z₁) =
        G.floorOccurrenceEdge (G.globalOccurrenceOfPacket q z₂) :=
      congrArg Subtype.val h
    have ho := G.floorOccurrenceEdge_injective hedge
    have hxval : z₁.1.1 = z₂.1.1 :=
      congrArg (fun o ↦ o.2.1.1) ho
    have hx : z₁.1 = z₂.1 := Subtype.ext hxval
    rcases z₁ with ⟨x₁, j₁⟩
    rcases z₂ with ⟨x₂, j₂⟩
    dsimp at hx ⊢
    cases hx
    have hjval : j₁.val = j₂.val :=
      congrArg (fun o ↦ o.2.2.2.val) ho
    have hj : j₁ = j₂ := Fin.ext hjval
    subst j₂
    rfl
  · intro e
    have heq := e.2
    unfold globalFloorPacketOf at heq
    split at heq
    next hassigned =>
      have hq :
          (⟨(G.occurrenceOfAssigned e.1 hassigned).1,
            (G.occurrenceOfAssigned e.1 hassigned).2.2.1⟩ :
              G.GlobalFloorPacket) = q :=
        Sum.inl_injective heq
      let o := G.occurrenceOfAssigned e.1 hassigned
      have hedge : G.floorOccurrenceEdge o = e.1 :=
        G.occurrenceOfAssigned_edge e.1 hassigned
      let z0 : G.FloorOccurrencesInPacket
          ⟨o.1, o.2.2.1⟩ := ⟨o.2.1, o.2.2.2⟩
      let z : G.FloorOccurrencesInPacket q :=
        cast (congrArg G.FloorOccurrencesInPacket hq) z0
      refine ⟨z, ?_⟩
      apply Subtype.ext
      have ho' :
          G.globalOccurrenceOfPacket q z = o := by
        calc
          G.globalOccurrenceOfPacket q z =
              G.globalOccurrenceOfPacket ⟨o.1, o.2.2.1⟩ z0 :=
            G.globalOccurrenceOfPacket_cast hq z0
          _ = o := rfl
      change G.floorOccurrenceEdge (G.globalOccurrenceOfPacket q z) = e.1
      rw [ho']
      exact hedge
    next hnot =>
      exact (Sum.inr_ne_inl heq).elim

theorem floorPacketWeight_eq_patternLoad (q : G.GlobalFloorPacket) :
    (∑ e : G.PhysicalEdgesInFloorPacket q, G.weight e.1) =
      ∑ x : G.EdgeSetWeightType (G.floorBundle q.1),
        (q.2.1.multiplicity x : ℝ) *
          (G.edgeSetWeightBinPackingInstance (G.floorBundle q.1)).weight x := by
  let E := G.floorOccurrencesInPacketEquiv q
  calc
    (∑ e : G.PhysicalEdgesInFloorPacket q, G.weight e.1) =
        ∑ z : G.FloorOccurrencesInPacket q,
          G.weight (E z).1 := (E.sum_comp (fun e ↦ G.weight e.1)).symm
    _ = ∑ z : G.FloorOccurrencesInPacket q, z.1.1 := by
      apply Finset.sum_congr rfl
      intro z _hz
      exact G.floorOccurrenceEdge_weight ⟨q.1, z.1, q.2, z.2⟩
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro x _hx
      simp [edgeSetWeightBinPackingInstance]

/-- Minimum-cover saturation forces every retained integral floor packet to
carry at least one unit of harmonic charge. -/
theorem floorPacket_harmonicPatternCharge_ge_one
    (q : G.GlobalFloorPacket) :
    1 ≤ q.2.1.harmonicPatternCharge := by
  by_contra hnot
  have hlt : q.2.1.harmonicPatternCharge < 1 := lt_of_not_ge hnot
  have hz :=
    BinPackingInstance.ExactDemandPatternCover.coeff_eq_zero_of_harmonicPatternCharge_lt_one
        (G.floorBundleCover q.1) (G.floorBundleCover_minimum q.1) q.2.1 hlt
  have hfloor : 0 < Nat.floor ((G.floorBundleCover q.1).coeff q.2.1) := by
    exact Nat.pos_of_ne_zero (fun hzero ↦ by
      simpa [hzero] using q.2.2.isLt)
  rw [hz] at hfloor
  simp at hfloor

/-- The physical edges assigned to a full floor packet have exactly the
harmonic charge of its bin pattern. -/
theorem floorPacketHarmonicCharge_eq_patternCharge
    (q : G.GlobalFloorPacket) :
    (∑ e : G.E,
      if G.globalFloorPacketOf e = Sum.inl q
        then harmonicCharge (G.weight e) else 0) =
      q.2.1.harmonicPatternCharge := by
  let E := G.floorOccurrencesInPacketEquiv q
  calc
    (∑ e : G.E,
      if G.globalFloorPacketOf e = Sum.inl q
        then harmonicCharge (G.weight e) else 0) =
        ∑ e : G.PhysicalEdgesInFloorPacket q,
          harmonicCharge (G.weight e.1) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype
        ((Finset.univ : Finset G.E).filter
          (fun e ↦ G.globalFloorPacketOf e = Sum.inl q))
        (by intro e; simp) (fun e ↦ harmonicCharge (G.weight e))
    _ = ∑ z : G.FloorOccurrencesInPacket q,
          harmonicCharge (G.weight (E z).1) :=
      (E.sum_comp (fun e ↦ harmonicCharge (G.weight e.1))).symm
    _ = ∑ z : G.FloorOccurrencesInPacket q,
          harmonicCharge z.1.1 := by
      apply Finset.sum_congr rfl
      intro z _hz
      change harmonicCharge
        (G.weight (G.floorOccurrenceEdge ⟨q.1, z.1, q.2, z.2⟩)) = _
      rw [G.floorOccurrenceEdge_weight ⟨q.1, z.1, q.2, z.2⟩]
    _ = q.2.1.harmonicPatternCharge := by
      rw [Fintype.sum_sigma]
      unfold BinPackingInstance.Pattern.harmonicPatternCharge
      apply Finset.sum_congr rfl
      intro x _hx
      simp [edgeSetWeightBinPackingInstance]

theorem sum_if_globalFloorPacketOf_eq (q : G.GlobalFloorPacket) :
    (∑ e : G.E,
      if G.globalFloorPacketOf e = Sum.inl q then G.weight e else 0) =
      ∑ e : G.PhysicalEdgesInFloorPacket q, G.weight e.1 := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    ((Finset.univ : Finset G.E).filter
      (fun e ↦ G.globalFloorPacketOf e = Sum.inl q))
    (by intro e; simp) G.weight

theorem floorTail_head_incidence (v : G.V) (e : G.E) :
    G.floorTail e = v ∨ G.floorHead e = v ↔ G.Inc v e := by
  unfold Inc floorTail floorHead
  split <;> simp [or_comm]

theorem globalFloorPacketOf_incidence (v : G.V) (e : G.E) :
    G.globalFloorTail (G.globalFloorPacketOf e) = v ∨
        G.globalFloorHead (G.globalFloorPacketOf e) = v ↔
      G.Inc v e := by
  by_cases h : G.IsFloorAssigned e
  · let o := G.occurrenceOfAssigned e h
    have hedge := G.occurrenceOfAssigned_edge e h
    have hkey := G.floorKey_eq_of_mem_floorBundle
      (G.floorOccurrenceEdge_mem_bundle o)
    unfold globalFloorPacketOf
    rw [dif_pos h]
    simp only [globalFloorTail, globalFloorHead]
    have ht : G.floorTail (G.floorOccurrenceEdge o) = o.1.1 :=
      congrArg Prod.fst hkey
    have hh : G.floorHead (G.floorOccurrenceEdge o) = o.1.2 :=
      congrArg Prod.snd hkey
    calc
      o.1.1 = v ∨ o.1.2 = v ↔
          G.floorTail (G.floorOccurrenceEdge o) = v ∨
            G.floorHead (G.floorOccurrenceEdge o) = v := by rw [ht, hh]
      _ ↔ G.Inc v (G.floorOccurrenceEdge o) :=
        G.floorTail_head_incidence v _
      _ ↔ G.Inc v e := by rw [hedge]
  · unfold globalFloorPacketOf
    rw [dif_neg h]
    simp only [globalFloorTail, globalFloorHead]
    exact G.floorTail_head_incidence v e

theorem globalFloorTail_ne_head (p : G.GlobalFloorPacketLabel) :
    G.globalFloorTail p ≠ G.globalFloorHead p := by
  cases p with
  | inr e => exact G.floorTail_ne_floorHead e.1
  | inl q =>
      let o := G.representativeOccurrence q
      have hkey := G.floorKey_eq_of_mem_floorBundle
        (G.floorOccurrenceEdge_mem_bundle o)
      have hne := G.floorTail_ne_floorHead (G.floorOccurrenceEdge o)
      simp only [globalFloorTail, globalFloorHead]
      have ht : G.floorTail (G.floorOccurrenceEdge o) = q.1.1 :=
        congrArg Prod.fst hkey
      have hh : G.floorHead (G.floorOccurrenceEdge o) = q.1.2 :=
        congrArg Prod.snd hkey
      rw [← ht, ← hh]
      exact hne

theorem globalFloorPacketOf_surjective :
    Function.Surjective G.globalFloorPacketOf := by
  intro p
  cases p with
  | inr e => exact ⟨e.1, G.globalFloorPacketOf_residual e⟩
  | inl q =>
      let o := G.representativeOccurrence q
      refine ⟨G.floorOccurrenceEdge o, ?_⟩
      rw [G.globalFloorPacketOf_occurrence o]
      simpa [o, representativeOccurrence]

/-- The global coefficient-floor construction as the packetization consumed
by the general weighted-coloring route. -/
noncomputable def floorPacketization : G.Packetization where
  Packet := G.GlobalFloorPacketLabel
  instFintypePacket := inferInstance
  instDecidableEqPacket := inferInstance
  packetOf := G.globalFloorPacketOf
  tail := G.globalFloorTail
  head := G.globalFloorHead
  noLoop := G.globalFloorTail_ne_head
  incidence := G.globalFloorPacketOf_incidence
  onto := G.globalFloorPacketOf_surjective
  weight_le_one := by
    classical
    intro p
    cases p with
    | inr e =>
        have hfiber : ∀ f : G.E,
            G.globalFloorPacketOf f = Sum.inr e ↔ f = e.1 := by
          intro f
          constructor
          · intro hf
            by_cases ha : G.IsFloorAssigned f
            · unfold globalFloorPacketOf at hf
              rw [dif_pos ha] at hf
              exact (Sum.inl_ne_inr hf).elim
            · unfold globalFloorPacketOf at hf
              rw [dif_neg ha] at hf
              exact congrArg Subtype.val (Sum.inr_injective hf)
          · intro h
            subst f
            exact G.globalFloorPacketOf_residual e
        have heq :
            (∑ f : G.E,
              if G.globalFloorPacketOf f = Sum.inr e then G.weight f else 0) =
              G.weight e.1 := by simp only [hfiber]; simp
        exact heq.trans_le (G.weight_le_one e.1)
    | inl q =>
        calc
          (∑ e : G.E,
              if G.globalFloorPacketOf e = Sum.inl q then G.weight e else 0) =
              ∑ e : G.PhysicalEdgesInFloorPacket q, G.weight e.1 :=
            G.sum_if_globalFloorPacketOf_eq q
          _ = ∑ x : G.EdgeSetWeightType (G.floorBundle q.1),
              (q.2.1.multiplicity x : ℝ) *
                (G.edgeSetWeightBinPackingInstance
                  (G.floorBundle q.1)).weight x :=
            G.floorPacketWeight_eq_patternLoad q
          _ ≤ 1 := q.2.1.capacity

/-- The selected full coefficient-floor packets; singleton residual packets
are precisely the complementary packet labels. -/
noncomputable def fullFloorPacketSet :
    Finset G.floorPacketization.Packet := by
  classical
  exact Finset.univ.filter fun p ↦
    match p with
    | Sum.inl _ => True
    | Sum.inr _ => False

@[simp] theorem mem_fullFloorPacketSet_inl (q : G.GlobalFloorPacket) :
    (Sum.inl q : G.floorPacketization.Packet) ∈ G.fullFloorPacketSet := by
  simp [fullFloorPacketSet, floorPacketization]

@[simp] theorem not_mem_fullFloorPacketSet_inr (e : G.GlobalResidualEdge) :
    (Sum.inr e : G.floorPacketization.Packet) ∉ G.fullFloorPacketSet := by
  simp [fullFloorPacketSet, floorPacketization]

end

end WeightedMultigraph
end WeightedEdgeColoring
