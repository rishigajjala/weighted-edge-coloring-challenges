import WeightedEdgeColoring.BPGeneralFloorPacketBase
import WeightedEdgeColoring.FiniteHarmonicResidualMultiplicity

/-!
# Finite harmonic refinement of the floor residual

After the exact-demand floor packets are removed, residual edges in each of
the first `T` harmonic classes are grouped in blocks of the class size inside
each canonically oriented endpoint pair.  The short remainders have endpoint
multiplicity at most `T(T-1)/2`; all edges outside these classes are uniformly
tiny.
-/

open scoped BigOperators Sym2

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- The physical edges not assigned to an exact-demand floor packet. -/
def floorResidualEdges : Finset G.E :=
  Finset.univ \
    G.floorPacketization.originalEdgesOfPackets G.fullFloorPacketSet

@[simp] theorem mem_floorResidualEdges_iff_not_floorAssigned (e : G.E) :
    e ∈ G.floorResidualEdges ↔ ¬ G.IsFloorAssigned e := by
  by_cases h : G.IsFloorAssigned e
  · simp [floorResidualEdges, Packetization.originalEdgesOfPackets,
      floorPacketization, globalFloorPacketOf, h, fullFloorPacketSet]
  · simp [floorResidualEdges, Packetization.originalEdgesOfPackets,
      floorPacketization, globalFloorPacketOf, h, fullFloorPacketSet]

theorem floorPairKey_comm (u v : G.V) :
    G.floorPairKey u v = G.floorPairKey v u := by
  unfold floorPairKey
  by_cases h : G.floorVertexCode u < G.floorVertexCode v
  · have hn : ¬G.floorVertexCode v < G.floorVertexCode u := by omega
    simp [h, hn]
  · by_cases heq : u = v
    · subst v
      rfl
    · have hcode : G.floorVertexCode u ≠ G.floorVertexCode v := by
        intro hc
        exact heq (G.floorVertexCode.injective hc)
      have hr : G.floorVertexCode v < G.floorVertexCode u := by omega
      simp [h, hr]

theorem floorKey_eq_floorPairKey_of_mem_endpointPairCell
    {u v : G.V} {e : G.E} (he : e ∈ G.endpointPairCell u v) :
    G.floorKey e = G.floorPairKey u v := by
  rw [G.floorKey_eq_floorPairKey]
  have hends := (G.mem_endpointPairCell_iff u v e).mp he
  rcases (Sym2.eq_iff).mp hends with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2, G.floorPairKey_comm]

/-- Oriented pair and one of the first `T` harmonic classes. -/
abbrev FloorResidualClassKey (T : ℕ) := (G.V × G.V) × Fin T

/-- Residual edges in one oriented endpoint-pair/harmonic-class cell. -/
def floorResidualClassCell (T : ℕ) (k : G.FloorResidualClassKey T) :
    Finset G.E :=
  G.floorResidualEdges.filter fun e ↦
    G.floorKey e = k.1 ∧
      Nat.floor (1 / G.weight e) = finiteClassSize k.2

/-- A simultaneous exact block partition of all finite harmonic cells. -/
structure FloorResidualHarmonicDecomposition (T : ℕ) where
  cellPartition : ∀ k : G.FloorResidualClassKey T,
    ExactBlockPartition (G.floorResidualClassCell T k)
      (finiteClassSize k.2)

theorem exists_floorResidualHarmonicDecomposition (T : ℕ) :
    Nonempty (G.FloorResidualHarmonicDecomposition T) := by
  classical
  refine ⟨⟨fun k ↦ Classical.choice ?_⟩⟩
  exact exists_exactBlockPartition (G.floorResidualClassCell T k)
    (finiteClassSize k.2) (finiteClassSize_pos k.2)

namespace FloorResidualHarmonicDecomposition

variable {G} {T : ℕ} (D : G.FloorResidualHarmonicDecomposition T)

/-- Full finite-class blocks, indexed by their endpoint/class cell. -/
abbrev FullBlockPacket :=
  Σ k : G.FloorResidualClassKey T,
    {A : Finset G.E // A ∈ (D.cellPartition k).blocks}

noncomputable instance instDecidableEqFullBlockPacket :
    DecidableEq D.FullBlockPacket := Classical.decEq _

/-- Physical edges carried by a full finite-class block. -/
def fullBlockPacketEdges (p : D.FullBlockPacket) : Finset G.E := p.2.1

/-- Total physical weight of a full finite-class block. -/
def fullBlockPacketWeight (p : D.FullBlockPacket) : ℝ :=
  ∑ e ∈ D.fullBlockPacketEdges p, G.weight e

theorem fullBlockPacketEdges_card (p : D.FullBlockPacket) :
    (D.fullBlockPacketEdges p).card = finiteClassSize p.1.2 :=
  (D.cellPartition p.1).block_card p.2.1 p.2.2

theorem fullBlockPacketEdges_subset_cell (p : D.FullBlockPacket) :
    D.fullBlockPacketEdges p ⊆ G.floorResidualClassCell T p.1 :=
  (D.cellPartition p.1).block_subset p.2.1 p.2.2

theorem floor_eq_classSize_of_mem_fullBlockPacketEdges
    (p : D.FullBlockPacket) {e : G.E}
    (he : e ∈ D.fullBlockPacketEdges p) :
    Nat.floor (1 / G.weight e) = finiteClassSize p.1.2 := by
  exact (Finset.mem_filter.mp (D.fullBlockPacketEdges_subset_cell p he)).2.2

theorem floorKey_eq_of_mem_fullBlockPacketEdges
    (p : D.FullBlockPacket) {e : G.E}
    (he : e ∈ D.fullBlockPacketEdges p) :
    G.floorKey e = p.1.1 := by
  exact (Finset.mem_filter.mp (D.fullBlockPacketEdges_subset_cell p he)).2.1

/-- Full blocks in the simultaneous cell decomposition are uniquely
determined by any one of their physical edges. -/
theorem fullBlockPacket_eq_of_mem_edges
    (p q : D.FullBlockPacket) {e : G.E}
    (hep : e ∈ D.fullBlockPacketEdges p)
    (heq : e ∈ D.fullBlockPacketEdges q) : p = q := by
  have hpair : p.1.1 = q.1.1 :=
    (D.floorKey_eq_of_mem_fullBlockPacketEdges p hep).symm.trans
      (D.floorKey_eq_of_mem_fullBlockPacketEdges q heq)
  have hsize : finiteClassSize p.1.2 = finiteClassSize q.1.2 :=
    (D.floor_eq_classSize_of_mem_fullBlockPacketEdges p hep).symm.trans
      (D.floor_eq_classSize_of_mem_fullBlockPacketEdges q heq)
  have hclass : p.1.2 = q.1.2 := by
    apply Fin.ext
    unfold finiteClassSize at hsize
    omega
  have hkey : p.1 = q.1 := Prod.ext hpair hclass
  cases p with
  | mk kp Ap =>
    cases q with
    | mk kq Aq =>
      simp only at hkey
      subst kq
      congr 1
      apply Subtype.ext
      by_contra hne
      have hd := (D.cellPartition kp).blocks_disjoint
        Ap.1 Ap.2 Aq.1 Aq.2 hne
      exact Finset.disjoint_left.mp hd hep heq

/-- Every added finite-class block is a valid unit-capacity packet. -/
theorem fullBlockPacketWeight_le_one (p : D.FullBlockPacket) :
    D.fullBlockPacketWeight p ≤ 1 := by
  let r := finiteClassSize p.1.2
  have hrNat : 0 < r := finiteClassSize_pos p.1.2
  have hr : (0 : ℝ) < r := by exact_mod_cast hrNat
  have hedge : ∀ e ∈ D.fullBlockPacketEdges p,
      G.weight e ≤ (1 : ℝ) / r := by
    intro e he
    have hfloor := Nat.floor_le
      (div_nonneg zero_le_one (G.weight_pos e).le)
    have hle : (r : ℝ) ≤ 1 / G.weight e := by
      rw [D.floor_eq_classSize_of_mem_fullBlockPacketEdges p he] at hfloor
      exact hfloor
    have hmul : G.weight e * (r : ℝ) ≤ 1 := by
      have := (le_div_iff₀ (G.weight_pos e)).1 hle
      simpa [mul_comm] using this
    exact (le_div_iff₀ hr).2 hmul
  calc
    D.fullBlockPacketWeight p ≤
        ∑ _e ∈ D.fullBlockPacketEdges p, (1 : ℝ) / r := by
      apply Finset.sum_le_sum
      intro e he
      exact hedge e he
    _ = ((D.fullBlockPacketEdges p).card : ℝ) / r := by
      simp [div_eq_mul_inv]
    _ = 1 := by
      rw [D.fullBlockPacketEdges_card p]
      exact div_self (by exact_mod_cast Nat.ne_of_gt hrNat)

/-- A full finite-class block carries exactly one unit of harmonic charge. -/
theorem fullBlockPacket_harmonicCharge_eq_one (p : D.FullBlockPacket) :
    (∑ e ∈ D.fullBlockPacketEdges p,
      harmonicCharge (G.weight e)) = 1 := by
  let r := finiteClassSize p.1.2
  have hr : r ≠ 0 := Nat.ne_of_gt (finiteClassSize_pos p.1.2)
  calc
    (∑ e ∈ D.fullBlockPacketEdges p,
        harmonicCharge (G.weight e)) =
        ∑ _e ∈ D.fullBlockPacketEdges p, (1 : ℝ) / r := by
      apply Finset.sum_congr rfl
      intro e he
      unfold harmonicCharge
      rw [D.floor_eq_classSize_of_mem_fullBlockPacketEdges p he]
    _ = ((D.fullBlockPacketEdges p).card : ℝ) / r := by
      simp [div_eq_mul_inv]
    _ = 1 := by
      rw [D.fullBlockPacketEdges_card p]
      exact div_self (by exact_mod_cast hr)

/-- A full class block is strictly heavier than one half. -/
theorem half_lt_fullBlockPacketWeight (p : D.FullBlockPacket) :
    (1 / 2 : ℝ) < D.fullBlockPacketWeight p := by
  let r := finiteClassSize p.1.2
  have hrNat : 0 < r := finiteClassSize_pos p.1.2
  have hrReal : (1 : ℝ) ≤ r := by exact_mod_cast hrNat
  have hden : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hfrac : (1 / 2 : ℝ) ≤ (r : ℝ) / ((r : ℝ) + 1) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hlower : ∀ e ∈ D.fullBlockPacketEdges p,
      (1 : ℝ) / ((r : ℝ) + 1) < G.weight e := by
    intro e he
    have hlt := Nat.lt_floor_add_one ((1 : ℝ) / G.weight e)
    rw [D.floor_eq_classSize_of_mem_fullBlockPacketEdges p he] at hlt
    have hmul := (div_lt_iff₀ (G.weight_pos e)).1 hlt
    exact (div_lt_iff₀ hden).2 (by nlinarith)
  have hsum :
      (∑ _e ∈ D.fullBlockPacketEdges p,
        (1 : ℝ) / ((r : ℝ) + 1)) < D.fullBlockPacketWeight p := by
    unfold fullBlockPacketWeight
    apply Finset.sum_lt_sum_of_nonempty
    · apply Finset.card_pos.mp
      rw [D.fullBlockPacketEdges_card p]
      exact hrNat
    · exact hlower
  have hconst :
      (∑ _e ∈ D.fullBlockPacketEdges p,
        (1 : ℝ) / ((r : ℝ) + 1)) =
        (r : ℝ) / ((r : ℝ) + 1) := by
    rw [Finset.sum_const, nsmul_eq_mul, D.fullBlockPacketEdges_card]
    simp [r, div_eq_mul_inv]
  calc
    (1 / 2 : ℝ) ≤ (r : ℝ) / ((r : ℝ) + 1) := hfrac
    _ = ∑ _e ∈ D.fullBlockPacketEdges p,
        (1 : ℝ) / ((r : ℝ) + 1) := hconst.symm
    _ < D.fullBlockPacketWeight p := hsum

/-- Union of all full finite-class blocks. -/
def fullBlockEdges : Finset G.E :=
  Finset.univ.filter fun e ↦
    ∃ p : D.FullBlockPacket, e ∈ D.fullBlockPacketEdges p

theorem mem_fullBlockEdges_iff (e : G.E) :
    e ∈ D.fullBlockEdges ↔
      ∃ p : D.FullBlockPacket, e ∈ D.fullBlockPacketEdges p := by
  simp [fullBlockEdges]

/-- The unique full harmonic block containing a block edge. -/
noncomputable def fullBlockPacketOf (e : G.E) (he : e ∈ D.fullBlockEdges) :
    D.FullBlockPacket :=
  Classical.choose ((D.mem_fullBlockEdges_iff e).1 he)

theorem mem_fullBlockPacketOf (e : G.E) (he : e ∈ D.fullBlockEdges) :
    e ∈ D.fullBlockPacketEdges (D.fullBlockPacketOf e he) :=
  Classical.choose_spec ((D.mem_fullBlockEdges_iff e).1 he)

theorem fullBlockPacketOf_eq_of_mem
    (e : G.E) (he : e ∈ D.fullBlockEdges) (p : D.FullBlockPacket)
    (hep : e ∈ D.fullBlockPacketEdges p) :
    D.fullBlockPacketOf e he = p :=
  D.fullBlockPacket_eq_of_mem_edges _ _
    (D.mem_fullBlockPacketOf e he) hep

/-- Residual physical edges not absorbed into a full finite-class block. -/
abbrev NonBlockResidualEdge :=
  {e : G.E // e ∈ G.floorResidualEdges ∧ e ∉ D.fullBlockEdges}

/-- Original coefficient-floor packets, added finite harmonic blocks, and
the remaining singleton physical edges. -/
abbrev RefinedFloorPacketLabel :=
  G.GlobalFloorPacket ⊕ (D.FullBlockPacket ⊕ D.NonBlockResidualEdge)

def refinedFloorPacketOf (e : G.E) : D.RefinedFloorPacketLabel :=
  if ha : G.IsFloorAssigned e then
    Sum.inl ⟨(G.occurrenceOfAssigned e ha).1,
      (G.occurrenceOfAssigned e ha).2.2.1⟩
  else if hb : e ∈ D.fullBlockEdges then
    Sum.inr (Sum.inl (D.fullBlockPacketOf e hb))
  else
    Sum.inr (Sum.inr ⟨e,
      (G.mem_floorResidualEdges_iff_not_floorAssigned e).2 ha, hb⟩)

def refinedFloorPacketTail : D.RefinedFloorPacketLabel → G.V
  | Sum.inl q => q.1.1
  | Sum.inr (Sum.inl p) => p.1.1.1
  | Sum.inr (Sum.inr e) => G.floorTail e.1

def refinedFloorPacketHead : D.RefinedFloorPacketLabel → G.V
  | Sum.inl q => q.1.2
  | Sum.inr (Sum.inl p) => p.1.1.2
  | Sum.inr (Sum.inr e) => G.floorHead e.1

theorem refinedFloorPacketOf_incidence (v : G.V) (e : G.E) :
    D.refinedFloorPacketTail (D.refinedFloorPacketOf e) = v ∨
        D.refinedFloorPacketHead (D.refinedFloorPacketOf e) = v ↔
      G.Inc v e := by
  by_cases ha : G.IsFloorAssigned e
  · have h := G.globalFloorPacketOf_incidence v e
    unfold globalFloorPacketOf at h
    rw [dif_pos ha] at h
    unfold refinedFloorPacketOf
    rw [dif_pos ha]
    simpa [refinedFloorPacketTail, refinedFloorPacketHead,
      globalFloorTail, globalFloorHead] using h
  · by_cases hb : e ∈ D.fullBlockEdges
    · unfold refinedFloorPacketOf
      rw [dif_neg ha, dif_pos hb]
      simp only [refinedFloorPacketTail, refinedFloorPacketHead]
      have hkey := D.floorKey_eq_of_mem_fullBlockPacketEdges
        (D.fullBlockPacketOf e hb) (D.mem_fullBlockPacketOf e hb)
      change (D.fullBlockPacketOf e hb).1.1.1 = v ∨
          (D.fullBlockPacketOf e hb).1.1.2 = v ↔ G.Inc v e
      rw [← hkey]
      exact G.floorTail_head_incidence v e
    · unfold refinedFloorPacketOf
      rw [dif_neg ha, dif_neg hb]
      simp only [refinedFloorPacketTail, refinedFloorPacketHead]
      exact G.floorTail_head_incidence v e

theorem refinedFloorPacketTail_ne_head (p : D.RefinedFloorPacketLabel) :
    D.refinedFloorPacketTail p ≠ D.refinedFloorPacketHead p := by
  cases p with
  | inl q =>
      exact G.globalFloorTail_ne_head (Sum.inl q)
  | inr p =>
      cases p with
      | inr e => exact G.floorTail_ne_floorHead e.1
      | inl p =>
          have hne : (D.fullBlockPacketEdges p).Nonempty := by
            apply Finset.card_pos.mp
            rw [D.fullBlockPacketEdges_card p]
            exact finiteClassSize_pos p.1.2
          obtain ⟨e, he⟩ := hne
          have hkey := D.floorKey_eq_of_mem_fullBlockPacketEdges p he
          change p.1.1.1 ≠ p.1.1.2
          rw [← hkey]
          exact G.floorTail_ne_floorHead e

theorem refinedFloorPacketOf_eq_inl_iff (e : G.E)
    (q : G.GlobalFloorPacket) :
    D.refinedFloorPacketOf e = Sum.inl q ↔
      G.globalFloorPacketOf e = Sum.inl q := by
  by_cases ha : G.IsFloorAssigned e
  · simp [refinedFloorPacketOf, globalFloorPacketOf, ha]
  · by_cases hb : e ∈ D.fullBlockEdges <;>
      simp [refinedFloorPacketOf, globalFloorPacketOf, ha, hb]

theorem refinedFloorPacketOf_eq_fullBlock_iff (e : G.E)
    (p : D.FullBlockPacket) :
    D.refinedFloorPacketOf e = Sum.inr (Sum.inl p) ↔
      e ∈ D.fullBlockPacketEdges p := by
  constructor
  · intro h
    by_cases ha : G.IsFloorAssigned e
    · simp [refinedFloorPacketOf, ha] at h
    · by_cases hb : e ∈ D.fullBlockEdges
      · unfold refinedFloorPacketOf at h
        rw [dif_neg ha, dif_pos hb] at h
        have hp : D.fullBlockPacketOf e hb = p :=
          Sum.inl.inj (Sum.inr.inj h)
        rw [← hp]
        exact D.mem_fullBlockPacketOf e hb
      · simp [refinedFloorPacketOf, ha, hb] at h
  · intro he
    have hres : e ∈ G.floorResidualEdges :=
      (Finset.mem_filter.mp (D.fullBlockPacketEdges_subset_cell p he)).1
    have ha : ¬ G.IsFloorAssigned e :=
      (G.mem_floorResidualEdges_iff_not_floorAssigned e).1 hres
    have hb : e ∈ D.fullBlockEdges :=
      (D.mem_fullBlockEdges_iff e).2 ⟨p, he⟩
    unfold refinedFloorPacketOf
    rw [dif_neg ha, dif_pos hb]
    rw [D.fullBlockPacketOf_eq_of_mem e hb p he]

theorem refinedFloorPacketOf_eq_singleton_iff
    (e : G.E) (r : D.NonBlockResidualEdge) :
    D.refinedFloorPacketOf e = Sum.inr (Sum.inr r) ↔ e = r.1 := by
  constructor
  · intro h
    by_cases ha : G.IsFloorAssigned e
    · simp [refinedFloorPacketOf, ha] at h
    · by_cases hb : e ∈ D.fullBlockEdges
      · simp [refinedFloorPacketOf, ha, hb] at h
      · unfold refinedFloorPacketOf at h
        rw [dif_neg ha, dif_neg hb] at h
        exact congrArg Subtype.val (Sum.inr.inj (Sum.inr.inj h))
  · intro he
    subst e
    have ha : ¬ G.IsFloorAssigned r.1 :=
      (G.mem_floorResidualEdges_iff_not_floorAssigned r.1).1 r.2.1
    simp [refinedFloorPacketOf, ha, r.2.2]

theorem refinedFloorPacketOf_surjective :
    Function.Surjective D.refinedFloorPacketOf := by
  intro p
  rcases p with q | p
  · let o := G.representativeOccurrence q
    refine ⟨G.floorOccurrenceEdge o, ?_⟩
    apply (D.refinedFloorPacketOf_eq_inl_iff _ q).2
    rw [G.globalFloorPacketOf_occurrence o]
    simpa [o, representativeOccurrence]
  · rcases p with p | r
    · have hne : (D.fullBlockPacketEdges p).Nonempty := by
        apply Finset.card_pos.mp
        rw [D.fullBlockPacketEdges_card p]
        exact finiteClassSize_pos p.1.2
      obtain ⟨e, he⟩ := hne
      exact ⟨e, (D.refinedFloorPacketOf_eq_fullBlock_iff e p).2 he⟩
    · exact ⟨r.1,
        (D.refinedFloorPacketOf_eq_singleton_iff r.1 r).2 rfl⟩

/-- The global packetization obtained by adjoining all full finite harmonic
blocks to the original coefficient-floor packets. -/
noncomputable def refinedFloorPacketization : G.Packetization where
  Packet := D.RefinedFloorPacketLabel
  instFintypePacket := inferInstance
  instDecidableEqPacket := inferInstance
  packetOf := D.refinedFloorPacketOf
  tail := D.refinedFloorPacketTail
  head := D.refinedFloorPacketHead
  noLoop := D.refinedFloorPacketTail_ne_head
  incidence := D.refinedFloorPacketOf_incidence
  onto := D.refinedFloorPacketOf_surjective
  weight_le_one := by
    classical
    intro p
    rcases p with q | p
    · have h := G.floorPacketization.weight_le_one (Sum.inl q)
      simpa only [D.refinedFloorPacketOf_eq_inl_iff] using h
    · rcases p with p | r
      · calc
          (∑ e : G.E,
              if D.refinedFloorPacketOf e = Sum.inr (Sum.inl p)
                then G.weight e else 0) =
              D.fullBlockPacketWeight p := by
                simp only [D.refinedFloorPacketOf_eq_fullBlock_iff]
                simp [fullBlockPacketWeight]
          _ ≤ 1 := D.fullBlockPacketWeight_le_one p
      · calc
          (∑ e : G.E,
              if D.refinedFloorPacketOf e = Sum.inr (Sum.inr r)
                then G.weight e else 0) = G.weight r.1 := by
              simp only [D.refinedFloorPacketOf_eq_singleton_iff]
              simp
          _ ≤ 1 := G.weight_le_one r.1

/-- Selected packets in the refined base: both coefficient-floor packets
and the newly adjoined full harmonic blocks. -/
noncomputable def refinedFullPacketSet :
    Finset D.refinedFloorPacketization.Packet := by
  classical
  exact Finset.univ.filter fun p ↦
    match p with
    | Sum.inl _ => True
    | Sum.inr (Sum.inl _) => True
    | Sum.inr (Sum.inr _) => False

@[simp] theorem mem_refinedFullPacketSet_inl (q : G.GlobalFloorPacket) :
    (Sum.inl q : D.refinedFloorPacketization.Packet) ∈
      D.refinedFullPacketSet := by
  simp [refinedFullPacketSet, refinedFloorPacketization]

@[simp] theorem mem_refinedFullPacketSet_fullBlock
    (p : D.FullBlockPacket) :
    (Sum.inr (Sum.inl p) : D.refinedFloorPacketization.Packet) ∈
      D.refinedFullPacketSet := by
  simp [refinedFullPacketSet, refinedFloorPacketization]

@[simp] theorem not_mem_refinedFullPacketSet_singleton
    (e : D.NonBlockResidualEdge) :
    (Sum.inr (Sum.inr e) : D.refinedFloorPacketization.Packet) ∉
      D.refinedFullPacketSet := by
  simp [refinedFullPacketSet, refinedFloorPacketization]

/-- Every packet selected in the refined ordinary base carries at least one
unit of original harmonic charge. -/
theorem one_le_refinedPacketCharge_of_mem
    {p : D.refinedFloorPacketization.Packet}
    (hp : p ∈ D.refinedFullPacketSet) :
    1 ≤ D.refinedFloorPacketization.packetCharge harmonicCharge p := by
  rcases p with q | p
  · have h := G.one_le_floorPacketCharge q
    change 1 ≤ ∑ e : G.E,
      if G.globalFloorPacketOf e = Sum.inl q
        then harmonicCharge (G.weight e) else 0 at h
    change 1 ≤ ∑ e : G.E,
      if D.refinedFloorPacketOf e = Sum.inl q
        then harmonicCharge (G.weight e) else 0
    simpa only [Packetization.packetCharge,
      D.refinedFloorPacketOf_eq_inl_iff] using h
  · rcases p with p | r
    · change 1 ≤ ∑ e : G.E,
        if D.refinedFloorPacketOf e = Sum.inr (Sum.inl p)
          then harmonicCharge (G.weight e) else 0
      rw [show (∑ e : G.E,
          if D.refinedFloorPacketOf e = Sum.inr (Sum.inl p)
            then harmonicCharge (G.weight e) else 0) =
          ∑ e ∈ D.fullBlockPacketEdges p,
            harmonicCharge (G.weight e) by
        simp only [D.refinedFloorPacketOf_eq_fullBlock_iff]
        simp]
      rw [D.fullBlockPacket_harmonicCharge_eq_one p]
    · exact (D.not_mem_refinedFullPacketSet_singleton r hp).elim

/-- Exact charge accounting survives after all full finite harmonic blocks
are moved from the residual into the ordinary packet base. -/
theorem refinedPacketDegree_add_residualHarmonicCharge_le
    (v : G.V) :
    (D.refinedFloorPacketization.groupedGraph.degreeOn
        D.refinedFullPacketSet v : ℝ) +
      G.chargeOn harmonicCharge
        (Finset.univ \
          D.refinedFloorPacketization.originalEdgesOfPackets
            D.refinedFullPacketSet) v ≤
      G.starCharge harmonicCharge v := by
  let P := D.refinedFloorPacketization
  let S := D.refinedFullPacketSet
  have hselected :
      (P.groupedGraph.degreeOn S v : ℝ) ≤
        G.chargeOn harmonicCharge (P.originalEdgesOfPackets S) v := by
    rw [P.chargeOn_originalEdgesOfPackets harmonicCharge S v]
    unfold WeightedMultigraph.degreeOn
    calc
      ((S.filter (P.groupedGraph.Inc v)).card : ℝ) =
          ∑ _p ∈ S.filter (P.groupedGraph.Inc v), (1 : ℝ) := by simp
      _ ≤ ∑ p ∈ S.filter (P.groupedGraph.Inc v),
          P.packetCharge harmonicCharge p := by
        apply Finset.sum_le_sum
        intro p hp
        exact D.one_le_refinedPacketCharge_of_mem
          (Finset.mem_filter.mp hp).1
      _ = ∑ p ∈ S,
          if P.groupedGraph.Inc v p
            then P.packetCharge harmonicCharge p else 0 := by
        rw [Finset.sum_filter]
        rfl
  have hdisj : Disjoint (P.originalEdgesOfPackets S)
      (Finset.univ \ P.originalEdgesOfPackets S) := by
    rw [Finset.disjoint_left]
    intro e heF heR
    exact (Finset.mem_sdiff.mp heR).2 heF
  have hunion :
      P.originalEdgesOfPackets S ∪
          (Finset.univ \ P.originalEdgesOfPackets S) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ _)
  calc
    (P.groupedGraph.degreeOn S v : ℝ) +
        G.chargeOn harmonicCharge
          (Finset.univ \ P.originalEdgesOfPackets S) v ≤
      G.chargeOn harmonicCharge (P.originalEdgesOfPackets S) v +
        G.chargeOn harmonicCharge
          (Finset.univ \ P.originalEdgesOfPackets S) v :=
      add_le_add hselected le_rfl
    _ = G.chargeOn harmonicCharge
        (P.originalEdgesOfPackets S ∪
          (Finset.univ \ P.originalEdgesOfPackets S)) v :=
      (G.chargeOn_union hdisj v).symm
    _ = G.chargeOn harmonicCharge Finset.univ v := by rw [hunion]
    _ = G.starCharge harmonicCharge v :=
      (G.starCharge_eq_chargeOn_univ harmonicCharge v).symm

theorem refinedPacketDegree_le_starCharge (v : G.V) :
    (D.refinedFloorPacketization.groupedGraph.degreeOn
        D.refinedFullPacketSet v : ℝ) ≤ G.starCharge harmonicCharge v := by
  have h := D.refinedPacketDegree_add_residualHarmonicCharge_le v
  have hres : 0 ≤ G.chargeOn harmonicCharge
      (Finset.univ \
        D.refinedFloorPacketization.originalEdgesOfPackets
          D.refinedFullPacketSet) v := by
    unfold WeightedMultigraph.chargeOn
    apply Finset.sum_nonneg
    intro e _he
    split
    · exact harmonicCharge_nonneg _
    · exact le_rfl
  linarith

/-- The unconditional triangle bound furnished by charge accounting alone.
For the target charge `Q = 8n/5 + 3` it is `12n/5 + 9/2`, exposing the
linear gap that prevents simply adjoining these blocks to the ordinary
`2n` base. -/
theorem refinedFloorPacketization_triangleEdgeCountAtMost_of_charge
    (Q : ℝ) (hcharge : ∀ v, G.starCharge harmonicCharge v ≤ Q) :
    D.refinedFloorPacketization.groupedGraph.TriangleEdgeCountAtMost
      D.refinedFullPacketSet ((3 / 2 : ℝ) * Q) := by
  intro U hU
  have hdegree : ∀ v,
      (D.refinedFloorPacketization.groupedGraph.degreeOn
        D.refinedFullPacketSet v : ℝ) ≤ Q := fun v ↦
    (D.refinedPacketDegree_le_starCharge v).trans (hcharge v)
  have hhand :=
    D.refinedFloorPacketization.groupedGraph
      |>.two_mul_internalEdges_card_le_card_mul_degreeCap
        D.refinedFullPacketSet U Q hdegree
  rw [hU] at hhand
  norm_num at hhand ⊢
  linarith

theorem refinedFloorPacketization_triangleEdgeCountAtMost_eightFifths
    (n : ℕ)
    (hcharge : ∀ v, G.starCharge harmonicCharge v ≤
      (8 / 5 : ℝ) * n + 3) :
    D.refinedFloorPacketization.groupedGraph.TriangleEdgeCountAtMost
      D.refinedFullPacketSet ((12 / 5 : ℝ) * n + 9 / 2) := by
  have h := D.refinedFloorPacketization_triangleEdgeCountAtMost_of_charge
    ((8 / 5 : ℝ) * n + 3) hcharge
  convert h using 1 <;> ring

/-- The corresponding all-odd-set bound.  Its factor `3/2` is forced by
the three-vertex handshake estimate, so this refinement alone does not
preserve the `2n` obstruction used by the target ordinary base. -/
theorem refinedFloorPacketization_oddSetDensityAtMost_of_charge
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hcharge : ∀ v, G.starCharge harmonicCharge v ≤ Q) :
    D.refinedFloorPacketization.groupedGraph.OddSetDensityAtMost
      D.refinedFullPacketSet ((3 / 2 : ℝ) * Q) := by
  have hdegree : ∀ v,
      (D.refinedFloorPacketization.groupedGraph.degreeOn
        D.refinedFullPacketSet v : ℝ) ≤ Q := fun v ↦
    (D.refinedPacketDegree_le_starCharge v).trans (hcharge v)
  have htriangle :=
    D.refinedFloorPacketization_triangleEdgeCountAtMost_of_charge Q hcharge
  have h :=
    D.refinedFloorPacketization.groupedGraph
      |>.oddSetDensityAtMost_max_two_fiveFourth
        D.refinedFullPacketSet ((3 / 4 : ℝ) * Q) Q
        (by positivity) hQ hdegree (by convert htriangle using 1 <;> ring)
  have hmax :
      max (2 * ((3 / 4 : ℝ) * Q)) ((5 / 4 : ℝ) * Q) =
        (3 / 2 : ℝ) * Q := by
    rw [max_eq_left]
    · ring
    · nlinarith
  simpa [hmax] using h

theorem refinedFloorPacketization_oddSetDensityAtMost_eightFifths
    (n : ℕ)
    (hcharge : ∀ v, G.starCharge harmonicCharge v ≤
      (8 / 5 : ℝ) * n + 3) :
    D.refinedFloorPacketization.groupedGraph.OddSetDensityAtMost
      D.refinedFullPacketSet ((12 / 5 : ℝ) * n + 9 / 2) := by
  have hQ : 0 ≤ (8 / 5 : ℝ) * (n : ℝ) + 3 := by positivity
  have h := D.refinedFloorPacketization_oddSetDensityAtMost_of_charge
    ((8 / 5 : ℝ) * n + 3) hQ hcharge
  convert h using 1 <;> ring

/-- Union of the short remainder in every finite harmonic cell. -/
def remainderEdges : Finset G.E :=
  Finset.univ.filter fun e ↦
    ∃ a : Fin T,
      e ∈ (D.cellPartition (G.floorKey e, a)).remainder

theorem mem_remainderEdges_iff (e : G.E) :
    e ∈ D.remainderEdges ↔
      ∃ a : Fin T,
        e ∈ (D.cellPartition (G.floorKey e, a)).remainder := by
  simp [remainderEdges]

/-- Remainders over one oriented pair have the standard quadratic bound. -/
theorem remainderEdges_pairKey_card_le (k : G.V × G.V) :
    (D.remainderEdges.filter fun e ↦ G.floorKey e = k).card ≤
      T * (T - 1) / 2 := by
  let R : Fin T → Finset G.E := fun a ↦
    (D.cellPartition (k, a)).remainder
  have hsub :
      D.remainderEdges.filter (fun e ↦ G.floorKey e = k) ⊆
        (Finset.univ : Finset (Fin T)).biUnion R := by
    intro e he
    have he' := Finset.mem_filter.mp he
    rcases (D.mem_remainderEdges_iff e).mp he'.1 with ⟨a, ha⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_univ _, ?_⟩
    rw [he'.2] at ha
    exact ha
  calc
    (D.remainderEdges.filter fun e ↦ G.floorKey e = k).card ≤
        ((Finset.univ : Finset (Fin T)).biUnion R).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ a : Fin T, (R a).card := Finset.card_biUnion_le
    _ ≤ ∑ a : Fin T, a.1 := by
      apply Finset.sum_le_sum
      intro a _ha
      exact Nat.le_pred_of_lt (D.cellPartition (k, a)).remainder_card_lt
    _ = T * (T - 1) / 2 := sum_fin_val T

/-- The graph induced by the short finite-class remainders. -/
abbrev remainderGraph : WeightedMultigraph.{u} :=
  G.edgeRestriction D.remainderEdges

theorem remainderGraph_pairMultiplicityAtMost :
    D.remainderGraph.PairMultiplicityAtMost (T * (T - 1) / 2) := by
  intro u v
  let emb : D.remainderGraph.E ↪ G.E :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let F := D.remainderGraph.endpointPairCell u v
  have hmap : F.map emb =
      D.remainderEdges.filter fun e ↦ e ∈ G.endpointPairCell u v := by
    ext e
    simp [F, emb, remainderGraph, WeightedMultigraph.endpointPairCell,
      WeightedMultigraph.endpoints, and_comm]
  have hkeySub :
      D.remainderEdges.filter (fun e ↦ e ∈ G.endpointPairCell u v) ⊆
        D.remainderEdges.filter
          (fun e ↦ G.floorKey e = G.floorPairKey u v) := by
    intro e he
    have he' := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr
      ⟨he'.1, G.floorKey_eq_floorPairKey_of_mem_endpointPairCell he'.2⟩
  calc
    F.card = (F.map emb).card := (Finset.card_map emb).symm
    _ = (D.remainderEdges.filter
        fun e ↦ e ∈ G.endpointPairCell u v).card :=
      congrArg Finset.card hmap
    _ ≤ (D.remainderEdges.filter
        fun e ↦ G.floorKey e = G.floorPairKey u v).card :=
      Finset.card_le_card hkeySub
    _ ≤ T * (T - 1) / 2 :=
      D.remainderEdges_pairKey_card_le (G.floorPairKey u v)

/-- Residual edges beyond the first `T` harmonic classes. -/
def tinyTailEdges : Finset G.E :=
  G.floorResidualEdges.filter fun e ↦
    T < Nat.floor (1 / G.weight e)

theorem weight_le_inv_succ_of_mem_tinyTailEdges
    {e : G.E} (he : e ∈ tinyTailEdges (G := G) (T := T)) :
    G.weight e ≤ (1 : ℝ) / (T + 1) := by
  have he' := (Finset.mem_filter.mp he).2
  have hfloor := Nat.floor_le
    (div_nonneg zero_le_one (G.weight_pos e).le)
  have hcast : ((T + 1 : ℕ) : ℝ) ≤
      (Nat.floor (1 / G.weight e) : ℕ) := by
    exact_mod_cast he'
  have hle : ((T + 1 : ℕ) : ℝ) ≤ 1 / G.weight e :=
    hcast.trans hfloor
  have hpos : (0 : ℝ) < ((T + 1 : ℕ) : ℝ) := by positivity
  rw [le_div_iff₀ (G.weight_pos e)] at hle
  have hmul : G.weight e * ((T + 1 : ℕ) : ℝ) ≤ 1 := by
    simpa [mul_comm] using hle
  simpa only [Nat.cast_add, Nat.cast_one] using
    (le_div_iff₀ hpos).2 hmul

/-- On the tiny tail, harmonic charge differs from physical weight by at
most the explicit factor `(T+2)/(T+1)`, which tends to one with the fixed
cutoff. -/
theorem harmonicCharge_le_tailFactor_mul_weight
    {e : G.E} (he : e ∈ tinyTailEdges (G := G) (T := T)) :
    harmonicCharge (G.weight e) ≤
      ((((T + 1) + 1 : ℕ) : ℝ) / (T + 1 : ℕ)) * G.weight e := by
  have hw : G.weight e ≤ (1 : ℝ) / ((T + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (weight_le_inv_succ_of_mem_tinyTailEdges (G := G) (T := T) he)
  exact harmonicCharge_le_mul_weight (t := T + 1) (Nat.succ_pos T)
    (G.weight_pos e) hw

theorem tinyTailHarmonicCharge_le_tailFactor_mul_weight (v : G.V) :
    G.chargeOn harmonicCharge (tinyTailEdges (G := G) (T := T)) v ≤
      ((((T + 1) + 1 : ℕ) : ℝ) / (T + 1 : ℕ)) *
        (∑ e ∈ tinyTailEdges (G := G) (T := T),
          if G.Inc v e then G.weight e else 0) := by
  unfold WeightedMultigraph.chargeOn
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  by_cases hinc : G.Inc v e
  · simp only [hinc, if_true]
    exact harmonicCharge_le_tailFactor_mul_weight (G := G) (T := T) he
  · simp [hinc]

/-- Every floor-residual edge lies in exactly the finite-class part or the
uniformly tiny tail; the finite-class part is covered by full blocks and
short remainders. -/
theorem mem_floorResidualEdges_iff_fullBlock_or_remainder_or_tinyTail
    (e : G.E) :
    e ∈ G.floorResidualEdges ↔
      e ∈ D.fullBlockEdges ∨
        e ∈ D.remainderEdges ∨
          e ∈ tinyTailEdges (G := G) (T := T) := by
  constructor
  · intro he
    let r : ℕ := Nat.floor (1 / G.weight e)
    by_cases htail : T < r
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨he, htail⟩))
    · have hrle : r ≤ T := Nat.le_of_not_gt htail
      have hone : 1 ≤ r := by
        have hinv : (1 : ℝ) ≤ 1 / G.weight e := by
          rw [le_div_iff₀ (G.weight_pos e)]
          simpa using G.weight_le_one e
        have hinv' : ((1 : ℕ) : ℝ) ≤ 1 / G.weight e := by
          norm_num at hinv ⊢
          exact hinv
        exact (Nat.le_floor_iff
          (div_nonneg zero_le_one (G.weight_pos e).le)).2 hinv'
      have hT : 0 < T := lt_of_lt_of_le (by omega) hrle
      let a : Fin T := ⟨r - 1, by omega⟩
      have hsize : finiteClassSize a = r := by
        simp [finiteClassSize, a]
        omega
      let k : G.FloorResidualClassKey T := (G.floorKey e, a)
      have heCell : e ∈ G.floorResidualClassCell T k := by
        apply Finset.mem_filter.mpr
        exact ⟨he, rfl, by simpa [r, k, hsize]⟩
      have heCover : e ∈
          (D.cellPartition k).blocks.biUnion id ∪
            (D.cellPartition k).remainder := by
        rw [(D.cellPartition k).cover]
        exact heCell
      rcases Finset.mem_union.mp heCover with hfull | hrem
      · rcases Finset.mem_biUnion.mp hfull with ⟨A, hA, heA⟩
        apply Or.inl
        apply (D.mem_fullBlockEdges_iff e).2
        exact ⟨⟨k, ⟨A, hA⟩⟩, heA⟩
      · apply Or.inr
        apply Or.inl
        apply (D.mem_remainderEdges_iff e).2
        exact ⟨a, by simpa [k] using hrem⟩
  · intro he
    rcases he with hfull | hrem | htail
    · rcases (D.mem_fullBlockEdges_iff e).1 hfull with ⟨p, hep⟩
      exact (Finset.mem_filter.mp
        (D.fullBlockPacketEdges_subset_cell p hep)).1
    · rcases (D.mem_remainderEdges_iff e).1 hrem with ⟨a, hea⟩
      exact (Finset.mem_filter.mp
        ((D.cellPartition (G.floorKey e, a)).remainder_subset hea)).1
    · exact (Finset.mem_filter.mp htail).1

/-- Exact set-level three-way decomposition of the floor residual. -/
theorem fullBlockEdges_union_remainder_union_tinyTailEdges :
    D.fullBlockEdges ∪ D.remainderEdges ∪
        tinyTailEdges (G := G) (T := T) = G.floorResidualEdges := by
  ext e
  rw [Finset.mem_union, Finset.mem_union,
    D.mem_floorResidualEdges_iff_fullBlock_or_remainder_or_tinyTail]
  tauto

theorem mem_refinedFullOriginalEdges_iff (e : G.E) :
    e ∈ D.refinedFloorPacketization.originalEdgesOfPackets
        D.refinedFullPacketSet ↔
      G.IsFloorAssigned e ∨ e ∈ D.fullBlockEdges := by
  by_cases ha : G.IsFloorAssigned e <;>
    by_cases hb : e ∈ D.fullBlockEdges <;>
      simp [Packetization.originalEdgesOfPackets, refinedFloorPacketization,
        refinedFloorPacketOf, refinedFullPacketSet, ha, hb]

theorem refinedFullOriginalEdges_eq :
    D.refinedFloorPacketization.originalEdgesOfPackets
        D.refinedFullPacketSet =
      (Finset.univ \ G.floorResidualEdges) ∪ D.fullBlockEdges := by
  ext e
  rw [D.mem_refinedFullOriginalEdges_iff]
  simp [G.mem_floorResidualEdges_iff_not_floorAssigned]

theorem refinedResidualEdges_eq :
    Finset.univ \
        D.refinedFloorPacketization.originalEdgesOfPackets
          D.refinedFullPacketSet =
      G.floorResidualEdges \ D.fullBlockEdges := by
  ext e
  rw [Finset.mem_sdiff, D.mem_refinedFullOriginalEdges_iff]
  simp [G.mem_floorResidualEdges_iff_not_floorAssigned]

theorem fullBlockEdges_disjoint_remainderEdges :
    Disjoint D.fullBlockEdges D.remainderEdges := by
  rw [Finset.disjoint_left]
  intro e heF heR
  rcases (D.mem_fullBlockEdges_iff e).1 heF with ⟨p, hep⟩
  rcases (D.mem_remainderEdges_iff e).1 heR with ⟨a, hea⟩
  have hpair : p.1.1 = G.floorKey e :=
    (D.floorKey_eq_of_mem_fullBlockPacketEdges p hep).symm
  have hfloorP := D.floor_eq_classSize_of_mem_fullBlockPacketEdges p hep
  have heaCell := (D.cellPartition (G.floorKey e, a)).remainder_subset hea
  have hfloorA : Nat.floor (1 / G.weight e) = finiteClassSize a :=
    (Finset.mem_filter.mp heaCell).2.2
  have hclass : p.1.2 = a := by
    apply Fin.ext
    unfold finiteClassSize at hfloorP hfloorA
    omega
  have hkey : p.1 = (G.floorKey e, a) := Prod.ext hpair hclass
  rw [← hkey] at hea
  exact Finset.disjoint_left.mp
    ((D.cellPartition p.1).remainder_disjoint p.2.1 p.2.2).symm
      hea hep

theorem fullBlockEdges_disjoint_tinyTailEdges :
    Disjoint D.fullBlockEdges (tinyTailEdges (G := G) (T := T)) := by
  rw [Finset.disjoint_left]
  intro e heF heT
  rcases (D.mem_fullBlockEdges_iff e).1 heF with ⟨p, hep⟩
  have hfloor := D.floor_eq_classSize_of_mem_fullBlockPacketEdges p hep
  have htail := (Finset.mem_filter.mp heT).2
  have hsize : finiteClassSize p.1.2 ≤ T := by
    unfold finiteClassSize
    omega
  omega

theorem remainderEdges_disjoint_tinyTailEdges :
    Disjoint D.remainderEdges (tinyTailEdges (G := G) (T := T)) := by
  rw [Finset.disjoint_left]
  intro e heR heT
  rcases (D.mem_remainderEdges_iff e).1 heR with ⟨a, hea⟩
  have heaCell := (D.cellPartition (G.floorKey e, a)).remainder_subset hea
  have hfloor : Nat.floor (1 / G.weight e) = finiteClassSize a :=
    (Finset.mem_filter.mp heaCell).2.2
  have htail := (Finset.mem_filter.mp heT).2
  have hsize : finiteClassSize a ≤ T := by
    unfold finiteClassSize
    omega
  omega

/-- The complementary physical edges after the refined packet base are
exactly the bounded-multiplicity finite-class remainders and the uniformly
tiny tail. -/
theorem refinedResidualEdges_eq_remainder_union_tinyTail :
    Finset.univ \
        D.refinedFloorPacketization.originalEdgesOfPackets
          D.refinedFullPacketSet =
      D.remainderEdges ∪ tinyTailEdges (G := G) (T := T) := by
  rw [D.refinedResidualEdges_eq]
  ext e
  have hcover := D.mem_floorResidualEdges_iff_fullBlock_or_remainder_or_tinyTail e
  have hFR := Finset.disjoint_left.mp D.fullBlockEdges_disjoint_remainderEdges
  have hFT := Finset.disjoint_left.mp D.fullBlockEdges_disjoint_tinyTailEdges
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · intro he
    rcases hcover.mp he.1 with hF | hR | hT
    · exact (he.2 hF).elim
    · exact Or.inl hR
    · exact Or.inr hT
  · intro he
    rcases he with hR | hT
    · exact ⟨hcover.mpr (Or.inr (Or.inl hR)), fun hF ↦ hFR hF hR⟩
    · exact ⟨hcover.mpr (Or.inr (Or.inr hT)), fun hF ↦ hFT hF hT⟩

/-- Conditional ordinary coloring of the refined base at the sharp bound
available from its proved odd-set density.  The displayed `12n/5` leading
term records why this construction cannot by itself establish the target
`2n + o(n)` theorem.  Its residual is nevertheless exactly the bounded
finite-class remainder plus the uniformly tiny tail. -/
theorem exists_uniform_refinedFloorGeneralColoredPacketBase
    (hordinary : OrdinaryMultigraphNearFractionalColoring.{u})
    (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (n T : ℕ)
      (D : G.FloorResidualHarmonicDecomposition T),
      N ≤ n →
      (∀ v, G.starCharge harmonicCharge v ≤
        (8 / 5 : ℝ) * n + 3) →
      ∃ (K : ℕ) (C : G.GeneralColoredPacketBase K),
        (K : ℝ) ≤ (12 / 5 : ℝ) * n + 9 / 2 + η * n ∧
        C.residualEdges =
          D.remainderEdges ∪ tinyTailEdges (G := G) (T := T) := by
  obtain ⟨Nordinary, hN⟩ := hordinary 7 η (by norm_num) hη
  let N := max Nordinary 1
  refine ⟨N, ?_⟩
  intro G n T D hn hcharge
  have hnOrdinary : Nordinary ≤ n := (le_max_left _ _).trans hn
  have hnOne : 1 ≤ n := (le_max_right _ _).trans hn
  let L : ℝ := (12 / 5 : ℝ) * n + 9 / 2
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hLupper : L ≤ 7 * (n : ℝ) := by
    dsimp [L]
    have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hnOne
    nlinarith
  have hdegree : ∀ v,
      (D.refinedFloorPacketization.groupedGraph.degreeOn
        D.refinedFullPacketSet v : ℝ) ≤ L := by
    intro v
    calc
      (D.refinedFloorPacketization.groupedGraph.degreeOn
          D.refinedFullPacketSet v : ℝ) ≤
          G.starCharge harmonicCharge v :=
        D.refinedPacketDegree_le_starCharge v
      _ ≤ (8 / 5 : ℝ) * n + 3 := hcharge v
      _ ≤ L := by dsimp [L]; nlinarith
  have hodd :
      D.refinedFloorPacketization.groupedGraph.OddSetDensityAtMost
        D.refinedFullPacketSet L := by
    dsimp [L]
    exact D.refinedFloorPacketization_oddSetDensityAtMost_eightFifths
      n hcharge
  obtain ⟨K, hKpos, hKbound, color, hproper⟩ :=
    hN D.refinedFloorPacketization.groupedGraph
      D.refinedFullPacketSet n L hnOrdinary hL0 hLupper hdegree hodd
  let C : G.GeneralColoredPacketBase K := {
    packetization := D.refinedFloorPacketization
    fullPackets := D.refinedFullPacketSet
    palette_pos := hKpos
    packetColor := color
    packetProper := hproper }
  refine ⟨K, C, by simpa [L] using hKbound, ?_⟩
  simpa [C, GeneralColoredPacketBase.residualEdges] using
    D.refinedResidualEdges_eq_remainder_union_tinyTail

end FloorResidualHarmonicDecomposition

end

end WeightedMultigraph
end WeightedEdgeColoring
