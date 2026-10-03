import WeightedEdgeColoring.FiniteHarmonicPackets
import WeightedEdgeColoring.BPEdgeRestriction
import WeightedEdgeColoring.BPLocalCharge
import WeightedEdgeColoring.BoundedMultiplicitySimpleLayers

/-!
# Coloring finite harmonic packets

This file turns the exact finite-class packet decomposition into the
colored packet skeleton used in the harmonic argument.  The full packets
form a bipartite weighted multigraph.  Its degree at a vertex is exactly
the packet count from `FiniteHarmonicPackets`, so Kőnig's theorem colors it
with any palette at least that large.  Expanding a packet color back to its
physical edges preserves every load.

The final certificate keeps the short residual, its bounded parallel
multiplicity, and the exact palette-slack inequality.  Thus no rounding of
the residual is hidden in the packet step.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable {G : WeightedMultigraph.{u}} {T : ℕ}
  {b : G.Bipartition} {classOf : G.E → Fin T}

/-- Merge a feasible base coloring with a feasible residual coloring whose
first palette block uses only colors missing at both endpoints of the base.
The second palette block is fresh, so it needs no support condition.

This is the deterministic bookkeeping behind the finite harmonic-packet
reduction.  The substantive residual theorem may work directly in the
combined palette `Fin (q + r)`; only its use of the first `q` colors is
constrained. -/
theorem merge_feasibleOn_addFresh_of_commonMissing
    {q r : ℕ} (F R : Finset G.E) (hdisj : Disjoint F R)
    (base : G.E → Fin q) (residual : G.E → Fin (q + r))
    (hbase : G.IsFeasibleOn F base)
    (hresidual : G.IsFeasibleOn R residual)
    (hsupport : ∀ e ∈ R, ∀ c : Fin q,
      residual e = Fin.castAdd r c →
        c ∈ G.missingColorsAt F base (G.fst e) ∧
          c ∈ G.missingColorsAt F base (G.snd e)) :
    ∃ color : G.E → Fin (q + r),
      G.IsFeasibleOn (F ∪ R) color := by
  classical
  let color : G.E → Fin (q + r) := fun e ↦
    if e ∈ F then Fin.castAdd r (base e) else residual e
  refine ⟨color, ?_⟩
  intro v i
  refine Fin.addCases ?_ ?_ i
  · intro c
    have hload :
        G.colorLoadOn (F ∪ R) color v (Fin.castAdd r c) =
          G.colorLoadOn F base v c +
            G.colorLoadOn R residual v (Fin.castAdd r c) := by
      unfold colorLoadOn
      rw [Finset.sum_union hdisj]
      congr 1
      · apply Finset.sum_congr rfl
        intro e heF
        simp [color, heF]
      · apply Finset.sum_congr rfl
        intro e heR
        have heNF : e ∉ F := fun heF ↦
          Finset.disjoint_left.mp hdisj heF heR
        simp [color, heNF]
    rw [hload]
    by_cases hused : ∃ f ∈ F, G.Inc v f ∧ base f = c
    · have hRzero :
          G.colorLoadOn R residual v (Fin.castAdd r c) = 0 := by
        unfold colorLoadOn
        apply Finset.sum_eq_zero
        intro e heR
        by_cases heInc : G.Inc v e
        · have hne : residual e ≠ Fin.castAdd r c := by
            intro heColor
            have hcommon := hsupport e heR c heColor
            have heMissing : c ∈ G.missingColorsAt F base v := by
              rcases heInc with hfst | hsnd
              · simpa [hfst] using hcommon.1
              · simpa [hsnd] using hcommon.2
            obtain ⟨f, hfF, hfInc, hfColor⟩ := hused
            have hnot := G.not_mem_missingColorsAt_of_used
              (base := base) hfF hfInc
            exact hnot (by simpa [hfColor] using heMissing)
          simp [heInc, hne]
        · simp [heInc]
      rw [hRzero, add_zero]
      exact hbase v c
    · have hFzero : G.colorLoadOn F base v c = 0 := by
        unfold colorLoadOn
        apply Finset.sum_eq_zero
        intro e heF
        by_cases heInc : G.Inc v e
        · have hne : base e ≠ c := by
            intro heColor
            exact hused ⟨e, heF, heInc, heColor⟩
          simp [heInc, hne]
        · simp [heInc]
      rw [hFzero, zero_add]
      exact hresidual v (Fin.castAdd r c)
  · intro c
    have hload :
        G.colorLoadOn (F ∪ R) color v (Fin.natAdd q c) =
          G.colorLoadOn R residual v (Fin.natAdd q c) := by
      unfold colorLoadOn
      rw [Finset.sum_union hdisj]
      have hFzero :
          (∑ e ∈ F,
            if G.Inc v e ∧ color e = Fin.natAdd q c
            then G.weight e else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro e heF
        have hne : Fin.castAdd r (base e) ≠ Fin.natAdd q c := by
          intro h
          have hval := congrArg Fin.val h
          simp at hval
          omega
        simp [color, heF, hne]
      rw [hFzero, zero_add]
      apply Finset.sum_congr rfl
      intro e heR
      have heNF : e ∉ F := fun heF ↦
        Finset.disjoint_left.mp hdisj heF heR
      simp [color, heNF]
    rw [hload]
    exact hresidual v (Fin.natAdd q c)

namespace FiniteClassPacketDecomposition

variable (D : G.FiniteClassPacketDecomposition b classOf)

/-- The physical edges covered by full packets. -/
def fullEdges : Finset G.E := Finset.univ \ D.residualEdges

@[simp] theorem mem_fullEdges_iff (e : G.E) :
    e ∈ D.fullEdges ↔ e ∉ D.residualEdges := by
  simp [fullEdges]

/-- Full packets are pairwise disjoint. -/
theorem packet_eq_of_mem_both (p q : D.Packet) {e : G.E}
    (hep : e ∈ D.packetEdges p) (heq : e ∈ D.packetEdges q) :
    p = q := by
  classical
  have hkey : p.1 = q.1 :=
    (D.key_eq_of_mem_packetEdges p hep).symm.trans
      (D.key_eq_of_mem_packetEdges q heq)
  cases p with
  | mk kp Ap =>
      cases q with
      | mk kq Aq =>
          dsimp at hkey
          subst kq
          have hA : Ap = Aq := by
            apply Subtype.ext
            by_contra hne
            have hd := (D.cellPartition kp).blocks_disjoint
              Ap.1 Ap.2 Aq.1 Aq.2 hne
            exact Finset.disjoint_left.mp hd hep heq
          cases hA
          rfl

/-- Every full physical edge belongs to a unique packet. -/
theorem existsUnique_packet_of_mem_fullEdges {e : G.E}
    (he : e ∈ D.fullEdges) :
    ∃! p : D.Packet, e ∈ D.packetEdges p := by
  have heNot : e ∉ D.residualEdges := (D.mem_fullEdges_iff e).mp he
  rcases D.mem_residualEdges_or_exists_packet e with heR | ⟨p, hp⟩
  · exact (heNot heR).elim
  · refine ⟨p, hp, ?_⟩
    intro q hq
    exact D.packet_eq_of_mem_both q p hq hp

/-- The unique full packet containing an edge of the full-edge restriction. -/
def packetOfFullEdge (e : (G.edgeRestriction D.fullEdges).E) : D.Packet :=
  Classical.choose (D.existsUnique_packet_of_mem_fullEdges e.property)

theorem packetOfFullEdge_mem (e : (G.edgeRestriction D.fullEdges).E) :
    e.1 ∈ D.packetEdges (D.packetOfFullEdge e) :=
  (Classical.choose_spec
    (D.existsUnique_packet_of_mem_fullEdges e.property)).1

theorem packetOfFullEdge_eq_iff
    (e : (G.edgeRestriction D.fullEdges).E) (p : D.Packet) :
    D.packetOfFullEdge e = p ↔ e.1 ∈ D.packetEdges p := by
  constructor
  · intro h
    rw [← h]
    exact D.packetOfFullEdge_mem e
  · intro h
    exact ((Classical.choose_spec
      (D.existsUnique_packet_of_mem_fullEdges e.property)).2 p h).symm

theorem packetEdges_subset_fullEdges (p : D.Packet) :
    D.packetEdges p ⊆ D.fullEdges := by
  intro e he
  apply (D.mem_fullEdges_iff e).mpr
  intro heR
  exact Finset.disjoint_left.mp
    (D.residualEdges_disjoint_packetEdges p) heR he

/-- The full packets, viewed as a packetization of the full-edge
restriction. -/
def fullPacketization (hpacket : ∀ p : D.Packet, D.packetWeight p ≤ 1) :
    (G.edgeRestriction D.fullEdges).BipartitePacketization
      (Bipartition.edgeRestriction G b D.fullEdges) where
  Packet := D.Packet
  instFintypePacket := inferInstance
  instDecidableEqPacket := inferInstance
  packetOf := D.packetOfFullEdge
  tail := D.packetTail
  head := D.packetHead
  endpoints := by
    intro e
    change b.leftEndpoint e.1 = D.packetTail (D.packetOfFullEdge e) ∧
      b.rightEndpoint e.1 = D.packetHead (D.packetOfFullEdge e)
    exact D.endpoints_eq_of_mem_packetEdges (D.packetOfFullEdge e)
      (D.packetOfFullEdge_mem e)
  onto := by
    intro p
    obtain ⟨e, he⟩ := D.packetEdges_nonempty p
    let eFull : (G.edgeRestriction D.fullEdges).E :=
      ⟨e, D.packetEdges_subset_fullEdges p he⟩
    refine ⟨eFull, ?_⟩
    exact (D.packetOfFullEdge_eq_iff eFull p).2 he
  weight_le_one := by
    intro p
    have hsum :
        (∑ e : (G.edgeRestriction D.fullEdges).E,
          if D.packetOfFullEdge e = p then G.weight e.1 else 0) =
          D.packetWeight p := by
      change
        (∑ e : (G.edgeRestriction D.fullEdges).E,
          if D.packetOfFullEdge e = p then G.weight e.1 else 0) =
        ∑ e ∈ D.packetEdges p, G.weight e
      calc
        (∑ e : (G.edgeRestriction D.fullEdges).E,
            if D.packetOfFullEdge e = p then G.weight e.1 else 0) =
            ∑ e ∈ (Finset.univ :
              Finset (G.edgeRestriction D.fullEdges).E).filter
                (fun e ↦ D.packetOfFullEdge e = p), G.weight e.1 := by
              rw [Finset.sum_filter]
        _ = ∑ e ∈ D.packetEdges p, G.weight e := by
          apply Finset.sum_bij (fun e _ ↦ e.1)
          · intro e he
            have hp := (Finset.mem_filter.mp he).2
            exact (D.packetOfFullEdge_eq_iff e p).1 hp
          · intro e₁ he₁ e₂ he₂ h
            exact Subtype.ext h
          · intro e he
            let eFull : (G.edgeRestriction D.fullEdges).E :=
              ⟨e, D.packetEdges_subset_fullEdges p he⟩
            refine ⟨eFull, ?_, rfl⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              (D.packetOfFullEdge_eq_iff eFull p).2 he⟩
          · intro e he
            rfl
    rw [hsum]
    exact hpacket p

/-- Incidence in the grouped full-packet graph is the incidence predicate
read from the packet's cell key. -/
theorem fullPacketization_groupedGraph_inc
    (hpacket : ∀ p : D.Packet, D.packetWeight p ≤ 1)
    (v : G.V) (p : D.Packet) :
    (D.fullPacketization hpacket).groupedGraph.Inc v p ↔
      Bipartition.finiteClassKeyInc v p.1 := by
  rfl

/-- The ordinary degree of the packet graph is exactly the number of full
packets recorded by the decomposition. -/
theorem fullPacketization_groupedGraph_degree
    (hpacket : ∀ p : D.Packet, D.packetWeight p ≤ 1)
    (v : G.V) :
    (D.fullPacketization hpacket).groupedGraph.degreeOn Finset.univ v =
      D.packetDegreeAt v := by
  classical
  let S : Finset D.Packet := Finset.univ.filter fun p ↦
    (D.fullPacketization hpacket).groupedGraph.Inc v p
  have hmaps : (S : Set D.Packet).MapsTo Sigma.fst
      (Finset.univ : Finset (FiniteClassKey G T)) := by
    intro p hp
    simp
  change S.card = _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  unfold packetDegreeAt
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hinc : Bipartition.finiteClassKeyInc v k
  · rw [if_pos hinc]
    change
      (S.filter fun p ↦ p.1 = k).card =
        (D.cellPartition k).blocks.card
    let embed : {A // A ∈ (D.cellPartition k).blocks} → D.Packet :=
      fun A ↦ ⟨k, A⟩
    apply Finset.card_bij (fun p _hp ↦ p.2)
    · intro p hp
      have hpk : p.1 = k := (Finset.mem_filter.mp hp).2
      subst k
      exact p.2.2
    · intro p₁ hp₁ p₂ hp₂ h
      have hk₁ : p₁.1 = k := (Finset.mem_filter.mp hp₁).2
      have hk₂ : p₂.1 = k := (Finset.mem_filter.mp hp₂).2
      rcases p₁ with ⟨k₁, A₁⟩
      rcases p₂ with ⟨k₂, A₂⟩
      dsimp at hk₁ hk₂ h
      subst k₁
      subst k₂
      have hA : A₁ = A₂ := Subtype.ext h
      subst A₂
      rfl
    · intro A hA
      let p : D.Packet := ⟨k, ⟨A, hA⟩⟩
      refine ⟨p, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by
        rw [D.fullPacketization_groupedGraph_inc]
        exact hinc⟩
  · rw [if_neg hinc]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro p hpS hpk
    have hpinc : Bipartition.finiteClassKeyInc v p.1 := by
      have := (Finset.mem_filter.mp hpS).2
      rwa [D.fullPacketization_groupedGraph_inc] at this
    exact hinc (hpk ▸ hpinc)

/-- König colors all full packets once their packet degree is bounded by
the palette size. -/
theorem exists_fullPacket_properColoring
    (hpacket : ∀ p : D.Packet, D.packetWeight p ≤ 1)
    (K : ℕ) (hK : 0 < K)
    (hdegree : ∀ v, D.packetDegreeAt v ≤ K) :
    ∃ color : D.Packet → Fin K,
      (D.fullPacketization hpacket).groupedGraph.IsProperOn
        Finset.univ color := by
  let P := D.fullPacketization hpacket
  apply P.groupedGraph.exists_isProperOn_bipartite_of_degreeOn_le
    P.groupedBipartition Finset.univ K hK
  intro v
  rw [D.fullPacketization_groupedGraph_degree hpacket v]
  exact hdegree v

/-- Expand a packet color to the physical full edges and use color zero as
an irrelevant fallback on the residual. -/
def expandedFullColor
    (hpacket : ∀ p : D.Packet, D.packetWeight p ≤ 1)
    {K : ℕ} (hK : 0 < K) (color : D.Packet → Fin K) :
    G.E → Fin K :=
  G.liftRestrictedColor hK D.fullEdges
    ((D.fullPacketization hpacket).expandColor color)

/-- A proper packet coloring expands to a feasible coloring of all physical
edges in full packets. -/
theorem expandedFullColor_feasibleOn
    (hpacket : ∀ p : D.Packet, D.packetWeight p ≤ 1)
    {K : ℕ} (hK : 0 < K) (color : D.Packet → Fin K)
    (hproper :
      (D.fullPacketization hpacket).groupedGraph.IsProperOn
        Finset.univ color) :
    G.IsFeasibleOn D.fullEdges
      (D.expandedFullColor hpacket hK color) := by
  let P := D.fullPacketization hpacket
  have hpacketFeasible : P.groupedGraph.IsFeasibleOn Finset.univ color :=
    P.groupedGraph.isFeasibleOn_of_isProperOn Finset.univ color hproper
  have hpacketWeighted : P.groupedGraph.IsWeightedColoring color :=
    (P.groupedGraph.isWeightedColoring_iff_feasibleOn_univ color).2
      hpacketFeasible
  have hfullWeighted :
      (G.edgeRestriction D.fullEdges).IsWeightedColoring
        (P.expandColor color) :=
    P.isWeightedColoring_expandColor color hpacketWeighted
  exact G.feasibleOn_liftRestrictedColor hK D.fullEdges
    (P.expandColor color) hfullWeighted

/-- The colors unused at a physical vertex by the expanded full packets are
exactly the colors missing at that vertex in the packet graph. -/
theorem missingColorsAt_expandedFullColor
    (hpacket : ∀ p : D.Packet, D.packetWeight p ≤ 1)
    {K : ℕ} (hK : 0 < K) (color : D.Packet → Fin K)
    (v : G.V) :
    G.missingColorsAt D.fullEdges
        (D.expandedFullColor hpacket hK color) v =
      (D.fullPacketization hpacket).groupedGraph.missingColorsAt
        Finset.univ color v := by
  classical
  let P := D.fullPacketization hpacket
  unfold missingColorsAt
  congr 1
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨e, he, hei⟩
    have heF : e ∈ D.fullEdges := (Finset.mem_filter.mp he).1
    let eF : (G.edgeRestriction D.fullEdges).E := ⟨e, heF⟩
    have heInc : G.Inc v e := (Finset.mem_filter.mp he).2
    have hpInc : P.groupedGraph.Inc v (D.packetOfFullEdge eF) :=
      (P.groupedGraph_inc_packetOf v eF).2 heInc
    apply Finset.mem_image.mpr
    refine ⟨D.packetOfFullEdge eF, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpInc⟩
    · rw [← hei]
      simp only [expandedFullColor,
        WeightedMultigraph.liftRestrictedColor, dif_pos heF,
        BipartitePacketization.expandColor]
      apply congrArg color
      apply congrArg D.packetOfFullEdge
      apply Subtype.ext
      rfl
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨p, hp, hpi⟩
    have hpInc : P.groupedGraph.Inc v p := (Finset.mem_filter.mp hp).2
    obtain ⟨eF, hePacket⟩ := P.onto p
    have heInc : G.Inc v eF.1 := by
      apply (P.groupedGraph_inc_packetOf v eF).1
      simpa [hePacket] using hpInc
    apply Finset.mem_image.mpr
    refine ⟨eF.1, Finset.mem_filter.mpr ⟨eF.property, heInc⟩, ?_⟩
    rw [← hpi, ← hePacket]
    simp [expandedFullColor, WeightedMultigraph.liftRestrictedColor,
      eF.property, P, BipartitePacketization.expandColor]

end FiniteClassPacketDecomposition

/-! ## The colored packet certificate -/

/-- A finite harmonic packet decomposition together with a proper coloring
of its full-packet graph.  All physical and residual conclusions are derived
below, so the certificate stores no redundant claims. -/
structure FiniteHarmonicPacketColoringCertificate
    (b : G.Bipartition) (classOf : G.E → Fin T) (K : ℕ) where
  decomposition : G.FiniteClassPacketDecomposition b classOf
  packetWeight_le :
    ∀ p : decomposition.Packet, decomposition.packetWeight p ≤ 1
  packetColor : decomposition.Packet → Fin K
  packetProper :
    (decomposition.fullPacketization packetWeight_le).groupedGraph.IsProperOn
      Finset.univ packetColor

namespace FiniteHarmonicPacketColoringCertificate

variable {K : ℕ}
  (C : G.FiniteHarmonicPacketColoringCertificate b classOf K)

/-- The full physical edges of a colored packet certificate. -/
abbrev fullEdges : Finset G.E := C.decomposition.fullEdges

/-- The short residual edges of a colored packet certificate. -/
abbrev residualEdges : Finset G.E := C.decomposition.residualEdges

/-- The residual weighted multigraph, retaining the original edge indices as
subtypes. -/
abbrev residualGraph : WeightedMultigraph.{u} :=
  G.edgeRestriction C.residualEdges

/-- The residual graph inherits the original bipartition. -/
def residualBipartition : C.residualGraph.Bipartition :=
  Bipartition.edgeRestriction G b C.residualEdges

/-- Expand the packet coloring to the physical full edges. -/
def baseColor (hK : 0 < K) : G.E → Fin K :=
  C.decomposition.expandedFullColor C.packetWeight_le hK C.packetColor

theorem baseColor_feasibleOn (hK : 0 < K) :
    G.IsFeasibleOn C.fullEdges (C.baseColor hK) :=
  C.decomposition.expandedFullColor_feasibleOn C.packetWeight_le hK
    C.packetColor C.packetProper

theorem fullEdges_union_residualEdges :
    C.fullEdges ∪ C.residualEdges = Finset.univ := by
  classical
  exact Finset.sdiff_union_of_subset (Finset.subset_univ _)

theorem fullEdges_disjoint_residualEdges :
    Disjoint C.fullEdges C.residualEdges := by
  classical
  exact Finset.sdiff_disjoint

/-- The certificate's physical missing palette has exact cardinality equal
to the palette size minus the packet degree. -/
theorem card_missingColorsAt_baseColor
    (hK : 0 < K) (v : G.V) :
    (G.missingColorsAt C.fullEdges (C.baseColor hK) v).card =
      K - C.decomposition.packetDegreeAt v := by
  change
    (G.missingColorsAt C.decomposition.fullEdges
      (C.decomposition.expandedFullColor C.packetWeight_le hK
        C.packetColor) v).card =
      K - C.decomposition.packetDegreeAt v
  rw [C.decomposition.missingColorsAt_expandedFullColor
    C.packetWeight_le hK C.packetColor v]
  rw [(C.decomposition.fullPacketization C.packetWeight_le).groupedGraph.card_missingColorsAt
    Finset.univ C.packetColor C.packetProper v]
  rw [C.decomposition.fullPacketization_groupedGraph_degree
    C.packetWeight_le v]

/-- The residual has the finite-class parallel-multiplicity bound given by
the sum of r minus one over the retained classes. -/
theorem residual_pair_multiplicity_le (u v : G.V) :
    (C.residualEdges.filter fun e ↦
      b.leftEndpoint e = u ∧ b.rightEndpoint e = v).card ≤
      ∑ a : Fin T, a.1 :=
  C.decomposition.residual_pair_multiplicity_le u v

/-- The residual edge restriction is bipartite, with the inherited shores. -/
theorem residualGraph_isBipartite : C.residualGraph.IsBipartite :=
  ⟨C.residualBipartition⟩

/-- Every local packing of the original graph restricts to the residual
graph.  This is the local-bin hypothesis needed by residual coloring
theorems. -/
theorem residualGraph_locallyPacksInto {n : ℕ}
    (hpack : G.LocallyPacksInto n) :
    C.residualGraph.LocallyPacksInto n :=
  G.edgeRestriction_locallyPacksInto C.residualEdges hpack

/-- Restriction to the residual cannot increase star weight. -/
theorem residualGraph_starWeight_le_original (v : G.V) :
    C.residualGraph.starWeight v ≤ G.starWeight v := by
  rw [G.edgeRestriction_starWeight C.residualEdges v,
    G.starWeight_eq_inc_sum v]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro e _he _heNot
  split
  · exact G.weight_nonneg e
  · exact le_rfl

/-- Hence an external star-weight scale for `G` is also valid for its
residual restriction. -/
theorem residualGraph_starWeight_le {n : ℕ}
    (hstar : ∀ v, G.starWeight v ≤ n) (v : G.V) :
    C.residualGraph.starWeight v ≤ n :=
  (C.residualGraph_starWeight_le_original v).trans (hstar v)

/-- Harmonic star charge in the residual edge restriction is exactly the
residual charge sum in the original graph. -/
theorem residualGraph_starCharge_eq (v : G.V) :
    C.residualGraph.starCharge harmonicCharge v =
      ∑ e ∈ C.residualEdges,
        if G.Inc v e then harmonicCharge (G.weight e) else 0 := by
  classical
  unfold starCharge
  change
    (∑ e : {e : (G.edgeRestriction C.residualEdges).E // G.Inc v e.1},
      harmonicCharge (G.weight e.1.1)) = _
  calc
    _ = ∑ e ∈ (Finset.univ :
          Finset (G.edgeRestriction C.residualEdges).E).filter
            (fun e ↦ G.Inc v e.1),
          harmonicCharge (G.weight e.1) := by
      symm
      exact Finset.sum_subtype
        (p := fun e : (G.edgeRestriction C.residualEdges).E ↦
          G.Inc v e.1)
        ((Finset.univ : Finset (G.edgeRestriction C.residualEdges).E).filter
          (fun e ↦ G.Inc v e.1)) (by simp)
        (fun e ↦ harmonicCharge (G.weight e.1))
    _ = ∑ e : (G.edgeRestriction C.residualEdges).E,
        if G.Inc v e.1 then harmonicCharge (G.weight e.1) else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ e ∈ C.residualEdges,
        if G.Inc v e then harmonicCharge (G.weight e) else 0 := by
      symm
      exact Finset.sum_subtype
        (p := fun e : G.E ↦ e ∈ C.residualEdges)
        C.residualEdges (by simp)
        (fun e ↦ if G.Inc v e then harmonicCharge (G.weight e) else 0)

/-- The bounded parallel multiplicity, stated directly on the residual
edge-restriction graph. -/
theorem residualGraph_pair_multiplicity_le (u v : G.V) :
    ((Finset.univ : Finset C.residualGraph.E).filter fun e ↦
      C.residualBipartition.leftEndpoint e = u ∧
        C.residualBipartition.rightEndpoint e = v).card ≤
      ∑ a : Fin T, a.1 := by
  let embed : C.residualGraph.E ↪ G.E :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let F : Finset C.residualGraph.E :=
    Finset.univ.filter fun e ↦
      C.residualBipartition.leftEndpoint e = u ∧
        C.residualBipartition.rightEndpoint e = v
  have hmap : F.map embed =
      C.residualEdges.filter fun e ↦
        b.leftEndpoint e = u ∧ b.rightEndpoint e = v := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_map.mp he with ⟨eR, heRF, heRe⟩
      change eR.1 = e at heRe
      subst e
      have hend := (Finset.mem_filter.mp heRF).2
      change b.leftEndpoint eR.1 = u ∧ b.rightEndpoint eR.1 = v at hend
      exact Finset.mem_filter.mpr ⟨eR.property, hend⟩
    · intro he
      have he' := Finset.mem_filter.mp he
      let eR : C.residualGraph.E := ⟨e, he'.1⟩
      apply Finset.mem_map.mpr
      refine ⟨eR, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change b.leftEndpoint e = u ∧ b.rightEndpoint e = v
      exact he'.2
  change F.card ≤ _
  have hcard : F.card =
      (C.residualEdges.filter fun e ↦
        b.leftEndpoint e = u ∧ b.rightEndpoint e = v).card := by
    calc
      F.card = (F.map embed).card := (Finset.card_map embed).symm
      _ = _ := congrArg Finset.card hmap
  rw [hcard]
  exact C.residual_pair_multiplicity_le u v

/-- The canonical decomposition of the bounded-multiplicity residual into
simple bipartite layers. -/
abbrev residualSimpleLayering :
    C.residualGraph.BoundedPairSimpleLayering C.residualBipartition
      (∑ a : Fin T, a.1) :=
  C.decomposition.residualSimpleLayering

/-- The exact packet-degree plus residual-charge identity. -/
theorem packetDegree_add_residualHarmonicChargeAt
    (hcharge : ∀ e, harmonicCharge (G.weight e) =
      (1 : ℝ) / finiteClassSize (classOf e))
    (v : G.V) :
    (C.decomposition.packetDegreeAt v : ℝ) +
        (∑ e ∈ C.residualEdges,
          if G.Inc v e then harmonicCharge (G.weight e) else 0) =
      ∑ e : G.E,
        if G.Inc v e then harmonicCharge (G.weight e) else 0 :=
  C.decomposition.packetDegree_add_residualHarmonicChargeAt hcharge v

/-- The exact missing-color slack used by support-preserving residual
rounding.  No additive loss occurs in packetization: every unit of palette
above the original charge bound remains as residual slack. -/
theorem residualHarmonicCharge_add_margin_le_missingColors
    (hK : 0 < K)
    (hcharge : ∀ e, harmonicCharge (G.weight e) =
      (1 : ℝ) / finiteClassSize (classOf e))
    (A margin : ℝ) (hmargin : 0 ≤ margin)
    (hpalette : A + margin ≤ (K : ℝ))
    (horiginal : ∀ v,
      (∑ e : G.E,
        if G.Inc v e then harmonicCharge (G.weight e) else 0) ≤ A)
    (v : G.V) :
    margin +
        (∑ e ∈ C.residualEdges,
          if G.Inc v e then harmonicCharge (G.weight e) else 0) ≤
      ((G.missingColorsAt C.fullEdges (C.baseColor hK) v).card : ℝ) := by
  let d : ℕ := C.decomposition.packetDegreeAt v
  let Q : ℝ := ∑ e ∈ C.residualEdges,
    if G.Inc v e then harmonicCharge (G.weight e) else 0
  let O : ℝ := ∑ e : G.E,
    if G.Inc v e then harmonicCharge (G.weight e) else 0
  have hQ : 0 ≤ Q := by
    unfold Q
    apply Finset.sum_nonneg
    intro e _he
    split
    · exact harmonicCharge_nonneg _
    · exact le_rfl
  have haccount : (d : ℝ) + Q = O := by
    simpa [d, Q, O] using
      C.packetDegree_add_residualHarmonicChargeAt hcharge v
  have hO : O ≤ A := by simpa [O] using horiginal v
  have hAleK : A ≤ (K : ℝ) := by linarith
  have hdReal : (d : ℝ) ≤ (K : ℝ) := by linarith
  have hd : d ≤ K := by exact_mod_cast hdReal
  have hcard :
      ((G.missingColorsAt C.fullEdges (C.baseColor hK) v).card : ℝ) =
        (K : ℝ) - (d : ℝ) := by
    rw [C.card_missingColorsAt_baseColor hK v, Nat.cast_sub hd]
  change margin + Q ≤ _
  rw [hcard]
  linarith

/-- The exact slack inequality, rewritten in the native star-charge language
of the residual graph.  Its hypotheses now line up with
`BipartiteHarmonicChargeColoring`. -/
theorem residualGraph_starCharge_add_margin_le_missingColors
    (hK : 0 < K)
    (hcharge : ∀ e, harmonicCharge (G.weight e) =
      (1 : ℝ) / finiteClassSize (classOf e))
    (A margin : ℝ) (hmargin : 0 ≤ margin)
    (hpalette : A + margin ≤ (K : ℝ))
    (horiginal : ∀ v,
      G.starCharge harmonicCharge v ≤ A)
    (v : G.V) :
    margin + C.residualGraph.starCharge harmonicCharge v ≤
      ((G.missingColorsAt C.fullEdges (C.baseColor hK) v).card : ℝ) := by
  rw [C.residualGraph_starCharge_eq v]
  apply C.residualHarmonicCharge_add_margin_le_missingColors
    hK hcharge A margin hmargin hpalette
  intro w
  calc
    (∑ e : G.E,
        if G.Inc w e then harmonicCharge (G.weight e) else 0) =
        ∑ e ∈ (Finset.univ : Finset G.E).filter (G.Inc w),
          harmonicCharge (G.weight e) := by
      rw [Finset.sum_filter]
    _ = ∑ e : G.StarEdge w, harmonicCharge (G.weight e.1) := by
      exact Finset.sum_subtype
        ((Finset.univ : Finset G.E).filter (G.Inc w)) (by simp)
        (fun e ↦ harmonicCharge (G.weight e))
    _ = G.starCharge harmonicCharge w := rfl
    _ ≤ A := horiginal w

/-- A residual coloring is support-preserving when every color in the
packet palette is missing from the packet base at both endpoints.  Colors
in the final `fresh` positions have no support condition. -/
def HasSupportPreservingResidualColoring
    (hK : 0 < K) (fresh : ℕ) : Prop :=
  ∃ residualColor : C.residualGraph.E → Fin (K + fresh),
    C.residualGraph.IsWeightedColoring residualColor ∧
      ∀ e (c : Fin K), residualColor e = Fin.castAdd fresh c →
        c ∈ G.missingColorsAt C.fullEdges (C.baseColor hK) (G.fst e.1) ∧
          c ∈ G.missingColorsAt C.fullEdges (C.baseColor hK) (G.snd e.1)

/-- Conditional completion of the finite harmonic-packet certificate.

The only residual input is a support-preserving coloring of the canonical
bounded-multiplicity residual in the packet palette plus `fresh` new colors.
All restriction, lifting, support compatibility, and palette merging are
handled here. -/
theorem hasWeightedColoring_add_fresh_of_supportPreservingResidual
    (hK : 0 < K) (fresh : ℕ)
    (hresidual : C.HasSupportPreservingResidualColoring hK fresh) :
    G.HasWeightedColoring (K + fresh) := by
  classical
  rcases hresidual with ⟨residualColor, hcolor, hsupport⟩
  have htotal : 0 < K + fresh := by omega
  let lifted : G.E → Fin (K + fresh) :=
    G.liftRestrictedColor htotal C.residualEdges residualColor
  have hlifted : G.IsFeasibleOn C.residualEdges lifted := by
    exact G.feasibleOn_liftRestrictedColor htotal C.residualEdges
      residualColor hcolor
  have hliftedSupport : ∀ e ∈ C.residualEdges, ∀ c : Fin K,
      lifted e = Fin.castAdd fresh c →
        c ∈ G.missingColorsAt C.fullEdges (C.baseColor hK) (G.fst e) ∧
          c ∈ G.missingColorsAt C.fullEdges (C.baseColor hK) (G.snd e) := by
    intro e heR c heColor
    let eR : C.residualGraph.E := ⟨e, heR⟩
    have heColor' : residualColor eR = Fin.castAdd fresh c := by
      simpa [lifted, WeightedMultigraph.liftRestrictedColor, heR, eR]
        using heColor
    exact hsupport eR c heColor'
  obtain ⟨merged, hmerged⟩ :=
    G.merge_feasibleOn_addFresh_of_commonMissing
      C.fullEdges C.residualEdges C.fullEdges_disjoint_residualEdges
      (C.baseColor hK) lifted (C.baseColor_feasibleOn hK) hlifted
      hliftedSupport
  refine ⟨merged, (G.isWeightedColoring_iff_feasibleOn_univ merged).2 ?_⟩
  rw [← C.fullEdges_union_residualEdges]
  exact hmerged

/-- Numerical form of the same conditional completion, ready for the final
asymptotic estimate once `fresh = o(n)` is supplied. -/
theorem chiW_cast_le_add_fresh_of_supportPreservingResidual
    (hK : 0 < K) (fresh : ℕ)
    (hresidual : C.HasSupportPreservingResidualColoring hK fresh) :
    (G.chiW : ℝ) ≤ (K : ℝ) + fresh := by
  have h := G.chiW_le_of_hasWeightedColoring
    (C.hasWeightedColoring_add_fresh_of_supportPreservingResidual
      hK fresh hresidual)
  exact_mod_cast h

end FiniteHarmonicPacketColoringCertificate

/-- Construct the colored packet certificate.  The palette assumption is
used only to dominate the packet degree; König then supplies the coloring. -/
theorem exists_finiteHarmonicPacketColoringCertificate
    (b : G.Bipartition) (classOf : G.E → Fin T)
    (hweight : ∀ e, G.weight e ≤
      (1 : ℝ) / finiteClassSize (classOf e))
    (hcharge : ∀ e, harmonicCharge (G.weight e) =
      (1 : ℝ) / finiteClassSize (classOf e))
    (K : ℕ) (hK : 0 < K) (A margin : ℝ) (hmargin : 0 ≤ margin)
    (hpalette : A + margin ≤ (K : ℝ))
    (horiginal : ∀ v,
      (∑ e : G.E,
        if G.Inc v e then harmonicCharge (G.weight e) else 0) ≤ A) :
    Nonempty (G.FiniteHarmonicPacketColoringCertificate b classOf K) := by
  classical
  obtain ⟨D, hpacket, haccount, _hmult⟩ :=
    G.exists_finiteHarmonicPacketDecomposition b classOf hweight hcharge
  have hdegree : ∀ v, D.packetDegreeAt v ≤ K := by
    intro v
    let Q : ℝ := ∑ e ∈ D.residualEdges,
      if G.Inc v e then harmonicCharge (G.weight e) else 0
    have hQ : 0 ≤ Q := by
      unfold Q
      apply Finset.sum_nonneg
      intro e _he
      split
      · exact harmonicCharge_nonneg _
      · exact le_rfl
    have hacc :
        (D.packetDegreeAt v : ℝ) + Q =
          ∑ e : G.E,
            if G.Inc v e then harmonicCharge (G.weight e) else 0 := by
      simpa [Q] using haccount v
    have hAleK : A ≤ (K : ℝ) := by linarith
    have hdReal : (D.packetDegreeAt v : ℝ) ≤ (K : ℝ) := by
      have := horiginal v
      linarith
    exact_mod_cast hdReal
  obtain ⟨color, hproper⟩ :=
    D.exists_fullPacket_properColoring hpacket K hK hdegree
  exact ⟨{
    decomposition := D
    packetWeight_le := hpacket
    packetColor := color
    packetProper := hproper }⟩

end

end WeightedMultigraph
end WeightedEdgeColoring
