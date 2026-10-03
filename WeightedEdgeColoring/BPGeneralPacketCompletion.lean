import WeightedEdgeColoring.BPGeneralPacketBase
import WeightedEdgeColoring.PartialCompletion

/-!
# Completing a colored general packet base

This file contains only palette bookkeeping.  It packages a proper coloring
of selected packet edges, defines the complementary physical residual, and
merges any support-preserving residual coloring into one coloring of the
original multigraph.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

/-- Merge a feasible base coloring with a residual coloring in the base
palette plus a fresh block.  A residual edge may use an old color only when
that color is missing from the base at both endpoints. -/
theorem merge_feasibleOn_addFresh_of_commonMissing_general
    (G : WeightedMultigraph.{u}) {q r : ℕ}
    (F R : Finset G.E) (hdisj : Disjoint F R)
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

/-- A proper coloring of a chosen family of packets. -/
structure GeneralColoredPacketBase (G : WeightedMultigraph.{u}) (K : ℕ) where
  packetization : G.Packetization
  fullPackets : Finset packetization.Packet
  palette_pos : 0 < K
  packetColor : packetization.Packet → Fin K
  packetProper :
    packetization.groupedGraph.IsProperOn fullPackets packetColor

namespace GeneralColoredPacketBase

variable {G : WeightedMultigraph.{u}} {K : ℕ}
  (C : G.GeneralColoredPacketBase K)

abbrev fullEdges : Finset G.E :=
  C.packetization.originalEdgesOfPackets C.fullPackets

abbrev residualEdges : Finset G.E := Finset.univ \ C.fullEdges

abbrev residualGraph : WeightedMultigraph.{u} :=
  G.edgeRestriction C.residualEdges

abbrev baseColor : G.E → Fin K :=
  C.packetization.expandColor C.packetColor

theorem baseColor_feasibleOn : G.IsFeasibleOn C.fullEdges C.baseColor := by
  apply C.packetization.isFeasibleOn_originalEdgesOfPackets
    C.fullPackets C.packetColor
  exact C.packetization.groupedGraph.isFeasibleOn_of_isProperOn
    C.fullPackets C.packetColor C.packetProper

theorem fullEdges_disjoint_residualEdges :
    Disjoint C.fullEdges C.residualEdges := by
  rw [Finset.disjoint_left]
  intro e heF heR
  exact (Finset.mem_sdiff.mp heR).2 heF

theorem fullEdges_union_residualEdges :
    C.fullEdges ∪ C.residualEdges = Finset.univ := by
  exact Finset.union_sdiff_of_subset (Finset.subset_univ _)

/-- The exact residual input needed after the packet base has been colored.
Old colors may be used only when missing at both physical endpoints; fresh
colors have no support restriction. -/
def HasSupportPreservingResidualColoring (fresh : ℕ) : Prop :=
  ∃ residualColor : C.residualGraph.E → Fin (K + fresh),
    C.residualGraph.IsWeightedColoring residualColor ∧
      ∀ e (c : Fin K), residualColor e = Fin.castAdd fresh c →
        c ∈ G.missingColorsAt C.fullEdges C.baseColor (G.fst e.1) ∧
          c ∈ G.missingColorsAt C.fullEdges C.baseColor (G.snd e.1)

/-- Merge a support-preserving coloring of the complementary edge
restriction with the expanded packet coloring. -/
theorem hasWeightedColoring_add_fresh
    (fresh : ℕ) (hresidual : C.HasSupportPreservingResidualColoring fresh) :
    G.HasWeightedColoring (K + fresh) := by
  classical
  rcases hresidual with ⟨residualColor, hcolor, hsupport⟩
  have htotal : 0 < K + fresh := C.palette_pos.trans_le (Nat.le_add_right K fresh)
  let lifted : G.E → Fin (K + fresh) :=
    G.liftRestrictedColor htotal C.residualEdges residualColor
  have hlifted : G.IsFeasibleOn C.residualEdges lifted :=
    G.feasibleOn_liftRestrictedColor htotal C.residualEdges
      residualColor hcolor
  have hliftedSupport : ∀ e ∈ C.residualEdges, ∀ c : Fin K,
      lifted e = Fin.castAdd fresh c →
        c ∈ G.missingColorsAt C.fullEdges C.baseColor (G.fst e) ∧
          c ∈ G.missingColorsAt C.fullEdges C.baseColor (G.snd e) := by
    intro e heR c heColor
    let eR : C.residualGraph.E := ⟨e, heR⟩
    have heColor' : residualColor eR = Fin.castAdd fresh c := by
      simpa [lifted, WeightedMultigraph.liftRestrictedColor, heR, eR]
        using heColor
    exact hsupport eR c heColor'
  obtain ⟨merged, hmerged⟩ :=
    merge_feasibleOn_addFresh_of_commonMissing_general G
      C.fullEdges C.residualEdges C.fullEdges_disjoint_residualEdges
      C.baseColor lifted C.baseColor_feasibleOn hlifted hliftedSupport
  refine ⟨merged, (G.isWeightedColoring_iff_feasibleOn_univ merged).2 ?_⟩
  rw [← C.fullEdges_union_residualEdges]
  exact hmerged

theorem chiW_cast_le_add_fresh
    (fresh : ℕ) (hresidual : C.HasSupportPreservingResidualColoring fresh) :
    (G.chiW : ℝ) ≤ (K : ℝ) + fresh := by
  have h := G.chiW_le_of_hasWeightedColoring
    (C.hasWeightedColoring_add_fresh fresh hresidual)
  exact_mod_cast h

end GeneralColoredPacketBase

/-- Package `exists_chargeSensitivePacketBase` into the object consumed by
the support-preserving completion theorem. -/
theorem exists_generalColoredPacketBase
    (hordinary : OrdinaryMultigraphNearFractionalColoring.{u})
    {G : WeightedMultigraph.{u}} (P : G.Packetization)
    (S : Finset P.Packet) (residualCharge : G.V → ℝ)
    (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ (n : ℕ) (Q : ℝ),
      N ≤ n →
      0 ≤ Q → Q ≤ 2 * (n : ℝ) →
      (∀ v, 0 ≤ residualCharge v) →
      (∀ v, (P.groupedGraph.degreeOn S v : ℝ) + residualCharge v ≤ Q) →
      P.groupedGraph.TriangleEdgeCountAtMost S (2 * (n : ℝ)) →
      ∃ (K : ℕ) (C : G.GeneralColoredPacketBase K),
        max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q) ≤ (K : ℝ) ∧
        (K : ℝ) ≤
          max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q) + η * n + 1 ∧
        ∀ v, residualCharge v + (2 / 5 : ℝ) * n ≤
          ((G.missingColorsAt C.fullEdges C.baseColor v).card : ℝ) := by
  obtain ⟨N, hN⟩ :=
    exists_chargeSensitivePacketBase hordinary P S residualCharge η hη
  refine ⟨N, ?_⟩
  intro n Q hn hQ0 hQ2 hres0 haccount htriangle
  obtain ⟨K, base, hK, hlower, hupper, hproper, _hfeasible, hreserve⟩ :=
    hN n Q hn hQ0 hQ2 hres0 haccount htriangle
  let C : G.GeneralColoredPacketBase K := {
    packetization := P
    fullPackets := S
    palette_pos := hK
    packetColor := base
    packetProper := hproper }
  refine ⟨K, C, hlower, hupper, ?_⟩
  intro v
  simpa [C, GeneralColoredPacketBase.fullEdges,
    GeneralColoredPacketBase.baseColor] using hreserve v

end

end WeightedMultigraph
end WeightedEdgeColoring
