import WeightedEdgeColoring.BPGeneralFloorPacketTriangle
import WeightedEdgeColoring.BPGeneralPacketCompletion
import WeightedEdgeColoring.BPGeneralReduction

/-!
# Charge-sensitive base from the coefficient-floor packetization

For coloring purposes we retain the full floor packets whose physical
harmonic charge is at least one.  The exact-demand triangle theorem remains
valid after this restriction.  Each retained packet then pays for its one
unit of grouped degree, while every omitted physical edge keeps its harmonic
charge.  This gives the exact accounting and missing-palette estimate needed
by the general packet base.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

namespace Packetization

variable {G} (P : G.Packetization)

/-- The total value of a physical edge charge inside one packet. -/
def packetCharge (charge : ℝ → ℝ) (p : P.Packet) : ℝ :=
  ∑ e : G.E, if P.packetOf e = p then charge (G.weight e) else 0

/-- Restricting a physical charge to selected packets is the same as summing
the corresponding packet charges in the grouped graph. -/
theorem chargeOn_originalEdgesOfPackets
    (charge : ℝ → ℝ) (S : Finset P.Packet) (v : G.V) :
    G.chargeOn charge (P.originalEdgesOfPackets S) v =
      ∑ p ∈ S,
        if P.groupedGraph.Inc v p then P.packetCharge charge p else 0 := by
  classical
  unfold WeightedMultigraph.chargeOn
  change
    (∑ e ∈ Finset.univ.filter (fun e ↦ P.packetOf e ∈ S),
      if G.Inc v e then charge (G.weight e) else 0) = _
  rw [Finset.sum_filter]
  calc
    (∑ e : G.E,
      if P.packetOf e ∈ S then
        (if G.Inc v e then charge (G.weight e) else 0) else 0) =
      ∑ p ∈ S, ∑ e : G.E,
        if P.packetOf e = p ∧ P.groupedGraph.Inc v p
          then charge (G.weight e) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases heS : P.packetOf e ∈ S
      · rw [Finset.sum_eq_single (P.packetOf e)]
        · have hinc := P.groupedGraph_inc_packetOf v e
          by_cases heinc : G.Inc v e
          · have hpinc := hinc.mpr heinc
            simp [heS, heinc, hpinc]
          · have hpinc : ¬P.groupedGraph.Inc v (P.packetOf e) :=
              fun h ↦ heinc (hinc.mp h)
            simp [heS, heinc, hpinc]
        · intro p _hpS hp
          simp [Ne.symm hp]
        · intro hnot
          exact (hnot heS).elim
      · have hzero :
          (∑ p ∈ S, if P.packetOf e = p ∧ P.groupedGraph.Inc v p
            then charge (G.weight e) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro p hpS
          have hne : P.packetOf e ≠ p := fun h ↦ heS (h ▸ hpS)
          simp [hne]
        rw [hzero]
        simp [heS]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hpinc : P.groupedGraph.Inc v p
      · simp [packetCharge, hpinc, and_comm]
      · simp [hpinc]

end Packetization

/-- Floor packets whose assigned physical edges carry at least one unit of
harmonic charge.  All singleton residual labels are excluded. -/
noncomputable def harmonicFullFloorPacketSet :
    Finset G.floorPacketization.Packet :=
  G.fullFloorPacketSet.filter fun p ↦
    1 ≤ G.floorPacketization.packetCharge harmonicCharge p

theorem harmonicFullFloorPacketSet_subset :
    G.harmonicFullFloorPacketSet ⊆ G.fullFloorPacketSet := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

theorem one_le_packetCharge_of_mem_harmonicFullFloorPacketSet
    {p : G.floorPacketization.Packet}
    (hp : p ∈ G.harmonicFullFloorPacketSet) :
    1 ≤ G.floorPacketization.packetCharge harmonicCharge p :=
  (Finset.mem_filter.mp hp).2

theorem one_le_floorPacketCharge (q : G.GlobalFloorPacket) :
    1 ≤ G.floorPacketization.packetCharge harmonicCharge
      (Sum.inl q) := by
  change 1 ≤
    ∑ e : G.E,
      if G.globalFloorPacketOf e = Sum.inl q
        then harmonicCharge (G.weight e) else 0
  rw [G.floorPacketHarmonicCharge_eq_patternCharge q]
  exact G.floorPacket_harmonicPatternCharge_ge_one q

/-- Saturation of the chosen minimum covers shows that the harmonic filter
keeps every full floor packet. -/
theorem harmonicFullFloorPacketSet_eq_fullFloorPacketSet :
    G.harmonicFullFloorPacketSet = G.fullFloorPacketSet := by
  apply Finset.Subset.antisymm G.harmonicFullFloorPacketSet_subset
  intro p hp
  apply Finset.mem_filter.mpr
  refine ⟨hp, ?_⟩
  cases p with
  | inl q => exact G.one_le_floorPacketCharge q
  | inr e => exact (G.not_mem_fullFloorPacketSet_inr e hp).elim

/-- Triangle bounds are inherited by a smaller edge set. -/
theorem TriangleEdgeCountAtMost.mono
    {F F' : Finset G.E} {B : ℝ}
    (h : G.TriangleEdgeCountAtMost F B) (hsub : F' ⊆ F) :
    G.TriangleEdgeCountAtMost F' B := by
  intro S hS
  have hi : G.internalEdges F' S ⊆ G.internalEdges F S := by
    intro e he
    have he' := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨hsub he'.1, he'.2⟩
  have hcard : ((G.internalEdges F' S).card : ℝ) ≤
      (G.internalEdges F S).card := by
    exact_mod_cast Finset.card_le_card hi
  exact hcard.trans (h S hS)

/-- The harmonic-charge-selected floor packets retain the exact `2n`
triangle bound furnished by the exact-demand construction. -/
theorem harmonicFloorPacketization_triangleEdgeCountAtMost
    (n : ℕ) (hlocal : G.LocallyPacksInto n) :
    G.floorPacketization.groupedGraph.TriangleEdgeCountAtMost
      G.harmonicFullFloorPacketSet (2 * (n : ℝ)) := by
  intro T hT
  have hi :
      G.floorPacketization.groupedGraph.internalEdges
          G.harmonicFullFloorPacketSet T ⊆
        G.floorPacketization.groupedGraph.internalEdges
          G.fullFloorPacketSet T := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨G.harmonicFullFloorPacketSet_subset hp'.1, hp'.2⟩
  have hcard :
      ((G.floorPacketization.groupedGraph.internalEdges
          G.harmonicFullFloorPacketSet T).card : ℝ) ≤
        (G.floorPacketization.groupedGraph.internalEdges
          G.fullFloorPacketSet T).card := by
    exact_mod_cast Finset.card_le_card hi
  exact hcard.trans
    (G.floorPacketization_triangleEdgeCountAtMost n hlocal T hT)

/-- A unit-charged packet pays for one unit of grouped degree.  The omitted
physical edges retain their harmonic charge, so the two contributions never
exceed the original harmonic star charge. -/
theorem floorPacketDegree_add_residualHarmonicCharge_le
    (v : G.V) :
    (G.floorPacketization.groupedGraph.degreeOn
        G.harmonicFullFloorPacketSet v : ℝ) +
      G.chargeOn harmonicCharge
        (Finset.univ \
          G.floorPacketization.originalEdgesOfPackets
            G.harmonicFullFloorPacketSet) v ≤
      G.starCharge harmonicCharge v := by
  let P := G.floorPacketization
  let S := G.harmonicFullFloorPacketSet
  have hselected :
      (P.groupedGraph.degreeOn S v : ℝ) ≤
        G.chargeOn harmonicCharge (P.originalEdgesOfPackets S) v := by
    rw [P.chargeOn_originalEdgesOfPackets harmonicCharge S v]
    unfold WeightedMultigraph.degreeOn
    calc
      ((S.filter (P.groupedGraph.Inc v)).card : ℝ) =
          ∑ p ∈ S.filter (P.groupedGraph.Inc v), (1 : ℝ) := by simp
      _ ≤ ∑ p ∈ S.filter (P.groupedGraph.Inc v),
          P.packetCharge harmonicCharge p := by
        apply Finset.sum_le_sum
        intro p hp
        exact G.one_le_packetCharge_of_mem_harmonicFullFloorPacketSet
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

theorem residualHarmonicCharge_nonneg (v : G.V) :
    0 ≤ G.chargeOn harmonicCharge
      (Finset.univ \
        G.floorPacketization.originalEdgesOfPackets
          G.harmonicFullFloorPacketSet) v := by
  unfold chargeOn
  apply Finset.sum_nonneg
  intro e _he
  split
  · exact harmonicCharge_nonneg _
  · exact le_rfl

/-- Charge accounting for the original, unfiltered full floor packet set. -/
theorem fullFloorPacketDegree_add_residualHarmonicCharge_le
    (v : G.V) :
    (G.floorPacketization.groupedGraph.degreeOn
        G.fullFloorPacketSet v : ℝ) +
      G.chargeOn harmonicCharge
        (Finset.univ \
          G.floorPacketization.originalEdgesOfPackets
            G.fullFloorPacketSet) v ≤
      G.starCharge harmonicCharge v := by
  rw [← G.harmonicFullFloorPacketSet_eq_fullFloorPacketSet]
  exact G.floorPacketDegree_add_residualHarmonicCharge_le v

theorem fullFloorResidualHarmonicCharge_nonneg (v : G.V) :
    0 ≤ G.chargeOn harmonicCharge
      (Finset.univ \
        G.floorPacketization.originalEdgesOfPackets
          G.fullFloorPacketSet) v := by
  rw [← G.harmonicFullFloorPacketSet_eq_fullFloorPacketSet]
  exact G.residualHarmonicCharge_nonneg v

/-- The explicit floor packetization, its exact-demand triangle estimate,
and harmonic charge accounting specialize the general colored-packet-base
theorem without any extra structural hypothesis. -/
theorem exists_harmonicFloorGeneralColoredPacketBase
    (hordinary : OrdinaryMultigraphNearFractionalColoring.{u})
    (G : WeightedMultigraph.{u}) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ (n : ℕ) (Q : ℝ),
      N ≤ n →
      G.LocallyPacksInto n →
      0 ≤ Q →
      (∀ v, G.starCharge harmonicCharge v ≤ Q) →
      ∃ (K : ℕ) (C : G.GeneralColoredPacketBase K),
        (K : ℝ) ≤
          max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q) + η * n + 1 ∧
        ∀ v,
          G.chargeOn harmonicCharge C.residualEdges v +
              (2 / 5 : ℝ) * n ≤
            ((G.missingColorsAt C.fullEdges C.baseColor v).card : ℝ) := by
  let residualCharge : G.V → ℝ := fun v ↦
    G.chargeOn harmonicCharge
      (Finset.univ \
        G.floorPacketization.originalEdgesOfPackets
          G.fullFloorPacketSet) v
  obtain ⟨N, hN⟩ := exists_chargeSensitivePacketBase hordinary
    G.floorPacketization G.fullFloorPacketSet residualCharge η hη
  refine ⟨N, ?_⟩
  intro n Q hn hlocal hQ0 hcharge
  let Q' : ℝ := min Q (2 * (n : ℝ))
  have hQ'0 : 0 ≤ Q' := by
    exact le_min hQ0 (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
  have hQ'2 : Q' ≤ 2 * (n : ℝ) := min_le_right _ _
  have hcharge2 : ∀ v, G.starCharge harmonicCharge v ≤ 2 * (n : ℝ) := by
    intro v
    apply G.harmonicStarCharge_le_two_mul_of_starWeight_le
    intro w
    exact G.starWeight_le_of_packsStarInto (hlocal w)
  have haccount : ∀ v,
      (G.floorPacketization.groupedGraph.degreeOn
          G.fullFloorPacketSet v : ℝ) + residualCharge v ≤ Q' := by
    intro v
    apply (G.fullFloorPacketDegree_add_residualHarmonicCharge_le v).trans
    exact le_min (hcharge v) (hcharge2 v)
  have hres0 : ∀ v, 0 ≤ residualCharge v := by
    intro v
    exact G.fullFloorResidualHarmonicCharge_nonneg v
  obtain ⟨K, base, hK, _hlower, hupper, hproper, _hfeasible, hmissing⟩ :=
    hN n Q' hn hQ'0 hQ'2 hres0 haccount
      (G.floorPacketization_triangleEdgeCountAtMost n hlocal)
  let C : G.GeneralColoredPacketBase K := {
    packetization := G.floorPacketization
    fullPackets := G.fullFloorPacketSet
    palette_pos := hK
    packetColor := base
    packetProper := hproper }
  refine ⟨K, C, ?_, ?_⟩
  · calc
      (K : ℝ) ≤
          max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q') + η * n + 1 := hupper
      _ ≤ max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q) + η * n + 1 := by
        gcongr
        exact min_le_left _ _
  · intro v
    simpa [C, GeneralColoredPacketBase.residualEdges,
      GeneralColoredPacketBase.fullEdges, GeneralColoredPacketBase.baseColor,
      residualCharge]
      using hmissing v

/-- Uniform version of the explicit harmonic floor packet base: its
threshold is independent of the input weighted multigraph. -/
theorem exists_uniform_harmonicFloorGeneralColoredPacketBase
    (hordinary : OrdinaryMultigraphNearFractionalColoring.{u})
    (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (n : ℕ) (Q : ℝ),
      N ≤ n →
      G.LocallyPacksInto n →
      0 ≤ Q →
      (∀ v, G.starCharge harmonicCharge v ≤ Q) →
      ∃ (K : ℕ) (C : G.GeneralColoredPacketBase K),
        (K : ℝ) ≤
          max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q) + η * n + 1 ∧
        ∀ v,
          G.chargeOn harmonicCharge C.residualEdges v +
              (2 / 5 : ℝ) * n ≤
            ((G.missingColorsAt C.fullEdges C.baseColor v).card : ℝ) := by
  obtain ⟨N, hN⟩ :=
    exists_uniform_chargeSensitivePacketBase hordinary η hη
  refine ⟨N, ?_⟩
  intro G n Q hn hlocal hQ0 hcharge
  let residualCharge : G.V → ℝ := fun v ↦
    G.chargeOn harmonicCharge
      (Finset.univ \
        G.floorPacketization.originalEdgesOfPackets
          G.fullFloorPacketSet) v
  let Q' : ℝ := min Q (2 * (n : ℝ))
  have hQ'0 : 0 ≤ Q' := by
    exact le_min hQ0 (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
  have hQ'2 : Q' ≤ 2 * (n : ℝ) := min_le_right _ _
  have hcharge2 : ∀ v, G.starCharge harmonicCharge v ≤ 2 * (n : ℝ) := by
    intro v
    apply G.harmonicStarCharge_le_two_mul_of_starWeight_le
    intro w
    exact G.starWeight_le_of_packsStarInto (hlocal w)
  have haccount : ∀ v,
      (G.floorPacketization.groupedGraph.degreeOn
          G.fullFloorPacketSet v : ℝ) + residualCharge v ≤ Q' := by
    intro v
    apply (G.fullFloorPacketDegree_add_residualHarmonicCharge_le v).trans
    exact le_min (hcharge v) (hcharge2 v)
  have hres0 : ∀ v, 0 ≤ residualCharge v := by
    intro v
    exact G.fullFloorResidualHarmonicCharge_nonneg v
  obtain ⟨K, base, hK, _hlower, hupper, hproper, _hfeasible, hmissing⟩ :=
    hN G G.floorPacketization G.fullFloorPacketSet residualCharge n Q'
      hn hQ'0 hQ'2 hres0 haccount
      (G.floorPacketization_triangleEdgeCountAtMost n hlocal)
  let C : G.GeneralColoredPacketBase K := {
    packetization := G.floorPacketization
    fullPackets := G.fullFloorPacketSet
    palette_pos := hK
    packetColor := base
    packetProper := hproper }
  refine ⟨K, C, ?_, ?_⟩
  · calc
      (K : ℝ) ≤
          max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q') + η * n + 1 := hupper
      _ ≤ max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q) + η * n + 1 := by
        gcongr
        exact min_le_left _ _
  · intro v
    simpa [C, GeneralColoredPacketBase.residualEdges,
      GeneralColoredPacketBase.fullEdges, GeneralColoredPacketBase.baseColor,
      residualCharge]
      using hmissing v

/-- The preceding construction packaged with the already proved
support-preserving merge theorem.  Thus any residual coloring using the
missing base colors (and `fresh` new colors) immediately colors the original
weighted multigraph. -/
theorem exists_harmonicFloorGeneralColoredPacketCompletion
    (hordinary : OrdinaryMultigraphNearFractionalColoring.{u})
    (G : WeightedMultigraph.{u}) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ (n : ℕ) (Q : ℝ),
      N ≤ n →
      G.LocallyPacksInto n →
      0 ≤ Q →
      (∀ v, G.starCharge harmonicCharge v ≤ Q) →
      ∃ (K : ℕ) (C : G.GeneralColoredPacketBase K),
        (K : ℝ) ≤
          max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q) + η * n + 1 ∧
        (∀ v,
          G.chargeOn harmonicCharge C.residualEdges v +
              (2 / 5 : ℝ) * n ≤
            ((G.missingColorsAt C.fullEdges C.baseColor v).card : ℝ)) ∧
        ∀ fresh : ℕ, C.HasSupportPreservingResidualColoring fresh →
          (G.chiW : ℝ) ≤ (K : ℝ) + fresh := by
  obtain ⟨N, hN⟩ :=
    exists_harmonicFloorGeneralColoredPacketBase hordinary G η hη
  refine ⟨N, ?_⟩
  intro n Q hn hlocal hQ hcharge
  obtain ⟨K, C, hK, hmissing⟩ := hN n Q hn hlocal hQ hcharge
  refine ⟨K, C, hK, hmissing, ?_⟩
  intro fresh hresidual
  exact C.chiW_cast_le_add_fresh fresh hresidual

/-- At the `8/5` charge cap supplied by the finite general reduction, the
packet-base palette has the precise `2n + 15/4` main term and reserves the
actual residual harmonic charge plus `2n/5` at every vertex. -/
theorem exists_eightFifthsHarmonicFloorGeneralColoredPacketCompletion
    (hordinary : OrdinaryMultigraphNearFractionalColoring.{u})
    (G : WeightedMultigraph.{u}) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n →
      G.LocallyPacksInto n →
      (∀ v, G.starCharge harmonicCharge v ≤
        (8 / 5 : ℝ) * n + 3) →
      ∃ (K : ℕ) (C : G.GeneralColoredPacketBase K),
        (K : ℝ) ≤ 2 * (n : ℝ) + 15 / 4 + η * n + 1 ∧
        (∀ v,
          G.chargeOn harmonicCharge C.residualEdges v +
              (2 / 5 : ℝ) * n ≤
            ((G.missingColorsAt C.fullEdges C.baseColor v).card : ℝ)) ∧
        ∀ fresh : ℕ, C.HasSupportPreservingResidualColoring fresh →
          (G.chiW : ℝ) ≤ (K : ℝ) + fresh := by
  obtain ⟨N, hN⟩ :=
    exists_harmonicFloorGeneralColoredPacketCompletion hordinary G η hη
  refine ⟨N, ?_⟩
  intro n hn hlocal hcharge
  let Q : ℝ := (8 / 5 : ℝ) * n + 3
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  obtain ⟨K, C, hK, hmissing, hcomplete⟩ :=
    hN n Q hn hlocal hQ (by simpa [Q] using hcharge)
  refine ⟨K, C, ?_, hmissing, hcomplete⟩
  have htwo : 2 * (n : ℝ) ≤ (5 / 4 : ℝ) * Q := by
    dsimp [Q]
    nlinarith
  rw [max_eq_right htwo] at hK
  dsimp [Q] at hK
  nlinarith

/-- Uniform completion wrapper; `N` is chosen before `G`. -/
theorem exists_uniform_harmonicFloorGeneralColoredPacketCompletion
    (hordinary : OrdinaryMultigraphNearFractionalColoring.{u})
    (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (n : ℕ) (Q : ℝ),
      N ≤ n →
      G.LocallyPacksInto n →
      0 ≤ Q →
      (∀ v, G.starCharge harmonicCharge v ≤ Q) →
      ∃ (K : ℕ) (C : G.GeneralColoredPacketBase K),
        (K : ℝ) ≤
          max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q) + η * n + 1 ∧
        (∀ v,
          G.chargeOn harmonicCharge C.residualEdges v +
              (2 / 5 : ℝ) * n ≤
            ((G.missingColorsAt C.fullEdges C.baseColor v).card : ℝ)) ∧
        ∀ fresh : ℕ, C.HasSupportPreservingResidualColoring fresh →
          (G.chiW : ℝ) ≤ (K : ℝ) + fresh := by
  obtain ⟨N, hN⟩ :=
    exists_uniform_harmonicFloorGeneralColoredPacketBase hordinary η hη
  refine ⟨N, ?_⟩
  intro G n Q hn hlocal hQ hcharge
  obtain ⟨K, C, hK, hmissing⟩ := hN G n Q hn hlocal hQ hcharge
  refine ⟨K, C, hK, hmissing, ?_⟩
  intro fresh hresidual
  exact C.chiW_cast_le_add_fresh fresh hresidual

/-- Uniform `8/5` endpoint matching the quantifier order of
`GeneralEightFifthsResidualColoringAsymptotic`. -/
theorem exists_uniform_eightFifthsHarmonicFloorGeneralColoredPacketCompletion
    (hordinary : OrdinaryMultigraphNearFractionalColoring.{u})
    (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (n : ℕ),
      N ≤ n →
      G.LocallyPacksInto n →
      (∀ v, G.starCharge harmonicCharge v ≤
        (8 / 5 : ℝ) * n + 3) →
      ∃ (K : ℕ) (C : G.GeneralColoredPacketBase K),
        (K : ℝ) ≤ 2 * (n : ℝ) + 15 / 4 + η * n + 1 ∧
        (∀ v,
          G.chargeOn harmonicCharge C.residualEdges v +
              (2 / 5 : ℝ) * n ≤
            ((G.missingColorsAt C.fullEdges C.baseColor v).card : ℝ)) ∧
        ∀ fresh : ℕ, C.HasSupportPreservingResidualColoring fresh →
          (G.chiW : ℝ) ≤ (K : ℝ) + fresh := by
  obtain ⟨N, hN⟩ :=
    exists_uniform_harmonicFloorGeneralColoredPacketCompletion hordinary η hη
  refine ⟨N, ?_⟩
  intro G n hn hlocal hcharge
  let Q : ℝ := (8 / 5 : ℝ) * n + 3
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  obtain ⟨K, C, hK, hmissing, hcomplete⟩ :=
    hN G n Q hn hlocal hQ (by simpa [Q] using hcharge)
  refine ⟨K, C, ?_, hmissing, hcomplete⟩
  have htwo : 2 * (n : ℝ) ≤ (5 / 4 : ℝ) * Q := by
    dsimp [Q]
    nlinarith
  rw [max_eq_right htwo] at hK
  dsimp [Q] at hK
  nlinarith

end

end WeightedMultigraph
end WeightedEdgeColoring
