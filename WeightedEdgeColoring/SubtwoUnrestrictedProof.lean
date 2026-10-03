import WeightedEdgeColoring.SubtwoSupportedBoundaryAsymptoticReduction
import WeightedEdgeColoring.SubtwoActualQuotientSmallError
import WeightedEdgeColoring.SubtwoActualPhysicalBoundaryColor
import WeightedEdgeColoring.SubtwoBlockPaddedPhysicalPackets

/-! The unrestricted asymptotic coefficient follows from the actual uniform boundary construction. -/

namespace WeightedEdgeColoring
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 5000000
universe u

theorem subtwoBPAsymptotic_unrestricted : SubtwoBPAsymptotic.{u} := by
  classical
  apply WeightedMultigraph.subtwoBPAsymptotic_of_uniform_supportedBoundary
  intro padding loss hpadding hpadding1 hloss
  obtain ⟨δ,k,S0,hδ,hk,hevenk,hsmall⟩ :=
    WeightedMultigraph.exists_uniform_smallActualQuotientResidualColor
      padding loss hpadding hloss
  obtain ⟨Npacket,hpacket⟩ :=
    WeightedMultigraph.exists_subtwoFloorBaseColor_blockPadded_uniform
      padding hpadding k hk
  refine ⟨S0,?_⟩
  intro S hS D
  obtain ⟨hrate0,hrate,hresidual⟩ := hsmall S hS
  obtain ⟨Nresidual,hresidualN⟩ := hresidual D
  let rate : ℝ := 2*((1:ℝ)/S)+8*δ
  refine ⟨rate,hrate0,hrate,max 1 (max Npacket Nresidual),?_⟩
  intro G P n hn hlocal hfloor
  dsimp only
  let H := P.mixedObjectGraph
  let block := H.subtwoFloorBlock n
  have hnpos : 0 < n := by
    have hh : 1 ≤ n := (le_max_left 1 (max Npacket Nresidual)).trans hn
    omega
  have hnPacket : Npacket ≤ n := (le_max_left Npacket Nresidual).trans
    ((le_max_right 1 (max Npacket Nresidual)).trans hn)
  have hnResidual : Nresidual ≤ n := (le_max_right Npacket Nresidual).trans
    ((le_max_right 1 (max Npacket Nresidual)).trans hn)
  obtain ⟨B,hfour,hevenB,heven,hpaletteLower,hpaletteUpper,baseColor,hproper⟩ :=
    hpacket H n hnPacket hlocal
  have hK : 0 < B*k := by omega
  have hB : 0 < B := Nat.pos_of_mul_pos_right hK
  have hKlowerReal : WeightedMultigraph.subtwoKappa*n ≤ ((B*k:ℕ):ℝ) := by
    have hpad0 : 0 ≤ (padding/2)*(n:ℝ) := by positivity
    nlinarith
  have hKlower : WeightedMultigraph.subtwoKappa*n ≤ (B:ℝ)*k := by
    simpa only [Nat.cast_mul] using hKlowerReal
  have hKupperReal : ((B*k:ℕ):ℝ) ≤ 4*n := by
    have hcoef : WeightedMultigraph.subtwoKappa+padding ≤ (4:ℝ) := by
      unfold WeightedMultigraph.subtwoKappa
      linarith
    exact hpaletteUpper.trans (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg n))
  have hKupper : B*k ≤ 4*n := by exact_mod_cast hKupperReal
  obtain ⟨C',mixed,hmixed,R,color,selectedLabel,hrec,hfull,hres,hfeas,
    hmissing,hselected,hlabelBudget,hleft⟩ :=
    hresidualN H n B hnResidual hB hnpos hlocal hfloor hKlower hKupper
      heven hfour baseColor hproper
  subst C'
  let C := H.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper
  let Cnew := C.quotientRecoloredBase mixed hmixed
  let fiber := H.subtwoFloorBlock_fiber_card_le_five hnpos hlocal
  let labelError : ℝ := rate*n+400*(S+1:ℝ)
  have hlabelBudget' : ∀ v : H.V,
      ((Finset.univ.filter fun c : Fin (B*k) =>
        selectedLabel (block v) c =
          some (H.subtwoLocalSixLabel block fiber (block v) v)).card : ℝ) ≤
        H.chargeOn harmonicCharge
          (H.subtwoCrossingSelectedEdges block Finset.univ \ H.subtwoFloorBaseEdges n) v +
          labelError := by
    intro v
    simpa only [labelError,rate,add_assoc] using hlabelBudget v
  obtain ⟨boundary,labels,hboundary,hboundarySupport,hcounts,hboundaryLoss⟩ :=
    H.exists_subtwoFloorPhysicalBoundaryColor hnpos hlocal hK baseColor hproper
      mixed hmixed R color hfeas hmissing selectedLabel hselected
      labelError (loss*n) hlabelBudget' hleft
  let boundaryEdges := H.subtwoFloorBaseEdges n ∪
    H.selectedResidualOriginalEdges block Cnew R
  refine ⟨B*k,hK,?_,?_,fiber,labels,boundaryEdges,boundary,?_,?_,
    hboundary,hboundarySupport,hboundaryLoss⟩
  · simpa only [WeightedMultigraph.subtwoKappa] using hpaletteLower
  · simpa only [WeightedMultigraph.subtwoKappa] using hpaletteUpper
  · intro q v hv
    subst q
    rw [Fintype.card_subtype]
    simpa only [labelError,add_assoc] using hcounts v
  · have hh := H.physicalBoundary_subset_crossing block Cnew
      (H.subtwoFloorBaseEdges n) R
    rw [H.subtwoFloorBaseEdges_crossing_eq n] at hh
    exact hh

/-- For every positive epsilon, the bound holds above one threshold that is
independent of graph order, multiplicity, and the positive edge weights. -/
theorem chiW_le_1999_add_epsilon_mul_bp :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ G : WeightedMultigraph.{u},
      N ≤ G.bp → (G.chiW : ℝ) ≤ ((1999 / 1000 : ℝ) + ε) * (G.bp : ℝ) :=
  subtwoBPAsymptotic_unrestricted

/-- Equivalent graph-independent additive formulation, valid for every graph. -/
theorem subtwoBPAdditive_unrestricted : SubtwoBPAdditive.{u} :=
  subtwoBPAsymptotic_iff_additive.mp subtwoBPAsymptotic_unrestricted

end
end WeightedEdgeColoring
