import WeightedEdgeColoring.SubtwoBoundedTypeAsymptoticReduction
import WeightedEdgeColoring.SubtwoUniformLabeledBoundaryCompletion

/-! A uniform supported boundary construction finishes the unrestricted theorem. -/

namespace WeightedEdgeColoring.WeightedMultigraph
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
universe u

/-- This is an assembly lemma, not an unconditional proof of the target.
Its boundary-construction premise includes actual colors and labels. -/
theorem subtwoBPAsymptotic_of_uniform_supportedBoundary
    (hboundary : ∀ padding loss : ℝ, 0 < padding → padding ≤ 1 → 0 < loss →
      ∃ S0 : ℕ, ∀ S : ℕ, max 160 S0 ≤ S → ∀ D : ℕ,
      ∃ rate : ℝ, 0 ≤ rate ∧ rate ≤ padding / 20 ∧
      ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u})
        (P : G.GeneralTinyThresholdPacketization ((1 : ℝ) / S)) (n : ℕ),
        N ≤ n → P.mixedObjectGraph.LocallyPacksInto n →
        P.mixedObjectGraph.FloorBundleAtMostOneTiny D S →
        let H := P.mixedObjectGraph
        let block := H.subtwoFloorBlock n
        ∃ (K : ℕ), 0 < K ∧
          (((1999 / 1000 : ℝ) + padding / 2) * n ≤ K) ∧
          ((K : ℝ) ≤ ((1999 / 1000 : ℝ) + padding) * n) ∧
        ∃ (hfiber : ∀ q, (H.subtwoFiber block q).card ≤ 5)
          (labels : (H.subtwoFloorQuotient n).V → Fin K → Option (Fin 6))
          (B : Finset H.E) (boundary : H.E → Fin K),
          (∀ q v, block v = q →
            (Fintype.card {c : Fin K // labels q c =
              some (H.subtwoLocalSixLabel block hfiber q v)} : ℝ) ≤
            H.subtwoExteriorHarmonicCharge (H.subtwoFiber block q) v +
              rate * n + 400 * (S + 1 : ℝ)) ∧
          B ⊆ H.subtwoCrossingSelectedEdges block Finset.univ ∧
          H.IsFeasibleOn B boundary ∧
          (∀ e ∈ B, ∀ v, H.Inc v e →
            labels (block v) (boundary e) =
              some (H.subtwoLocalSixLabel block hfiber (block v) v)) ∧
          ∀ v, (∑ e ∈ H.subtwoCrossingSelectedEdges block Finset.univ \ B,
            if H.Inc v e then H.weight e else 0) ≤ loss * n) :
    SubtwoBPAsymptotic.{u} := by
  apply subtwoBPAsymptotic_of_uniform_boundedTypeMixedColorings
  intro η hη
  let padding : ℝ := min η 1
  have hp : 0 < padding := lt_min hη zero_lt_one
  have hp1 : padding ≤ 1 := min_le_right _ _
  have hpη : padding ≤ η := min_le_left _ _
  have hquarter : 0 < η / 4 := by positivity
  obtain ⟨S0,hS0⟩ := hboundary padding (η/4) hp hp1 hquarter
  refine ⟨max 160 S0,?_⟩
  intro S hS D
  have hSbound : max 160 S0 ≤ S := (le_max_right _ _).trans hS
  have hSpos : 0 < S := by omega
  obtain ⟨rate,hrate0,hrate,Nboundary,hboundaryN⟩ := hS0 S hSbound D
  obtain ⟨Ninside,hNinside,hinside⟩ := exists_uniform_labeledBoundary_completion
    S hSpos (η/4) padding rate (400*(S+1:ℝ))
    hquarter hp hrate0 hrate (by positivity)
  let Nconstant : ℕ := ⌈50 / ((S : ℝ) * η)⌉₊
  refine ⟨max Nboundary (max Ninside Nconstant),?_⟩
  intro G P n hn hlocal hfloor
  have hnBoundary := (le_max_left Nboundary (max Ninside Nconstant)).trans hn
  have hnInside : Ninside ≤ n := (le_max_left Ninside Nconstant).trans
    ((le_max_right Nboundary (max Ninside Nconstant)).trans hn)
  have hnConstant : Nconstant ≤ n := (le_max_right Ninside Nconstant).trans
    ((le_max_right Nboundary (max Ninside Nconstant)).trans hn)
  obtain ⟨K,hK,hKlo,hKhi,hfiber,labels,B,boundary,hcounts,hB,hfeas,hsupport,hloss⟩ :=
    hboundaryN G P n hnBoundary hlocal hfloor
  obtain ⟨F,color,hcolor,hkeep,hleft⟩ :=
    hinside G P n hnInside hlocal K hK hKlo hfiber labels hcounts
      B boundary ((η/4)*n) hB hfeas hsupport hloss
  refine ⟨F,K,color,hK,hcolor,?_,?_⟩
  · exact hKhi.trans (mul_le_mul_of_nonneg_right
      (add_le_add le_rfl hpη) (Nat.cast_nonneg n))
  · have hSn : (0 : ℝ) < S := by exact_mod_cast hSpos
    have hNreal : 50 / ((S : ℝ) * η) ≤ (n : ℝ) := by
      calc
        _ ≤ (Nconstant : ℝ) := Nat.le_ceil _
        _ ≤ n := by exact_mod_cast hnConstant
    have hmul := (div_le_iff₀ (mul_pos hSn hη)).1 hNreal
    have hconstant : 25 / (S : ℝ) ≤ (η/2)*n := by
      apply (div_le_iff₀ hSn).2
      nlinarith
    intro v
    have hv := hleft v
    linarith

end
end WeightedEdgeColoring.WeightedMultigraph
