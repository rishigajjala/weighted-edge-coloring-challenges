import WeightedEdgeColoring.SubtwoPartialColoringAsymptotic
import WeightedEdgeColoring.GeneralTinyThresholdMixedRepacking

/-!
# From the actual finite/tiny object construction to the unrestricted target

The cutoff and partial-coloring error are chosen before the arbitrary
original graph. Tiny aggregation increases the local packing scale by only
4/S, its coloring expands exactly, and the four-ceil cleanup absorbs the
remaining weighted loss. Constructing the uniform mixed-object partial
coloring is an explicit, still substantive hypothesis of this reduction.
-/

open scoped BigOperators
namespace WeightedEdgeColoring
noncomputable section
universe u

/-- The final construction on actual threshold objects suffices for the
unrestricted coefficient 1999/1000, with uniform graph-independent thresholds. -/
theorem subtwoBPAsymptotic_of_uniform_fineCutoffPartialColorings
    (h : ∀ η : ℝ, 0 < η → ∃ S0 : ℕ, ∀ S : ℕ, max 40 S0 ≤ S → ∃ N : ℕ,
      ∀ (G : WeightedMultigraph.{u})
        (P : G.GeneralTinyThresholdPacketization ((1 : ℝ)/S)) (n : ℕ),
        N ≤ n → P.mixedObjectGraph.LocallyPacksInto n →
        ∃ (F : Finset P.mixedObjectGraph.E) (q : ℕ)
          (color : P.mixedObjectGraph.E → Fin q),
          P.mixedObjectGraph.IsFeasibleOn F color ∧
          (q : ℝ) ≤ ((1999/1000 : ℝ)+η)*n ∧
          ∀ v, (∑ e ∈ Finset.univ \ F,
            if P.mixedObjectGraph.Inc v e then P.mixedObjectGraph.weight e else 0) ≤ η*n) :
    SubtwoBPAsymptotic.{u} := by
  intro ε hε
  let ε0 : ℝ := min ε 1
  have hε0 : 0 < ε0 := lt_min hε (by norm_num)
  have hε01 : ε0 ≤ 1 := min_le_right _ _
  have hε0ε : ε0 ≤ ε := min_le_left _ _
  let η : ℝ := ε0/100
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨S0,hfine⟩ := h η hη
  let S : ℕ := max (max 40 S0) (Nat.ceil (100/ε0))
  have hSfine : max 40 S0 ≤ S := le_max_left _ _
  have hS40 : 40 ≤ S := (le_max_left _ _).trans hSfine
  have hS : 0 < S := by omega
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have hcutoff : (1 : ℝ)/S ≤ 1/4 := by
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 4≤S by omega))
  have hscale : (4 : ℝ)/S ≤ ε0/25 := by
    have hb : 100/ε0 ≤ (S : ℝ) := by
      calc
        _ ≤ (Nat.ceil (100/ε0) : ℝ) := Nat.le_ceil _
        _ ≤ S := by exact_mod_cast le_max_right (max 40 S0) (Nat.ceil (100/ε0))
    have hh := (div_le_iff₀ hε0).mp hb
    apply (div_le_iff₀ hSR).mpr
    nlinarith
  obtain ⟨N0,hN⟩ := hfine S hSfine
  let N : ℕ := max (max 1 N0) (Nat.ceil (100/ε0))
  refine ⟨N,?_⟩
  intro G hn
  let n : ℕ := G.bp
  have hn1 : 1 ≤ n := (le_max_left 1 N0).trans ((le_max_left _ _).trans hn)
  have hn0 : N0 ≤ n := (le_max_right 1 N0).trans ((le_max_left _ _).trans hn)
  have hnlarge : 100 ≤ (n : ℝ)*ε0 := by
    apply (div_le_iff₀ hε0).mp
    calc
      100/ε0 ≤ (Nat.ceil (100/ε0) : ℝ) := Nat.le_ceil _
      _ ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  have htau : (0 : ℝ)<1/S := one_div_pos.mpr hSR
  obtain ⟨P⟩ := G.exists_generalTinyThresholdPacketization ((1 : ℝ)/S)
    htau (hcutoff.trans (by norm_num))
  let n0 : ℕ := n+Nat.ceil (4*((1 : ℝ)/S)*n)+1
  have hlocal : P.mixedObjectGraph.LocallyPacksInto n0 :=
    P.mixedObjectGraph_locallyPacksInto_nat_add_ceil_four_mul htau.le hcutoff
      G.locallyPacksInto_bp
  have hn0n : n ≤ n0 := by dsimp [n0]; omega
  have hn0bound : (n0 : ℝ) ≤ (n : ℝ)+(ε0/25)*n+2 := by
    have hc : (Nat.ceil (4*((1 : ℝ)/S)*n) : ℝ) < 4*((1 : ℝ)/S)*n+1 :=
      Nat.ceil_lt_add_one (by positivity)
    have heq : 4*((1 : ℝ)/S)*n = (4/(S : ℝ))*n := by ring
    rw [heq] at hc
    have hm := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg n)
    dsimp only [n0]
    push_cast
    rw [heq]
    nlinarith
  obtain ⟨F,q,color,hfeasible,hpalette,hleft⟩ :=
    hN G P n0 (hn0.trans hn0n) hlocal
  let loss : ℝ := η*n0
  have hloss : 0 ≤ loss := mul_nonneg hη.le (Nat.cast_nonneg _)
  have hobject := P.mixedObjectGraph.complete_partial_with_four_ceil
    F color hfeasible loss hloss hleft
  have horiginal := P.hasWeightedColoring_of_mixedObjectGraph hobject
  have hchi : (G.chiW : ℝ) ≤ (q : ℝ)+4*(Nat.ceil loss : ℝ)+1 := by
    exact_mod_cast G.chiW_le_of_hasWeightedColoring horiginal
  have hceil : (Nat.ceil loss : ℝ) < loss+1 := Nat.ceil_lt_add_one hloss
  have hcoef0 : (0 : ℝ) ≤ (1999/1000 : ℝ)+5*η := by positivity
  have hcoef3 : (1999/1000 : ℝ)+5*η ≤ 3 := by dsimp [η]; nlinarith
  have hprod := mul_le_mul_of_nonneg_left hn0bound hcoef0
  have hrest := mul_le_mul_of_nonneg_right hcoef3
    (show 0 ≤ (ε0/25)*(n : ℝ)+2 by positivity)
  have hepsprod := mul_le_mul_of_nonneg_right hε0ε (Nat.cast_nonneg n)
  dsimp only [loss,η] at hchi hceil hpalette hprod hrest
  change (G.chiW : ℝ) ≤ ((1999/1000 : ℝ)+ε)*(n : ℝ)
  nlinarith

/-- Compatibility form when the construction happens to work at every
cutoff at least forty. The proof above only needs sufficiently fine cutoffs. -/
theorem subtwoBPAsymptotic_of_uniform_mixedObjectPartialColorings
    (h : ∀ η : ℝ, 0 < η → ∀ S : ℕ, 40 ≤ S → ∃ N : ℕ,
      ∀ (G : WeightedMultigraph.{u})
        (P : G.GeneralTinyThresholdPacketization ((1 : ℝ)/S)) (n : ℕ),
        N ≤ n → P.mixedObjectGraph.LocallyPacksInto n →
        ∃ (F : Finset P.mixedObjectGraph.E) (q : ℕ)
          (color : P.mixedObjectGraph.E → Fin q),
          P.mixedObjectGraph.IsFeasibleOn F color ∧
          (q : ℝ) ≤ ((1999/1000 : ℝ)+η)*n ∧
          ∀ v, (∑ e ∈ Finset.univ \ F,
            if P.mixedObjectGraph.Inc v e then P.mixedObjectGraph.weight e else 0) ≤ η*n) :
    SubtwoBPAsymptotic.{u} := by
  apply subtwoBPAsymptotic_of_uniform_fineCutoffPartialColorings
  intro η hη
  refine ⟨0,?_⟩
  intro S hS
  exact h η hη S (by simpa using hS)

end
end WeightedEdgeColoring
