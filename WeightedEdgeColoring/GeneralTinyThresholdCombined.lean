import WeightedEdgeColoring.GeneralTinyThresholdRepacking
import WeightedEdgeColoring.GeneralTinyThresholdMixedObjects
import WeightedEdgeColoring.BipartiteDegreeCriterion

/-!
# One-call general tiny-threshold reduction

This module packages the general endpoint-pair packetization, its mixed
object decomposition, the local repacking estimate, and harmonic-charge
control.  The main theorem has no auxiliary reciprocal-denominator
hypotheses: those are constructed directly from `0 < tau ≤ 1/4`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

/-- Every threshold in `(0,1/4]` lies within a factor two of the reciprocal
of a positive natural number.  This is the numerical input needed by the
harmonic packet-charge estimate. -/
theorem exists_tinyThreshold_harmonicDenominator
    {tau : ℝ} (htau : 0 < tau) (htauquarter : tau ≤ 1 / 4) :
    ∃ t : ℕ, 0 < t ∧
      2 * tau ≤ (1 : ℝ) / t ∧ (1 : ℝ) / t ≤ 4 * tau := by
  let x : ℝ := 1 / (2 * tau)
  let t : ℕ := Nat.floor x
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have htwo_le_x : (2 : ℝ) ≤ x := by
    dsimp [x]
    rw [le_div_iff₀ (by positivity : 0 < 2 * tau)]
    linarith
  have htwo_le_t : 2 ≤ t := by
    apply (Nat.le_floor_iff hx.le).2
    exact_mod_cast htwo_le_x
  have ht : 0 < t := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have ht_le_x : (t : ℝ) ≤ x := by
    exact Nat.floor_le hx.le
  have hx_lt_succ : x < (t : ℝ) + 1 := by
    simpa [t] using Nat.lt_floor_add_one x
  have hx_le_two_mul_t : x ≤ 2 * (t : ℝ) := by
    have hone_le_t : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
    linarith
  have hinvx : (1 : ℝ) / x = 2 * tau := by
    dsimp [x]
    field_simp [htau.ne']
  have hupper : 2 * tau ≤ (1 : ℝ) / t := by
    rw [← hinvx]
    exact one_div_le_one_div_of_le htR ht_le_x
  have hhalf : (1 : ℝ) / (2 * (t : ℝ)) ≤ 1 / x := by
    exact one_div_le_one_div_of_le hx hx_le_two_mul_t
  have hlower : (1 : ℝ) / t ≤ 4 * tau := by
    have hid : (1 : ℝ) / t = 2 * (1 / (2 * (t : ℝ))) := by
      field_simp [htR.ne']
    calc
      (1 : ℝ) / t = 2 * (1 / (2 * (t : ℝ))) := hid
      _ ≤ 2 * (1 / x) := by gcongr
      _ = 4 * tau := by rw [hinvx]; ring
  exact ⟨t, ht, hupper, hlower⟩

namespace GeneralTinyThresholdPacketization

variable {G : WeightedMultigraph.{u}} {tau : ℝ}
  (P : G.GeneralTinyThresholdPacketization tau)

/-- The mixed graph inherits the uniform harmonic-charge estimate from the
original local packing, with no reciprocal-denominator parameters exposed. -/
theorem mixedObjectGraph_starCharge_le_add_four_mul_n
    {n : ℕ} (htau : 0 < tau) (htauquarter : tau ≤ 1 / 4)
    (hlocal : G.LocallyPacksInto n) (v : G.V) :
    P.mixedObjectGraph.starCharge harmonicCharge v ≤
      G.starCharge harmonicCharge v + 4 * tau * n := by
  obtain ⟨t, ht, hupper, hlower⟩ :=
    exists_tinyThreshold_harmonicDenominator htau htauquarter
  have hcharge := P.mixedObjectGraph_starCharge_le_add_four_mul
    t ht hupper hlower v
  have hstar : G.starWeight v ≤ (n : ℝ) :=
    G.starWeight_le_of_packsStarInto (hlocal v)
  calc
    P.mixedObjectGraph.starCharge harmonicCharge v ≤
        G.starCharge harmonicCharge v + 4 * tau * G.starWeight v := hcharge
    _ ≤ G.starCharge harmonicCharge v + 4 * tau * n := by
      gcongr

/-- At the reciprocal cutoff, the heavy mixed core has the ordinary-degree
bound used in linear grouping: at most `n(T+1)` core objects meet a vertex. -/
theorem coreObjects_degreeOn_le_mul_succ
    {T n : ℕ}
    (P : G.GeneralTinyThresholdPacketization ((1 : ℝ) / (T + 1)))
    (hlocal : G.LocallyPacksInto n) (v : G.V) :
    P.mixedObjectGraph.degreeOn P.coreObjects v ≤ n * (T + 1) := by
  have hweighted := P.mixedObjectGraph.degreeOn_mul_le_restrictedWeight
    P.coreObjects ((1 : ℝ) / (T + 1))
    (fun o ho ↦ P.coreObject_weight_ge ho) v
  have hrestricted :=
    P.mixedObjectGraph.restrictedStarWeight_le_starWeight P.coreObjects v
  have hstar : G.starWeight v ≤ (n : ℝ) :=
    G.starWeight_le_of_packsStarInto (hlocal v)
  have htotal :
      (P.mixedObjectGraph.degreeOn P.coreObjects v : ℝ) *
          ((1 : ℝ) / (T + 1)) ≤ n := by
    calc
      _ ≤ ∑ o ∈ P.coreObjects,
          if P.mixedObjectGraph.Inc v o then
            P.mixedObjectGraph.weight o else 0 := hweighted
      _ ≤ P.mixedObjectGraph.starWeight v := hrestricted
      _ = G.starWeight v := P.mixedObjectGraph_starWeight v
      _ ≤ n := hstar
  have hden : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hreal :
      (P.mixedObjectGraph.degreeOn P.coreObjects v : ℝ) ≤
        (n : ℝ) * ((T : ℝ) + 1) := by
    calc
      (P.mixedObjectGraph.degreeOn P.coreObjects v : ℝ) =
          ((P.mixedObjectGraph.degreeOn P.coreObjects v : ℝ) *
            ((1 : ℝ) / (T + 1))) * ((T : ℝ) + 1) := by
              field_simp
      _ ≤ (n : ℝ) * ((T : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right htotal hden.le
  exact_mod_cast hreal

end GeneralTinyThresholdPacketization

/-- One-call unconditional general tiny-threshold reduction.  It constructs
the endpoint-pair packets and simultaneously exposes the local repacking
bound, exact mixed-star weight, the heavy core, the endpoint-simple tiny
remainder, coloring expansion, and the mixed harmonic-charge estimate. -/
theorem exists_generalTinyThresholdCombined
    (G : WeightedMultigraph.{u}) (tau : ℝ)
    (htau : 0 < tau) (htauquarter : tau ≤ 1 / 4)
    {n : ℕ} (hlocal : G.LocallyPacksInto n) :
    ∃ P : G.GeneralTinyThresholdPacketization tau,
      P.packetization.groupedGraph.LocallyPacksInto
          (n + Nat.ceil (4 * tau * n) + 1) ∧
      (∀ v, P.mixedObjectGraph.starWeight v = G.starWeight v) ∧
      (∀ o : P.coreObjectGraph.E, tau ≤ P.coreObjectGraph.weight o) ∧
      (∀ o : P.smallObjectGraph.E, P.smallObjectGraph.weight o ≤ tau) ∧
      P.smallObjectGraph.asMultigraph.PairMultiplicityAtMost 1 ∧
      (∀ q : ℕ, ∀ color : P.Object → Fin q,
        P.mixedObjectGraph.IsWeightedColoring color →
          G.IsWeightedColoring (P.mixedPacketization.expandColor color)) ∧
      (∀ v, P.mixedObjectGraph.starCharge harmonicCharge v ≤
        G.starCharge harmonicCharge v + 4 * tau * n) := by
  have htauhalf : tau ≤ 1 / 2 := by linarith
  obtain ⟨P⟩ := G.exists_generalTinyThresholdPacketization
    tau htau htauhalf
  refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact P.groupedGraph_locallyPacksInto_nat_add_ceil_four_mul_of_original
      htau.le htauquarter hlocal
  · exact P.mixedObjectGraph_starWeight
  · exact P.coreObjectGraph_weight_ge
  · exact P.smallObjectGraph_weight_le
  · exact P.smallObjectGraph_pairMultiplicityAtMost
  · intro q color hcolor
    exact P.isWeightedColoring_expandMixedColor color hcolor
  · exact P.mixedObjectGraph_starCharge_le_add_four_mul_n
      htau htauquarter hlocal

/-- Reciprocal-cutoff specialization used by finite harmonic classes and
pre-cover linear grouping.  The clean condition `3 ≤ T` is exactly what is
needed to put `tau = 1/(T+1)` in `(0,1/4]`. -/
theorem exists_generalTinyThresholdCombined_reciprocal
    (G : WeightedMultigraph.{u}) (T : ℕ) (hT : 3 ≤ T)
    {n : ℕ} (hlocal : G.LocallyPacksInto n) :
    ∃ P : G.GeneralTinyThresholdPacketization ((1 : ℝ) / (T + 1)),
      P.packetization.groupedGraph.LocallyPacksInto
          (n + Nat.ceil (4 * (n : ℝ) / (T + 1 : ℝ)) + 1) ∧
      (∀ v, P.mixedObjectGraph.starWeight v = G.starWeight v) ∧
      (∀ o : P.coreObjectGraph.E,
        (1 : ℝ) / (T + 1) ≤ P.coreObjectGraph.weight o) ∧
      (∀ v, P.mixedObjectGraph.degreeOn P.coreObjects v ≤ n * (T + 1)) ∧
      (∀ o : P.smallObjectGraph.E,
        P.smallObjectGraph.weight o ≤ (1 : ℝ) / (T + 1)) ∧
      P.smallObjectGraph.asMultigraph.PairMultiplicityAtMost 1 ∧
      (∀ q : ℕ, ∀ color : P.Object → Fin q,
        P.mixedObjectGraph.IsWeightedColoring color →
          G.IsWeightedColoring (P.mixedPacketization.expandColor color)) ∧
      (∀ v, P.mixedObjectGraph.starCharge harmonicCharge v ≤
        G.starCharge harmonicCharge v + 4 * n / (T + 1)) := by
  have hden : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have htau : 0 < (1 : ℝ) / (T + 1) := by positivity
  have hTR : (4 : ℝ) ≤ (T : ℝ) + 1 := by exact_mod_cast (show 4 ≤ T + 1 by omega)
  have htauquarter : (1 : ℝ) / (T + 1) ≤ 1 / 4 := by
    exact one_div_le_one_div_of_le (by norm_num) hTR
  obtain ⟨P, hpack, hstar, hcore, hsmall, hsimple, hcolor, hcharge⟩ :=
    exists_generalTinyThresholdCombined G ((1 : ℝ) / (T + 1))
      htau htauquarter hlocal
  refine ⟨P, ?_, hstar, hcore, ?_, hsmall, hsimple, hcolor, ?_⟩
  · convert hpack using 1
    ring_nf
  · exact P.coreObjects_degreeOn_le_mul_succ hlocal
  · intro v
    convert hcharge v using 1
    ring

end

end WeightedMultigraph
end WeightedEdgeColoring
