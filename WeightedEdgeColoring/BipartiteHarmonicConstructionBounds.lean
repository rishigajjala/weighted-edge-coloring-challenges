import WeightedEdgeColoring.BipartiteTinyChargeAccounting
import WeightedEdgeColoring.BipartiteHarmonicParameterBounds

/-!
# Graph bounds for the bipartite finite-plus-tiny construction

The scalar targets in `BipartiteHarmonicParameterBounds` are chosen so that
the threshold packetization satisfies all charge hypotheses of the joint
rounding theorem.  This file proves those graph-dependent inequalities once,
independently of the final asymptotic quantifier bookkeeping.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable {G : WeightedMultigraph.{u}} {b : G.Bipartition}
variable {t : ℕ} (P : G.TinyThresholdPacketization b
  (reciprocalTinyThreshold t))

/-- The complete mixed-object graph has the charge prescribed by the scalar
mixed target. -/
theorem TinyThresholdPacketization.mixedObject_starCharge_le_target
    (ht : 0 < t) {n : ℕ} {A : ℝ}
    (hstar : ∀ v, G.starWeight v ≤ n)
    (hcharge : ∀ v, G.starCharge harmonicCharge v ≤ A)
    (v : G.V) :
    P.mixedObjectGraph.starCharge harmonicCharge v ≤
      bipartiteMixedChargeTarget A n (reciprocalTinyThreshold t) := by
  let tau := reciprocalTinyThreshold t
  have htau0 : 0 ≤ tau := (reciprocalTinyThreshold_pos ht).le
  have hupper : 2 * tau ≤ (1 : ℝ) / t := by
    exact (two_mul_reciprocalTinyThreshold ht).le
  have hlower : (1 : ℝ) / t ≤ 4 * tau := by
    exact inv_le_four_mul_reciprocalTinyThreshold ht
  have hmixed := P.mixedObject_starCharge_le_add_four_mul
    t ht hupper hlower v
  have horiginal : G.starCharge harmonicCharge v ≤ min A (2 * (n : ℝ)) := by
    apply le_min (hcharge v)
    exact G.harmonicStarCharge_le_two_mul_of_starWeight_le hstar v
  have hweight : 4 * tau * G.starWeight v ≤ 4 * tau * n := by
    exact mul_le_mul_of_nonneg_left (hstar v)
      (mul_nonneg (by norm_num) htau0)
  unfold bipartiteMixedChargeTarget
  exact hmixed.trans (add_le_add horiginal hweight)

/-- Restricting to the finite core can only lower harmonic star charge. -/
theorem TinyThresholdPacketization.coreObject_starCharge_le_target
    (ht : 0 < t) {n : ℕ} {A : ℝ}
    (hstar : ∀ v, G.starWeight v ≤ n)
    (hcharge : ∀ v, G.starCharge harmonicCharge v ≤ A)
    (v : G.V) :
    P.coreObjectGraph.starCharge harmonicCharge v ≤
      bipartiteMixedChargeTarget A n (reciprocalTinyThreshold t) := by
  have hsmall0 : 0 ≤ P.smallObjectStarCharge v := by
    unfold TinyThresholdPacketization.smallObjectStarCharge
    exact Finset.sum_nonneg fun o _ho ↦ by
      split
      · exact harmonicCharge_nonneg _
      · exact le_rfl
  have hsplit := P.core_add_small_starCharge v
  have hmixed := P.mixedObject_starCharge_le_target ht hstar hcharge v
  linarith

/-- The finite core really is above the reciprocal cutoff represented by
the `2*t` finite harmonic classes. -/
theorem TinyThresholdPacketization.coreObject_weight_ge_inv_two_mul
    (o : P.coreObjectGraph.E) :
    (1 : ℝ) / (2 * t : ℕ) ≤ P.coreObjectGraph.weight o := by
  rw [inv_double_eq_reciprocalTinyThreshold]
  exact P.coreObjectGraph_weight_ge o

/-- Canonical finite harmonic class used by the threshold construction. -/
abbrev TinyThresholdPacketization.coreHarmonicClass
    (ht : 0 < t) : P.coreObjectGraph.E → Fin (2 * t) :=
  P.coreObjectGraph.finiteHarmonicClassOf (2 * t) (Nat.mul_pos (by decide) ht)
    P.coreObject_weight_ge_inv_two_mul

theorem TinyThresholdPacketization.coreHarmonicClass_weight_le
    (ht : 0 < t) (e : P.coreObjectGraph.E) :
    P.coreObjectGraph.weight e ≤
      (1 : ℝ) / finiteClassSize (P.coreHarmonicClass ht e) :=
  P.coreObjectGraph.weight_le_inv_finiteClassSize_finiteHarmonicClassOf
    (2 * t) (Nat.mul_pos (by decide) ht)
    P.coreObject_weight_ge_inv_two_mul e

theorem TinyThresholdPacketization.coreHarmonicClass_charge
    (ht : 0 < t) (e : P.coreObjectGraph.E) :
    harmonicCharge (P.coreObjectGraph.weight e) =
      (1 : ℝ) / finiteClassSize (P.coreHarmonicClass ht e) :=
  P.coreObjectGraph.harmonicCharge_eq_inv_finiteClassSize_finiteHarmonicClassOf
    (2 * t) (Nat.mul_pos (by decide) ht)
    P.coreObject_weight_ge_inv_two_mul e

/-- The even target palette colors the full finite-class packet skeleton. -/
theorem TinyThresholdPacketization.exists_targetPacketColoringCertificate
    (ht : 0 < t) {n : ℕ} {A gamma : ℝ}
    (hgamma : 0 ≤ gamma)
    (hstar : ∀ v, G.starWeight v ≤ n)
    (hcharge : ∀ v, G.starCharge harmonicCharge v ≤ A) :
    Nonempty
      (P.coreObjectGraph.FiniteHarmonicPacketColoringCertificate
        P.coreBipartition (P.coreHarmonicClass ht)
        (evenCeilingPalette (bipartitePaletteTarget A n
          (reciprocalTinyThreshold t) gamma))) := by
  let tau := reciprocalTinyThreshold t
  let Q := bipartiteMixedChargeTarget A n tau
  let margin := tau / (1 - tau) * n + gamma * n
  let K := evenCeilingPalette (bipartitePaletteTarget A n tau gamma)
  have hT : 0 < 2 * t := Nat.mul_pos (by decide) ht
  have htau0 : 0 ≤ tau := (reciprocalTinyThreshold_pos ht).le
  have htauHalf : tau ≤ (1 : ℝ) / 2 :=
    reciprocalTinyThreshold_le_half (Nat.one_le_iff_ne_zero.mpr ht.ne')
  have htau1 : tau < 1 := by linarith
  have hmargin : 0 ≤ margin := by
    have hden : 0 ≤ 1 - tau := (sub_pos.mpr htau1).le
    dsimp [margin]
    exact add_nonneg
      (mul_nonneg (div_nonneg htau0 hden) (Nat.cast_nonneg n))
      (mul_nonneg hgamma (Nat.cast_nonneg n))
  have hpalette : Q + margin ≤ (K : ℝ) := by
    calc
      Q + margin = bipartitePaletteTarget A n tau gamma := by
        dsimp [Q, margin, bipartitePaletteTarget]
        ring
      _ ≤ (K : ℝ) := by
        dsimp [K]
        exact le_evenCeilingPalette _
  have horiginal : ∀ v,
      (∑ e : P.coreObjectGraph.E,
        if P.coreObjectGraph.Inc v e then
          harmonicCharge (P.coreObjectGraph.weight e) else 0) ≤ Q := by
    intro v
    have h := P.coreObject_starCharge_le_target ht hstar hcharge v
    rw [P.coreObjectGraph.starCharge_eq_edgeStarCharge,
      P.coreObjectGraph.edgeStarCharge_eq_inc_sum] at h
    exact h
  simpa [K, Q, margin, TinyThresholdPacketization.coreHarmonicClass] using
    P.coreObjectGraph.exists_finiteHarmonicPacketColoringCertificate_of_weight_ge_inv
      (2 * t) hT P.coreObject_weight_ge_inv_two_mul P.coreBipartition K
      (evenCeilingPalette_pos _) Q margin hmargin hpalette horiginal

namespace FiniteHarmonicPacketColoringCertificate

variable {P : G.TinyThresholdPacketization b (reciprocalTinyThreshold t)}
variable {n : ℕ} {A gamma : ℝ}

theorem jointResidualStarCharge_nonneg_of_tau_lt_one
    {tau : ℝ} {P : G.TinyThresholdPacketization b tau}
    {T K : ℕ} {classOf : P.coreObjectGraph.E → Fin T}
    (C : P.coreObjectGraph.FiniteHarmonicPacketColoringCertificate
      P.coreBipartition classOf K)
    (htau1 : tau < 1) (v : G.V) :
    0 ≤ C.jointResidualStarCharge v := by
  unfold jointResidualStarCharge
  exact Finset.sum_nonneg fun e _he ↦ C.jointResidualCharge_nonneg htau1 e.1

/-- The chosen palette leaves `gamma*n` colors beyond the complete joint
residual artificial charge at every vertex. -/
theorem jointResidualStarCharge_add_slack_le_missingColors
    (ht : 0 < t)
    (C : P.coreObjectGraph.FiniteHarmonicPacketColoringCertificate
      P.coreBipartition (P.coreHarmonicClass ht)
      (evenCeilingPalette (bipartitePaletteTarget A n
        (reciprocalTinyThreshold t) gamma)))
    (hgamma : 0 ≤ gamma)
    (hstar : ∀ v, G.starWeight v ≤ n)
    (hcharge : ∀ v, G.starCharge harmonicCharge v ≤ A)
    (v : G.V) :
    C.jointResidualStarCharge v + gamma * n ≤
      ((P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
        (C.ambientBaseColor (evenCeilingPalette_pos _)) v).card : ℝ) := by
  let tau := reciprocalTinyThreshold t
  let Q := bipartiteMixedChargeTarget A n tau
  let K := evenCeilingPalette (bipartitePaletteTarget A n tau gamma)
  have htau0 : 0 ≤ tau := (reciprocalTinyThreshold_pos ht).le
  have htau1 : tau < 1 := by
    have htauHalf := reciprocalTinyThreshold_le_half
      (Nat.one_le_iff_ne_zero.mpr ht.ne')
    linarith
  have hclassCharge : ∀ e : P.coreObjectGraph.E,
      harmonicCharge (P.coreObjectGraph.weight e) =
        (1 : ℝ) / finiteClassSize (P.coreHarmonicClass ht e) :=
    P.coreHarmonicClass_charge ht
  have hmixed : P.mixedObjectGraph.starCharge harmonicCharge v ≤ Q :=
    P.mixedObject_starCharge_le_target ht hstar hcharge v
  have hsmall : P.smallObjectStarWeight v ≤ (n : ℝ) :=
    (P.smallObjectStarWeight_le_original v).trans (hstar v)
  have hpalette : Q + tau / (1 - tau) * n + gamma * n ≤ (K : ℝ) := by
    dsimp [Q, K, bipartitePaletteTarget]
    exact le_evenCeilingPalette _
  simpa [tau, Q, K] using
    C.jointResidualStarCharge_add_gap_le_missingColors
      (evenCeilingPalette_pos _) hclassCharge Q (gamma * n) n htau0 htau1
      (mul_nonneg hgamma (Nat.cast_nonneg n)) (Nat.cast_nonneg n)
      hmixed hsmall hpalette

end FiniteHarmonicPacketColoringCertificate

end

end WeightedMultigraph
end WeightedEdgeColoring
