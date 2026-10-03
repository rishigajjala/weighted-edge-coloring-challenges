import WeightedEdgeColoring.BPGeneralOddSetDensity
import WeightedEdgeColoring.GeneralPacketization
import WeightedEdgeColoring.HarmonicBinCharge
import WeightedEdgeColoring.BPLocalCharge

/-!
# Palette slack for the general charge-sensitive packet proof

The packet graph is coloured near
`max (2n) ((5/4)Q)`.  Since harmonic charge is at most twice physical
weight, we may take `Q ≤ 2n`.  The displayed maximum then exceeds `Q` by
at least `(2/5)n`.  This file proves that arithmetic fact and turns it into
an exact missing-colour bound after padding an ordinary proper colouring.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

universe u

theorem harmonicCharge_le_two_mul_weight {w : ℝ}
    (hw : 0 < w) (hw1 : w ≤ 1) :
    harmonicCharge w ≤ 2 * w := by
  have h := harmonicCharge_le_mul_weight (t := 1) (by norm_num) hw
    (by simpa using hw1)
  norm_num at h ⊢
  exact h

namespace WeightedMultigraph

variable (G : WeightedMultigraph.{u})

theorem harmonicStarCharge_le_two_starWeight (v : G.V) :
    G.starCharge harmonicCharge v ≤ 2 * G.starWeight v := by
  unfold starCharge starWeight
  calc
    (∑ e : G.StarEdge v, harmonicCharge (G.weight e.1)) ≤
        ∑ e : G.StarEdge v, 2 * G.weight e.1 := by
      exact Finset.sum_le_sum fun e _he ↦
        harmonicCharge_le_two_mul_weight
          (G.weight_pos e.1) (G.weight_le_one e.1)
    _ = 2 * ∑ e : G.StarEdge v, G.weight e.1 := by
      rw [Finset.mul_sum]

theorem harmonicStarCharge_le_two_mul_of_starWeight_le
    {n : ℕ} (hstar : ∀ v, G.starWeight v ≤ n) (v : G.V) :
    G.starCharge harmonicCharge v ≤ 2 * (n : ℝ) := by
  calc
    G.starCharge harmonicCharge v ≤ 2 * G.starWeight v :=
      G.harmonicStarCharge_le_two_starWeight v
    _ ≤ 2 * (n : ℝ) := mul_le_mul_of_nonneg_left (hstar v) (by norm_num)

/-- The worst charge-sensitive palette slack occurs when `Q = (8/5)n`.
It is exactly `(2/5)n`. -/
theorem charge_add_two_fifths_le_max_two_fiveFourth
    (n Q : ℝ) (hn : 0 ≤ n) (hQ0 : 0 ≤ Q) (hQ2 : Q ≤ 2 * n) :
    Q + (2 / 5 : ℝ) * n ≤
      max (2 * n) ((5 / 4 : ℝ) * Q) := by
  by_cases h : Q ≤ (8 / 5 : ℝ) * n
  · calc
      Q + (2 / 5 : ℝ) * n ≤ 2 * n := by linarith
      _ ≤ max (2 * n) ((5 / 4 : ℝ) * Q) := le_max_left _ _
  · have hQ : (8 / 5 : ℝ) * n ≤ Q := le_of_not_ge h
    calc
      Q + (2 / 5 : ℝ) * n ≤ (5 / 4 : ℝ) * Q := by
        nlinarith
      _ ≤ max (2 * n) ((5 / 4 : ℝ) * Q) := le_max_right _ _

/-- Cast a proper edge colouring into a larger palette. -/
def padProperColor {q K : ℕ} (hqK : q ≤ K)
    (color : G.E → Fin q) : G.E → Fin K :=
  fun e ↦ Fin.castLE hqK (color e)

theorem isProperOn_padProperColor {q K : ℕ} (hqK : q ≤ K)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) :
    G.IsProperOn F (G.padProperColor hqK color) := by
  intro v e he f hf hef
  apply hproper v he hf
  exact Fin.castLE_inj.mp hef

/-- Pad a near-fractional ordinary colouring until the real target `L` is
also below the integer palette.  The padding costs less than one colour. -/
theorem exists_padded_properColoring
    (F : Finset G.E) (n q : ℕ) (L η : ℝ)
    (hL0 : 0 ≤ L) (hη0 : 0 ≤ η) (hq : 0 < q)
    (hqBound : (q : ℝ) ≤ L + η * n)
    (color : G.E → Fin q) (hproper : G.IsProperOn F color) :
    ∃ K : ℕ, ∃ padded : G.E → Fin K,
      0 < K ∧ L ≤ (K : ℝ) ∧
      (K : ℝ) ≤ L + η * n + 1 ∧
      G.IsProperOn F padded := by
  let K : ℕ := max q (Nat.ceil L)
  have hqK : q ≤ K := le_max_left _ _
  have hceilK : Nat.ceil L ≤ K := le_max_right _ _
  let padded : G.E → Fin K := G.padProperColor hqK color
  refine ⟨K, padded, hq.trans_le hqK, ?_, ?_,
    G.isProperOn_padProperColor hqK F color hproper⟩
  · exact (Nat.le_ceil L).trans (by exact_mod_cast hceilK)
  · have hceil : ((Nat.ceil L : ℕ) : ℝ) ≤ L + 1 :=
      (Nat.ceil_lt_add_one hL0).le
    have hq' : (q : ℝ) ≤ L + η * n + 1 :=
      hqBound.trans (le_add_of_nonneg_right zero_le_one)
    have hc' : ((Nat.ceil L : ℕ) : ℝ) ≤ L + η * n + 1 := by
      calc
        ((Nat.ceil L : ℕ) : ℝ) ≤ L + 1 := hceil
        _ ≤ L + η * n + 1 := by
          have : 0 ≤ η * (n : ℝ) :=
            mul_nonneg hη0 (Nat.cast_nonneg n)
          linarith
    dsimp [K]
    push_cast
    exact max_le hq' hc'

/-- Charge accounting plus the padded target gives the exact missing-palette
margin needed by the residual completion theorem. -/
theorem residualCharge_add_two_fifths_le_missingColors
    {K : ℕ} (hK : 0 < K) (F : Finset G.E)
    (base : G.E → Fin K) (hproper : G.IsProperOn F base)
    (n Q residualCharge : ℝ)
    (hn : 0 ≤ n) (hQ0 : 0 ≤ Q) (hQ2 : Q ≤ 2 * n)
    (hresidual0 : 0 ≤ residualCharge)
    (haccount : (G.degreeOn F v : ℝ) + residualCharge ≤ Q)
    (hpalette : max (2 * n) ((5 / 4 : ℝ) * Q) ≤ (K : ℝ)) :
    residualCharge + (2 / 5 : ℝ) * n ≤
      ((G.missingColorsAt F base v).card : ℝ) := by
  have htarget :=
    charge_add_two_fifths_le_max_two_fiveFourth n Q hn hQ0 hQ2
  have hdK : G.degreeOn F v ≤ K := by
    have hdQ : (G.degreeOn F v : ℝ) ≤ Q := by linarith
    have hQK : Q ≤ (K : ℝ) := by
      calc
        Q ≤ Q + (2 / 5 : ℝ) * n := by nlinarith
        _ ≤ max (2 * n) ((5 / 4 : ℝ) * Q) := htarget
        _ ≤ (K : ℝ) := hpalette
    exact_mod_cast hdQ.trans hQK
  have hcard := G.card_missingColorsAt F base hproper v
  rw [hcard, Nat.cast_sub hdK]
  have hsum :
      (G.degreeOn F v : ℝ) + residualCharge +
          (2 / 5 : ℝ) * n ≤ (K : ℝ) := by
    calc
      (G.degreeOn F v : ℝ) + residualCharge + (2 / 5 : ℝ) * n ≤
          Q + (2 / 5 : ℝ) * n := by linarith
      _ ≤ max (2 * n) ((5 / 4 : ℝ) * Q) := htarget
      _ ≤ (K : ℝ) := hpalette
  linarith

namespace Packetization

/-- The same reserve calculation for an expanded packet coloring.  The base
coloring need only be proper on packets: physical edges inside one packet
may share their color. -/
theorem residualCharge_add_two_fifths_le_expandedMissingColors
    (P : G.Packetization) {K : ℕ} (S : Finset P.Packet)
    (base : P.Packet → Fin K)
    (hproper : P.groupedGraph.IsProperOn S base)
    (n Q residualCharge : ℝ)
    (hn : 0 ≤ n) (hQ0 : 0 ≤ Q) (hQ2 : Q ≤ 2 * n)
    (hresidual0 : 0 ≤ residualCharge)
    (haccount : (P.groupedGraph.degreeOn S v : ℝ) + residualCharge ≤ Q)
    (hpalette : max (2 * n) ((5 / 4 : ℝ) * Q) ≤ (K : ℝ)) :
    residualCharge + (2 / 5 : ℝ) * n ≤
      ((G.missingColorsAt (P.originalEdgesOfPackets S)
        (P.expandColor base) v).card : ℝ) := by
  have htarget :=
    charge_add_two_fifths_le_max_two_fiveFourth n Q hn hQ0 hQ2
  have hdK : P.groupedGraph.degreeOn S v ≤ K := by
    have hdQ : (P.groupedGraph.degreeOn S v : ℝ) ≤ Q := by linarith
    have hQK : Q ≤ (K : ℝ) := by
      calc
        Q ≤ Q + (2 / 5 : ℝ) * n := by nlinarith
        _ ≤ max (2 * n) ((5 / 4 : ℝ) * Q) := htarget
        _ ≤ (K : ℝ) := hpalette
    exact_mod_cast hdQ.trans hQK
  rw [P.card_missingColorsAt_expandColor S base hproper v,
    Nat.cast_sub hdK]
  have hsum :
      (P.groupedGraph.degreeOn S v : ℝ) + residualCharge +
          (2 / 5 : ℝ) * n ≤ (K : ℝ) := by
    calc
      (P.groupedGraph.degreeOn S v : ℝ) + residualCharge +
            (2 / 5 : ℝ) * n ≤ Q + (2 / 5 : ℝ) * n := by linarith
      _ ≤ max (2 * n) ((5 / 4 : ℝ) * Q) := htarget
      _ ≤ (K : ℝ) := hpalette
  linarith

end Packetization

end WeightedMultigraph
end WeightedEdgeColoring
