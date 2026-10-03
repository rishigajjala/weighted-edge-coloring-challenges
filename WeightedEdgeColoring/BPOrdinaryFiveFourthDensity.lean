import WeightedEdgeColoring.BPGeneralPacketSlack

/-!
# The exact ordinary theorem needed by the general packet range

The full near-fractional edge-colouring theorem is stronger than what the
packet proof uses.  In the packet graph the maximum degree is at most `Q`,
whereas the odd-set target is

`L = max (2 n) ((5 / 4) Q)`.

Thus the classical `m = 5` Andersen--Goldberg theorem is already enough.
This file states that theorem as one explicit boundary and checks the whole
numerical reduction to the packet-specific ordinary-colouring interface.
-/

namespace WeightedEdgeColoring

universe u

/-- Certificate form of the classical `m = 5` theorem.  Above the
`(5 Delta + 2) / 4` threshold, failure of a `k`-edge-colouring produces one
odd vertex set whose edge count is too large for `k` matchings. -/
def OrdinaryMultigraphFiveFourthOddSetCertificate : Prop :=
  ∀ (G : WeightedMultigraph.{u}) (F : Finset G.E) (A : ℝ) (k : ℕ),
    0 ≤ A →
    0 < k →
    (∀ v, (G.degreeOn F v : ℝ) ≤ A) →
    (5 / 4 : ℝ) * A + 1 / 2 < (k : ℝ) + 1 →
    (¬ ∃ color : G.E → Fin k, G.IsProperOn F color) →
    ∃ S : Finset G.V, Odd S.card ∧ 3 ≤ S.card ∧
      (k : ℝ) * ((S.card : ℝ) - 1) <
        (2 : ℝ) * (G.internalEdges F S).card

/-- The sharp integer form of the `m = 5` critical-graph step.

If `k + 1` lies strictly above the Andersen--Goldberg threshold
`5 A / 4 + 1 / 2`, then every obstruction to a `k`-edge-colouring must
violate an odd-set inequality at level `k`.  This is the precise
Tashkinov-style statement used below.  All packet estimates and all real to
integer rounding are proved in this file; only this recolouring statement is
left as an explicit input. -/
def OrdinaryMultigraphFiveFourthObstructionColoring : Prop :=
  ∀ (G : WeightedMultigraph.{u}) (F : Finset G.E) (A : ℝ) (k : ℕ),
    0 ≤ A →
    0 < k →
    (∀ v, (G.degreeOn F v : ℝ) ≤ A) →
    (5 / 4 : ℝ) * A + 1 / 2 < (k : ℝ) + 1 →
    G.OddSetDensityAtMost F (k : ℝ) →
    ∃ color : G.E → Fin k, G.IsProperOn F color

/-- The odd-set-certificate and obstruction-colouring formulations are
logically equivalent.  This proof contains no graph theory; it only unfolds
the odd-set inequality. -/
theorem ordinaryMultigraphFiveFourthOddSetCertificate_iff_obstructionColoring :
    OrdinaryMultigraphFiveFourthOddSetCertificate.{u} ↔
      OrdinaryMultigraphFiveFourthObstructionColoring.{u} := by
  constructor
  · intro hcertificate G F A k hA hk hdegree hthreshold hodd
    by_contra hnoColor
    obtain ⟨S, hSodd, hS3, hviolate⟩ :=
      hcertificate G F A k hA hk hdegree hthreshold hnoColor
    have hbound := hodd S hSodd hS3
    linarith
  · intro hcoloring G F A k hA hk hdegree hthreshold hnoColor
    by_contra hnoCertificate
    push_neg at hnoCertificate
    have hodd : G.OddSetDensityAtMost F (k : ℝ) := by
      intro S hSodd hS3
      exact hnoCertificate S hSodd hS3
    exact hnoColor (hcoloring G F A k hA hk hdegree hthreshold hodd)

/-- The `m = 5` Andersen--Goldberg edge-colouring statement, in the only
form needed here.  Its published formulation says that a non-elementary
multigraph has chromatic index at most `(5 Delta + 2) / 4`; an elementary
multigraph is controlled by its odd-set density.  The harmless `+1` below
absorbs both integer roundings.

This is intentionally kept separate from
`OrdinaryMultigraphNearFractionalColoring`: it is a strictly weaker input
and is the precise remaining recolouring theorem for the packet range. -/
def OrdinaryMultigraphFiveFourthDensityColoring : Prop :=
  ∀ (G : WeightedMultigraph.{u}) (F : Finset G.E) (A L : ℝ),
    0 ≤ A →
    0 ≤ L →
    (∀ v, (G.degreeOn F v : ℝ) ≤ A) →
    G.OddSetDensityAtMost F L →
    ∃ q : ℕ, 0 < q ∧
      (q : ℝ) ≤ max L ((5 / 4 : ℝ) * A) + 1 ∧
      ∃ color : G.E → Fin q, G.IsProperOn F color

/-- The critical obstruction statement gives the real-valued density form
with only one colour of integer rounding. -/
theorem ordinaryMultigraphFiveFourthDensityColoring_of_obstruction
    (hcritical : OrdinaryMultigraphFiveFourthObstructionColoring.{u}) :
    OrdinaryMultigraphFiveFourthDensityColoring.{u} := by
  intro G F A L hA hL hdegree hodd
  let M : ℝ := max L ((5 / 4 : ℝ) * A)
  let k : ℕ := max 1 (Nat.ceil M)
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact le_max_of_le_left hL
  have hk : 0 < k := by
    dsimp [k]
    omega
  have hMle : M ≤ (k : ℝ) := by
    calc
      M ≤ (Nat.ceil M : ℕ) := Nat.le_ceil M
      _ ≤ (k : ℕ) := by
        exact_mod_cast
          (show Nat.ceil M ≤ k by
            dsimp [k]
            exact le_max_right 1 (Nat.ceil M))
  have hkUpper : (k : ℝ) ≤ M + 1 := by
    have hone : (1 : ℝ) ≤ M + 1 := by linarith
    have hceil : ((Nat.ceil M : ℕ) : ℝ) ≤ M + 1 :=
      (Nat.ceil_lt_add_one hM0).le
    dsimp [k]
    push_cast
    exact max_le hone hceil
  have hthreshold :
      (5 / 4 : ℝ) * A + 1 / 2 < (k : ℝ) + 1 := by
    have hbranch : (5 / 4 : ℝ) * A ≤ M := by
      exact le_max_right _ _
    linarith
  have hoddK : G.OddSetDensityAtMost F (k : ℝ) := by
    intro S hSodd hS3
    have hbase := hodd S hSodd hS3
    have hLK : L ≤ (k : ℝ) :=
      (le_max_left L ((5 / 4 : ℝ) * A)).trans hMle
    have hfactor : (0 : ℝ) ≤ (S.card : ℝ) - 1 := by
      exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ S.card by omega))
    exact hbase.trans (mul_le_mul_of_nonneg_right hLK hfactor)
  obtain ⟨color, hproper⟩ :=
    hcritical G F A k hA hk hdegree hthreshold hoddK
  refine ⟨k, hk, ?_, color, hproper⟩
  simpa [M] using hkUpper

/-- Packet-specific ordinary edge colouring.  This is the smallest
asymptotic interface used when building the colored packet base. -/
def ChargeSensitivePacketOrdinaryColoring : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N : ℕ,
    ∀ (G : WeightedMultigraph.{u}) (F : Finset G.E)
      (n : ℕ) (Q : ℝ),
      N ≤ n →
      0 ≤ Q →
      Q ≤ 2 * (n : ℝ) →
      (∀ v, (G.degreeOn F v : ℝ) ≤ Q) →
      G.TriangleEdgeCountAtMost F (2 * (n : ℝ)) →
      ∃ q : ℕ, 0 < q ∧
        (q : ℝ) ≤
          max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q) + η * n ∧
        ∃ color : G.E → Fin q, G.IsProperOn F color

/-- The standard near-fractional theorem implies the much narrower packet
interface.  This records that the new boundary is a genuine weakening of
the old one. -/
theorem chargeSensitivePacketOrdinaryColoring_of_nearFractional
    (hordinary : OrdinaryMultigraphNearFractionalColoring.{u}) :
    ChargeSensitivePacketOrdinaryColoring.{u} := by
  intro η hη
  obtain ⟨N, hN⟩ := hordinary (5 / 2 : ℝ) η (by norm_num) hη
  refine ⟨N, ?_⟩
  intro G F n Q hn hQ0 hQ2 hdegree htriangle
  let L : ℝ := max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact le_max_of_le_left (mul_nonneg (by norm_num) hn0)
  have hLupper : L ≤ (5 / 2 : ℝ) * n := by
    dsimp [L]
    apply max_le <;> nlinarith
  have hdegreeL : ∀ v, (G.degreeOn F v : ℝ) ≤ L := by
    intro v
    calc
      (G.degreeOn F v : ℝ) ≤ Q := hdegree v
      _ ≤ (5 / 4 : ℝ) * Q := by nlinarith
      _ ≤ L := le_max_right _ _
  have hodd : G.OddSetDensityAtMost F L := by
    dsimp [L]
    exact G.oddSetDensityAtMost_max_two_fiveFourth
      F (n : ℝ) Q hn0 hQ0 hdegree htriangle
  simpa [L] using hN G F n L hn hL0 hLupper hdegreeL hodd

/-- The classical `m = 5` theorem implies the packet-specific interface.
Only its additive rounding constant has to be absorbed into `η n`. -/
theorem chargeSensitivePacketOrdinaryColoring_of_fiveFourthDensity
    (hfive : OrdinaryMultigraphFiveFourthDensityColoring.{u}) :
    ChargeSensitivePacketOrdinaryColoring.{u} := by
  intro η hη
  let N : ℕ := Nat.ceil (1 / η)
  refine ⟨N, ?_⟩
  intro G F n Q hn hQ0 hQ2 hdegree htriangle
  let L : ℝ := max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact le_max_of_le_left (mul_nonneg (by norm_num) hn0)
  have hodd : G.OddSetDensityAtMost F L := by
    dsimp [L]
    exact G.oddSetDensityAtMost_max_two_fiveFourth
      F (n : ℝ) Q hn0 hQ0 hdegree htriangle
  obtain ⟨q, hq, hqBound, color, hproper⟩ :=
    hfive G F Q L hQ0 hL0 hdegree hodd
  have hbranch : (5 / 4 : ℝ) * Q ≤ L := by
    exact le_max_right _ _
  have hmax : max L ((5 / 4 : ℝ) * Q) = L :=
    max_eq_left hbranch
  have hNreal : (1 : ℝ) / η ≤ n := by
    calc
      (1 : ℝ) / η ≤ (N : ℕ) := Nat.le_ceil _
      _ ≤ (n : ℕ) := by exact_mod_cast hn
  have hone : (1 : ℝ) ≤ η * n := by
    have := (div_le_iff₀ hη).mp hNreal
    simpa [mul_comm] using this
  refine ⟨q, hq, ?_, color, hproper⟩
  rw [hmax] at hqBound
  exact hqBound.trans (by linarith)

/-- Direct packet interface from the sharp `m = 5` obstruction theorem. -/
theorem chargeSensitivePacketOrdinaryColoring_of_fiveFourthObstruction
    (hcritical : OrdinaryMultigraphFiveFourthObstructionColoring.{u}) :
    ChargeSensitivePacketOrdinaryColoring.{u} :=
  chargeSensitivePacketOrdinaryColoring_of_fiveFourthDensity
    (ordinaryMultigraphFiveFourthDensityColoring_of_obstruction hcritical)

end WeightedEdgeColoring
