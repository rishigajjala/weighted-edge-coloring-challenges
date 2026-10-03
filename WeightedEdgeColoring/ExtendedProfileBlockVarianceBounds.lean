import WeightedEdgeColoring.ExtendedProfileBlockVarianceRows
import WeightedEdgeColoring.ExtendedProfileBlockCandidateCapacityRows
import WeightedEdgeColoring.FiniteDependentWordBlockMoments

/-!
# Concrete envelopes and expectations for block variance

This file instantiates the generic independent-block moment bound with the
extended-profile option mass.  The common one-coordinate upper envelope is
read from the already proved candidate-capacity scale.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})
variable {B k : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

local instance : DecidableEq G.V := Classical.decEq G.V
local instance (center source : G.V) (e : G.E) :
    Decidable (G.CandidateEdgeMatches center source e) :=
  Classical.propDecidable _

/-- Uniform upper bound for the total one-colour option mass. -/
def extendedProfileCoordinateOptionUpper
    (rho s omega β q r : ℝ) (B k : ℕ) : ℝ :=
  ((explicitLargeSlotBound β q r : ℝ) + 1) *
    extendedProfileCandidateCapacityScale rho s omega β q r / (B * k)

/-- Exact one-colour target mean. -/
def extendedProfileCoordinateOptionMean
    (rho s : ℝ) (B k : ℕ) : ℝ :=
  rho * s / (B * k)

/-- Pointwise envelope for the squared error of one complete block. -/
def extendedProfileBlockVariancePairScale
    (rho s omega β q r : ℝ) (B k : ℕ) : ℝ :=
  (k * extendedProfileCoordinateOptionUpper rho s omega β q r B k +
    rho * s / B) ^ 2

/-- Envelope for one conditional star sum. -/
def extendedProfileBlockVarianceSelfScale
    (rho s omega β q r : ℝ) (B k : ℕ) : ℝ :=
  (B * k) * extendedProfileBlockVariancePairScale
    rho s omega β q r B k

/-- Uniform bound on the fully averaged total block variance at one star. -/
def extendedProfileBlockVarianceMeanBound
    (rho s omega β q r : ℝ) (B k : ℕ) : ℝ :=
  ((B * k : ℕ) : ℝ) ^ 2 *
    extendedProfileCoordinateOptionUpper rho s omega β q r B k *
      extendedProfileCoordinateOptionMean rho s B k

/-- Polynomial column bound for both variance row families. -/
def extendedProfileBlockVarianceColumnBound
    (B k : ℕ) (β q r : ℝ) : ℝ :=
  (extendedProfileStateBound β q r : ℝ) ^ k * (B * k) + 1

/-- Parameter-only numerator of the block error envelope.  Writing the
scales through this quantity makes the dependence on the number of blocks
transparent. -/
def extendedProfileBlockVarianceAmplitude
    (rho s omega β q r : ℝ) : ℝ :=
  ((explicitLargeSlotBound β q r : ℝ) + 1) *
      extendedProfileCandidateCapacityScale rho s omega β q r +
    rho * s

theorem extendedProfileBlockCoordinateEnvelope_eq_amplitude_div
    (hB : 0 < B) (hk : 0 < k) :
    k * extendedProfileCoordinateOptionUpper
          rho s omega β q r B k + rho * s / B =
      extendedProfileBlockVarianceAmplitude rho s omega β q r / B := by
  have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  unfold extendedProfileCoordinateOptionUpper
    extendedProfileBlockVarianceAmplitude
  push_cast
  field_simp [hBR, hkR]

theorem extendedProfileBlockVariancePairScale_eq
    (hB : 0 < B) (hk : 0 < k) :
    extendedProfileBlockVariancePairScale rho s omega β q r B k =
      (extendedProfileBlockVarianceAmplitude rho s omega β q r / B) ^ 2 := by
  unfold extendedProfileBlockVariancePairScale
  rw [extendedProfileBlockCoordinateEnvelope_eq_amplitude_div
    (B := B) (k := k) hB hk]

theorem B_mul_extendedProfileBlockVariancePairScale_eq
    (hB : 0 < B) (hk : 0 < k) :
    B * extendedProfileBlockVariancePairScale rho s omega β q r B k =
      (extendedProfileBlockVarianceAmplitude rho s omega β q r) ^ 2 / B := by
  have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  rw [extendedProfileBlockVariancePairScale_eq
    (B := B) (k := k) hB hk]
  field_simp [hBR]

theorem B_sq_mul_extendedProfileBlockVariancePairScale_eq
    (hB : 0 < B) (hk : 0 < k) :
    B * B * extendedProfileBlockVariancePairScale
        rho s omega β q r B k =
      (extendedProfileBlockVarianceAmplitude rho s omega β q r) ^ 2 := by
  have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  rw [extendedProfileBlockVariancePairScale_eq
    (B := B) (k := k) hB hk]
  field_simp [hBR]

theorem B_mul_extendedProfileBlockVarianceSelfScale_eq
    (hB : 0 < B) (hk : 0 < k) :
    B * extendedProfileBlockVarianceSelfScale rho s omega β q r B k =
      k * (extendedProfileBlockVarianceAmplitude rho s omega β q r) ^ 2 := by
  have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  unfold extendedProfileBlockVarianceSelfScale
  rw [extendedProfileBlockVariancePairScale_eq
    (B := B) (k := k) hB hk]
  push_cast
  field_simp [hBR]

theorem extendedProfileBlockVarianceMeanBound_eq
    (hB : 0 < B) (hk : 0 < k) :
    extendedProfileBlockVarianceMeanBound rho s omega β q r B k =
      ((explicitLargeSlotBound β q r : ℝ) + 1) *
        extendedProfileCandidateCapacityScale rho s omega β q r *
          (rho * s) := by
  have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  unfold extendedProfileBlockVarianceMeanBound
    extendedProfileCoordinateOptionUpper extendedProfileCoordinateOptionMean
  push_cast
  field_simp [hBR, hkR]

/-- Atom-level form of the coordinate option mass. -/
def extendedProfileCoordinateOptionMass
    (rho omega : ℝ) (e : G.E)
    (P : G.ExtendedProfileState R0 (G.fst e))
    (Q : G.ExtendedProfileState R0 (G.snd e)) : ℝ :=
  (∑ i, ∑ l,
    G.extendedProfileProductOptionMass R0 rho omega e P Q i l) +
  G.extendedProfileTinyProductOptionMass R0 rho omega e P Q

theorem extendedProfileCoordinateOptionMass_nonneg
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (e : G.E)
    (P : G.ExtendedProfileState R0 (G.fst e))
    (Q : G.ExtendedProfileState R0 (G.snd e)) :
    0 ≤ G.extendedProfileCoordinateOptionMass R0 rho omega e P Q := by
  unfold extendedProfileCoordinateOptionMass
  exact add_nonneg
    (Finset.sum_nonneg fun i _hi ↦ Finset.sum_nonneg fun l _hl ↦
      G.extendedProfileProductOptionMass_nonneg R0 hs hn hq hr0 hleft
        homega0 homega1 hrho e P Q i l)
    (G.extendedProfileTinyProductOptionMass_nonneg R0 hs hn hq hr0 hleft
      homega0 homega1 hrho e P Q)

theorem extendedProfileCoordinateOptionMass_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (e : G.E)
    (P : G.ExtendedProfileState R0 (G.fst e))
    (Q : G.ExtendedProfileState R0 (G.snd e)) :
    G.extendedProfileCoordinateOptionMass R0 rho omega e P Q ≤
      extendedProfileCoordinateOptionUpper rho s omega β q r B k := by
  classical
  let n := B * k
  let scale := extendedProfileCandidateCapacityScale rho s omega β q r
  let c0 : Fin n := ⟨0, hn⟩
  let qCode : ExtendedProfilePackedWordState n β q r :=
    repeatedExtendedProfileAtomWord (n := n)
      (G.extendedProfileStateCode R0 (G.snd e) Q)
  have hlargeSlot : ∀ i : Fin (explicitLargeSlotBound β q r),
      (n : ℝ) * ∑ l,
          G.extendedProfileProductOptionMass R0 rho omega e P Q i l ≤
        scale := by
    intro i
    let row : G.ExtendedProfileLargeCandidateRow R0
        (n := n) (β := β) (q := q) (r := r) := {
      center := G.fst e
      color := c0
      candidate := P
      slot := i }
    have h := G.packedExtendedProfileLargeCandidateEdgeUse_le_scale R0
      hn hs hq hr0 hleft homega0 homega1 hrho
      (G.snd e) qCode e row
    dsimp [n, scale]
    simpa [packedExtendedProfileLargeCandidateEdgeUse, row, qCode, c0,
      G.noLoop e, Nat.cast_mul] using h
  have hlargeMul :
      (n : ℝ) * (∑ i, ∑ l,
        G.extendedProfileProductOptionMass R0 rho omega e P Q i l) ≤
        (explicitLargeSlotBound β q r : ℝ) * scale := by
    calc
      (n : ℝ) * (∑ i, ∑ l,
          G.extendedProfileProductOptionMass R0 rho omega e P Q i l) =
          ∑ i, (n : ℝ) * ∑ l,
            G.extendedProfileProductOptionMass R0 rho omega e P Q i l := by
        rw [Finset.mul_sum]
      _ ≤ ∑ _i : Fin (explicitLargeSlotBound β q r), scale :=
        Finset.sum_le_sum fun i _hi ↦ hlargeSlot i
      _ = (explicitLargeSlotBound β q r : ℝ) * scale := by simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlarge :
      (∑ i, ∑ l,
        G.extendedProfileProductOptionMass R0 rho omega e P Q i l) ≤
        (explicitLargeSlotBound β q r : ℝ) * scale / n := by
    apply (le_div_iff₀ hnR).2
    simpa [mul_comm] using hlargeMul
  let tinyRow : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r) := {
    center := G.fst e
    color := c0
    candidate := P }
  have htinyWeighted :=
    G.packedExtendedProfileTinyCandidateEdgeUse_le_weight_mul_scale R0
      hn hs hq hr0 hleft homega0 homega1 hrho
      (G.snd e) qCode e tinyRow
  have htinyMul :
      (n : ℝ) * G.extendedProfileTinyProductOptionMass
          R0 rho omega e P Q ≤ scale := by
    have hweighted :
        G.weight e * ((n : ℝ) *
          G.extendedProfileTinyProductOptionMass R0 rho omega e P Q) ≤
            G.weight e * scale := by
      dsimp [n, scale]
      simpa [packedExtendedProfileTinyCandidateEdgeUse, tinyRow, qCode, c0,
        G.noLoop e, Nat.cast_mul, mul_assoc, mul_left_comm] using htinyWeighted
    nlinarith [G.weight_pos e]
  have htiny :
      G.extendedProfileTinyProductOptionMass R0 rho omega e P Q ≤
        scale / n := by
    apply (le_div_iff₀ hnR).2
    simpa [mul_comm] using htinyMul
  unfold extendedProfileCoordinateOptionMass
    extendedProfileCoordinateOptionUpper
  dsimp [n, scale] at hlarge htiny ⊢
  push_cast at hlarge htiny ⊢
  exact (add_le_add hlarge htiny).trans_eq (by ring)

private theorem expected_largeCoordinateOptionMass
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (e : G.E) :
    (∑ P : G.ExtendedProfileState R0 (G.fst e),
      G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
        ∑ Q : G.ExtendedProfileState R0 (G.snd e),
          G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
            ∑ i, ∑ l,
              G.extendedProfileProductOptionMass R0 rho omega e P Q i l) =
      rho * G.extendedProfileEdgeColorMass
        (s := s) (β := β) (n := B * k) e := by
  let y := G.extendedProfileEdgeColorMass
    (s := s) (β := β) (n := B * k) e
  by_cases hy : y = 0
  · simp [extendedProfileProductOptionMass, pairedOption, y, hy]
  · have h := G.extendedProfileProductOptionMass_expectation R0
      (rho := rho)
      hs hq hr0 hleft homega0 homega1 hy
    calc
      (∑ P : G.ExtendedProfileState R0 (G.fst e),
        G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
          ∑ Q : G.ExtendedProfileState R0 (G.snd e),
            G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
              ∑ i, ∑ l,
                G.extendedProfileProductOptionMass R0 rho omega e P Q i l) =
          ∑ P : G.ExtendedProfileState R0 (G.fst e),
            G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
              ∑ i, ∑ Q : G.ExtendedProfileState R0 (G.snd e),
                G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
                  ∑ l, G.extendedProfileProductOptionMass
                    R0 rho omega e P Q i l := by
        apply Finset.sum_congr rfl
        intro P _hP
        congr 1
        calc
          (∑ Q : G.ExtendedProfileState R0 (G.snd e),
            G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
              ∑ i, ∑ l,
                G.extendedProfileProductOptionMass R0 rho omega e P Q i l) =
              ∑ Q, ∑ i,
                G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
                  ∑ l, G.extendedProfileProductOptionMass
                    R0 rho omega e P Q i l := by
            apply Finset.sum_congr rfl
            intro Q _hQ
            rw [Finset.mul_sum]
          _ = ∑ i, ∑ Q,
              G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
                ∑ l, G.extendedProfileProductOptionMass
                  R0 rho omega e P Q i l := by rw [Finset.sum_comm]
      _ = rho * G.extendedProfileEdgeColorMass
          (s := s) (β := β) (n := B * k) e := h

theorem expected_extendedProfileCoordinateOptionMass
    (hn : 0 < B * k) (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (e : G.E) :
    (∑ P : G.ExtendedProfileState R0 (G.fst e),
      G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
        ∑ Q : G.ExtendedProfileState R0 (G.snd e),
          G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
            G.extendedProfileCoordinateOptionMass R0 rho omega e P Q) =
      extendedProfileCoordinateOptionMean rho s B k := by
  have hlarge := G.expected_largeCoordinateOptionMass R0
    hn hs hq hr0 hleft homega0 homega1 rho e
  let yt := G.extendedProfileTinyEdgeColorMass
    (s := s) (β := β) (n := B * k) e
  have htiny :
      (∑ P : G.ExtendedProfileState R0 (G.fst e),
        G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
          ∑ Q : G.ExtendedProfileState R0 (G.snd e),
            G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
              G.extendedProfileTinyProductOptionMass R0 rho omega e P Q) =
        rho * yt := by
    by_cases hy : yt = 0
    · simp [extendedProfileTinyProductOptionMass, pairedOption, yt, hy]
    · simpa [yt] using G.extendedProfileTinyProductOptionMass_expectation
        R0 hs hq hr0 hleft homega0 homega1 hy
  have hsplit :
      G.extendedProfileEdgeColorMass
          (s := s) (β := β) (n := B * k) e + yt =
        s * ((1 : ℝ) / ((B * k : ℕ) : ℝ)) := by
    dsimp [yt]
    unfold extendedProfileEdgeColorMass extendedProfileTinyEdgeColorMass
    by_cases hlargeEdge : β ≤ G.weight e
    · simp [hlargeEdge, not_lt.mpr hlargeEdge]
    · have htinyEdge : G.weight e < β := lt_of_not_ge hlargeEdge
      simp [hlargeEdge, htinyEdge]
  unfold extendedProfileCoordinateOptionMass
    extendedProfileCoordinateOptionMean
  calc
    (∑ P : G.ExtendedProfileState R0 (G.fst e),
      G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
        ∑ Q : G.ExtendedProfileState R0 (G.snd e),
          G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
            ((∑ i, ∑ l,
                G.extendedProfileProductOptionMass R0 rho omega e P Q i l) +
              G.extendedProfileTinyProductOptionMass R0 rho omega e P Q)) =
        (∑ P : G.ExtendedProfileState R0 (G.fst e),
          G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
            ∑ Q : G.ExtendedProfileState R0 (G.snd e),
              G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
                ∑ i, ∑ l,
                  G.extendedProfileProductOptionMass R0 rho omega e P Q i l) +
        (∑ P : G.ExtendedProfileState R0 (G.fst e),
          G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
            ∑ Q : G.ExtendedProfileState R0 (G.snd e),
              G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
                G.extendedProfileTinyProductOptionMass R0 rho omega e P Q) := by
          simp_rw [mul_add, Finset.sum_add_distrib]
          simp_rw [mul_add, Finset.sum_add_distrib]
    _ = rho * G.extendedProfileEdgeColorMass
          (s := s) (β := β) (n := B * k) e + rho * yt := by
          rw [hlarge, htiny]
    _ = rho * (s * ((1 : ℝ) / ((B * k : ℕ) : ℝ))) := by
          rw [← mul_add, hsplit]
    _ = rho * s / ((B : ℝ) * (k : ℝ)) := by
          push_cast
          ring

@[simp] theorem extendedProfileBlockCoordinateOptionMass_eq_coordinate
    (rho omega : ℝ) (e : G.E)
    (fstCode sndCode : ExtendedProfilePackedBlockState k β q r)
    (j : Fin k) :
    G.extendedProfileBlockCoordinateOptionMass R0 rho omega e
        fstCode sndCode j =
      G.extendedProfileCoordinateOptionMass R0 rho omega e
        (G.decodeExtendedProfileBlock R0 (G.fst e) fstCode j)
        (G.decodeExtendedProfileBlock R0 (G.snd e) sndCode j) := by
  rfl

theorem extendedProfileCoordinateOptionUpper_nonneg
    (hn : 0 < B * k) (hrho : 0 ≤ rho) (hs : 0 ≤ s) :
    0 ≤ extendedProfileCoordinateOptionUpper rho s omega β q r B k := by
  unfold extendedProfileCoordinateOptionUpper
  exact div_nonneg
    (mul_nonneg (by positivity)
      (extendedProfileCandidateCapacityScale_nonneg
        (omega := omega) (β := β) (q := q) (r := r) hrho hs))
    (mul_nonneg (Nat.cast_nonneg B) (Nat.cast_nonneg k))

theorem extendedProfileBlockOptionMass_nonneg
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (e : G.E)
    (fstCode sndCode : ExtendedProfilePackedBlockState k β q r) :
    0 ≤ G.extendedProfileBlockOptionMass R0 rho omega e
      fstCode sndCode := by
  unfold extendedProfileBlockOptionMass
  exact Finset.sum_nonneg fun j _hj ↦
    G.extendedProfileCoordinateOptionMass_nonneg R0
      hn hs hq hr0 hleft homega0 homega1 hrho e _ _

theorem extendedProfileBlockOptionMass_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (e : G.E)
    (fstCode sndCode : ExtendedProfilePackedBlockState k β q r) :
    G.extendedProfileBlockOptionMass R0 rho omega e fstCode sndCode ≤
      k * extendedProfileCoordinateOptionUpper rho s omega β q r B k := by
  unfold extendedProfileBlockOptionMass
  calc
    (∑ j : Fin k, G.extendedProfileBlockCoordinateOptionMass
        R0 rho omega e fstCode sndCode j) ≤
        ∑ _j : Fin k,
          extendedProfileCoordinateOptionUpper rho s omega β q r B k := by
      exact Finset.sum_le_sum fun j _hj ↦
        G.extendedProfileCoordinateOptionMass_le R0
          hn hs hq hr0 hleft homega0 homega1 hrho e _ _
    _ = k * extendedProfileCoordinateOptionUpper
        rho s omega β q r B k := by simp

theorem extendedProfileBlockVariancePairScale_pos
    (hB : 0 < B) (hrho : 0 < rho) (hs : 0 < s) :
    0 < extendedProfileBlockVariancePairScale
      rho s omega β q r B k := by
  unfold extendedProfileBlockVariancePairScale
  have htarget : 0 < rho * s / (B : ℝ) := by positivity
  have hupper : 0 ≤ extendedProfileCoordinateOptionUpper
      rho s omega β q r B k := by
    unfold extendedProfileCoordinateOptionUpper
    exact div_nonneg
      (mul_nonneg (by positivity)
        (extendedProfileCandidateCapacityScale_nonneg
          (omega := omega) (β := β) (q := q) (r := r)
          hrho.le hs.le))
      (mul_nonneg (Nat.cast_nonneg B) (Nat.cast_nonneg k))
  exact sq_pos_of_pos (add_pos_of_nonneg_of_pos
    (mul_nonneg (Nat.cast_nonneg k) hupper) htarget)

theorem extendedProfileBlockVarianceSelfScale_pos
    (hB : 0 < B) (hk : 0 < k) (hrho : 0 < rho) (hs : 0 < s) :
    0 < extendedProfileBlockVarianceSelfScale
      rho s omega β q r B k := by
  unfold extendedProfileBlockVarianceSelfScale
  exact mul_pos (by exact_mod_cast Nat.mul_pos hB hk)
    (extendedProfileBlockVariancePairScale_pos hB hrho hs)

theorem extendedProfileBlockVariance_le_weight_mul_pairScale
    (hB : 0 < B) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (e : G.E)
    (fstCode sndCode : ExtendedProfilePackedBlockState k β q r) :
    G.extendedProfileBlockVariance R0 rho omega e fstCode sndCode ≤
      G.weight e * extendedProfileBlockVariancePairScale
        rho s omega β q r B k := by
  let X := G.extendedProfileBlockOptionMass R0 rho omega e fstCode sndCode
  let U := k * extendedProfileCoordinateOptionUpper rho s omega β q r B k
  let mu := rho * s / B
  have hX0 : 0 ≤ X := G.extendedProfileBlockOptionMass_nonneg R0
    hn hs hq hr0 hleft homega0 homega1 hrho e fstCode sndCode
  have hXU : X ≤ U := G.extendedProfileBlockOptionMass_le R0
    hn hs hq hr0 hleft homega0 homega1 hrho e fstCode sndCode
  have hU0 : 0 ≤ U := mul_nonneg (Nat.cast_nonneg k)
    (extendedProfileCoordinateOptionUpper_nonneg hn hrho hs)
  have hmu0 : 0 ≤ mu := by
    exact div_nonneg (mul_nonneg hrho hs) (Nat.cast_nonneg B)
  have hprod : 0 ≤ (U - X) * (U + X + 2 * mu) :=
    mul_nonneg (sub_nonneg.mpr hXU) (by positivity)
  have hsquare : (X - mu) ^ 2 ≤ (U + mu) ^ 2 := by
    nlinarith
  unfold extendedProfileBlockVariance
    extendedProfileBlockVariancePairScale
  exact mul_le_mul_of_nonneg_left hsquare (G.weight_nonneg e)

/-- Independent coordinates make the expected squared block error grow
linearly, rather than quadratically, with the block size. -/
theorem expected_extendedProfileBlockVariance_le
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho) (e : G.E) :
    (∑ left : ExtendedProfilePackedBlockState k β q r,
      G.paddedExtendedProfileBlockProbability R0 omega (G.fst e) left *
        ∑ right : ExtendedProfilePackedBlockState k β q r,
          G.paddedExtendedProfileBlockProbability R0 omega (G.snd e) right *
            G.extendedProfileBlockVariance R0 rho omega e left right) ≤
      G.weight e *
        (k * extendedProfileCoordinateOptionUpper
          rho s omega β q r B k *
            extendedProfileCoordinateOptionMean rho s B k) := by
  let atomProb : ∀ v, G.ExtendedProfileState R0 v → ℝ :=
    fun v z ↦ G.smoothedExtendedProfileProbability R0 omega v z
  let value : Fin k → G.ExtendedProfileState R0 (G.fst e) →
      G.ExtendedProfileState R0 (G.snd e) → ℝ :=
    fun _j P Q ↦ G.extendedProfileCoordinateOptionMass R0 rho omega e P Q
  let mu := extendedProfileCoordinateOptionMean rho s B k
  let U := extendedProfileCoordinateOptionUpper rho s omega β q r B k
  have hmoment :=
    FiniteDependentWordPadding.sum_twoPaddedWordProbability_mul_decode_block_sum_sub_card_sq_le
      (fun v ↦ G.ExtendedProfileState R0 v)
      (G.extendedProfileStateEncoding R0)
      (G.inactiveExtendedProfileState R0)
      atomProb
      (fun v z ↦ G.smoothedExtendedProfileProbability_pos R0
        hs hq hr0 hleft homega0 homega1 v z |>.le)
      (G.sum_smoothedExtendedProfileProbability R0 omega)
      (G.fst e) (G.snd e) value mu U
      (fun _j P Q ↦ G.extendedProfileCoordinateOptionMass_nonneg R0
        hn hs hq hr0 hleft homega0 homega1 hrho e P Q)
      (fun _j P Q ↦ G.extendedProfileCoordinateOptionMass_le R0
        hn hs hq hr0 hleft homega0 homega1 hrho e P Q)
      (fun _j ↦ G.expected_extendedProfileCoordinateOptionMass R0
        hn hs hspos hq hr0 hleft homega0 homega1 rho e)
  have htarget : (k : ℝ) * mu = rho * s / B := by
    have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
    dsimp [mu, extendedProfileCoordinateOptionMean]
    field_simp [hBR, hkR]
  have hmoment' :
      (∑ left : ExtendedProfilePackedBlockState k β q r,
        G.paddedExtendedProfileBlockProbability R0 omega (G.fst e) left *
          ∑ right : ExtendedProfilePackedBlockState k β q r,
            G.paddedExtendedProfileBlockProbability R0 omega (G.snd e) right *
              (G.extendedProfileBlockOptionMass R0 rho omega e left right -
                rho * s / B) ^ 2) ≤ k * U * mu := by
    simpa [atomProb, value, mu, U,
      paddedExtendedProfileBlockProbability,
      decodeExtendedProfileBlock, extendedProfileBlockOptionMass,
      extendedProfileBlockCoordinateOptionMass_eq_coordinate, htarget] using
        hmoment
  have hfactor :
      (∑ left : ExtendedProfilePackedBlockState k β q r,
        G.paddedExtendedProfileBlockProbability R0 omega (G.fst e) left *
          ∑ right : ExtendedProfilePackedBlockState k β q r,
            G.paddedExtendedProfileBlockProbability R0 omega (G.snd e) right *
              G.extendedProfileBlockVariance R0 rho omega e left right) =
        G.weight e *
          (∑ left : ExtendedProfilePackedBlockState k β q r,
            G.paddedExtendedProfileBlockProbability R0 omega (G.fst e) left *
              ∑ right : ExtendedProfilePackedBlockState k β q r,
                G.paddedExtendedProfileBlockProbability R0 omega
                    (G.snd e) right *
                  (G.extendedProfileBlockOptionMass R0 rho omega e
                    left right - rho * s / B) ^ 2) := by
    unfold extendedProfileBlockVariance extendedProfileBlockTarget
    calc
      (∑ left : ExtendedProfilePackedBlockState k β q r,
        G.paddedExtendedProfileBlockProbability R0 omega (G.fst e) left *
          ∑ right : ExtendedProfilePackedBlockState k β q r,
            G.paddedExtendedProfileBlockProbability R0 omega (G.snd e) right *
              (G.weight e *
                (G.extendedProfileBlockOptionMass R0 rho omega e left right -
                  rho * s / B) ^ 2)) =
          ∑ left : ExtendedProfilePackedBlockState k β q r,
            G.weight e *
              (G.paddedExtendedProfileBlockProbability R0 omega (G.fst e) left *
                ∑ right : ExtendedProfilePackedBlockState k β q r,
                  G.paddedExtendedProfileBlockProbability R0 omega (G.snd e) right *
                    (G.extendedProfileBlockOptionMass R0 rho omega e left right -
                      rho * s / B) ^ 2) := by
            apply Finset.sum_congr rfl
            intro left _hleft
            rw [Finset.mul_sum, Finset.mul_sum]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro right _hright
            ring
      _ = G.weight e *
          (∑ left : ExtendedProfilePackedBlockState k β q r,
            G.paddedExtendedProfileBlockProbability R0 omega (G.fst e) left *
              ∑ right : ExtendedProfilePackedBlockState k β q r,
                G.paddedExtendedProfileBlockProbability R0 omega (G.snd e) right *
                  (G.extendedProfileBlockOptionMass R0 rho omega e left right -
                    rho * s / B) ^ 2) := by
            rw [Finset.mul_sum]
  rw [hfactor]
  exact mul_le_mul_of_nonneg_left hmoment' (G.weight_nonneg e)

/-- Fully averaged block variance of one edge. -/
def expectedExtendedProfileBlockVariance
    (rho omega : ℝ) (e : G.E) : ℝ :=
  ∑ left : ExtendedProfilePackedBlockState k β q r,
    G.paddedExtendedProfileBlockProbability R0 omega (G.fst e) left *
      ∑ right : ExtendedProfilePackedBlockState k β q r,
        G.paddedExtendedProfileBlockProbability R0 omega (G.snd e) right *
          G.extendedProfileBlockVariance R0 rho omega e left right

/-- Expand one conditional candidate row as a direct sum over incident
edges, with the opposite endpoint averaged. -/
theorem conditionalExtendedProfileBlockVariance_eq_edge_sum
    (rho omega : ℝ) (v : G.V) (b : Fin B)
    (centerCode : ExtendedProfilePackedBlockState k β q r) :
    G.conditionalExtendedProfileBlockVariance R0 rho omega
        (v, b, centerCode) =
      ∑ e : G.E,
        if v = G.fst e then
          ∑ oppositeCode : ExtendedProfilePackedBlockState k β q r,
            G.paddedExtendedProfileBlockProbability R0 omega
                (G.snd e) oppositeCode *
              G.extendedProfileBlockVariance R0 rho omega e
                centerCode oppositeCode
        else if v = G.snd e then
          ∑ oppositeCode : ExtendedProfilePackedBlockState k β q r,
            G.paddedExtendedProfileBlockProbability R0 omega
                (G.fst e) oppositeCode *
              G.extendedProfileBlockVariance R0 rho omega e
                oppositeCode centerCode
        else 0 := by
  classical
  unfold conditionalExtendedProfileBlockVariance
    FiniteCategoricalSelection.rowMean
    rawExtendedProfileBlockVarianceCandidateUse
  simp_rw [Finset.mul_sum]
  calc
    (∑ source : G.V × Fin B,
      ∑ sourceCode : ExtendedProfilePackedBlockState k β q r,
        ∑ e : G.E,
          G.paddedExtendedProfileBlockProbability R0 omega source.1 sourceCode *
            G.extendedProfileBlockVarianceCandidateEdgeUse R0 rho omega
              source sourceCode e (v, b, centerCode)) =
        ∑ source : G.V × Fin B, ∑ e : G.E,
          ∑ sourceCode : ExtendedProfilePackedBlockState k β q r,
            G.paddedExtendedProfileBlockProbability R0 omega source.1 sourceCode *
              G.extendedProfileBlockVarianceCandidateEdgeUse R0 rho omega
                source sourceCode e (v, b, centerCode) := by
      apply Finset.sum_congr rfl
      intro source _hsource
      rw [Finset.sum_comm]
    _ = ∑ e : G.E, ∑ source : G.V × Fin B,
          ∑ sourceCode : ExtendedProfilePackedBlockState k β q r,
            G.paddedExtendedProfileBlockProbability R0 omega source.1 sourceCode *
              G.extendedProfileBlockVarianceCandidateEdgeUse R0 rho omega
                source sourceCode e (v, b, centerCode) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [Fintype.sum_prod_type]
      by_cases hfst : v = G.fst e
      · subst v
        have hne : G.fst e ≠ G.snd e := G.noLoop e
        simp [extendedProfileBlockVarianceCandidateEdgeUse, hne]
      · by_cases hsnd : v = G.snd e
        · subst v
          have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
          simp [extendedProfileBlockVarianceCandidateEdgeUse, hfst, hne]
        · simp [extendedProfileBlockVarianceCandidateEdgeUse, hfst, hsnd]

theorem sum_centerProbability_mul_conditionalBlockVariance
    (rho omega : ℝ) (v : G.V) (b : Fin B) :
    (∑ centerCode : ExtendedProfilePackedBlockState k β q r,
      G.paddedExtendedProfileBlockProbability R0 omega v centerCode *
        G.conditionalExtendedProfileBlockVariance R0 rho omega
          (v, b, centerCode)) =
      ∑ e : G.StarEdge v,
        G.expectedExtendedProfileBlockVariance R0 rho omega e.1 := by
  classical
  simp_rw [G.conditionalExtendedProfileBlockVariance_eq_edge_sum
    R0 rho omega v b]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ e : G.E,
      ∑ centerCode : ExtendedProfilePackedBlockState k β q r,
        G.paddedExtendedProfileBlockProbability R0 omega v centerCode *
          (if v = G.fst e then
            ∑ oppositeCode : ExtendedProfilePackedBlockState k β q r,
              G.paddedExtendedProfileBlockProbability R0 omega
                  (G.snd e) oppositeCode *
                G.extendedProfileBlockVariance R0 rho omega e
                  centerCode oppositeCode
          else if v = G.snd e then
            ∑ oppositeCode : ExtendedProfilePackedBlockState k β q r,
              G.paddedExtendedProfileBlockProbability R0 omega
                  (G.fst e) oppositeCode *
                G.extendedProfileBlockVariance R0 rho omega e
                  oppositeCode centerCode
          else 0)) =
        ∑ e : G.E, if G.Inc v e then
          G.expectedExtendedProfileBlockVariance R0 rho omega e else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hfst : v = G.fst e
      · subst v
        simp [WeightedSimpleGraph.Inc,
          expectedExtendedProfileBlockVariance]
      · by_cases hsnd : v = G.snd e
        · have hne : G.snd e ≠ G.fst e := by
            intro h
            exact G.noLoop e h.symm
          subst v
          have hswap :
              (∑ centerCode : ExtendedProfilePackedBlockState k β q r,
                G.paddedExtendedProfileBlockProbability R0 omega
                    (G.snd e) centerCode *
                  ∑ oppositeCode : ExtendedProfilePackedBlockState k β q r,
                    G.paddedExtendedProfileBlockProbability R0 omega
                        (G.fst e) oppositeCode *
                      G.extendedProfileBlockVariance R0 rho omega e
                        oppositeCode centerCode) =
                G.expectedExtendedProfileBlockVariance
                  R0 rho omega e := by
            unfold expectedExtendedProfileBlockVariance
            calc
              (∑ centerCode : ExtendedProfilePackedBlockState k β q r,
                G.paddedExtendedProfileBlockProbability R0 omega
                    (G.snd e) centerCode *
                  ∑ oppositeCode : ExtendedProfilePackedBlockState k β q r,
                    G.paddedExtendedProfileBlockProbability R0 omega
                        (G.fst e) oppositeCode *
                      G.extendedProfileBlockVariance R0 rho omega e
                        oppositeCode centerCode) =
                  ∑ centerCode, ∑ oppositeCode,
                    G.paddedExtendedProfileBlockProbability R0 omega
                        (G.snd e) centerCode *
                      (G.paddedExtendedProfileBlockProbability R0 omega
                          (G.fst e) oppositeCode *
                        G.extendedProfileBlockVariance R0 rho omega e
                          oppositeCode centerCode) := by
                    apply Finset.sum_congr rfl
                    intro centerCode _hc
                    rw [Finset.mul_sum]
              _ = ∑ oppositeCode, ∑ centerCode,
                    G.paddedExtendedProfileBlockProbability R0 omega
                        (G.snd e) centerCode *
                      (G.paddedExtendedProfileBlockProbability R0 omega
                          (G.fst e) oppositeCode *
                        G.extendedProfileBlockVariance R0 rho omega e
                          oppositeCode centerCode) := by rw [Finset.sum_comm]
              _ = ∑ oppositeCode,
                    G.paddedExtendedProfileBlockProbability R0 omega
                        (G.fst e) oppositeCode *
                      ∑ centerCode,
                        G.paddedExtendedProfileBlockProbability R0 omega
                            (G.snd e) centerCode *
                          G.extendedProfileBlockVariance R0 rho omega e
                            oppositeCode centerCode := by
                    apply Finset.sum_congr rfl
                    intro oppositeCode _ho
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro centerCode _hc
                    ring
          simp [WeightedSimpleGraph.Inc, hne, hswap]
        · have hinc : ¬ G.Inc v e := by
            intro h
            rcases h with h | h
            · exact hfst h.symm
            · exact hsnd h.symm
          simp [hfst, hsnd, hinc]
    _ = ∑ e ∈ Finset.univ.filter (G.Inc v),
          G.expectedExtendedProfileBlockVariance R0 rho omega e := by
      rw [Finset.sum_filter]
    _ = ∑ e : G.StarEdge v,
        G.expectedExtendedProfileBlockVariance R0 rho omega e.1 := by
      exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
        (by intro e; simp)
        (fun e ↦ G.expectedExtendedProfileBlockVariance R0 rho omega e)

theorem meanTotalExtendedProfileBlockVariance_eq
    (rho omega : ℝ) (v : G.V) :
    G.meanTotalExtendedProfileBlockVariance R0 rho omega v =
      B * ∑ e : G.StarEdge v,
        G.expectedExtendedProfileBlockVariance R0 rho omega e.1 := by
  unfold meanTotalExtendedProfileBlockVariance
  simp_rw [G.sum_centerProbability_mul_conditionalBlockVariance
    R0 rho omega v]
  simp

theorem meanTotalExtendedProfileBlockVariance_le
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (hpack : G.LocallyPacksInto (B * k)) (v : G.V) :
    G.meanTotalExtendedProfileBlockVariance R0 rho omega v ≤
      extendedProfileBlockVarianceMeanBound
        rho s omega β q r B k := by
  let U := extendedProfileCoordinateOptionUpper rho s omega β q r B k
  let mu := extendedProfileCoordinateOptionMean rho s B k
  have hU0 : 0 ≤ U :=
    extendedProfileCoordinateOptionUpper_nonneg hn hrho hs
  have hmu0 : 0 ≤ mu := by
    unfold mu extendedProfileCoordinateOptionMean
    exact div_nonneg (mul_nonneg hrho hs)
      (mul_nonneg (Nat.cast_nonneg B) (Nat.cast_nonneg k))
  have hstar := G.starWeight_le_of_packsStarInto (hpack v)
  rw [G.meanTotalExtendedProfileBlockVariance_eq R0 rho omega v]
  calc
    (B : ℝ) * ∑ e : G.StarEdge v,
        G.expectedExtendedProfileBlockVariance R0 rho omega e.1 ≤
      (B : ℝ) * ∑ e : G.StarEdge v,
        G.weight e.1 * ((k : ℝ) * U * mu) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B)
      exact Finset.sum_le_sum fun e _he ↦
        G.expected_extendedProfileBlockVariance_le R0
          hB hk hn hs hspos hq hr0 hleft homega0 homega1
          rho hrho e.1
    _ = (B : ℝ) * G.starWeight v * ((k : ℝ) * U * mu) := by
      unfold starWeight
      calc
        (B : ℝ) * ∑ e : G.StarEdge v,
            G.weight e.1 * ((k : ℝ) * U * mu) =
          (B : ℝ) * ((∑ e : G.StarEdge v, G.weight e.1) *
            ((k : ℝ) * U * mu)) := by
              congr 1
              rw [Finset.sum_mul]
        _ = (B : ℝ) * (∑ e : G.StarEdge v, G.weight e.1) *
            ((k : ℝ) * U * mu) := by ring
    _ ≤ (B : ℝ) * (B * k : ℕ) * ((k : ℝ) * U * mu) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hstar (Nat.cast_nonneg B))
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hU0) hmu0)
    _ = extendedProfileBlockVarianceMeanBound
        rho s omega β q r B k := by
      unfold extendedProfileBlockVarianceMeanBound
        U mu
      push_cast
      ring

private theorem blockVarianceCandidateEdgeUse_eq_zero_of_not_matches
    (rho omega : ℝ) (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r) (e : G.E)
    (row : G.ExtendedProfileBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r))
    (h : ¬ G.CandidateEdgeMatches row.1 source.1 e) :
    G.extendedProfileBlockVarianceCandidateEdgeUse R0 rho omega
      source sourceCode e row = 0 := by
  unfold CandidateEdgeMatches at h
  simp only [not_or] at h
  simp [extendedProfileBlockVarianceCandidateEdgeUse, h.1, h.2]

theorem rawExtendedProfileBlockVarianceCandidateUse_nonneg
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    0 ≤ G.rawExtendedProfileBlockVarianceCandidateUse R0 rho omega
      source sourceCode row := by
  unfold rawExtendedProfileBlockVarianceCandidateUse
  apply Finset.sum_nonneg
  intro e _he
  unfold extendedProfileBlockVarianceCandidateEdgeUse
  split
  · split
    · exact G.extendedProfileBlockVariance_nonneg R0 rho omega _ _ _
    · split
      · exact G.extendedProfileBlockVariance_nonneg R0 rho omega _ _ _
      · exact le_rfl
  · exact le_rfl

theorem rawExtendedProfileBlockVarianceCandidateUse_le_pairScale
    (hB : 0 < B) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    G.rawExtendedProfileBlockVarianceCandidateUse R0 rho omega
        source sourceCode row ≤
      extendedProfileBlockVariancePairScale rho s omega β q r B k := by
  classical
  let pairScale := extendedProfileBlockVariancePairScale
    rho s omega β q r B k
  unfold rawExtendedProfileBlockVarianceCandidateUse
  by_cases hblock : source.2 = row.2.1
  · by_cases hex : ∃ e, G.CandidateEdgeMatches row.1 source.1 e
    · obtain ⟨e, he⟩ := hex
      calc
        (∑ f, G.extendedProfileBlockVarianceCandidateEdgeUse R0 rho omega
            source sourceCode f row) =
            G.extendedProfileBlockVarianceCandidateEdgeUse R0 rho omega
              source sourceCode e row := by
          apply Finset.sum_eq_single e
          · intro f _hf hfe
            apply G.blockVarianceCandidateEdgeUse_eq_zero_of_not_matches R0
            intro hfmatch
            exact hfe (G.candidateEdgeMatches_unique hfmatch he)
          · simp
        _ ≤ G.weight e * pairScale := by
          rcases he with he | he
          · simp [extendedProfileBlockVarianceCandidateEdgeUse, hblock,
              he.1, he.2, pairScale]
            exact G.extendedProfileBlockVariance_le_weight_mul_pairScale R0
              hB hn hs hq hr0 hleft homega0 homega1 hrho e _ _
          · have hnotFirst : ¬ (row.1 = G.fst e ∧ source.1 = G.snd e) := by
              intro hfirst
              exact G.noLoop e (hfirst.1.symm.trans he.1)
            rw [extendedProfileBlockVarianceCandidateEdgeUse,
              if_pos hblock, if_neg hnotFirst, if_pos ⟨he.1, he.2⟩]
            exact G.extendedProfileBlockVariance_le_weight_mul_pairScale R0
              hB hn hs hq hr0 hleft homega0 homega1 hrho e _ _
        _ ≤ pairScale := by
          exact mul_le_of_le_one_left
            (sq_nonneg _) (G.weight_le_one e)
    · calc
        (∑ e, G.extendedProfileBlockVarianceCandidateEdgeUse R0 rho omega
            source sourceCode e row) = 0 := by
          apply Finset.sum_eq_zero
          intro e _he
          exact G.blockVarianceCandidateEdgeUse_eq_zero_of_not_matches R0
            rho omega source sourceCode e row (fun h ↦ hex ⟨e, h⟩)
        _ ≤ pairScale := sq_nonneg _
  · have hzero : ∀ e,
        G.extendedProfileBlockVarianceCandidateEdgeUse R0 rho omega
          source sourceCode e row = 0 := by
      intro e
      simp [extendedProfileBlockVarianceCandidateEdgeUse, hblock]
    rw [show (∑ e, G.extendedProfileBlockVarianceCandidateEdgeUse R0 rho omega
      source sourceCode e row) = 0 by simp [hzero]]
    exact sq_nonneg _

theorem conditionalExtendedProfileBlockVariance_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (row : G.ExtendedProfileBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    0 ≤ G.conditionalExtendedProfileBlockVariance R0 rho omega row := by
  unfold conditionalExtendedProfileBlockVariance
    FiniteCategoricalSelection.rowMean
  exact Finset.sum_nonneg fun source _hs ↦
    Finset.sum_nonneg fun a _ha ↦ mul_nonneg
      (G.paddedExtendedProfileBlockProbability_nonneg R0
        hs hq hr0 hleft homega0 homega1 source.1 a)
      (G.rawExtendedProfileBlockVarianceCandidateUse_nonneg R0
        source a row)

theorem conditionalExtendedProfileBlockVariance_le_selfScale
    (hB : 0 < B) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (hpack : G.LocallyPacksInto (B * k))
    (row : G.ExtendedProfileBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    G.conditionalExtendedProfileBlockVariance R0 rho omega row ≤
      extendedProfileBlockVarianceSelfScale
        rho s omega β q r B k := by
  rcases row with ⟨v, b, centerCode⟩
  rw [G.conditionalExtendedProfileBlockVariance_eq_edge_sum
    R0 rho omega v b centerCode]
  let pairScale := extendedProfileBlockVariancePairScale
    rho s omega β q r B k
  have hedge : ∀ e : G.E,
      (if v = G.fst e then
        ∑ oppositeCode : ExtendedProfilePackedBlockState k β q r,
          G.paddedExtendedProfileBlockProbability R0 omega (G.snd e)
              oppositeCode *
            G.extendedProfileBlockVariance R0 rho omega e
              centerCode oppositeCode
      else if v = G.snd e then
        ∑ oppositeCode : ExtendedProfilePackedBlockState k β q r,
          G.paddedExtendedProfileBlockProbability R0 omega (G.fst e)
              oppositeCode *
            G.extendedProfileBlockVariance R0 rho omega e
              oppositeCode centerCode
      else 0) ≤
        if G.Inc v e then G.weight e * pairScale else 0 := by
    intro e
    by_cases hfst : v = G.fst e
    · subst v
      simp only [eq_self, if_true, WeightedSimpleGraph.Inc, true_or]
      calc
        (∑ a, G.paddedExtendedProfileBlockProbability R0 omega
            (G.snd e) a *
              G.extendedProfileBlockVariance R0 rho omega e centerCode a) ≤
            ∑ a, G.paddedExtendedProfileBlockProbability R0 omega
              (G.snd e) a * (G.weight e * pairScale) := by
          exact Finset.sum_le_sum fun a _ha ↦
            mul_le_mul_of_nonneg_left
              (G.extendedProfileBlockVariance_le_weight_mul_pairScale R0
                hB hn hs hq hr0 hleft homega0 homega1 hrho e _ _)
              (G.paddedExtendedProfileBlockProbability_nonneg R0
                hs hq hr0 hleft homega0 homega1 _ a)
        _ = G.weight e * pairScale := by
          rw [← Finset.sum_mul,
            G.sum_paddedExtendedProfileBlockProbability R0 omega]
          ring
    · by_cases hsnd : v = G.snd e
      · have hne : G.snd e ≠ G.fst e := by
          intro h
          exact G.noLoop e h.symm
        subst v
        simp [hne, WeightedSimpleGraph.Inc]
        calc
          (∑ a, G.paddedExtendedProfileBlockProbability R0 omega
              (G.fst e) a *
                G.extendedProfileBlockVariance R0 rho omega e a centerCode) ≤
              ∑ a, G.paddedExtendedProfileBlockProbability R0 omega
                (G.fst e) a * (G.weight e * pairScale) := by
            exact Finset.sum_le_sum fun a _ha ↦
              mul_le_mul_of_nonneg_left
                (G.extendedProfileBlockVariance_le_weight_mul_pairScale R0
                  hB hn hs hq hr0 hleft homega0 homega1 hrho e _ _)
                (G.paddedExtendedProfileBlockProbability_nonneg R0
                  hs hq hr0 hleft homega0 homega1 _ a)
          _ = G.weight e * pairScale := by
            rw [← Finset.sum_mul,
              G.sum_paddedExtendedProfileBlockProbability R0 omega]
            ring
      · have hinc : ¬ G.Inc v e := by
          intro h
          rcases h with h | h
          · exact hfst h.symm
          · exact hsnd h.symm
        simp [hfst, hsnd, hinc]
  calc
    (∑ e : G.E,
      if v = G.fst e then
        ∑ oppositeCode, G.paddedExtendedProfileBlockProbability R0 omega
            (G.snd e) oppositeCode *
          G.extendedProfileBlockVariance R0 rho omega e
            centerCode oppositeCode
      else if v = G.snd e then
        ∑ oppositeCode, G.paddedExtendedProfileBlockProbability R0 omega
            (G.fst e) oppositeCode *
          G.extendedProfileBlockVariance R0 rho omega e
            oppositeCode centerCode
      else 0) ≤
        ∑ e : G.E, if G.Inc v e then G.weight e * pairScale else 0 :=
      Finset.sum_le_sum fun e _he ↦ hedge e
    _ = pairScale * G.starWeight v := by
      calc
        (∑ e : G.E, if G.Inc v e then G.weight e * pairScale else 0) =
            ∑ e ∈ Finset.univ.filter (G.Inc v),
              G.weight e * pairScale := by rw [Finset.sum_filter]
        _ = ∑ e : G.StarEdge v, G.weight e.1 * pairScale := by
          exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
            (by intro e; simp) (fun e ↦ G.weight e * pairScale)
        _ = pairScale * G.starWeight v := by
          unfold starWeight
          calc
            (∑ e : G.StarEdge v, G.weight e.1 * pairScale) =
                (∑ e : G.StarEdge v, G.weight e.1) * pairScale := by
              rw [Finset.sum_mul]
            _ = pairScale * ∑ e : G.StarEdge v, G.weight e.1 := by ring
    _ ≤ pairScale * (B * k : ℕ) := by
      exact mul_le_mul_of_nonneg_left
        (G.starWeight_le_of_packsStarInto (hpack v)) (sq_nonneg _)
    _ = extendedProfileBlockVarianceSelfScale
        rho s omega β q r B k := by
      unfold extendedProfileBlockVarianceSelfScale pairScale
      push_cast
      ring

theorem scaledExtendedProfileBlockVarianceCandidateUse_nonneg
    (hpair0 : 0 ≤ pairScale)
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    0 ≤ G.scaledExtendedProfileBlockVarianceCandidateUse
      R0 rho omega pairScale source sourceCode row := by
  unfold scaledExtendedProfileBlockVarianceCandidateUse
  exact div_nonneg
    (G.rawExtendedProfileBlockVarianceCandidateUse_nonneg R0
      source sourceCode row) hpair0

theorem scaledExtendedProfileBlockVarianceCandidateUse_le_one
    (hB : 0 < B) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    G.scaledExtendedProfileBlockVarianceCandidateUse R0 rho omega
        (extendedProfileBlockVariancePairScale
          rho s omega β q r B k) source sourceCode row ≤ 1 := by
  apply (div_le_one
    (extendedProfileBlockVariancePairScale_pos hB hrho hspos)).2
  exact G.rawExtendedProfileBlockVarianceCandidateUse_le_pairScale R0
    hB hn hs hq hr0 hleft homega0 homega1 hrho.le source sourceCode row

theorem scaledExtendedProfileBlockVarianceSelfUse_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hself0 : 0 ≤ selfScale)
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r) (v : G.V) :
    0 ≤ G.scaledExtendedProfileBlockVarianceSelfUse R0 rho omega
      selfScale source sourceCode v := by
  unfold scaledExtendedProfileBlockVarianceSelfUse
  split
  · exact div_nonneg
      (G.conditionalExtendedProfileBlockVariance_nonneg R0
        hs hq hr0 hleft homega0 homega1 _) hself0
  · exact le_rfl

theorem scaledExtendedProfileBlockVarianceSelfUse_le_one
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (hpack : G.LocallyPacksInto (B * k))
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r) (v : G.V) :
    G.scaledExtendedProfileBlockVarianceSelfUse R0 rho omega
        (extendedProfileBlockVarianceSelfScale
          rho s omega β q r B k) source sourceCode v ≤ 1 := by
  unfold scaledExtendedProfileBlockVarianceSelfUse
  split
  · apply (div_le_one
      (extendedProfileBlockVarianceSelfScale_pos hB hk hrho hspos)).2
    exact G.conditionalExtendedProfileBlockVariance_le_selfScale R0
      hB hn hs hq hr0 hleft homega0 homega1 hrho.le hpack _
  · norm_num

theorem scaledExtendedProfileBlockVarianceUse_nonneg
    (hB : 0 < B) (hk : 0 < k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileBlockVarianceRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    0 ≤ G.scaledExtendedProfileBlockVarianceUse R0 rho omega
      (extendedProfileBlockVariancePairScale rho s omega β q r B k)
      (extendedProfileBlockVarianceSelfScale rho s omega β q r B k)
      source sourceCode row := by
  rcases row with candidate | v
  · exact G.scaledExtendedProfileBlockVarianceCandidateUse_nonneg R0
      (extendedProfileBlockVariancePairScale_pos hB hrho hspos).le
      source sourceCode candidate
  · exact G.scaledExtendedProfileBlockVarianceSelfUse_nonneg R0
      hs hq hr0 hleft homega0 homega1
      (extendedProfileBlockVarianceSelfScale_pos hB hk hrho hspos).le
      source sourceCode v

theorem scaledExtendedProfileBlockVarianceUse_le_one
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (hpack : G.LocallyPacksInto (B * k))
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileBlockVarianceRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    G.scaledExtendedProfileBlockVarianceUse R0 rho omega
      (extendedProfileBlockVariancePairScale rho s omega β q r B k)
      (extendedProfileBlockVarianceSelfScale rho s omega β q r B k)
      source sourceCode row ≤ 1 := by
  rcases row with candidate | v
  · exact G.scaledExtendedProfileBlockVarianceCandidateUse_le_one R0
      hB hn hs hspos hq hr0 hleft homega0 homega1 rho hrho
      source sourceCode candidate
  · exact G.scaledExtendedProfileBlockVarianceSelfUse_le_one R0
      hB hk hn hs hspos hq hr0 hleft homega0 homega1 rho hrho hpack
      source sourceCode v

theorem meanTotalExtendedProfileBlockVariance_le_B_mul_selfScale
    (hB : 0 < B) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (hpack : G.LocallyPacksInto (B * k)) (v : G.V) :
    G.meanTotalExtendedProfileBlockVariance R0 rho omega v ≤
      B * extendedProfileBlockVarianceSelfScale
        rho s omega β q r B k := by
  unfold meanTotalExtendedProfileBlockVariance
  calc
    (∑ b : Fin B, ∑ a : ExtendedProfilePackedBlockState k β q r,
      G.paddedExtendedProfileBlockProbability R0 omega v a *
        G.conditionalExtendedProfileBlockVariance R0 rho omega (v, b, a)) ≤
        ∑ _b : Fin B, ∑ a : ExtendedProfilePackedBlockState k β q r,
          G.paddedExtendedProfileBlockProbability R0 omega v a *
            extendedProfileBlockVarianceSelfScale
              rho s omega β q r B k := by
      apply Finset.sum_le_sum
      intro b _hb
      apply Finset.sum_le_sum
      intro a _ha
      exact mul_le_mul_of_nonneg_left
        (G.conditionalExtendedProfileBlockVariance_le_selfScale R0
          hB hn hs hq hr0 hleft homega0 homega1 hrho hpack (v, b, a))
        (G.paddedExtendedProfileBlockProbability_nonneg R0
          hs hq hr0 hleft homega0 homega1 v a)
    _ = B * extendedProfileBlockVarianceSelfScale
        rho s omega β q r B k := by
      simp_rw [← Finset.sum_mul,
        G.sum_paddedExtendedProfileBlockProbability R0 omega v]
      simp

theorem rowMean_scaledExtendedProfileBlockVarianceUse_le_n
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (hpack : G.LocallyPacksInto (B * k))
    (row : G.ExtendedProfileBlockVarianceRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
        (fun source a ↦
          G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
        (G.scaledExtendedProfileBlockVarianceUse R0 rho omega
          (extendedProfileBlockVariancePairScale rho s omega β q r B k)
          (extendedProfileBlockVarianceSelfScale rho s omega β q r B k))
        row ≤ B * k := by
  let pairScale := extendedProfileBlockVariancePairScale
    rho s omega β q r B k
  let selfScale := extendedProfileBlockVarianceSelfScale
    rho s omega β q r B k
  have hpair : 0 < pairScale :=
    extendedProfileBlockVariancePairScale_pos hB hrho hspos
  have hself : 0 < selfScale :=
    extendedProfileBlockVarianceSelfScale_pos hB hk hrho hspos
  rcases row with candidate | v
  · change FiniteCategoricalSelection.rowMean
        (fun source a ↦
          G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
        (G.scaledExtendedProfileBlockVarianceCandidateUse
          R0 rho omega pairScale) candidate ≤ B * k
    rw [G.rowMean_scaledBlockVarianceCandidate_eq R0]
    apply (div_le_iff₀ hpair).2
    calc
      G.conditionalExtendedProfileBlockVariance R0 rho omega candidate ≤
          selfScale :=
        G.conditionalExtendedProfileBlockVariance_le_selfScale R0
          hB hn hs hq hr0 hleft homega0 homega1 hrho.le hpack candidate
      _ = (B * k : ℕ) * pairScale := by
        unfold selfScale extendedProfileBlockVarianceSelfScale pairScale
        push_cast
        ring
      _ ≤ (B : ℝ) * (k : ℝ) * pairScale := by
        rw [Nat.cast_mul]
  · change FiniteCategoricalSelection.rowMean
        (fun source a ↦
          G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
        (G.scaledExtendedProfileBlockVarianceSelfUse
          R0 rho omega selfScale) v ≤ B * k
    rw [G.rowMean_scaledBlockVarianceSelf_eq R0]
    apply (div_le_iff₀ hself).2
    calc
      G.meanTotalExtendedProfileBlockVariance R0 rho omega v ≤
          B * selfScale :=
        G.meanTotalExtendedProfileBlockVariance_le_B_mul_selfScale R0
          hB hn hs hq hr0 hleft homega0 homega1 rho hrho.le hpack v
      _ ≤ (B * k : ℕ) * selfScale := by
        apply mul_le_mul_of_nonneg_right _ hself.le
        exact_mod_cast Nat.le_mul_of_pos_right B hk
      _ ≤ (B : ℝ) * (k : ℝ) * selfScale := by
        rw [Nat.cast_mul]

private theorem blockVarianceCandidateEdgeUse_div_pairScale_le_weight
    (hB : 0 < B) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r) (e : G.E)
    (row : G.ExtendedProfileBlockVarianceCandidateRow
      (B := B) (k := k) (β := β) (q := q) (r := r)) :
    G.extendedProfileBlockVarianceCandidateEdgeUse R0 rho omega
        source sourceCode e row /
          extendedProfileBlockVariancePairScale
            rho s omega β q r B k ≤
      if source.2 = row.2.1 ∧
          G.CandidateEdgeMatches row.1 source.1 e then
        G.weight e else 0 := by
  classical
  let pairScale := extendedProfileBlockVariancePairScale
    rho s omega β q r B k
  have hpair : 0 < pairScale :=
    extendedProfileBlockVariancePairScale_pos hB hrho hspos
  by_cases hblock : source.2 = row.2.1
  · by_cases hmatch : G.CandidateEdgeMatches row.1 source.1 e
    · rw [if_pos ⟨hblock, hmatch⟩]
      rcases hmatch with hmatch | hmatch
      · simp [extendedProfileBlockVarianceCandidateEdgeUse, hblock,
          hmatch.1, hmatch.2, pairScale]
        apply (div_le_iff₀ hpair).2
        simpa [mul_comm] using
          G.extendedProfileBlockVariance_le_weight_mul_pairScale R0
            hB hn hs hq hr0 hleft homega0 homega1 hrho.le e _ _
      · have hnotFirst :
            ¬ (row.1 = G.fst e ∧ source.1 = G.snd e) := by
          intro hfirst
          exact G.noLoop e (hfirst.1.symm.trans hmatch.1)
        rw [extendedProfileBlockVarianceCandidateEdgeUse,
          if_pos hblock, if_neg hnotFirst,
          if_pos ⟨hmatch.1, hmatch.2⟩]
        apply (div_le_iff₀ hpair).2
        simpa [mul_comm] using
          G.extendedProfileBlockVariance_le_weight_mul_pairScale R0
            hB hn hs hq hr0 hleft homega0 homega1 hrho.le e _ _
    · rw [if_neg (not_and_or.mpr (Or.inr hmatch))]
      rw [G.blockVarianceCandidateEdgeUse_eq_zero_of_not_matches R0
        rho omega source sourceCode e row hmatch]
      simp
  · rw [if_neg (not_and_or.mpr (Or.inl hblock))]
    simp [extendedProfileBlockVarianceCandidateEdgeUse, hblock]

private theorem sum_blockVarianceCandidateRows_edge_le
    (hB : 0 < B) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r) (e : G.E) :
    (∑ row : G.ExtendedProfileBlockVarianceCandidateRow
        (B := B) (k := k) (β := β) (q := q) (r := r),
      G.extendedProfileBlockVarianceCandidateEdgeUse R0 rho omega
        source sourceCode e row /
          extendedProfileBlockVariancePairScale
            rho s omega β q r B k) ≤
      if G.Inc source.1 e then
        (extendedProfileStateBound β q r : ℝ) ^ k * G.weight e
      else 0 := by
  classical
  calc
    (∑ row : G.ExtendedProfileBlockVarianceCandidateRow
        (B := B) (k := k) (β := β) (q := q) (r := r),
      G.extendedProfileBlockVarianceCandidateEdgeUse R0 rho omega
        source sourceCode e row /
          extendedProfileBlockVariancePairScale
            rho s omega β q r B k) ≤
        ∑ row : G.ExtendedProfileBlockVarianceCandidateRow
            (B := B) (k := k) (β := β) (q := q) (r := r),
          if source.2 = row.2.1 ∧
              G.CandidateEdgeMatches row.1 source.1 e then
            G.weight e else 0 := by
      exact Finset.sum_le_sum fun row _hrow ↦
        G.blockVarianceCandidateEdgeUse_div_pairScale_le_weight R0
          hB hn hs hspos hq hr0 hleft homega0 homega1 rho hrho
          source sourceCode e row
    _ = if G.Inc source.1 e then
        (extendedProfileStateBound β q r : ℝ) ^ k * G.weight e
      else 0 := by
      simp only [Fintype.sum_prod_type]
      by_cases hfst : source.1 = G.fst e
      · have hne : G.fst e ≠ G.snd e := G.noLoop e
        simp [CandidateEdgeMatches, WeightedSimpleGraph.Inc, hne,
          hfst, FiniteDependentWordPadding.packedWordState_card, ite_and]
      · by_cases hsnd : source.1 = G.snd e
        · have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
          simp [CandidateEdgeMatches, WeightedSimpleGraph.Inc, hfst, hsnd,
            hne, FiniteDependentWordPadding.packedWordState_card, ite_and]
        · have hinc : ¬ G.Inc source.1 e := by
            intro h
            rcases h with h | h
            · exact hfst h.symm
            · exact hsnd h.symm
          simp [CandidateEdgeMatches, hfst, hsnd, hinc, ite_and]

theorem sum_scaledBlockVarianceCandidateUse_le_column
    (hB : 0 < B) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (hpack : G.LocallyPacksInto (B * k))
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r) :
    (∑ row : G.ExtendedProfileBlockVarianceCandidateRow
        (B := B) (k := k) (β := β) (q := q) (r := r),
      G.scaledExtendedProfileBlockVarianceCandidateUse R0 rho omega
        (extendedProfileBlockVariancePairScale
          rho s omega β q r B k) source sourceCode row) ≤
      (extendedProfileStateBound β q r : ℝ) ^ k * (B * k) := by
  unfold scaledExtendedProfileBlockVarianceCandidateUse
    rawExtendedProfileBlockVarianceCandidateUse
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  calc
    (∑ e : G.E,
      ∑ row : G.ExtendedProfileBlockVarianceCandidateRow
          (B := B) (k := k) (β := β) (q := q) (r := r),
        G.extendedProfileBlockVarianceCandidateEdgeUse R0 rho omega
          source sourceCode e row /
            extendedProfileBlockVariancePairScale
              rho s omega β q r B k) ≤
        ∑ e : G.E, if G.Inc source.1 e then
          (extendedProfileStateBound β q r : ℝ) ^ k * G.weight e
          else 0 :=
      Finset.sum_le_sum fun e _he ↦
        G.sum_blockVarianceCandidateRows_edge_le R0
          hB hn hs hspos hq hr0 hleft homega0 homega1 rho hrho
          source sourceCode e
    _ = (extendedProfileStateBound β q r : ℝ) ^ k *
        G.starWeight source.1 := by
      calc
        (∑ e : G.E, if G.Inc source.1 e then
          (extendedProfileStateBound β q r : ℝ) ^ k * G.weight e
          else 0) =
            ∑ e ∈ Finset.univ.filter (G.Inc source.1),
              (extendedProfileStateBound β q r : ℝ) ^ k *
                G.weight e := by rw [Finset.sum_filter]
        _ = ∑ e : G.StarEdge source.1,
              (extendedProfileStateBound β q r : ℝ) ^ k *
                G.weight e.1 := by
          exact Finset.sum_subtype (Finset.univ.filter (G.Inc source.1))
            (by intro e; simp)
            (fun e ↦ (extendedProfileStateBound β q r : ℝ) ^ k *
              G.weight e)
        _ = (extendedProfileStateBound β q r : ℝ) ^ k *
              G.starWeight source.1 := by
          unfold starWeight
          rw [Finset.mul_sum]
    _ ≤ (extendedProfileStateBound β q r : ℝ) ^ k * (B * k) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Nat.cast_mul] using
        G.starWeight_le_of_packsStarInto (hpack source.1)

theorem sum_scaledBlockVarianceSelfUse_le_one
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (hpack : G.LocallyPacksInto (B * k))
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r) :
    (∑ v, G.scaledExtendedProfileBlockVarianceSelfUse R0 rho omega
      (extendedProfileBlockVarianceSelfScale rho s omega β q r B k)
      source sourceCode v) ≤ 1 := by
  rw [Finset.sum_eq_single source.1]
  · exact G.scaledExtendedProfileBlockVarianceSelfUse_le_one R0
      hB hk hn hs hspos hq hr0 hleft homega0 homega1 rho hrho hpack
      source sourceCode source.1
  · intro v _hv hv
    simp [scaledExtendedProfileBlockVarianceSelfUse, hv, Ne.symm hv]
  · simp

theorem sum_scaledExtendedProfileBlockVarianceUse_le_column
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (hpack : G.LocallyPacksInto (B * k))
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r) :
    (∑ row : G.ExtendedProfileBlockVarianceRow
        (B := B) (k := k) (β := β) (q := q) (r := r),
      G.scaledExtendedProfileBlockVarianceUse R0 rho omega
        (extendedProfileBlockVariancePairScale rho s omega β q r B k)
        (extendedProfileBlockVarianceSelfScale rho s omega β q r B k)
        source sourceCode row) ≤
      extendedProfileBlockVarianceColumnBound B k β q r := by
  rw [Fintype.sum_sum_type]
  exact add_le_add
    (G.sum_scaledBlockVarianceCandidateUse_le_column R0
      hB hn hs hspos hq hr0 hleft homega0 homega1 rho hrho hpack
      source sourceCode)
    (G.sum_scaledBlockVarianceSelfUse_le_one R0
      hB hk hn hs hspos hq hr0 hleft homega0 homega1 rho hrho hpack
      source sourceCode)

end WeightedSimpleGraph

end

end WeightedEdgeColoring
