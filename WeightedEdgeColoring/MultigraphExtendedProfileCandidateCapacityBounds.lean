import WeightedEdgeColoring.MultigraphExtendedProfileCandidateCapacityRows
import WeightedEdgeColoring.FiniteDependentWordMarginals
import WeightedEdgeColoring.MultigraphLargeStarCategoricalDependency

/-!
# Mean and column bounds for candidate-state capacity rows

This file supplies the estimates needed to feed the additive candidate rows
to the finite categorical packing selector.  Put

`M = extendedProfileStateBound beta q r`,
`delta = omega / M`, and
`kappa = 1 - omega + delta`.

The natural normalization is

`Bcap = rho * s * (M / omega)^2 = rho * s / delta^2`.

Every normalized source--state--row entry is at most one.  Every normalized
row mean is at most `n * rho / (Bcap * kappa)`.  Under a local `n`-bin
packing, the polynomial column bound proved below is
`n^2 * M * (K / beta + 1)`, where `K` is the padded large-slot bound.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)

def extendedProfileSmoothingDelta (omega β q r : ℝ) : ℝ :=
  omega / extendedProfileStateBound β q r

def extendedProfileSmoothingKappa (omega β q r : ℝ) : ℝ :=
  1 - omega + extendedProfileSmoothingDelta omega β q r

theorem extendedProfileProbability_le_one
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (v : G.V) (z : G.ExtendedProfileState R0 v) :
    G.extendedProfileProbability R0 v z ≤ 1 := by
  have hsingle : G.extendedProfileProbability R0 v z ≤
      ∑ z', G.extendedProfileProbability R0 v z' :=
    Finset.single_le_sum
      (fun z' _ ↦ G.extendedProfileProbability_nonneg R0 hs hq hr0
        hleft v z')
      (Finset.mem_univ z)
  simpa [G.sum_extendedProfileProbability R0 v] using hsingle

theorem extendedProfileSmoothingDelta_pos (homega : 0 < omega) :
    0 < extendedProfileSmoothingDelta omega β q r := by
  unfold extendedProfileSmoothingDelta extendedProfileStateBound
  positivity

theorem extendedProfileSmoothingKappa_pos
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) :
    0 < extendedProfileSmoothingKappa omega β q r := by
  unfold extendedProfileSmoothingKappa
  exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr homega1)
    (extendedProfileSmoothingDelta_pos (β := β) (q := q) (r := r) homega0)

/-- Smoothing dominates `kappa` times the original atom mass. -/
theorem kappa_mul_extendedProfileProbability_le_smoothed
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V) (z : G.ExtendedProfileState R0 v) :
    extendedProfileSmoothingKappa omega β q r *
        G.extendedProfileProbability R0 v z ≤
      G.smoothedExtendedProfileProbability R0 omega v z := by
  let p := G.extendedProfileProbability R0 v z
  let delta := extendedProfileSmoothingDelta omega β q r
  have hp0 : 0 ≤ p := G.extendedProfileProbability_nonneg R0 hs hq hr0
    hleft v z
  have hp1 : p ≤ 1 := G.extendedProfileProbability_le_one R0 hs hq hr0
    hleft v z
  have hdelta0 : 0 ≤ delta :=
    (extendedProfileSmoothingDelta_pos
      (β := β) (q := q) (r := r) homega0).le
  have hdeltaP : delta * p ≤ delta := by
    simpa using mul_le_mul_of_nonneg_left hp1 hdelta0
  have hcardNat := G.extendedProfileState_card_le R0 v
  have hcard : (Fintype.card (G.ExtendedProfileState R0 v) : ℝ) ≤
      extendedProfileStateBound β q r := by exact_mod_cast hcardNat
  have hcard0 : 0 < (Fintype.card (G.ExtendedProfileState R0 v) : ℝ) := by
    positivity
  have hbound0 : 0 < (extendedProfileStateBound β q r : ℝ) := by
    unfold extendedProfileStateBound
    positivity
  have huniform : delta ≤
      omega / Fintype.card (G.ExtendedProfileState R0 v) := by
    dsimp [delta, extendedProfileSmoothingDelta]
    exact (div_le_div_iff₀ hbound0 hcard0).2
      (mul_le_mul_of_nonneg_left hcard homega0.le)
  calc
    extendedProfileSmoothingKappa omega β q r * p =
        (1 - omega) * p + delta * p := by
      simp [extendedProfileSmoothingKappa, delta]
      ring
    _ ≤ (1 - omega) * p +
        omega / Fintype.card (G.ExtendedProfileState R0 v) := by
      exact add_le_add le_rfl (hdeltaP.trans huniform)
    _ = G.smoothedExtendedProfileProbability R0 omega v z := by
      rfl

/-! ## Symmetric endpoint expectation identities -/

/-- Existing files state the right-endpoint expectation explicitly.  This
is the symmetric left-endpoint form used when a candidate row is centered at
the second endpoint of an edge. -/
theorem extendedProfileProductOptionMass_left_expectation
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hy : G.extendedProfileEdgeColorMass
      (s := s) (β := β) (n := n) e ≠ 0)
    (Q : G.ExtendedProfileState R0 (G.snd e))
    (j : Fin (explicitLargeSlotBound β q r)) :
    (∑ P : G.ExtendedProfileState R0 (G.fst e),
      G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
        ∑ i, G.extendedProfileProductOptionMass R0 rho omega e P Q i j) =
      rho * G.extendedProfileLargeAssign R0 (G.snd e)
        (G.sndStarEdge e) Q j /
        G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q := by
  unfold extendedProfileProductOptionMass
  apply sum_pairedOption_left
  · exact hy
  · intro P
    exact (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
      homega0 homega1 _ P).ne'
  · exact (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
      homega0 homega1 _ Q).ne'
  · exact G.sum_extendedProfileLargeAssign_fst R0 e

theorem extendedProfileTinyProductOptionMass_left_expectation
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hy : G.extendedProfileTinyEdgeColorMass
      (s := s) (β := β) (n := n) e ≠ 0)
    (Q : G.ExtendedProfileState R0 (G.snd e)) :
    (∑ P : G.ExtendedProfileState R0 (G.fst e),
      G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
        G.extendedProfileTinyProductOptionMass R0 rho omega e P Q) =
      rho * G.extendedProfileTinyAssign R0 (G.snd e)
        (G.sndStarEdge e) Q /
        G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q := by
  have h := sum_pairedOption_left rho
    (G.extendedProfileTinyEdgeColorMass (s := s) (β := β) (n := n) e)
    (G.smoothedExtendedProfileProbability R0 omega (G.fst e))
    (G.smoothedExtendedProfileProbability R0 omega (G.snd e))
    (fun P (_ : Unit) ↦
      G.extendedProfileTinyAssign R0 (G.fst e) (G.fstStarEdge e) P)
    (fun Q (_ : Unit) ↦
      G.extendedProfileTinyAssign R0 (G.snd e) (G.sndStarEdge e) Q)
    Q () hy
    (fun P ↦ (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0
      hleft homega0 homega1 _ P).ne')
    (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
      homega0 homega1 _ Q).ne'
    (by simpa using G.sum_extendedProfileTinyAssign_fst R0 e)
  simpa [extendedProfileTinyProductOptionMass] using h

/-! ## Center assignments -/

private def largeCandidateCenterAssign
    (row : G.ExtendedProfileLargeCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) (e : G.E) : ℝ :=
  if h : G.Inc row.center e then
    G.extendedProfileLargeAssign R0 row.center ⟨e, h⟩
      row.candidate row.slot
  else 0

private def tinyCandidateCenterAssign
    (row : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) (e : G.E) : ℝ :=
  if h : G.Inc row.center e then
    G.extendedProfileTinyAssign R0 row.center ⟨e, h⟩ row.candidate
  else 0

private theorem sum_largeCandidateCenterAssign_le_probability
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (row : G.ExtendedProfileLargeCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    (∑ e, G.largeCandidateCenterAssign R0 row e) ≤
      G.extendedProfileProbability R0 row.center row.candidate := by
  calc
    (∑ e, G.largeCandidateCenterAssign R0 row e) =
        ∑ e ∈ Finset.univ.filter (G.Inc row.center),
          G.largeCandidateCenterAssign R0 row e := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hinc : G.Inc row.center e <;>
        simp [largeCandidateCenterAssign, hinc]
    _ = ∑ e : G.StarEdge row.center,
          G.largeCandidateCenterAssign R0 row e.1 := by
      exact Finset.sum_subtype (p := G.Inc row.center)
        (Finset.univ.filter (G.Inc row.center)) (by intro e; simp)
        (G.largeCandidateCenterAssign R0 row)
    _ =
        ∑ e : G.StarEdge row.center,
          G.extendedProfileLargeAssign R0 row.center e
            row.candidate row.slot := by
      apply Finset.sum_congr rfl
      intro e _he
      simp [largeCandidateCenterAssign, e.property]
    _ ≤ G.extendedProfileProbability R0 row.center row.candidate :=
      G.sum_extendedProfileLargeAssign_star_le R0 hs hq hr0 hleft
        row.center row.candidate row.slot

private theorem sum_weight_mul_tinyCandidateCenterAssign_le_probability_mul_reservoir
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (row : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    (∑ e, G.weight e * G.tinyCandidateCenterAssign R0 row e) ≤
      G.extendedProfileProbability R0 row.center row.candidate *
        G.extendedProfileReservoirSize R0 row.center row.candidate := by
  have hcap := G.sum_weight_mul_extendedProfileTinyAssign_le R0
    row.center row.candidate
  calc
    (∑ e, G.weight e * G.tinyCandidateCenterAssign R0 row e) =
        ∑ e ∈ Finset.univ.filter (G.Inc row.center),
          G.weight e * G.tinyCandidateCenterAssign R0 row e := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hinc : G.Inc row.center e <;>
        simp [tinyCandidateCenterAssign, hinc]
    _ = ∑ e : G.StarEdge row.center,
          G.weight e.1 * G.tinyCandidateCenterAssign R0 row e.1 := by
      exact Finset.sum_subtype (p := G.Inc row.center)
        (Finset.univ.filter (G.Inc row.center)) (by intro e; simp)
        (fun e ↦ G.weight e * G.tinyCandidateCenterAssign R0 row e)
    _ =
        ∑ e : G.StarEdge row.center,
          G.weight e.1 * G.extendedProfileTinyAssign R0 row.center e
            row.candidate := by
      apply Finset.sum_congr rfl
      intro e _he
      simp [tinyCandidateCenterAssign, e.property]
    _ ≤ G.extendedProfileProbability R0 row.center row.candidate *
          G.extendedProfileReservoirSize R0 row.center row.candidate := hcap

private theorem sum_weight_mul_tinyCandidateCenterAssign_le_probability
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (row : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    (∑ e, G.weight e * G.tinyCandidateCenterAssign R0 row e) ≤
      G.extendedProfileProbability R0 row.center row.candidate := by
  have hsharp :=
    G.sum_weight_mul_tinyCandidateCenterAssign_le_probability_mul_reservoir
      R0 hs hq hr0 hleft row
  have hres := G.extendedProfileReservoirSize_le_one R0
    row.center row.candidate
  have hp0 := G.extendedProfileProbability_nonneg R0
    hs hq hr0 hleft row.center row.candidate
  exact hsharp.trans (by simpa using mul_le_of_le_one_right hp0 hres)

/-! ## Exact one-edge expectations -/

private theorem largeCandidateEdge_mean
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ)
    (row : G.ExtendedProfileLargeCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) (e : G.E) :
    (∑ source : G.V,
      ∑ a : ExtendedProfilePackedWordState n β q r,
        G.paddedExtendedProfileWordProbability R0 omega source a *
          G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
            source a e row) =
      (n : ℝ) * rho * G.largeCandidateCenterAssign R0 row e /
        G.smoothedExtendedProfileProbability R0 omega
          row.center row.candidate := by
  classical
  rcases row with ⟨center, color, candidate, slot⟩
  let row : G.ExtendedProfileLargeCandidateRow R0
      (n := n) (β := β) (q := q) (r := r) :=
    { center := center, color := color, candidate := candidate, slot := slot }
  by_cases hfst : row.center = G.fst e
  · have hsnd : row.center ≠ G.snd e := by
      intro h
      exact G.noLoop e (hfst.symm.trans h)
    change center = G.fst e at hfst
    subst center
    have hfst : row.center = G.fst e := rfl
    have hcenter : G.largeCandidateCenterAssign R0 row e =
        G.extendedProfileLargeAssign R0 (G.fst e) (G.fstStarEdge e)
          candidate slot := by
      unfold largeCandidateCenterAssign
      split
      · dsimp [row]
        apply congrArg (fun se : G.StarEdge (G.fst e) ↦
          G.extendedProfileLargeAssign R0 (G.fst e) se candidate slot)
        apply Subtype.ext
        rfl
      · rename_i hinc
        exact (hinc (by simp [row, WeightedMultigraph.Inc])).elim
    let P : G.ExtendedProfileState R0 (G.fst e) := hfst ▸ row.candidate
    let y := G.extendedProfileEdgeColorMass
      (s := s) (β := β) (n := n) e
    have hlam : G.smoothedExtendedProfileProbability R0 omega
        (G.fst e) P ≠ 0 :=
      (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
        homega0 homega1 _ P).ne'
    by_cases hy : y = 0
    · have haCenter : G.largeCandidateCenterAssign R0 row e = 0 := by
        unfold largeCandidateCenterAssign
        split
        · rename_i hinc
          exact le_antisymm
            ((G.extendedProfileLargeAssign_le_edgeColorMass R0 row.center
              ⟨e, hinc⟩ row.candidate row.slot).trans_eq hy)
            (G.extendedProfileLargeAssign_nonneg R0 row.center
              ⟨e, hinc⟩ row.candidate row.slot)
        · rfl
      simp [row, packedExtendedProfileLargeCandidateEdgeUse, hfst, hsnd,
        extendedProfileProductOptionMass, pairedOption, y, hy,
        haCenter]
    · have hmarg :=
        FiniteDependentWordPadding.sum_paddedWordProbability_mul_decode_coordinate
          (fun v ↦ G.ExtendedProfileState R0 v)
          (G.extendedProfileStateEncoding R0)
          (G.inactiveExtendedProfileState R0)
          (fun v z ↦ G.smoothedExtendedProfileProbability R0 omega v z)
          (G.sum_smoothedExtendedProfileProbability R0 omega)
          (G.snd e) row.color
          (fun Q ↦ ∑ j,
            G.extendedProfileProductOptionMass R0 rho omega e P Q
              row.slot j)
      have hexpect := G.extendedProfileProductOptionMass_right_expectation
        R0 (rho := rho) hs hq hr0 hleft homega0 homega1 hy P row.slot
      calc
        (∑ source : G.V,
          ∑ a : ExtendedProfilePackedWordState n β q r,
            G.paddedExtendedProfileWordProbability R0 omega source a *
              G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
                source a e row) =
            (n : ℝ) *
              (∑ a : ExtendedProfilePackedWordState n β q r,
                G.paddedExtendedProfileWordProbability R0 omega (G.snd e) a *
                  ∑ j, G.extendedProfileProductOptionMass R0 rho omega e P
                    (G.decodeExtendedProfileWord R0 (G.snd e) a row.color)
                    row.slot j) := by
          rw [Fintype.sum_eq_single (G.snd e)]
          · simp [row, packedExtendedProfileLargeCandidateEdgeUse, hfst,
              hsnd, P, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
            apply Finset.sum_congr rfl
            intro a _ha
            rw [Finset.sum_mul, Finset.mul_sum]
          · intro source hsource
            simp [row, packedExtendedProfileLargeCandidateEdgeUse, hfst,
              hsnd, hsource]
        _ = (n : ℝ) *
            (∑ Q : G.ExtendedProfileState R0 (G.snd e),
              G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
                ∑ j, G.extendedProfileProductOptionMass R0 rho omega e P Q
                  row.slot j) := by
          congr 1
        _ = (n : ℝ) *
            (rho * G.extendedProfileLargeAssign R0 (G.fst e)
              (G.fstStarEdge e) P row.slot /
              G.smoothedExtendedProfileProbability R0 omega (G.fst e) P) := by
          rw [hexpect]
        _ = (n : ℝ) * rho * G.largeCandidateCenterAssign R0 row e /
            G.smoothedExtendedProfileProbability R0 omega
              row.center row.candidate := by
          rw [hcenter]
          simp [row, P]
          ring
  · by_cases hsnd : row.center = G.snd e
    · change center = G.snd e at hsnd
      subst center
      have hsnd : row.center = G.snd e := rfl
      have hcenter : G.largeCandidateCenterAssign R0 row e =
          G.extendedProfileLargeAssign R0 (G.snd e) (G.sndStarEdge e)
            candidate slot := by
        unfold largeCandidateCenterAssign
        split
        · dsimp [row]
          apply congrArg (fun se : G.StarEdge (G.snd e) ↦
            G.extendedProfileLargeAssign R0 (G.snd e) se candidate slot)
          apply Subtype.ext
          rfl
        · rename_i hinc
          exact (hinc (by simp [row, WeightedMultigraph.Inc])).elim
      let Q : G.ExtendedProfileState R0 (G.snd e) := hsnd ▸ row.candidate
      let y := G.extendedProfileEdgeColorMass
        (s := s) (β := β) (n := n) e
      have hlam : G.smoothedExtendedProfileProbability R0 omega
          (G.snd e) Q ≠ 0 :=
        (G.smoothedExtendedProfileProbability_pos R0 hs hq hr0 hleft
          homega0 homega1 _ Q).ne'
      by_cases hy : y = 0
      · have haCenter : G.largeCandidateCenterAssign R0 row e = 0 := by
          unfold largeCandidateCenterAssign
          split
          · rename_i hinc
            exact le_antisymm
              ((G.extendedProfileLargeAssign_le_edgeColorMass R0 row.center
                ⟨e, hinc⟩ row.candidate row.slot).trans_eq hy)
              (G.extendedProfileLargeAssign_nonneg R0 row.center
                ⟨e, hinc⟩ row.candidate row.slot)
          · rfl
        simp [row, packedExtendedProfileLargeCandidateEdgeUse, hfst, hsnd,
          extendedProfileProductOptionMass, pairedOption, y, hy,
          haCenter]
      · have hmarg :=
          FiniteDependentWordPadding.sum_paddedWordProbability_mul_decode_coordinate
            (fun v ↦ G.ExtendedProfileState R0 v)
            (G.extendedProfileStateEncoding R0)
            (G.inactiveExtendedProfileState R0)
            (fun v z ↦ G.smoothedExtendedProfileProbability R0 omega v z)
            (G.sum_smoothedExtendedProfileProbability R0 omega)
            (G.fst e) row.color
            (fun P ↦ ∑ i,
              G.extendedProfileProductOptionMass R0 rho omega e P Q
                i row.slot)
        have hexpect := G.extendedProfileProductOptionMass_left_expectation
          R0 (rho := rho) hs hq hr0 hleft homega0 homega1 hy Q row.slot
        calc
          (∑ source : G.V,
            ∑ a : ExtendedProfilePackedWordState n β q r,
              G.paddedExtendedProfileWordProbability R0 omega source a *
                G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
                  source a e row) =
              (n : ℝ) *
                (∑ a : ExtendedProfilePackedWordState n β q r,
                  G.paddedExtendedProfileWordProbability R0 omega (G.fst e) a *
                    ∑ i, G.extendedProfileProductOptionMass R0 rho omega e
                      (G.decodeExtendedProfileWord R0 (G.fst e) a row.color)
                      Q i row.slot) := by
            rw [Fintype.sum_eq_single (G.fst e)]
            · simp [row, packedExtendedProfileLargeCandidateEdgeUse, hfst,
                hsnd, Q, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
            · intro source hsource
              simp [row, packedExtendedProfileLargeCandidateEdgeUse, hfst,
                hsnd, hsource]
          _ = (n : ℝ) *
              (∑ P : G.ExtendedProfileState R0 (G.fst e),
                G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
                  ∑ i, G.extendedProfileProductOptionMass R0 rho omega e P Q
                    i row.slot) := by
            congr 1
          _ = (n : ℝ) *
              (rho * G.extendedProfileLargeAssign R0 (G.snd e)
                (G.sndStarEdge e) Q row.slot /
                G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q) := by
            rw [hexpect]
          _ = (n : ℝ) * rho * G.largeCandidateCenterAssign R0 row e /
              G.smoothedExtendedProfileProbability R0 omega
                row.center row.candidate := by
            rw [hcenter]
            simp [row, Q]
            ring
    · have hfst' : G.fst e ≠ row.center := Ne.symm hfst
      have hsnd' : G.snd e ≠ row.center := Ne.symm hsnd
      simp [row, packedExtendedProfileLargeCandidateEdgeUse,
        largeCandidateCenterAssign, WeightedMultigraph.Inc, hfst, hsnd,
        hfst', hsnd']

private theorem tinyCandidateEdge_mean
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ)
    (row : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) (e : G.E) :
    (∑ source : G.V,
      ∑ a : ExtendedProfilePackedWordState n β q r,
        G.paddedExtendedProfileWordProbability R0 omega source a *
          G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
            source a e row) =
      (n : ℝ) * G.weight e * rho *
          G.tinyCandidateCenterAssign R0 row e /
        G.smoothedExtendedProfileProbability R0 omega
          row.center row.candidate := by
  classical
  rcases row with ⟨center, color, candidate⟩
  let row : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r) :=
    { center := center, color := color, candidate := candidate }
  by_cases hfst : row.center = G.fst e
  · have hsnd : row.center ≠ G.snd e := by
      intro h
      exact G.noLoop e (hfst.symm.trans h)
    change center = G.fst e at hfst
    subst center
    have hfst : row.center = G.fst e := rfl
    have hcenter : G.tinyCandidateCenterAssign R0 row e =
        G.extendedProfileTinyAssign R0 (G.fst e) (G.fstStarEdge e)
          candidate := by
      unfold tinyCandidateCenterAssign
      split
      · dsimp [row]
        apply congrArg (fun se : G.StarEdge (G.fst e) ↦
          G.extendedProfileTinyAssign R0 (G.fst e) se candidate)
        apply Subtype.ext
        rfl
      · rename_i hinc
        exact (hinc (by simp [row, WeightedMultigraph.Inc])).elim
    let P : G.ExtendedProfileState R0 (G.fst e) := hfst ▸ row.candidate
    let y := G.extendedProfileTinyEdgeColorMass
      (s := s) (β := β) (n := n) e
    by_cases hy : y = 0
    · have haCenter : G.tinyCandidateCenterAssign R0 row e = 0 := by
        unfold tinyCandidateCenterAssign
        split
        · rename_i hinc
          exact le_antisymm
            ((G.extendedProfileTinyAssign_le_edgeColorMass R0 row.center
              ⟨e, hinc⟩ row.candidate).trans_eq hy)
            (G.extendedProfileTinyAssign_nonneg R0 row.center
              ⟨e, hinc⟩ row.candidate)
        · rfl
      simp [row, packedExtendedProfileTinyCandidateEdgeUse, hfst, hsnd,
        extendedProfileTinyProductOptionMass, pairedOption, y, hy,
        haCenter]
    · have hmarg :=
        FiniteDependentWordPadding.sum_paddedWordProbability_mul_decode_coordinate
          (fun v ↦ G.ExtendedProfileState R0 v)
          (G.extendedProfileStateEncoding R0)
          (G.inactiveExtendedProfileState R0)
          (fun v z ↦ G.smoothedExtendedProfileProbability R0 omega v z)
          (G.sum_smoothedExtendedProfileProbability R0 omega)
          (G.snd e) row.color
          (fun Q ↦ G.extendedProfileTinyProductOptionMass R0 rho omega e P Q)
      have hexpect := G.extendedProfileTinyProductOptionMass_right_expectation
        R0 (rho := rho) hs hq hr0 hleft homega0 homega1 hy P
      calc
        (∑ source : G.V,
          ∑ a : ExtendedProfilePackedWordState n β q r,
            G.paddedExtendedProfileWordProbability R0 omega source a *
              G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
                source a e row) =
            (n : ℝ) * G.weight e *
              (∑ a : ExtendedProfilePackedWordState n β q r,
                G.paddedExtendedProfileWordProbability R0 omega (G.snd e) a *
                  G.extendedProfileTinyProductOptionMass R0 rho omega e P
                    (G.decodeExtendedProfileWord R0 (G.snd e) a row.color)) := by
          rw [Fintype.sum_eq_single (G.snd e)]
          · simp [row, packedExtendedProfileTinyCandidateEdgeUse, hfst,
              hsnd, P, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
          · intro source hsource
            simp [row, packedExtendedProfileTinyCandidateEdgeUse, hfst,
              hsnd, hsource]
        _ = (n : ℝ) * G.weight e *
            (∑ Q : G.ExtendedProfileState R0 (G.snd e),
              G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
                G.extendedProfileTinyProductOptionMass R0 rho omega e P Q) := by
          congr 1
        _ = (n : ℝ) * G.weight e *
            (rho * G.extendedProfileTinyAssign R0 (G.fst e)
              (G.fstStarEdge e) P /
              G.smoothedExtendedProfileProbability R0 omega (G.fst e) P) := by
          rw [hexpect]
        _ = (n : ℝ) * G.weight e * rho *
              G.tinyCandidateCenterAssign R0 row e /
            G.smoothedExtendedProfileProbability R0 omega
              row.center row.candidate := by
          rw [hcenter]
          simp [row, P]
          ring
  · by_cases hsnd : row.center = G.snd e
    · change center = G.snd e at hsnd
      subst center
      have hsnd : row.center = G.snd e := rfl
      have hcenter : G.tinyCandidateCenterAssign R0 row e =
          G.extendedProfileTinyAssign R0 (G.snd e) (G.sndStarEdge e)
            candidate := by
        unfold tinyCandidateCenterAssign
        split
        · dsimp [row]
          apply congrArg (fun se : G.StarEdge (G.snd e) ↦
            G.extendedProfileTinyAssign R0 (G.snd e) se candidate)
          apply Subtype.ext
          rfl
        · rename_i hinc
          exact (hinc (by simp [row, WeightedMultigraph.Inc])).elim
      let Q : G.ExtendedProfileState R0 (G.snd e) := hsnd ▸ row.candidate
      let y := G.extendedProfileTinyEdgeColorMass
        (s := s) (β := β) (n := n) e
      by_cases hy : y = 0
      · have haCenter : G.tinyCandidateCenterAssign R0 row e = 0 := by
          unfold tinyCandidateCenterAssign
          split
          · rename_i hinc
            exact le_antisymm
              ((G.extendedProfileTinyAssign_le_edgeColorMass R0 row.center
                ⟨e, hinc⟩ row.candidate).trans_eq hy)
              (G.extendedProfileTinyAssign_nonneg R0 row.center
                ⟨e, hinc⟩ row.candidate)
          · rfl
        simp [row, packedExtendedProfileTinyCandidateEdgeUse, hfst, hsnd,
          extendedProfileTinyProductOptionMass, pairedOption, y, hy,
          haCenter]
      · have hmarg :=
          FiniteDependentWordPadding.sum_paddedWordProbability_mul_decode_coordinate
            (fun v ↦ G.ExtendedProfileState R0 v)
            (G.extendedProfileStateEncoding R0)
            (G.inactiveExtendedProfileState R0)
            (fun v z ↦ G.smoothedExtendedProfileProbability R0 omega v z)
            (G.sum_smoothedExtendedProfileProbability R0 omega)
            (G.fst e) row.color
            (fun P ↦ G.extendedProfileTinyProductOptionMass R0 rho omega e P Q)
        have hexpect :=
          G.extendedProfileTinyProductOptionMass_left_expectation R0
            (rho := rho) hs hq hr0 hleft homega0 homega1 hy Q
        calc
          (∑ source : G.V,
            ∑ a : ExtendedProfilePackedWordState n β q r,
              G.paddedExtendedProfileWordProbability R0 omega source a *
                G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
                  source a e row) =
              (n : ℝ) * G.weight e *
                (∑ a : ExtendedProfilePackedWordState n β q r,
                  G.paddedExtendedProfileWordProbability R0 omega (G.fst e) a *
                    G.extendedProfileTinyProductOptionMass R0 rho omega e
                      (G.decodeExtendedProfileWord R0 (G.fst e) a row.color)
                      Q) := by
            rw [Fintype.sum_eq_single (G.fst e)]
            · simp [row, packedExtendedProfileTinyCandidateEdgeUse, hfst,
                hsnd, Q, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
            · intro source hsource
              simp [row, packedExtendedProfileTinyCandidateEdgeUse, hfst,
                hsnd, hsource]
          _ = (n : ℝ) * G.weight e *
              (∑ P : G.ExtendedProfileState R0 (G.fst e),
                G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
                  G.extendedProfileTinyProductOptionMass R0 rho omega e P Q) := by
            congr 1
          _ = (n : ℝ) * G.weight e *
              (rho * G.extendedProfileTinyAssign R0 (G.snd e)
                (G.sndStarEdge e) Q /
                G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q) := by
            rw [hexpect]
          _ = (n : ℝ) * G.weight e * rho *
                G.tinyCandidateCenterAssign R0 row e /
              G.smoothedExtendedProfileProbability R0 omega
                row.center row.candidate := by
            rw [hcenter]
            simp [row, Q]
            ring
    · have hfst' : G.fst e ≠ row.center := Ne.symm hfst
      have hsnd' : G.snd e ≠ row.center := Ne.symm hsnd
      simp [row, packedExtendedProfileTinyCandidateEdgeUse,
        tinyCandidateCenterAssign, WeightedMultigraph.Inc, hfst, hsnd,
        hfst', hsnd']

/-! ## Row means -/

theorem rowMean_largeCandidateUse_eq
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ)
    (row : G.ExtendedProfileLargeCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
        (G.paddedExtendedProfileWordProbability R0 omega)
        (G.packedExtendedProfileLargeCandidateUse R0 rho omega) row =
      (n : ℝ) * rho *
          (∑ e, G.largeCandidateCenterAssign R0 row e) /
        G.smoothedExtendedProfileProbability R0 omega
          row.center row.candidate := by
  classical
  unfold FiniteCategoricalSelection.rowMean
  calc
    (∑ source : G.V,
      ∑ a : ExtendedProfilePackedWordState n β q r,
        G.paddedExtendedProfileWordProbability R0 omega source a *
          G.packedExtendedProfileLargeCandidateUse R0 rho omega
            source a row) =
        ∑ source : G.V,
          ∑ a : ExtendedProfilePackedWordState n β q r,
            ∑ e, G.paddedExtendedProfileWordProbability R0 omega source a *
              G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
                source a e row := by
      apply Finset.sum_congr rfl
      intro source _hsource
      apply Finset.sum_congr rfl
      intro a _ha
      unfold packedExtendedProfileLargeCandidateUse
      rw [Finset.mul_sum]
    _ = ∑ source : G.V, ∑ e, ∑ a,
          G.paddedExtendedProfileWordProbability R0 omega source a *
            G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
              source a e row := by
      apply Finset.sum_congr rfl
      intro source _hsource
      rw [Finset.sum_comm]
    _ = ∑ e, ∑ source : G.V, ∑ a,
          G.paddedExtendedProfileWordProbability R0 omega source a *
            G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
              source a e row := by
      rw [Finset.sum_comm]
    _ = ∑ e, (n : ℝ) * rho * G.largeCandidateCenterAssign R0 row e /
          G.smoothedExtendedProfileProbability R0 omega
            row.center row.candidate := by
      apply Finset.sum_congr rfl
      intro e _he
      exact G.largeCandidateEdge_mean R0 hn hs hq hr0 hleft
        homega0 homega1 rho row e
    _ = (n : ℝ) * rho *
          (∑ e, G.largeCandidateCenterAssign R0 row e) /
        G.smoothedExtendedProfileProbability R0 omega
          row.center row.candidate := by
      rw [Finset.mul_sum, Finset.sum_div]

theorem rowMean_tinyCandidateUse_eq
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ)
    (row : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
        (G.paddedExtendedProfileWordProbability R0 omega)
        (G.packedExtendedProfileTinyCandidateUse R0 rho omega) row =
      (n : ℝ) * rho *
          (∑ e, G.weight e * G.tinyCandidateCenterAssign R0 row e) /
        G.smoothedExtendedProfileProbability R0 omega
          row.center row.candidate := by
  classical
  unfold FiniteCategoricalSelection.rowMean
  calc
    (∑ source : G.V,
      ∑ a : ExtendedProfilePackedWordState n β q r,
        G.paddedExtendedProfileWordProbability R0 omega source a *
          G.packedExtendedProfileTinyCandidateUse R0 rho omega
            source a row) =
        ∑ source : G.V,
          ∑ a : ExtendedProfilePackedWordState n β q r,
            ∑ e, G.paddedExtendedProfileWordProbability R0 omega source a *
              G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
                source a e row := by
      apply Finset.sum_congr rfl
      intro source _hsource
      apply Finset.sum_congr rfl
      intro a _ha
      unfold packedExtendedProfileTinyCandidateUse
      rw [Finset.mul_sum]
    _ = ∑ source : G.V, ∑ e, ∑ a,
          G.paddedExtendedProfileWordProbability R0 omega source a *
            G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
              source a e row := by
      apply Finset.sum_congr rfl
      intro source _hsource
      rw [Finset.sum_comm]
    _ = ∑ e, ∑ source : G.V, ∑ a,
          G.paddedExtendedProfileWordProbability R0 omega source a *
            G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
              source a e row := by
      rw [Finset.sum_comm]
    _ = ∑ e, (n : ℝ) * G.weight e * rho *
          G.tinyCandidateCenterAssign R0 row e /
          G.smoothedExtendedProfileProbability R0 omega
            row.center row.candidate := by
      apply Finset.sum_congr rfl
      intro e _he
      exact G.tinyCandidateEdge_mean R0 hn hs hq hr0 hleft
        homega0 homega1 rho row e
    _ = (n : ℝ) * rho *
          (∑ e, G.weight e * G.tinyCandidateCenterAssign R0 row e) /
        G.smoothedExtendedProfileProbability R0 omega
          row.center row.candidate := by
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e _he
      ring

private theorem centerMass_div_smoothed_le_inv_kappa
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    {v : G.V} {z : G.ExtendedProfileState R0 v}
    {mass : ℝ} (hmass0 : 0 ≤ mass)
    (hmass : mass ≤ G.extendedProfileProbability R0 v z) :
    mass / G.smoothedExtendedProfileProbability R0 omega v z ≤
      1 / extendedProfileSmoothingKappa omega β q r := by
  have hlam := G.smoothedExtendedProfileProbability_pos R0 hs hq hr0
    hleft homega0 homega1 v z
  have hkappa := extendedProfileSmoothingKappa_pos
    (β := β) (q := q) (r := r) homega0 homega1
  apply (div_le_div_iff₀ hlam hkappa).2
  calc
    mass * extendedProfileSmoothingKappa omega β q r ≤
        G.extendedProfileProbability R0 v z *
          extendedProfileSmoothingKappa omega β q r :=
      mul_le_mul_of_nonneg_right hmass hkappa.le
    _ = extendedProfileSmoothingKappa omega β q r *
          G.extendedProfileProbability R0 v z := by ring
    _ ≤ G.smoothedExtendedProfileProbability R0 omega v z :=
      G.kappa_mul_extendedProfileProbability_le_smoothed R0 hs hq hr0
        hleft homega0 homega1 v z
    _ = 1 * G.smoothedExtendedProfileProbability R0 omega v z := by ring

/-- Retaining a nonnegative reservoir factor in the center-mass estimate
retains the same factor after smoothing. -/
private theorem centerMass_div_smoothed_le_reservoir_div_kappa
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    {v : G.V} {z : G.ExtendedProfileState R0 v}
    {mass reservoir : ℝ} (hreservoir : 0 ≤ reservoir)
    (hmass : mass ≤
      G.extendedProfileProbability R0 v z * reservoir) :
    mass / G.smoothedExtendedProfileProbability R0 omega v z ≤
      reservoir / extendedProfileSmoothingKappa omega β q r := by
  have hlam := G.smoothedExtendedProfileProbability_pos R0 hs hq hr0
    hleft homega0 homega1 v z
  have hkappa := extendedProfileSmoothingKappa_pos
    (β := β) (q := q) (r := r) homega0 homega1
  apply (div_le_div_iff₀ hlam hkappa).2
  calc
    mass * extendedProfileSmoothingKappa omega β q r ≤
        (G.extendedProfileProbability R0 v z * reservoir) *
          extendedProfileSmoothingKappa omega β q r :=
      mul_le_mul_of_nonneg_right hmass hkappa.le
    _ = reservoir *
        (extendedProfileSmoothingKappa omega β q r *
          G.extendedProfileProbability R0 v z) := by ring
    _ ≤ reservoir *
        G.smoothedExtendedProfileProbability R0 omega v z :=
      mul_le_mul_of_nonneg_left
        (G.kappa_mul_extendedProfileProbability_le_smoothed R0
          hs hq hr0 hleft homega0 homega1 v z) hreservoir
    _ = reservoir *
        G.smoothedExtendedProfileProbability R0 omega v z := rfl

/-- The expected tiny candidate-row load retains the reservoir size of its
fixed center state.  This is the sharp form needed after a supported center
state is selected. -/
theorem rowMean_tinyCandidateUse_le_reservoir
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (row : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
        (G.paddedExtendedProfileWordProbability R0 omega)
        (G.packedExtendedProfileTinyCandidateUse R0 rho omega) row ≤
      (n : ℝ) * rho *
          G.extendedProfileReservoirSize R0 row.center row.candidate /
        extendedProfileSmoothingKappa omega β q r := by
  rw [G.rowMean_tinyCandidateUse_eq R0 hn hs hq hr0 hleft
    homega0 homega1 rho row]
  have hratio :=
    G.centerMass_div_smoothed_le_reservoir_div_kappa R0
      hs hq hr0 hleft homega0 homega1
      (G.extendedProfileReservoirSize_nonneg R0 row.center row.candidate)
      (G.sum_weight_mul_tinyCandidateCenterAssign_le_probability_mul_reservoir R0
        hs hq hr0 hleft row)
  have hcoef0 : 0 ≤ (n : ℝ) * rho :=
    mul_nonneg (Nat.cast_nonneg n) hrho
  calc
    (n : ℝ) * rho *
          (∑ e, G.weight e * G.tinyCandidateCenterAssign R0 row e) /
          G.smoothedExtendedProfileProbability R0 omega
            row.center row.candidate =
        ((n : ℝ) * rho) *
          ((∑ e, G.weight e * G.tinyCandidateCenterAssign R0 row e) /
            G.smoothedExtendedProfileProbability R0 omega
              row.center row.candidate) := by ring
    _ ≤ ((n : ℝ) * rho) *
        (G.extendedProfileReservoirSize R0 row.center row.candidate /
          extendedProfileSmoothingKappa omega β q r) :=
      mul_le_mul_of_nonneg_left hratio hcoef0
    _ = (n : ℝ) * rho *
          G.extendedProfileReservoirSize R0 row.center row.candidate /
        extendedProfileSmoothingKappa omega β q r := by ring

/-- Normalized sharp tiny-row mean bound. -/
theorem rowMean_scaledTinyCandidateCapacityUse_le_reservoir
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s)
    (row : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
        (G.paddedExtendedProfileWordProbability R0 omega)
        (G.scaledPackedExtendedProfileCandidateCapacityUse R0 rho omega
          (extendedProfileCandidateCapacityScale rho s omega β q r))
        (Sum.inr row) ≤
      ((n : ℝ) * rho *
          G.extendedProfileReservoirSize R0 row.center row.candidate) /
        (extendedProfileCandidateCapacityScale rho s omega β q r *
          extendedProfileSmoothingKappa omega β q r) := by
  let scale := extendedProfileCandidateCapacityScale rho s omega β q r
  have hraw := G.rowMean_tinyCandidateUse_le_reservoir R0
    hn hs hq hr0 hleft homega0 homega1 hrho.le row
  have hscale : 0 < scale :=
    extendedProfileCandidateCapacityScale_pos
      (β := β) (q := q) (r := r) hrho hspos homega0
  unfold FiniteCategoricalSelection.rowMean
    scaledPackedExtendedProfileCandidateCapacityUse
    packedExtendedProfileCandidateCapacityUse at ⊢
  have hrewrite :
      (∑ source : G.V,
        ∑ a : ExtendedProfilePackedWordState n β q r,
          G.paddedExtendedProfileWordProbability R0 omega source a *
            (G.packedExtendedProfileTinyCandidateUse R0 rho omega
              source a row / scale)) =
        (∑ source : G.V,
          ∑ a : ExtendedProfilePackedWordState n β q r,
            G.paddedExtendedProfileWordProbability R0 omega source a *
              G.packedExtendedProfileTinyCandidateUse R0 rho omega
                source a row) / scale := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro source _hsource
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  change
    (∑ source : G.V,
      ∑ a : ExtendedProfilePackedWordState n β q r,
        G.paddedExtendedProfileWordProbability R0 omega source a *
          (G.packedExtendedProfileTinyCandidateUse R0 rho omega
            source a row / scale)) ≤
      ((n : ℝ) * rho *
          G.extendedProfileReservoirSize R0 row.center row.candidate) /
        (scale * extendedProfileSmoothingKappa omega β q r)
  rw [hrewrite]
  change FiniteCategoricalSelection.rowMean
      (G.paddedExtendedProfileWordProbability R0 omega)
      (G.packedExtendedProfileTinyCandidateUse R0 rho omega) row / scale ≤ _
  calc
    FiniteCategoricalSelection.rowMean
        (G.paddedExtendedProfileWordProbability R0 omega)
        (G.packedExtendedProfileTinyCandidateUse R0 rho omega) row / scale ≤
      (((n : ℝ) * rho *
          G.extendedProfileReservoirSize R0 row.center row.candidate) /
        extendedProfileSmoothingKappa omega β q r) / scale :=
      div_le_div_of_nonneg_right hraw hscale.le
    _ = ((n : ℝ) * rho *
          G.extendedProfileReservoirSize R0 row.center row.candidate) /
        (scale * extendedProfileSmoothingKappa omega β q r) := by ring

theorem rowMean_candidateCapacityUse_le
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
        (G.paddedExtendedProfileWordProbability R0 omega)
        (G.packedExtendedProfileCandidateCapacityUse R0 rho omega) row ≤
      (n : ℝ) * rho /
        extendedProfileSmoothingKappa omega β q r := by
  rcases row with large | tiny
  · change FiniteCategoricalSelection.rowMean
      (G.paddedExtendedProfileWordProbability R0 omega)
      (G.packedExtendedProfileLargeCandidateUse R0 rho omega) large ≤ _
    rw [G.rowMean_largeCandidateUse_eq R0 hn hs hq hr0 hleft
      homega0 homega1 rho large]
    have hmass0 : 0 ≤ ∑ e, G.largeCandidateCenterAssign R0 large e := by
      apply Finset.sum_nonneg
      intro e _he
      unfold largeCandidateCenterAssign
      split
      · exact G.extendedProfileLargeAssign_nonneg R0 _ _ _ _
      · exact le_rfl
    have hratio := G.centerMass_div_smoothed_le_inv_kappa R0
      hs hq hr0 hleft homega0 homega1 hmass0
      (G.sum_largeCandidateCenterAssign_le_probability R0 hs hq hr0
        hleft large)
    have hcoef0 : 0 ≤ (n : ℝ) * rho :=
      mul_nonneg (Nat.cast_nonneg n) hrho
    calc
      (n : ℝ) * rho * (∑ e, G.largeCandidateCenterAssign R0 large e) /
          G.smoothedExtendedProfileProbability R0 omega
            large.center large.candidate =
          ((n : ℝ) * rho) *
            ((∑ e, G.largeCandidateCenterAssign R0 large e) /
              G.smoothedExtendedProfileProbability R0 omega
                large.center large.candidate) := by ring
      _ ≤ ((n : ℝ) * rho) *
          (1 / extendedProfileSmoothingKappa omega β q r) :=
        mul_le_mul_of_nonneg_left hratio hcoef0
      _ = (n : ℝ) * rho /
          extendedProfileSmoothingKappa omega β q r := by ring
  · change FiniteCategoricalSelection.rowMean
      (G.paddedExtendedProfileWordProbability R0 omega)
      (G.packedExtendedProfileTinyCandidateUse R0 rho omega) tiny ≤ _
    rw [G.rowMean_tinyCandidateUse_eq R0 hn hs hq hr0 hleft
      homega0 homega1 rho tiny]
    have hmass0 : 0 ≤
        ∑ e, G.weight e * G.tinyCandidateCenterAssign R0 tiny e := by
      apply Finset.sum_nonneg
      intro e _he
      apply mul_nonneg (G.weight_nonneg e)
      unfold tinyCandidateCenterAssign
      split
      · exact G.extendedProfileTinyAssign_nonneg R0 _ _ _
      · exact le_rfl
    have hratio := G.centerMass_div_smoothed_le_inv_kappa R0
      hs hq hr0 hleft homega0 homega1 hmass0
      (G.sum_weight_mul_tinyCandidateCenterAssign_le_probability R0
        hs hq hr0 hleft tiny)
    have hcoef0 : 0 ≤ (n : ℝ) * rho :=
      mul_nonneg (Nat.cast_nonneg n) hrho
    calc
      (n : ℝ) * rho *
          (∑ e, G.weight e * G.tinyCandidateCenterAssign R0 tiny e) /
          G.smoothedExtendedProfileProbability R0 omega
            tiny.center tiny.candidate =
          ((n : ℝ) * rho) *
            ((∑ e, G.weight e * G.tinyCandidateCenterAssign R0 tiny e) /
              G.smoothedExtendedProfileProbability R0 omega
                tiny.center tiny.candidate) := by ring
      _ ≤ ((n : ℝ) * rho) *
          (1 / extendedProfileSmoothingKappa omega β q r) :=
        mul_le_mul_of_nonneg_left hratio hcoef0
      _ = (n : ℝ) * rho /
          extendedProfileSmoothingKappa omega β q r := by ring

/-- Normalized row-mean bound in the exact form consumed by the selector. -/
theorem rowMean_scaledCandidateCapacityUse_le
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
        (G.paddedExtendedProfileWordProbability R0 omega)
        (G.scaledPackedExtendedProfileCandidateCapacityUse R0 rho omega
          (extendedProfileCandidateCapacityScale rho s omega β q r)) row ≤
      ((n : ℝ) * rho) /
        (extendedProfileCandidateCapacityScale rho s omega β q r *
          extendedProfileSmoothingKappa omega β q r) := by
  have hraw := G.rowMean_candidateCapacityUse_le R0 hn hs hq hr0 hleft
    homega0 homega1 hrho.le row
  have hscale := extendedProfileCandidateCapacityScale_pos
    (β := β) (q := q) (r := r) hrho hspos homega0
  unfold FiniteCategoricalSelection.rowMean
    scaledPackedExtendedProfileCandidateCapacityUse at ⊢
  have hrewrite :
      (∑ source : G.V,
        ∑ a : ExtendedProfilePackedWordState n β q r,
          G.paddedExtendedProfileWordProbability R0 omega source a *
            (G.packedExtendedProfileCandidateCapacityUse R0 rho omega
              source a row /
                extendedProfileCandidateCapacityScale rho s omega β q r)) =
        (∑ source : G.V,
          ∑ a : ExtendedProfilePackedWordState n β q r,
            G.paddedExtendedProfileWordProbability R0 omega source a *
              G.packedExtendedProfileCandidateCapacityUse R0 rho omega
                source a row) /
          extendedProfileCandidateCapacityScale rho s omega β q r := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro source _hsource
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  rw [hrewrite]
  change FiniteCategoricalSelection.rowMean
      (G.paddedExtendedProfileWordProbability R0 omega)
      (G.packedExtendedProfileCandidateCapacityUse R0 rho omega) row /
        extendedProfileCandidateCapacityScale rho s omega β q r ≤ _
  calc
    FiniteCategoricalSelection.rowMean
        (G.paddedExtendedProfileWordProbability R0 omega)
        (G.packedExtendedProfileCandidateCapacityUse R0 rho omega) row /
          extendedProfileCandidateCapacityScale rho s omega β q r ≤
        (((n : ℝ) * rho) /
          extendedProfileSmoothingKappa omega β q r) /
            extendedProfileCandidateCapacityScale rho s omega β q r :=
      div_le_div_of_nonneg_right hraw hscale.le
    _ = ((n : ℝ) * rho) /
        (extendedProfileCandidateCapacityScale rho s omega β q r *
          extendedProfileSmoothingKappa omega β q r) := by ring

/-! ## A polynomial source-state column bound -/

private theorem sum_largeCandidateRows
    (f : G.ExtendedProfileLargeCandidateRow R0
      (n := n) (β := β) (q := q) (r := r) → ℝ) :
    (∑ row, f row) =
      ∑ v, ∑ c, ∑ z : G.ExtendedProfileState R0 v,
        ∑ i, f { center := v, color := c, candidate := z, slot := i } := by
  calc
    (∑ row, f row) =
        ∑ x : Σ v : G.V, Fin n × G.ExtendedProfileState R0 v ×
          Fin (explicitLargeSlotBound β q r),
          f ((G.extendedProfileLargeCandidateRowEquiv R0).symm x) := by
      exact Fintype.sum_equiv
        (G.extendedProfileLargeCandidateRowEquiv R0) _ _
        (fun _ ↦ rfl)
    _ = ∑ v, ∑ c, ∑ z : G.ExtendedProfileState R0 v,
        ∑ i, f { center := v, color := c, candidate := z, slot := i } := by
      simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
      rfl

private theorem sum_tinyCandidateRows
    (f : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r) → ℝ) :
    (∑ row, f row) =
      ∑ v, ∑ c, ∑ z : G.ExtendedProfileState R0 v,
        f { center := v, color := c, candidate := z } := by
  calc
    (∑ row, f row) =
        ∑ x : Σ v : G.V, Fin n × G.ExtendedProfileState R0 v,
          f ((G.extendedProfileTinyCandidateRowEquiv R0).symm x) := by
      exact Fintype.sum_equiv
        (G.extendedProfileTinyCandidateRowEquiv R0) _ _
        (fun _ ↦ rfl)
    _ = ∑ v, ∑ c, ∑ z : G.ExtendedProfileState R0 v,
        f { center := v, color := c, candidate := z } := by
      simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
      rfl

private theorem sum_largeCandidateRows_edge_le
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s)
    (source : G.V) (sourceCode : ExtendedProfilePackedWordState n β q r)
    (e : G.E) :
    (∑ row : G.ExtendedProfileLargeCandidateRow R0
        (n := n) (β := β) (q := q) (r := r),
      G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
        source sourceCode e row /
          extendedProfileCandidateCapacityScale rho s omega β q r) ≤
      if G.Inc source e ∧ β ≤ G.weight e then
        (n : ℝ) * extendedProfileStateBound β q r *
          explicitLargeSlotBound β q r
      else 0 := by
  classical
  rw [G.sum_largeCandidateRows R0]
  by_cases hsourceFst : source = G.fst e
  · have hsourceSnd : source ≠ G.snd e := by
      intro h
      exact G.noLoop e (hsourceFst.symm.trans h)
    subst source
    have hsourceSnd' : G.snd e ≠ G.fst e := Ne.symm hsourceSnd
    by_cases hlarge : β ≤ G.weight e
    · simp only [WeightedMultigraph.Inc, eq_self, true_or, true_and,
        hlarge, if_true]
      have hterm : ∀ (c : Fin n)
          (z : G.ExtendedProfileState R0 (G.snd e))
          (i : Fin (explicitLargeSlotBound β q r)),
          G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
              (G.fst e) sourceCode e
                { center := G.snd e, color := c, candidate := z, slot := i } /
              extendedProfileCandidateCapacityScale rho s omega β q r ≤ 1 := by
        intro c z i
        apply (div_le_one (extendedProfileCandidateCapacityScale_pos
          (β := β) (q := q) (r := r) hrho hspos homega0)).2
        exact G.packedExtendedProfileLargeCandidateEdgeUse_le_scale R0
          hn hs hq hr0 hleft homega0 homega1 hrho.le (G.fst e) sourceCode e _
      have hsum :
          (∑ c : Fin n, ∑ z : G.ExtendedProfileState R0 (G.snd e),
            ∑ i : Fin (explicitLargeSlotBound β q r),
              G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
                (G.fst e) sourceCode e
                  { center := G.snd e, color := c, candidate := z, slot := i } /
                extendedProfileCandidateCapacityScale rho s omega β q r) ≤
            ∑ _c : Fin n, ∑ _z : G.ExtendedProfileState R0 (G.snd e),
              ∑ _i : Fin (explicitLargeSlotBound β q r), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro c _hc
        apply Finset.sum_le_sum
        intro z _hz
        apply Finset.sum_le_sum
        intro i _hi
        exact hterm c z i
      have hcard := G.extendedProfileState_card_le R0 (G.snd e)
      calc
        (∑ v, ∑ c, ∑ z : G.ExtendedProfileState R0 v, ∑ i,
            G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
              (G.fst e) sourceCode e
                { center := v, color := c, candidate := z, slot := i } /
                extendedProfileCandidateCapacityScale rho s omega β q r) =
            ∑ c, ∑ z : G.ExtendedProfileState R0 (G.snd e), ∑ i,
              G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
                (G.fst e) sourceCode e
                  { center := G.snd e, color := c, candidate := z, slot := i } /
                  extendedProfileCandidateCapacityScale rho s omega β q r := by
          apply Fintype.sum_eq_single (G.snd e)
          intro v hv
          simp [packedExtendedProfileLargeCandidateEdgeUse, hv,
            hsourceSnd, hsourceSnd']
        _ ≤ ∑ _c : Fin n, ∑ _z : G.ExtendedProfileState R0 (G.snd e),
            ∑ _i : Fin (explicitLargeSlotBound β q r), (1 : ℝ) := hsum
        _ = (n : ℝ) * Fintype.card (G.ExtendedProfileState R0 (G.snd e)) *
            explicitLargeSlotBound β q r := by simp; ring
        _ ≤ (n : ℝ) * extendedProfileStateBound β q r *
            explicitLargeSlotBound β q r := by
          gcongr
    · have hy : G.extendedProfileEdgeColorMass
          (s := s) (β := β) (n := n) e = 0 := by
        simp [extendedProfileEdgeColorMass, hlarge]
      simp [WeightedMultigraph.Inc, hsourceSnd, hsourceSnd', hlarge,
        packedExtendedProfileLargeCandidateEdgeUse,
        extendedProfileProductOptionMass, pairedOption, hy]
  · by_cases hsourceSnd : source = G.snd e
    · subst source
      have hsourceFst' : G.fst e ≠ G.snd e := Ne.symm hsourceFst
      by_cases hlarge : β ≤ G.weight e
      · simp only [WeightedMultigraph.Inc, hsourceFst', eq_self,
          false_or, true_and, hlarge, if_true]
        have hterm : ∀ (c : Fin n)
            (z : G.ExtendedProfileState R0 (G.fst e))
            (i : Fin (explicitLargeSlotBound β q r)),
            G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
                (G.snd e) sourceCode e
                  { center := G.fst e, color := c, candidate := z, slot := i } /
                extendedProfileCandidateCapacityScale rho s omega β q r ≤ 1 := by
          intro c z i
          apply (div_le_one (extendedProfileCandidateCapacityScale_pos
            (β := β) (q := q) (r := r) hrho hspos homega0)).2
          exact G.packedExtendedProfileLargeCandidateEdgeUse_le_scale R0
            hn hs hq hr0 hleft homega0 homega1 hrho.le (G.snd e) sourceCode e _
        have hsum :
            (∑ c : Fin n, ∑ z : G.ExtendedProfileState R0 (G.fst e),
              ∑ i : Fin (explicitLargeSlotBound β q r),
                G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
                  (G.snd e) sourceCode e
                    { center := G.fst e, color := c, candidate := z, slot := i } /
                  extendedProfileCandidateCapacityScale rho s omega β q r) ≤
              ∑ _c : Fin n, ∑ _z : G.ExtendedProfileState R0 (G.fst e),
                ∑ _i : Fin (explicitLargeSlotBound β q r), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro c _hc
          apply Finset.sum_le_sum
          intro z _hz
          apply Finset.sum_le_sum
          intro i _hi
          exact hterm c z i
        have hcard := G.extendedProfileState_card_le R0 (G.fst e)
        calc
          (∑ v, ∑ c, ∑ z : G.ExtendedProfileState R0 v, ∑ i,
              G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
                (G.snd e) sourceCode e
                  { center := v, color := c, candidate := z, slot := i } /
                  extendedProfileCandidateCapacityScale rho s omega β q r) =
              ∑ c, ∑ z : G.ExtendedProfileState R0 (G.fst e), ∑ i,
                G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
                  (G.snd e) sourceCode e
                    { center := G.fst e, color := c, candidate := z, slot := i } /
                    extendedProfileCandidateCapacityScale rho s omega β q r := by
            apply Fintype.sum_eq_single (G.fst e)
            intro v hv
            simp [packedExtendedProfileLargeCandidateEdgeUse, hv,
              hsourceFst, hsourceFst']
          _ ≤ ∑ _c : Fin n, ∑ _z : G.ExtendedProfileState R0 (G.fst e),
              ∑ _i : Fin (explicitLargeSlotBound β q r), (1 : ℝ) := hsum
          _ = (n : ℝ) * Fintype.card (G.ExtendedProfileState R0 (G.fst e)) *
              explicitLargeSlotBound β q r := by simp; ring
          _ ≤ (n : ℝ) * extendedProfileStateBound β q r *
              explicitLargeSlotBound β q r := by
            gcongr
      · have hy : G.extendedProfileEdgeColorMass
            (s := s) (β := β) (n := n) e = 0 := by
          simp [extendedProfileEdgeColorMass, hlarge]
        simp [WeightedMultigraph.Inc, hsourceFst, hsourceFst', hlarge,
          packedExtendedProfileLargeCandidateEdgeUse,
          extendedProfileProductOptionMass, pairedOption, hy]
    · have hsourceFst' : G.fst e ≠ source := Ne.symm hsourceFst
      have hsourceSnd' : G.snd e ≠ source := Ne.symm hsourceSnd
      simp [WeightedMultigraph.Inc, hsourceFst, hsourceSnd,
        hsourceFst', hsourceSnd', packedExtendedProfileLargeCandidateEdgeUse]

private theorem sum_tinyCandidateRows_edge_le
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s)
    (source : G.V) (sourceCode : ExtendedProfilePackedWordState n β q r)
    (e : G.E) :
    (∑ row : G.ExtendedProfileTinyCandidateRow R0
        (n := n) (β := β) (q := q) (r := r),
      G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
        source sourceCode e row /
          extendedProfileCandidateCapacityScale rho s omega β q r) ≤
      if G.Inc source e then
        (n : ℝ) * extendedProfileStateBound β q r * G.weight e
      else 0 := by
  classical
  rw [G.sum_tinyCandidateRows R0]
  by_cases hsourceFst : source = G.fst e
  · have hsourceSnd : source ≠ G.snd e := by
      intro h
      exact G.noLoop e (hsourceFst.symm.trans h)
    subst source
    have hsourceSnd' : G.snd e ≠ G.fst e := Ne.symm hsourceSnd
    simp only [WeightedMultigraph.Inc, eq_self, true_or, if_true]
    have hterm : ∀ (c : Fin n)
        (z : G.ExtendedProfileState R0 (G.snd e)),
        G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
            (G.fst e) sourceCode e
              { center := G.snd e, color := c, candidate := z } /
            extendedProfileCandidateCapacityScale rho s omega β q r ≤
          G.weight e := by
      intro c z
      apply (div_le_iff₀ (extendedProfileCandidateCapacityScale_pos
        (β := β) (q := q) (r := r) hrho hspos homega0)).2
      simpa [mul_comm] using
        G.packedExtendedProfileTinyCandidateEdgeUse_le_weight_mul_scale R0
          hn hs hq hr0 hleft homega0 homega1 hrho.le (G.fst e) sourceCode e _
    have hsum :
        (∑ c : Fin n, ∑ z : G.ExtendedProfileState R0 (G.snd e),
          G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
            (G.fst e) sourceCode e
              { center := G.snd e, color := c, candidate := z } /
            extendedProfileCandidateCapacityScale rho s omega β q r) ≤
          ∑ _c : Fin n, ∑ _z : G.ExtendedProfileState R0 (G.snd e),
            G.weight e := by
      apply Finset.sum_le_sum
      intro c _hc
      apply Finset.sum_le_sum
      intro z _hz
      exact hterm c z
    have hcard := G.extendedProfileState_card_le R0 (G.snd e)
    calc
      (∑ v, ∑ c, ∑ z : G.ExtendedProfileState R0 v,
          G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
            (G.fst e) sourceCode e { center := v, color := c, candidate := z } /
              extendedProfileCandidateCapacityScale rho s omega β q r) =
          ∑ c, ∑ z : G.ExtendedProfileState R0 (G.snd e),
            G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
              (G.fst e) sourceCode e
                { center := G.snd e, color := c, candidate := z } /
                extendedProfileCandidateCapacityScale rho s omega β q r := by
        apply Fintype.sum_eq_single (G.snd e)
        intro v hv
        simp [packedExtendedProfileTinyCandidateEdgeUse, hv,
          hsourceSnd, hsourceSnd']
      _ ≤ ∑ _c : Fin n, ∑ _z : G.ExtendedProfileState R0 (G.snd e),
          G.weight e := hsum
      _ = (n : ℝ) * Fintype.card (G.ExtendedProfileState R0 (G.snd e)) *
          G.weight e := by simp; ring
      _ ≤ (n : ℝ) * extendedProfileStateBound β q r * G.weight e := by
        have hcardR :
            (Fintype.card (G.ExtendedProfileState R0 (G.snd e)) : ℝ) ≤
              extendedProfileStateBound β q r := by
          exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcardR (Nat.cast_nonneg n))
          (G.weight_nonneg e)
  · by_cases hsourceSnd : source = G.snd e
    · subst source
      have hsourceFst' : G.fst e ≠ G.snd e := Ne.symm hsourceFst
      simp only [WeightedMultigraph.Inc, hsourceFst', eq_self,
        false_or, if_true]
      have hterm : ∀ (c : Fin n)
          (z : G.ExtendedProfileState R0 (G.fst e)),
          G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
              (G.snd e) sourceCode e
                { center := G.fst e, color := c, candidate := z } /
              extendedProfileCandidateCapacityScale rho s omega β q r ≤
            G.weight e := by
        intro c z
        apply (div_le_iff₀ (extendedProfileCandidateCapacityScale_pos
          (β := β) (q := q) (r := r) hrho hspos homega0)).2
        simpa [mul_comm] using
          G.packedExtendedProfileTinyCandidateEdgeUse_le_weight_mul_scale R0
            hn hs hq hr0 hleft homega0 homega1 hrho.le (G.snd e) sourceCode e _
      have hsum :
          (∑ c : Fin n, ∑ z : G.ExtendedProfileState R0 (G.fst e),
            G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
              (G.snd e) sourceCode e
                { center := G.fst e, color := c, candidate := z } /
              extendedProfileCandidateCapacityScale rho s omega β q r) ≤
            ∑ _c : Fin n, ∑ _z : G.ExtendedProfileState R0 (G.fst e),
              G.weight e := by
        apply Finset.sum_le_sum
        intro c _hc
        apply Finset.sum_le_sum
        intro z _hz
        exact hterm c z
      have hcard := G.extendedProfileState_card_le R0 (G.fst e)
      calc
        (∑ v, ∑ c, ∑ z : G.ExtendedProfileState R0 v,
            G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
              (G.snd e) sourceCode e { center := v, color := c, candidate := z } /
                extendedProfileCandidateCapacityScale rho s omega β q r) =
            ∑ c, ∑ z : G.ExtendedProfileState R0 (G.fst e),
              G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
                (G.snd e) sourceCode e
                  { center := G.fst e, color := c, candidate := z } /
                  extendedProfileCandidateCapacityScale rho s omega β q r := by
          apply Fintype.sum_eq_single (G.fst e)
          intro v hv
          simp [packedExtendedProfileTinyCandidateEdgeUse, hv,
            hsourceFst, hsourceFst']
        _ ≤ ∑ _c : Fin n, ∑ _z : G.ExtendedProfileState R0 (G.fst e),
            G.weight e := hsum
        _ = (n : ℝ) * Fintype.card (G.ExtendedProfileState R0 (G.fst e)) *
            G.weight e := by simp; ring
        _ ≤ (n : ℝ) * extendedProfileStateBound β q r * G.weight e := by
          have hcardR :
              (Fintype.card (G.ExtendedProfileState R0 (G.fst e)) : ℝ) ≤
                extendedProfileStateBound β q r := by
            exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcardR (Nat.cast_nonneg n))
            (G.weight_nonneg e)
    · have hsourceFst' : G.fst e ≠ source := Ne.symm hsourceFst
      have hsourceSnd' : G.snd e ≠ source := Ne.symm hsourceSnd
      simp [WeightedMultigraph.Inc, hsourceFst, hsourceSnd,
        hsourceFst', hsourceSnd', packedExtendedProfileTinyCandidateEdgeUse]

/-- A simple polynomial bound for a source-state column.  The sharper
candidate-summed estimate removes the fixed factor
`extendedProfileStateBound * explicitLargeSlotBound`; this safe form already
has logarithm `O(log n)` and is sufficient for the asymptotic selector. -/
def extendedProfileCandidateCapacityColumnBound
    (n : ℕ) (β q r : ℝ) : ℝ :=
  (n : ℝ) ^ 2 * extendedProfileStateBound β q r *
    (explicitLargeSlotBound β q r / β + 1)

theorem sum_scaledCandidateCapacityUse_le_column
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s)
    (hpack : G.LocallyPacksInto n)
    (source : G.V) (sourceCode : ExtendedProfilePackedWordState n β q r) :
    (∑ row : G.ExtendedProfileCandidateCapacityRow R0
        (n := n) (β := β) (q := q) (r := r),
      G.scaledPackedExtendedProfileCandidateCapacityUse R0 rho omega
        (extendedProfileCandidateCapacityScale rho s omega β q r)
        source sourceCode row) ≤
      extendedProfileCandidateCapacityColumnBound n β q r := by
  classical
  let B := extendedProfileCandidateCapacityScale rho s omega β q r
  let M : ℝ := extendedProfileStateBound β q r
  let K : ℝ := explicitLargeSlotBound β q r
  have hlargeEdges :
      ((G.largeStarEdges β source).card : ℝ) ≤ (n : ℝ) / β :=
    G.largeStarEdges_card_le_div_of_locallyPacksInto hpack hβ source
  have hstar : G.starWeight source ≤ n :=
    G.starWeight_le_of_locallyPacksInto hpack source
  have hlarge :
      (∑ row : G.ExtendedProfileLargeCandidateRow R0
          (n := n) (β := β) (q := q) (r := r),
        G.scaledPackedExtendedProfileCandidateCapacityUse R0 rho omega B
          source sourceCode (Sum.inl row)) ≤
        (n : ℝ) * M * K * ((G.largeStarEdges β source).card : ℝ) := by
    calc
      (∑ row : G.ExtendedProfileLargeCandidateRow R0
          (n := n) (β := β) (q := q) (r := r),
        G.scaledPackedExtendedProfileCandidateCapacityUse R0 rho omega B
          source sourceCode (Sum.inl row)) =
          ∑ row, ∑ e,
            G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
              source sourceCode e row / B := by
        apply Finset.sum_congr rfl
        intro row _hrow
        simp [scaledPackedExtendedProfileCandidateCapacityUse,
          packedExtendedProfileCandidateCapacityUse,
          packedExtendedProfileLargeCandidateUse, B, Finset.sum_div]
      _ = ∑ e, ∑ row,
            G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
              source sourceCode e row / B := by
        rw [Finset.sum_comm]
      _ ≤ ∑ e, if G.Inc source e ∧ β ≤ G.weight e then
            (n : ℝ) * M * K else 0 := by
        apply Finset.sum_le_sum
        intro e _he
        simpa [B, M, K] using G.sum_largeCandidateRows_edge_le R0
          hn hs hq hr0 hleft homega0 homega1 hrho hspos
          source sourceCode e
      _ = (n : ℝ) * M * K *
          ((G.largeStarEdges β source).card : ℝ) := by
        calc
          (∑ e, if G.Inc source e ∧ β ≤ G.weight e then
              (n : ℝ) * M * K else 0) =
              ∑ e, if G.Inc source e then
                (if β ≤ G.weight e then (n : ℝ) * M * K else 0)
                else 0 := by
            apply Finset.sum_congr rfl
            intro e _he
            by_cases hinc : G.Inc source e <;> simp [hinc]
          _ = ∑ e ∈ Finset.univ.filter (G.Inc source),
              if β ≤ G.weight e then (n : ℝ) * M * K else 0 := by
            rw [← Finset.sum_filter]
          _ = ∑ e : G.StarEdge source,
                if β ≤ G.weight e.1 then (n : ℝ) * M * K else 0 := by
            exact Finset.sum_subtype (Finset.univ.filter (G.Inc source))
              (by intro e; simp)
              (fun e ↦ if β ≤ G.weight e then (n : ℝ) * M * K else 0)
          _ = (n : ℝ) * M * K *
              ((G.largeStarEdges β source).card : ℝ) := by
            rw [← Finset.sum_filter]
            simp [largeStarEdges]
            ring
  have htiny :
      (∑ row : G.ExtendedProfileTinyCandidateRow R0
          (n := n) (β := β) (q := q) (r := r),
        G.scaledPackedExtendedProfileCandidateCapacityUse R0 rho omega B
          source sourceCode (Sum.inr row)) ≤
        (n : ℝ) * M * G.starWeight source := by
    calc
      (∑ row : G.ExtendedProfileTinyCandidateRow R0
          (n := n) (β := β) (q := q) (r := r),
        G.scaledPackedExtendedProfileCandidateCapacityUse R0 rho omega B
          source sourceCode (Sum.inr row)) =
          ∑ row, ∑ e,
            G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
              source sourceCode e row / B := by
        apply Finset.sum_congr rfl
        intro row _hrow
        simp [scaledPackedExtendedProfileCandidateCapacityUse,
          packedExtendedProfileCandidateCapacityUse,
          packedExtendedProfileTinyCandidateUse, B, Finset.sum_div]
      _ = ∑ e, ∑ row,
            G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
              source sourceCode e row / B := by
        rw [Finset.sum_comm]
      _ ≤ ∑ e, if G.Inc source e then
            (n : ℝ) * M * G.weight e else 0 := by
        apply Finset.sum_le_sum
        intro e _he
        simpa [B, M] using G.sum_tinyCandidateRows_edge_le R0
          hn hs hq hr0 hleft homega0 homega1 hrho hspos
          source sourceCode e
      _ = (n : ℝ) * M * G.starWeight source := by
        calc
          (∑ e, if G.Inc source e then
              (n : ℝ) * M * G.weight e else 0) =
              (n : ℝ) * M *
                (∑ e, if G.Inc source e then G.weight e else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e _he
            split <;> simp
          _ = (n : ℝ) * M * G.starWeight source := by
            rw [← Finset.sum_filter]
            congr 1
            exact Finset.sum_subtype (Finset.univ.filter (G.Inc source))
              (by intro e; simp) G.weight
  rw [Fintype.sum_sum_type]
  calc
    (∑ row : G.ExtendedProfileLargeCandidateRow R0
          (n := n) (β := β) (q := q) (r := r),
        G.scaledPackedExtendedProfileCandidateCapacityUse R0 rho omega B
          source sourceCode (Sum.inl row)) +
      ∑ row : G.ExtendedProfileTinyCandidateRow R0
          (n := n) (β := β) (q := q) (r := r),
        G.scaledPackedExtendedProfileCandidateCapacityUse R0 rho omega B
          source sourceCode (Sum.inr row) ≤
        (n : ℝ) * M * K * ((n : ℝ) / β) +
          (n : ℝ) * M * n := by
      exact add_le_add
        (hlarge.trans (mul_le_mul_of_nonneg_left hlargeEdges (by positivity)))
        (htiny.trans (mul_le_mul_of_nonneg_left hstar (by positivity)))
    _ = extendedProfileCandidateCapacityColumnBound n β q r := by
      simp [extendedProfileCandidateCapacityColumnBound, M, K]
      field_simp [hβ.ne']
      <;> ring

end WeightedMultigraph

end

end WeightedEdgeColoring
