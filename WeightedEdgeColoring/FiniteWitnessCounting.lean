import Mathlib

/-!
# Counting finite witness certificates

This file isolates the last elementary averaging step in a finite witness
argument.  Every sample supplies `N` distinct certificates.  If the total
mass of samples on which a fixed certificate appears is at most the weight
of that certificate, then the sum of all certificate weights is at least
`N`.

The statement uses only finite sums.  It is useful for a finite-horizon
resampling proof because it avoids probability measures and limits.
-/

namespace WeightedEdgeColoring.FiniteWitnessCounting

open scoped BigOperators

variable {Sample Certificate : Type*}
variable [Fintype Sample] [Fintype Certificate]

/-- Finite witness-counting inequality.

For each sample, `certificate sample` embeds `Fin N` into the certificates
which appear on that sample.  The mass of the appearance event of each fixed
certificate is bounded by its assigned weight. -/
theorem horizon_le_sum_certificateWeight
    (N : ℕ)
    (mass : Sample → ℝ)
    (appears : Sample → Certificate → Prop)
    [DecidableRel appears]
    (certificateWeight : Certificate → ℝ)
    (certificate : Sample → Fin N → Certificate)
    (hmass_nonneg : ∀ sample, 0 ≤ mass sample)
    (hmass_sum : ∑ sample, mass sample = 1)
    (hcertificate_injective : ∀ sample,
      Function.Injective (certificate sample))
    (hcertificate_appears : ∀ sample t,
      appears sample (certificate sample t))
    (happearance : ∀ cert,
      (∑ sample, if appears sample cert then mass sample else 0) ≤
        certificateWeight cert) :
    (N : ℝ) ≤ ∑ cert, certificateWeight cert := by
  classical
  have hsample : ∀ sample,
      (N : ℝ) * mass sample ≤
        ∑ cert : Certificate,
          if appears sample cert then mass sample else 0 := by
    intro sample
    let image : Finset Certificate :=
      Finset.univ.image (certificate sample)
    calc
      (N : ℝ) * mass sample = ∑ _t : Fin N, mass sample := by
        simp
      _ = ∑ cert ∈ image, mass sample := by
        rw [show (∑ cert ∈ image, mass sample) =
            ∑ t : Fin N, mass sample by
          unfold image
          rw [Finset.sum_image (hcertificate_injective sample).injOn]]
      _ = ∑ cert ∈ image,
          (if appears sample cert then mass sample else 0) := by
        apply Finset.sum_congr rfl
        intro cert hcert
        rcases Finset.mem_image.mp hcert with ⟨t, _ht, rfl⟩
        simp [hcertificate_appears sample t]
      _ ≤ ∑ cert : Certificate,
          (if appears sample cert then mass sample else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ image)
        intro cert _hcert _hnot
        split
        · exact hmass_nonneg sample
        · exact le_rfl
  calc
    (N : ℝ) = (N : ℝ) * ∑ sample, mass sample := by rw [hmass_sum, mul_one]
    _ = ∑ sample, (N : ℝ) * mass sample := by rw [Finset.mul_sum]
    _ ≤ ∑ sample, ∑ cert : Certificate,
        (if appears sample cert then mass sample else 0) :=
      Finset.sum_le_sum fun sample _hsample ↦ hsample sample
    _ = ∑ cert, ∑ sample : Sample,
        (if appears sample cert then mass sample else 0) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ cert, certificateWeight cert :=
      Finset.sum_le_sum fun cert _hcert ↦ happearance cert

/-- Finite witness-counting inequality when certificates are known to be
valid only on samples of positive mass.

Zero-mass samples make no contribution to either side of the double-counting
argument.  Consequently, injectivity and appearance of the `N` designated
certificates are needed only when the sample itself has positive mass. -/
theorem horizon_le_sum_certificateWeight_of_positive_mass
    (N : ℕ)
    (mass : Sample → ℝ)
    (appears : Sample → Certificate → Prop)
    [DecidableRel appears]
    (certificateWeight : Certificate → ℝ)
    (certificate : Sample → Fin N → Certificate)
    (hmass_nonneg : ∀ sample, 0 ≤ mass sample)
    (hmass_sum : ∑ sample, mass sample = 1)
    (hcertificate_injective : ∀ sample, 0 < mass sample →
      Function.Injective (certificate sample))
    (hcertificate_appears : ∀ sample, 0 < mass sample → ∀ t,
      appears sample (certificate sample t))
    (happearance : ∀ cert,
      (∑ sample, if appears sample cert then mass sample else 0) ≤
        certificateWeight cert) :
    (N : ℝ) ≤ ∑ cert, certificateWeight cert := by
  classical
  have hsample : ∀ sample,
      (N : ℝ) * mass sample ≤
        ∑ cert : Certificate,
          if appears sample cert then mass sample else 0 := by
    intro sample
    by_cases hpos : 0 < mass sample
    · let image : Finset Certificate :=
        Finset.univ.image (certificate sample)
      calc
        (N : ℝ) * mass sample = ∑ _t : Fin N, mass sample := by
          simp
        _ = ∑ cert ∈ image, mass sample := by
          rw [show (∑ cert ∈ image, mass sample) =
              ∑ t : Fin N, mass sample by
            unfold image
            rw [Finset.sum_image
              (hcertificate_injective sample hpos).injOn]]
        _ = ∑ cert ∈ image,
            (if appears sample cert then mass sample else 0) := by
          apply Finset.sum_congr rfl
          intro cert hcert
          rcases Finset.mem_image.mp hcert with ⟨t, _ht, rfl⟩
          simp [hcertificate_appears sample hpos t]
        _ ≤ ∑ cert : Certificate,
            (if appears sample cert then mass sample else 0) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ image)
          intro cert _hcert _hnot
          split
          · exact hmass_nonneg sample
          · exact le_rfl
    · have hzero : mass sample = 0 :=
        le_antisymm (le_of_not_gt hpos) (hmass_nonneg sample)
      simp [hzero]
  calc
    (N : ℝ) = (N : ℝ) * ∑ sample, mass sample := by
      rw [hmass_sum, mul_one]
    _ = ∑ sample, (N : ℝ) * mass sample := by rw [Finset.mul_sum]
    _ ≤ ∑ sample, ∑ cert : Certificate,
        (if appears sample cert then mass sample else 0) :=
      Finset.sum_le_sum fun sample _hsample ↦ hsample sample
    _ = ∑ cert, ∑ sample : Sample,
        (if appears sample cert then mass sample else 0) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ cert, certificateWeight cert :=
      Finset.sum_le_sum fun cert _hcert ↦ happearance cert

/-- If the certificate weights sum to less than the horizon, the hypotheses
of the finite witness count cannot all hold. -/
theorem not_all_samples_have_N_witnesses_of_sum_lt
    (N : ℕ)
    (mass : Sample → ℝ)
    (appears : Sample → Certificate → Prop)
    [DecidableRel appears]
    (certificateWeight : Certificate → ℝ)
    (certificate : Sample → Fin N → Certificate)
    (hmass_nonneg : ∀ sample, 0 ≤ mass sample)
    (hmass_sum : ∑ sample, mass sample = 1)
    (hcertificate_injective : ∀ sample,
      Function.Injective (certificate sample))
    (hcertificate_appears : ∀ sample t,
      appears sample (certificate sample t))
    (happearance : ∀ cert,
      (∑ sample, if appears sample cert then mass sample else 0) ≤
        certificateWeight cert)
    (hweight_lt : (∑ cert, certificateWeight cert) < N) : False := by
  have hle := horizon_le_sum_certificateWeight N mass appears
    certificateWeight certificate hmass_nonneg hmass_sum
    hcertificate_injective hcertificate_appears happearance
  exact (not_lt_of_ge hle) hweight_lt

/-- Positive-mass version of
`not_all_samples_have_N_witnesses_of_sum_lt`: zero-mass samples need not
carry valid certificates. -/
theorem not_all_positive_mass_samples_have_N_witnesses_of_sum_lt
    (N : ℕ)
    (mass : Sample → ℝ)
    (appears : Sample → Certificate → Prop)
    [DecidableRel appears]
    (certificateWeight : Certificate → ℝ)
    (certificate : Sample → Fin N → Certificate)
    (hmass_nonneg : ∀ sample, 0 ≤ mass sample)
    (hmass_sum : ∑ sample, mass sample = 1)
    (hcertificate_injective : ∀ sample, 0 < mass sample →
      Function.Injective (certificate sample))
    (hcertificate_appears : ∀ sample, 0 < mass sample → ∀ t,
      appears sample (certificate sample t))
    (happearance : ∀ cert,
      (∑ sample, if appears sample cert then mass sample else 0) ≤
        certificateWeight cert)
    (hweight_lt : (∑ cert, certificateWeight cert) < N) : False := by
  have hle := horizon_le_sum_certificateWeight_of_positive_mass N mass
    appears certificateWeight certificate hmass_nonneg hmass_sum
    hcertificate_injective hcertificate_appears happearance
  exact (not_lt_of_ge hle) hweight_lt

end WeightedEdgeColoring.FiniteWitnessCounting
