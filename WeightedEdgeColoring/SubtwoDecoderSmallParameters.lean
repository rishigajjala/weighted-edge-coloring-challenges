import WeightedEdgeColoring.SubtwoMixedGraphBlockUniformEventualDecoder

/-! A fixed decoder loss parameter and then a fixed even inner palette make
both the residual and endpoint-label rates arbitrarily small. -/

namespace WeightedEdgeColoring

noncomputable section

/-- Once the candidate coefficient has been fixed, increasing the fixed inner
palette makes the variance term small. -/
theorem exists_even_innerPalette_small_variance
    (δ a : ℝ) (hδ : 0 < δ) (ha : 0 ≤ a) :
    ∃ k : ℕ, 0 < k ∧ Even k ∧ a / ((k : ℝ) * δ) ≤ δ := by
  let m : ℕ := ⌈a / δ ^ 2⌉₊ + 1
  let k : ℕ := 2 * m
  have hm : 0 < m := by dsimp [m]; omega
  have hk : 0 < k := by dsimp [k]; omega
  have hceil : a / δ ^ 2 ≤ (m : ℝ) := by
    dsimp [m]
    have h := Nat.le_ceil (a / δ ^ 2)
    push_cast
    linarith
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have haBound : a ≤ (m : ℝ) * δ ^ 2 := by
    have h := (div_le_iff₀ hδsq).1 hceil
    nlinarith
  refine ⟨k, hk, by dsimp [k]; exact even_two_mul m, ?_⟩
  have hkR : (k : ℝ) = 2 * m := by simp [k]
  apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) * δ)).2
  rw [hkR]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ m by positivity) (sq_nonneg δ)]

/-- The two rates entering the block decoder can be simultaneously made
small. The coefficient `a` is allowed to depend on `δ`; only the palette `k`
is chosen after `a` is known. -/
theorem exists_small_decoder_rates
    (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 1000 ∧ δ ≤ ξ / 1000 ∧
      ∀ a : ℝ, 0 ≤ a → ∃ k : ℕ,
        0 < k ∧ Even k ∧
        4 * δ + δ + δ + a / ((k : ℝ) * δ) + δ ≤ ξ / 100 ∧
        4 * δ + 4 * δ ≤ ξ / 100 := by
  let δ : ℝ := min (ξ / 1000) (1 / 1000)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ ≤ 1 / 1000 := min_le_right _ _
  have hδξ : δ ≤ ξ / 1000 := min_le_left _ _
  refine ⟨δ, hδ, hδ1, hδξ, ?_⟩
  intro a ha
  obtain ⟨k, hk, heven, hvar⟩ :=
    exists_even_innerPalette_small_variance δ a hδ ha
  refine ⟨k, hk, heven, ?_, ?_⟩ <;> linarith

/-- A fixed multiple of the endpoint block scale `m^16` plus a fixed
constant is negligible compared with the palette parameter `n`, since
`m = dyadicSimpleRoot n` and `m^20≤n`. -/
theorem eventually_dyadicRoot_additive_sublinear
    (coefficient constant ε : ℝ)
    (hcoef : 0 ≤ coefficient) (hconstant : 0 ≤ constant)
    (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      coefficient * (dyadicSimpleRoot n : ℝ) ^ 16 + constant ≤ ε * n := by
  let M : ℕ := max 1 ⌈2 * coefficient / ε⌉₊
  let N : ℕ := max (M ^ 20) ⌈2 * constant / ε⌉₊
  refine ⟨N, ?_⟩
  intro n hn
  let m := dyadicSimpleRoot n
  have hMpow : M ^ 20 ≤ n := (le_max_left _ _).trans hn
  have hM : M ≤ m := le_dyadicSimpleRoot_of_pow_le hMpow
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hM
  have hm20 : m ^ 20 ≤ n := dyadicSimpleRoot_pow_le n
  have hceilC : 2 * coefficient / ε ≤ (m : ℝ) := by
    calc
      _ ≤ ((⌈2 * coefficient / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      _ ≤ (M : ℝ) := by exact_mod_cast le_max_right (1 : ℕ) _
      _ ≤ (m : ℝ) := by exact_mod_cast hM
  have hcoefm : coefficient ≤ ε / 2 * m := by
    have hh := (div_le_iff₀ hε).1 hceilC
    nlinarith
  have hm4Nat : m ≤ m ^ 4 := by
    calc
      m = m ^ 1 := by simp
      _ ≤ m ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm4 : (m : ℝ) ≤ (m : ℝ) ^ 4 := by exact_mod_cast hm4Nat
  have hcoef4 : coefficient ≤ ε / 2 * (m : ℝ) ^ 4 := by
    nlinarith [mul_nonneg (show 0 ≤ ε by linarith)
      (sub_nonneg.mpr hm4)]
  have hpart : coefficient * (m : ℝ) ^ 16 ≤ ε / 2 * (m : ℝ) ^ 20 := by
    have hh := mul_le_mul_of_nonneg_right hcoef4
      (show 0 ≤ (m : ℝ) ^ 16 by positivity)
    nlinarith [hh]
  have hceilB : 2 * constant / ε ≤ (n : ℝ) := by
    calc
      _ ≤ ((⌈2 * constant / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      _ ≤ (N : ℝ) := by exact_mod_cast le_max_right (M ^ 20) _
      _ ≤ (n : ℝ) := by exact_mod_cast hn
  have hB : constant ≤ ε / 2 * n := by
    have hh := (div_le_iff₀ hε).1 hceilB
    nlinarith
  have hm20R : (m : ℝ) ^ 20 ≤ n := by exact_mod_cast hm20
  have hε0 : 0 ≤ ε / 2 := by linarith
  have hpart' := mul_le_mul_of_nonneg_left hm20R hε0
  nlinarith

/-- The explicit floor, endpoint-block and reserve terms in the mixed decoder
are uniformly `o(n)` for every fixed dyadic bucket count. -/
theorem eventually_mixedDecoder_additive_small
    (Lbucket : ℕ) (β ε : ℝ) (hβ : 0 ≤ β) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (((Lbucket + 1) *
        (dyadicSimpleEndpointBlockScale 1 (dyadicSimpleRoot n) - 1) : ℕ) : ℝ) +
          8 * (1 + (dyadicSimpleReserveScale (dyadicSimpleRoot n) : ℝ)) +
          2 * β ≤ ε * n := by
  let coefficient : ℝ := Lbucket + 9
  let constant : ℝ := 8 + 2 * β
  obtain ⟨N, hN⟩ := eventually_dyadicRoot_additive_sublinear
    coefficient constant ε (by dsimp [coefficient]; positivity)
    (by dsimp [constant]; positivity) hε
  refine ⟨N, ?_⟩
  intro n hn
  let m := dyadicSimpleRoot n
  have hsub : dyadicSimpleEndpointBlockScale 1 m - 1 ≤
      dyadicSimpleEndpointBlockScale 1 m := Nat.sub_le _ _
  have hmulNat := Nat.mul_le_mul_left (Lbucket + 1) hsub
  have hmul :
      (((Lbucket + 1) * (dyadicSimpleEndpointBlockScale 1 m - 1) : ℕ) : ℝ) ≤
        (Lbucket + 1 : ℝ) * (m : ℝ) ^ 16 := by
    have hh : (((Lbucket + 1) *
        (dyadicSimpleEndpointBlockScale 1 m - 1) : ℕ) : ℝ) ≤
        ((Lbucket + 1) * dyadicSimpleEndpointBlockScale 1 m : ℕ) := by
      exact_mod_cast hmulNat
    simpa [dyadicSimpleEndpointBlockScale, Nat.cast_mul] using hh
  have hmain := hN n hn
  dsimp [coefficient, constant] at hmain
  change (Lbucket + 9 : ℝ) * (m : ℝ) ^ 16 + (8 + 2 * β) ≤ ε * n at hmain
  have hreserve : (dyadicSimpleReserveScale m : ℝ) = (m : ℝ) ^ 16 := by
    simp [dyadicSimpleReserveScale]
  rw [hreserve]
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ m by positivity) 16]

/-- The compact decoder's bulk residual expression fits the requested
original-graph loss after running at the fourfold quotient scale. -/
theorem compact_decoder_loss_le_original
    (loss tau trace rate additive : ℝ) (n : ℕ)
    (hloss : 0 < loss) (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1 / 4)
    (htrace0 : 0 ≤ trace) (htrace : trace ≤ loss / 4000)
    (hrate0 : 0 ≤ rate) (hrate : rate ≤ loss / 400)
    (hadd : additive ≤ (loss / 400) * (4 * n : ℕ)) :
    trace * (4 * n : ℕ) +
      (4 / (1 - tau / 4) + 1) * (rate * (4 * n : ℕ)) + additive ≤
        loss * n := by
  have hden : 0 < 1 - tau / 4 := by linarith
  have hfactor : 4 / (1 - tau / 4) + 1 ≤ 6 := by
    have hh : 4 / (1 - tau / 4) ≤ 5 :=
      (div_le_iff₀ hden).2 (by linarith)
    linarith
  have hfactor0 : 0 ≤ 4 / (1 - tau / 4) + 1 := by positivity
  have hrateFactor : (4 / (1 - tau / 4) + 1) * rate ≤
      6 * (loss / 400) := by
    calc
      _ ≤ 6 * rate := mul_le_mul_of_nonneg_right hfactor hrate0
      _ ≤ 6 * (loss / 400) := by nlinarith
  have hn0 : (0 : ℝ) ≤ (4 * n : ℕ) := Nat.cast_nonneg _
  have htraceMul := mul_le_mul_of_nonneg_right htrace hn0
  have hrateMul := mul_le_mul_of_nonneg_right hrateFactor hn0
  push_cast at htraceMul hrateMul hadd ⊢
  nlinarith

/-- Algebraic normalization matching the compact decoder's displayed rate
to the rate selected by `exists_uniform_decoder_parameter_package`. -/
theorem compact_decoder_rate_eq_small
    (δ A rho s : ℝ) (k : ℕ) (hδ : δ ≠ 0) (hk : 0 < k) :
    4 * δ + δ + δ +
      ((4 : ℝ) / k) * (A * (rho * s)) / (4 * δ) + δ =
    4 * δ + δ + δ + A * (rho * s) / ((k : ℝ) * δ) + δ := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  field_simp
  <;> ring

/-- Exact scalar form of the compact decoder's displayed residual bound. -/
theorem compact_decoder_displayed_loss_small
    (loss δ A rho s β : ℝ) (k Lbucket n : ℕ)
    (hloss : 0 < loss) (hδ0 : 0 < δ) (hδquart : δ ≤ 1 / 4)
    (hδloss : δ ≤ loss / 4000) (hk : 0 < k)
    (hβ0 : 0 ≤ β) (hA : 0 ≤ A * (rho * s))
    (hrate : 4 * δ + δ + δ +
      A * (rho * s) / ((k : ℝ) * δ) + δ ≤ loss / 400)
    (hadd :
      (((Lbucket + 1) *
        (dyadicSimpleEndpointBlockScale 1 (dyadicSimpleRoot (4 * n)) - 1) : ℕ) : ℝ) +
          8 * (1 + (dyadicSimpleReserveScale (dyadicSimpleRoot (4 * n)) : ℝ)) +
          2 * β ≤ (loss / 400) * (4 * n : ℕ)) :
    δ * (4 * n : ℕ) +
      (((Lbucket + 1) *
        (dyadicSimpleEndpointBlockScale 1 (dyadicSimpleRoot (4 * n)) - 1) : ℕ) : ℝ) +
      (4 / (1 - δ / 4) + 1) *
        ((4 * δ + δ + δ + ((4 : ℝ) / k) *
          (A * (rho * s)) / (4 * δ) + δ) * (4 * n : ℕ)) +
      8 * (1 + (dyadicSimpleReserveScale (dyadicSimpleRoot (4 * n)) : ℝ)) +
      2 * β ≤ loss * n := by
  let rate : ℝ := 4 * δ + δ + δ +
    ((4 : ℝ) / k) * (A * (rho * s)) / (4 * δ) + δ
  let additive : ℝ :=
    (((Lbucket + 1) *
      (dyadicSimpleEndpointBlockScale 1 (dyadicSimpleRoot (4 * n)) - 1) : ℕ) : ℝ) +
    8 * (1 + (dyadicSimpleReserveScale (dyadicSimpleRoot (4 * n)) : ℝ)) +
    2 * β
  have hrate0 : 0 ≤ rate := by
    dsimp [rate]
    positivity
  have hrateBound : rate ≤ loss / 400 := by
    dsimp [rate]
    rw [compact_decoder_rate_eq_small δ A rho s k hδ0.ne' hk]
    exact hrate
  have hbase := compact_decoder_loss_le_original loss δ δ rate additive n
    hloss hδ0.le hδquart hδ0.le hδloss hrate0 hrateBound hadd
  dsimp [rate, additive] at hbase
  convert hbase using 1 <;> ring

namespace WeightedMultigraph

/-- Choose the decoder profile and its fixed even inner palette before the
graph, then choose a physical tiny cutoff large enough for the original-label
allowance. The decoder profile `δ` is independent of the physical cutoff
`1/S`; only the eventual threshold can depend on the residual pair bound. -/
theorem exists_uniform_decoder_parameter_package
    (padding loss : ℝ) (hpadding : 0 < padding) (hloss : 0 < loss) :
    ∃ (δ : ℝ) (k Lbucket S0 Nadd : ℕ),
      0 < δ ∧ δ ≤ 1 / 1000 ∧ δ ≤ loss / 4000 ∧
      0 < k ∧ Even k ∧
      1 ≤ dyadicScale (jointProfileBeta δ) Lbucket ∧
      dyadicScale (jointProfileBeta δ) Lbucket < 2 ∧
      (let A := mixedCandidateOrientedScale (Label := Fin 6)
        (β := jointProfileBeta δ) (qstep := jointProfileQ δ)
        (r := jointProfileR δ)
        (jointProfileRho δ) (jointProfileS δ)
        (jointProfileOmega δ) 400
       4 * δ + δ + δ +
         A * (jointProfileRho δ * jointProfileS δ) / ((k : ℝ) * δ) + δ ≤
           loss / 400 ∧
       0 ≤ A * (jointProfileRho δ * jointProfileS δ)) ∧
      (∀ S : ℕ, S0 ≤ S → 160 ≤ S ∧
        2 * ((1 : ℝ) / S) + 8 * δ ≤ padding / 20) ∧
      (∀ nDecode : ℕ, Nadd ≤ nDecode →
        (((Lbucket + 1) *
          (dyadicSimpleEndpointBlockScale 1 (dyadicSimpleRoot nDecode) - 1) : ℕ) : ℝ) +
          8 * (1 + (dyadicSimpleReserveScale (dyadicSimpleRoot nDecode) : ℝ)) +
          2 * jointProfileBeta δ ≤ (loss / 400) * nDecode) := by
  let ξ : ℝ := min padding (loss / 4)
  have hξ : 0 < ξ := lt_min hpadding (by positivity)
  obtain ⟨δ, hδ0, hδsmall, hδξ, hchoose⟩ := exists_small_decoder_rates ξ hξ
  have hδquart : δ ≤ 1 / 4 := by linarith
  have hβ0 : 0 < jointProfileBeta δ := by
    exact (jointProfile_parameters hδ0 hδquart).2.1
  have hβ1 : jointProfileBeta δ ≤ 1 := by
    unfold jointProfileBeta
    nlinarith [sq_nonneg δ]
  obtain ⟨Lbucket, hcover, htop⟩ :=
    exists_dyadic_scale_mem_Ico_one_two (jointProfileBeta δ) hβ0 hβ1
  let A : ℝ := mixedCandidateOrientedScale (Label := Fin 6)
    (β := jointProfileBeta δ) (qstep := jointProfileQ δ)
    (r := jointProfileR δ)
    (jointProfileRho δ) (jointProfileS δ)
    (jointProfileOmega δ) 400
  have hA : 0 ≤ A := by
    exact mixedCandidateOrientedScale_nonneg (Label := Fin 6)
      (β := jointProfileBeta δ) (qstep := jointProfileQ δ)
      (r := jointProfileR δ)
      (by unfold jointProfileRho; linarith)
      (by unfold jointProfileS; linarith)
      (by simpa [jointProfileOmega] using hδ0)
      (by norm_num)
  have ha : 0 ≤ A * (jointProfileRho δ * jointProfileS δ) := by
    apply mul_nonneg hA
    exact mul_nonneg
      (by unfold jointProfileRho; linarith)
      (by unfold jointProfileS; linarith)
  obtain ⟨k, hk, heven, hrate, _hlabel⟩ := hchoose _ ha
  have hξloss : ξ ≤ loss / 4 := min_le_right _ _
  have hrateLoss : 4 * δ + δ + δ +
      A * (jointProfileRho δ * jointProfileS δ) / ((k : ℝ) * δ) + δ ≤
      loss / 400 := by
    linarith
  let S0 : ℕ := max 160 (⌈80 / padding⌉₊ + 1)
  have hβnonneg : 0 ≤ jointProfileBeta δ := hβ0.le
  obtain ⟨Nadd, hNadd⟩ :=
    eventually_mixedDecoder_additive_small Lbucket
      (jointProfileBeta δ) (loss / 400) hβnonneg (by positivity)
  have hδloss : δ ≤ loss / 4000 := by linarith
  refine ⟨δ, k, Lbucket, S0, Nadd, hδ0, hδsmall, hδloss, hk, heven,
    hcover, htop, ?_, ?_, hNadd⟩
  · exact ⟨hrateLoss, ha⟩
  · intro S hS
    have hS160 : 160 ≤ S := (le_max_left _ _).trans hS
    have hceil : 80 / padding ≤ (S : ℝ) := by
      calc
        _ ≤ ((⌈80 / padding⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
        _ ≤ (S : ℝ) := by
          exact_mod_cast (show ⌈80 / padding⌉₊ ≤ S by
            have : ⌈80 / padding⌉₊ + 1 ≤ S :=
              (le_max_right (160 : ℕ) _).trans hS
            omega)
    have hSpos : (0 : ℝ) < S := by exact_mod_cast (by omega : 0 < S)
    have hSbound : 2 * ((1 : ℝ) / S) ≤ padding / 40 := by
      have hh := (div_le_iff₀ hpadding).1 hceil
      have hh' : (2 : ℝ) / S ≤ padding / 40 :=
        (div_le_iff₀ hSpos).2 (by nlinarith)
      calc
        _ = (2 : ℝ) / S := by ring
        _ ≤ padding / 40 := hh'
    have hδpadding : δ ≤ padding / 1000 := by
      have hξpadding : ξ ≤ padding := min_le_left _ _
      linarith
    constructor
    · exact hS160
    · linarith

end WeightedMultigraph
end
end WeightedEdgeColoring
