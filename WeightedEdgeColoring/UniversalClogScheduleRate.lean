import WeightedEdgeColoring.WeightedMomentGraphInitialEnergy
import WeightedEdgeColoring.MomentBlockAccumulatedRate
import Mathlib.Data.Nat.Log

/-!
# Explicit decay of the universal logarithmic schedule

Sixteen binary-ceiling-log stages make the universal operator loss smaller
than `2 q² / n¹⁶`.  Under `q ≤ C n`, the first/pair square-root errors are
therefore bounded by inverse sixth powers, and the diagonal error by an
inverse seventh power.
-/

namespace WeightedEdgeColoring

noncomputable section

def universalClogStages (n : ℕ) : ℕ := 16 * Nat.clog 2 n

def universalClogLoss (n q : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ universalClogStages n * (2 * (q : ℝ) ^ 2)

theorem half_pow_universalClogStages_le_inv_pow_sixteen
    {n : ℕ} (hn : 0 < n) :
    (1 / 2 : ℝ) ^ universalClogStages n ≤ 1 / (n : ℝ) ^ 16 := by
  let k := Nat.clog 2 n
  have hncast : (0 : ℝ) < n := by exact_mod_cast hn
  have hpowNat : n ≤ 2 ^ k := Nat.le_pow_clog (by omega) n
  have hpowReal : (n : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hpowNat
  have hbase : (1 / 2 : ℝ) ^ k ≤ 1 / (n : ℝ) := by
    rw [one_div_pow]
    exact one_div_le_one_div_of_le hncast hpowReal
  have hpow := pow_le_pow_left₀ (by positivity) hbase 16
  calc
    (1 / 2 : ℝ) ^ universalClogStages n =
        ((1 / 2 : ℝ) ^ k) ^ 16 := by
      simp [universalClogStages, k, pow_mul, mul_comm]
    _ ≤ (1 / (n : ℝ)) ^ 16 := hpow
    _ = 1 / (n : ℝ) ^ 16 := by rw [one_div_pow]

theorem universalClogLoss_le_inv_fourteen
    {n q : ℕ} {C : ℝ} (hn : 0 < n) (hC : 0 ≤ C)
    (hq : (q : ℝ) ≤ C * n) :
    universalClogLoss n q ≤ 2 * C ^ 2 / (n : ℝ) ^ 14 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqSq : (q : ℝ) ^ 2 ≤ (C * n) ^ 2 :=
    pow_le_pow_left₀ hq0 hq 2
  unfold universalClogLoss
  calc
    (1 / 2 : ℝ) ^ universalClogStages n * (2 * (q : ℝ) ^ 2) ≤
        (1 / (n : ℝ) ^ 16) * (2 * (C * n) ^ 2) := by
      exact mul_le_mul
        (half_pow_universalClogStages_le_inv_pow_sixteen hn)
        (mul_le_mul_of_nonneg_left hqSq (by norm_num))
        (by positivity) (by positivity)
    _ = 2 * C ^ 2 / (n : ℝ) ^ 14 := by
      field_simp

theorem universalClog_first_radicand_le
    {n q : ℕ} {C : ℝ} (hn : 0 < n) (hC : 0 ≤ C)
    (hq : (q : ℝ) ≤ C * n) :
    (n : ℝ) ^ 2 * universalClogLoss n q ≤
      2 * C ^ 2 / (n : ℝ) ^ 12 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (n : ℝ) ^ 2 * universalClogLoss n q ≤
        (n : ℝ) ^ 2 * (2 * C ^ 2 / (n : ℝ) ^ 14) :=
      mul_le_mul_of_nonneg_left
        (universalClogLoss_le_inv_fourteen hn hC hq) (by positivity)
    _ = 2 * C ^ 2 / (n : ℝ) ^ 12 := by field_simp

theorem universalClog_diagonal_radicand_le
    {n q : ℕ} {alpha C : ℝ} (hn : 0 < n)
    (halpha : 0 < alpha) (hC : 0 ≤ C) (hq : (q : ℝ) ≤ C * n) :
    (1 / alpha) ^ 2 * universalClogLoss n q ≤
      (2 * C ^ 2 / alpha ^ 2) / (n : ℝ) ^ 14 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (1 / alpha) ^ 2 * universalClogLoss n q ≤
        (1 / alpha) ^ 2 * (2 * C ^ 2 / (n : ℝ) ^ 14) :=
      mul_le_mul_of_nonneg_left
        (universalClogLoss_le_inv_fourteen hn hC hq) (sq_nonneg _)
    _ = (2 * C ^ 2 / alpha ^ 2) / (n : ℝ) ^ 14 := by
      field_simp

theorem universalClog_pair_radicand_le
    {n q : ℕ} {C : ℝ} (hn : 0 < n) (hC : 0 ≤ C)
    (hq : (q : ℝ) ≤ C * n) :
    ((n : ℝ) ^ 2 / 4) * universalClogLoss n q ≤
      (C ^ 2 / 2) / (n : ℝ) ^ 12 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    ((n : ℝ) ^ 2 / 4) * universalClogLoss n q ≤
        ((n : ℝ) ^ 2 / 4) * (2 * C ^ 2 / (n : ℝ) ^ 14) :=
      mul_le_mul_of_nonneg_left
        (universalClogLoss_le_inv_fourteen hn hC hq) (by positivity)
    _ = (C ^ 2 / 2) / (n : ℝ) ^ 12 := by
      field_simp
      norm_num

theorem eventually_sqrt_const_div_pow_twelve_le_inv
    {A epsilon : ℝ} (hA : 0 ≤ A) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.sqrt (A / (n : ℝ) ^ 12) ≤ epsilon / n := by
  obtain ⟨N0, hN0⟩ := exists_nat_gt (A / epsilon ^ 2)
  refine ⟨max 1 N0, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left 1 N0).trans hn
  have hN0n : N0 ≤ n := (le_max_right 1 N0).trans hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
  have hAlinear : A ≤ epsilon ^ 2 * n := by
    have hlt : A / epsilon ^ 2 < (n : ℝ) :=
      hN0.trans_le (by exact_mod_cast hN0n)
    rw [div_lt_iff₀ (sq_pos_of_pos hepsilon)] at hlt
    simpa [mul_comm] using hlt.le
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ 10 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    calc
      (n : ℝ) = (n : ℝ) ^ 1 := by ring
      _ ≤ (n : ℝ) ^ 10 := pow_le_pow_right₀ hnR (by omega)
  have hAcross : A * (n : ℝ) ^ 2 ≤
      epsilon ^ 2 * (n : ℝ) ^ 12 := by
    calc
      A * (n : ℝ) ^ 2 ≤
          (epsilon ^ 2 * (n : ℝ) ^ 10) * (n : ℝ) ^ 2 := by
        gcongr
        exact hAlinear.trans
          (mul_le_mul_of_nonneg_left hpow (sq_nonneg epsilon))
      _ = epsilon ^ 2 * (n : ℝ) ^ 12 := by ring
  have hdiv : A / (n : ℝ) ^ 12 ≤ (epsilon / n) ^ 2 := by
    rw [div_pow]
    exact (div_le_div_iff₀ (pow_pos hnreal 12) (pow_pos hnreal 2)).2 hAcross
  rw [Real.sqrt_le_iff]
  exact ⟨div_nonneg hepsilon.le hnreal.le, hdiv⟩

theorem eventually_sqrt_const_div_pow_fourteen_le_inv
    {A epsilon : ℝ} (hA : 0 ≤ A) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.sqrt (A / (n : ℝ) ^ 14) ≤ epsilon / n := by
  obtain ⟨N0, hN0⟩ := exists_nat_gt (A / epsilon ^ 2)
  refine ⟨max 1 N0, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left 1 N0).trans hn
  have hN0n : N0 ≤ n := (le_max_right 1 N0).trans hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
  have hAlinear : A ≤ epsilon ^ 2 * n := by
    have hlt : A / epsilon ^ 2 < (n : ℝ) :=
      hN0.trans_le (by exact_mod_cast hN0n)
    rw [div_lt_iff₀ (sq_pos_of_pos hepsilon)] at hlt
    simpa [mul_comm] using hlt.le
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ 12 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    calc
      (n : ℝ) = (n : ℝ) ^ 1 := by ring
      _ ≤ (n : ℝ) ^ 12 := pow_le_pow_right₀ hnR (by omega)
  have hAcross : A * (n : ℝ) ^ 2 ≤
      epsilon ^ 2 * (n : ℝ) ^ 14 := by
    calc
      A * (n : ℝ) ^ 2 ≤
          (epsilon ^ 2 * (n : ℝ) ^ 12) * (n : ℝ) ^ 2 := by
        gcongr
        exact hAlinear.trans
          (mul_le_mul_of_nonneg_left hpow (sq_nonneg epsilon))
      _ = epsilon ^ 2 * (n : ℝ) ^ 14 := by ring
  have hdiv : A / (n : ℝ) ^ 14 ≤ (epsilon / n) ^ 2 := by
    rw [div_pow]
    exact (div_le_div_iff₀ (pow_pos hnreal 14) (pow_pos hnreal 2)).2 hAcross
  rw [Real.sqrt_le_iff]
  exact ⟨div_nonneg hepsilon.le hnreal.le, hdiv⟩

/-- All three ideal coordinate errors have the scales needed by the final
moment estimate: first error tends to zero and both second-moment errors are
`o(1/n)`. -/
theorem eventually_universalClog_ideal_errors
    {alpha C epsilon : ℝ} (halpha : 0 < alpha) (hC : 0 < C)
    (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n q : ℕ, N ≤ n → 0 < n → (q : ℝ) ≤ C * n →
      Real.sqrt ((n : ℝ) ^ 2 * universalClogLoss n q) ≤ epsilon ∧
      Real.sqrt ((1 / alpha) ^ 2 * universalClogLoss n q) ≤ epsilon / n ∧
      Real.sqrt (((n : ℝ) ^ 2 / 4) * universalClogLoss n q) ≤ epsilon / n := by
  rcases eventually_sqrt_const_div_pow_twelve_le_inv
      (A := 2 * C ^ 2) (epsilon := epsilon) (by positivity) hepsilon with
    ⟨Nfirst, hfirst⟩
  rcases eventually_sqrt_const_div_pow_fourteen_le_inv
      (A := 2 * C ^ 2 / alpha ^ 2) (epsilon := epsilon)
      (by positivity) hepsilon with ⟨Ndiag, hdiag⟩
  rcases eventually_sqrt_const_div_pow_twelve_le_inv
      (A := C ^ 2 / 2) (epsilon := epsilon) (by positivity) hepsilon with
    ⟨Npair, hpair⟩
  refine ⟨max Nfirst (max Ndiag Npair), ?_⟩
  intro n q hn hnpos hq
  have hnFirst : Nfirst ≤ n := (le_max_left _ _).trans hn
  have hnDiag : Ndiag ≤ n :=
    (le_max_left Ndiag Npair).trans ((le_max_right Nfirst _).trans hn)
  have hnPair : Npair ≤ n :=
    (le_max_right Ndiag Npair).trans ((le_max_right Nfirst _).trans hn)
  have hzRad := universalClog_first_radicand_le hnpos hC.le hq
  have hdRad := universalClog_diagonal_radicand_le hnpos halpha hC.le hq
  have hpRad := universalClog_pair_radicand_le hnpos hC.le hq
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnpos.ne')
  refine ⟨?_, ?_, ?_⟩
  · exact (Real.sqrt_le_sqrt hzRad).trans
      ((hfirst n hnFirst).trans (div_le_self hepsilon.le hnreal))
  · exact (Real.sqrt_le_sqrt hdRad).trans (hdiag n hnDiag)
  · exact (Real.sqrt_le_sqrt hpRad).trans (hpair n hnPair)

namespace WeightedMultigraph

universe u

/-- Quantitative graph output of the logarithmic universal schedule.  The
first coordinates have an arbitrary constant error, while both second-
moment coordinate families have arbitrary `constant/n` error. -/
theorem eventually_exists_clogMixed_coordinates
    {alpha C L epsilon1 epsilon2 : ℝ}
    (halpha : 0 < alpha) (hC : 0 < C) (hL : 0 < L)
    (hepsilon1 : 0 < epsilon1) (hepsilon2 : 0 < epsilon2) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (n q : ℕ),
      N ≤ n → 0 < n → Even q → 4 ≤ q → (q : ℝ) ≤ C * n →
      ∀ (R : Finset G.E) (charge : G.E → ℝ)
        (F : Finset G.E) (color : G.E → Fin q),
      G.IsProperOn F color →
      (∀ e ∈ R, 0 ≤ charge e) →
      (∀ w, alpha * n ≤ G.momentMissingSize F color w) →
      (∀ w, G.restrictedCharge R charge w ≤ n) →
      (∀ v w, G.pairCharge R charge v w ≤ L) →
      ∃ mixed : G.E → Fin q,
        G.IsProperOn F mixed ∧
        (∀ v c,
          |G.graphFirstMoment R charge F mixed v c -
            G.restrictedCharge R charge v / q| ≤ epsilon1) ∧
        (∀ v c,
          |G.graphDiagonalMoment R charge F mixed v c -
            G.graphHarmonicMoment R charge F color v / q| ≤ epsilon2 / n) ∧
        ∀ v c d,
          |G.graphPairMoment R charge F mixed v c d -
            offDiagonalConstant
              ((G.restrictedCharge R charge v -
                  G.graphHarmonicMoment R charge F color v) /
                ((q : ℝ) * ((q : ℝ) - 1))) c d| ≤ epsilon2 / n := by
  let eta : ℝ := min (epsilon1 / 2) (epsilon2 / 4)
  let theta : ℝ := min (epsilon1 / 2) (epsilon2 / 2)
  have heta : 0 < eta := by dsimp [eta]; positivity
  have htheta : 0 < theta := by dsimp [theta]; positivity
  rcases eventually_sixteen_clog_mul_momentBlockError_le
      halpha hC hL eta heta with ⟨Nselector, hselector⟩
  rcases eventually_universalClog_ideal_errors halpha hC htheta with
    ⟨Nideal, hideal⟩
  refine ⟨max Nselector Nideal, ?_⟩
  intro G n q hn hnpos heven hq4 hq R charge F color hproper hcharge
    hmissing hrestricted hpair
  have hnSelector : Nselector ≤ n := (le_max_left _ _).trans hn
  have hnIdeal : Nideal ≤ n := (le_max_right _ _).trans hn
  have hsel := hselector G n q hnSelector hnpos hq
  have hid := hideal n q hnIdeal hnpos hq
  rcases G.exists_realizing_universalSchedule_coordinates_coarse
      (s := universalClogStages n) R charge F color hproper heven hq4
      alpha L halpha hL hnpos hcharge hmissing hrestricted hpair with
    ⟨mixed, hproperMixed, hfirst, hdiag, hpairCoord⟩
  refine ⟨mixed, hproperMixed, ?_, ?_, ?_⟩
  · intro v c
    have hz := hfirst v c
    have hzIdeal :
        Real.sqrt ((n : ℝ) ^ 2 *
          ((1 / 2 : ℝ) ^ universalClogStages n *
            (2 * (q : ℝ) ^ 2))) ≤ theta := by
      simpa [universalClogLoss] using hid.1
    have heta1 : eta ≤ epsilon1 / 2 := min_le_left _ _
    have htheta1 : theta ≤ epsilon1 / 2 := min_le_left _ _
    have hsel' :
        (universalClogStages n : ℝ) *
            G.momentBlockError alpha L n q ≤ eta := by
      simpa [universalClogStages] using hsel
    exact hz.trans (by linarith)
  · intro v c
    have hd := hdiag v c
    have hdIdeal :
        Real.sqrt ((1 / alpha) ^ 2 *
          ((1 / 2 : ℝ) ^ universalClogStages n *
            (2 * (q : ℝ) ^ 2))) ≤ theta / n := by
      simpa [universalClogLoss] using hid.2.1
    have heta2 : eta ≤ epsilon2 / 4 := min_le_right _ _
    have htheta2 : theta ≤ epsilon2 / 2 := min_le_right _ _
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hselDiv :
        (universalClogStages n : ℝ) *
            (G.momentBlockError alpha L n q / n) ≤ eta / n := by
      calc
        _ = ((universalClogStages n : ℝ) *
            G.momentBlockError alpha L n q) / n := by ring
        _ ≤ eta / n := div_le_div_of_nonneg_right hsel hnreal.le
    exact hd.trans (by
      calc
        _ ≤ eta / n + theta / n := add_le_add hselDiv hdIdeal
        _ = (eta + theta) / n := by ring
        _ ≤ epsilon2 / n :=
          div_le_div_of_nonneg_right (by linarith) hnreal.le)
  · intro v c d
    have hp := hpairCoord v c d
    have hpIdeal :
        Real.sqrt (((n : ℝ) ^ 2 / 4) *
          ((1 / 2 : ℝ) ^ universalClogStages n *
            (2 * (q : ℝ) ^ 2))) ≤ theta / n := by
      simpa [universalClogLoss] using hid.2.2
    have heta2 : eta ≤ epsilon2 / 4 := min_le_right _ _
    have htheta2 : theta ≤ epsilon2 / 2 := min_le_right _ _
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hselDiv :
        2 * (universalClogStages n : ℝ) *
            (G.momentBlockError alpha L n q / n) ≤ 2 * eta / n := by
      calc
        _ = 2 * (((universalClogStages n : ℝ) *
            G.momentBlockError alpha L n q) / n) := by ring
        _ ≤ 2 * (eta / n) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hsel hnreal.le) (by norm_num)
        _ = 2 * eta / n := by ring
    exact hp.trans (by
      calc
        _ ≤ 2 * eta / n + theta / n := add_le_add hselDiv hpIdeal
        _ = (2 * eta + theta) / n := by ring
        _ ≤ epsilon2 / n :=
          div_le_div_of_nonneg_right (by linarith) hnreal.le)

end WeightedMultigraph

end
end WeightedEdgeColoring
