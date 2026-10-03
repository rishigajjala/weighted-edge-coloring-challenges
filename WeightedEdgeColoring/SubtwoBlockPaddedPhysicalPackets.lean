import WeightedEdgeColoring.SubtwoPaddedPhysicalPacketBase

/-! A fixed block length can divide the actual packet palette exactly. -/

set_option maxHeartbeats 2000000
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u

theorem exists_subtwoFloorBaseColor_blockPadded_uniform
    (η : ℝ) (hη : 0 < η) (k : ℕ) (hkpos : 0 < k) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (n : ℕ),
      N ≤ n → G.LocallyPacksInto n →
      ∃ B : ℕ, 4 ≤ B*k ∧ Even B ∧ Even (B*k) ∧
        (subtwoKappa+η/2)*(n : ℝ) ≤ (B*k : ℕ) ∧
        ((B*k : ℕ) : ℝ) ≤ (subtwoKappa+η)*n ∧
        ∃ color : (G.subtwoFloorQuotient n).E → Fin (B*k),
          (G.subtwoFloorQuotient n).IsProperOn (G.subtwoFloorQuotientEdges n) color := by
  obtain ⟨N0,hN0⟩ := exists_subtwoFloorBaseColor_uniform.{u} (η/4) (by positivity)
  let N : ℕ := max N0 (max 1 (Nat.ceil (12*(k : ℝ)/η)))
  refine ⟨N, ?_⟩
  intro G n hn hlocal
  have hn0 : N0 ≤ n := (le_max_left _ _).trans hn
  have hlarge : 12*(k : ℝ) ≤ η*(n : ℝ) := by
    have hb : 12*(k : ℝ)/η ≤ (n : ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right 1 (Nat.ceil (12*(k : ℝ)/η))).trans
        ((le_max_right _ _).trans hn))
    have hh := (div_le_iff₀ hη).1 hb
    nlinarith
  obtain ⟨q,_,hq,color,hproper,_,_⟩ := hN0 G n hn0 hlocal
  let a : ℝ := (subtwoKappa+η/2)*n
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hden : (0 : ℝ) < 2*k := by positivity
  have ha : 0 ≤ a/(2*k) := by dsimp [a,subtwoKappa]; positivity
  let m : ℕ := Nat.ceil (a/(2*k))+2
  let B : ℕ := 2*m
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hK4 : 4 ≤ B*k := by dsimp [B]; nlinarith
  have haK : a ≤ ((B*k : ℕ) : ℝ) := by
    have hb := (div_le_iff₀ hden).1 (Nat.le_ceil (a/(2*k)))
    dsimp only [B,m]
    push_cast
    nlinarith
  have hKupper : ((B*k : ℕ) : ℝ) ≤ (subtwoKappa+η)*n := by
    have hb := Nat.ceil_lt_add_one ha
    have hb' := mul_lt_mul_of_pos_right hb hden
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hden)] at hb'
    dsimp only [B,m]
    push_cast
    dsimp only [a] at hb'
    nlinarith
  have hqK : q ≤ B*k := by
    have hh : (q : ℝ) ≤ ((B*k : ℕ) : ℝ) := by dsimp only [a] at haK; nlinarith
    exact_mod_cast hh
  let padded : (G.subtwoFloorQuotient n).E → Fin (B*k) := fun e => Fin.castLE hqK (color e)
  refine ⟨B,hK4,⟨m,by dsimp [B]; omega⟩,
    ⟨m*k,by dsimp [B]; ring⟩,haK,hKupper,padded,?_⟩
  intro v e he f hf hef
  apply hproper v he hf
  apply Fin.ext
  exact congrArg (fun c : Fin (B*k) => c.val) hef

end
end WeightedEdgeColoring.WeightedMultigraph
