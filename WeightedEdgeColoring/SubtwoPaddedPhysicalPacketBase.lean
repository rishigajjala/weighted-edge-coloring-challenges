import WeightedEdgeColoring.SubtwoPacketQuotientBase

/-! An even actual packet palette with a prescribed linear reserve. -/

set_option maxHeartbeats 2000000
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u

theorem exists_subtwoFloorBaseColor_padded_uniform (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (n : ℕ),
      N ≤ n → G.LocallyPacksInto n →
      ∃ K : ℕ, 4 ≤ K ∧ Even K ∧
        (subtwoKappa+η/2)*(n : ℝ) ≤ K ∧
        (K : ℝ) ≤ (subtwoKappa+η)*n ∧
        ∃ color : (G.subtwoFloorQuotient n).E → Fin K,
          (G.subtwoFloorQuotient n).IsProperOn (G.subtwoFloorQuotientEdges n) color := by
  obtain ⟨N0,hN0⟩ := exists_subtwoFloorBaseColor_uniform.{u} (η/4) (by positivity)
  let N : ℕ := max N0 (max 1 (Nat.ceil (12/η)))
  refine ⟨N, ?_⟩
  intro G n hn hlocal
  have hn0 : N0 ≤ n := (le_max_left _ _).trans hn
  have hlarge : 12 ≤ η*(n : ℝ) := by
    have hb : 12/η ≤ (n : ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right 1 (Nat.ceil (12/η))).trans ((le_max_right _ _).trans hn))
    have hh := (div_le_iff₀ hη).1 hb
    nlinarith
  obtain ⟨k,_,hk,color,hproper,_,_⟩ := hN0 G n hn0 hlocal
  let a : ℝ := (subtwoKappa+η/2)*n
  have ha : 0 ≤ a/2 := by dsimp [a,subtwoKappa]; positivity
  let m : ℕ := Nat.ceil (a/2)+2
  let K : ℕ := 2*m
  have hK4 : 4 ≤ K := by dsimp [K,m]; omega
  have haK : a ≤ (K : ℝ) := by
    have hb := Nat.le_ceil (a/2)
    dsimp [K,m]
    push_cast
    linarith
  have hKupper : (K : ℝ) ≤ (subtwoKappa+η)*n := by
    have hb := Nat.ceil_lt_add_one ha
    dsimp only [K,m]
    push_cast
    dsimp only [a] at hb
    nlinarith
  have hkK : k ≤ K := by
    have hh : (k : ℝ) ≤ K := by dsimp only [a] at haK; nlinarith
    exact_mod_cast hh
  let padded : (G.subtwoFloorQuotient n).E → Fin K := fun e => Fin.castLE hkK (color e)
  refine ⟨K,hK4,⟨m,by dsimp [K]; omega⟩,haK,hKupper,padded,?_⟩
  intro v e he f hf hef
  apply hproper v he hf
  apply Fin.ext
  exact congrArg (fun c : Fin K => c.val) hef

/-- The padded coloring is packaged on the actual physical quotient with
exactly the selected original full-packet edges. -/
theorem exists_subtwoFloorPhysicalColoredPacketBase_padded_uniform
    (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (n : ℕ),
      N ≤ n → G.LocallyPacksInto n →
      ∃ K : ℕ, ∃ C :
        (G.subtwoQuotient (G.subtwoFloorBlock n)).GeneralColoredPacketBase K,
        4 ≤ K ∧ Even K ∧ (subtwoKappa+η/2)*(n : ℝ) ≤ K ∧
        (K : ℝ) ≤ (subtwoKappa+η)*n ∧
        C.fullEdges = G.subtwoQuotientSelectedEdges
          (G.subtwoFloorBlock n) (G.subtwoFloorBaseEdges n) := by
  obtain ⟨N,hN⟩ := exists_subtwoFloorBaseColor_padded_uniform.{u} η hη
  refine ⟨N,?_⟩
  intro G n hn hlocal
  obtain ⟨K,hK4,heven,hlower,hupper,color,hproper⟩ := hN G n hn hlocal
  have hK : 0 < K := by omega
  exact ⟨K,G.subtwoFloorPhysicalColoredPacketBase hK n color hproper,
    hK4,heven,hlower,hupper,
    G.subtwoFloorPhysicalColoredPacketBase_fullEdges hK n color hproper⟩

end
end WeightedEdgeColoring.WeightedMultigraph
