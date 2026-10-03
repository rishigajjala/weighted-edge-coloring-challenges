import WeightedEdgeColoring.SubtwoLinearGroupedPhysicalRestoration
import WeightedEdgeColoring.BPGeneralPhysicalDegreeBound

/-! A uniform grouping width and threshold for every block of at most five vertices. -/

set_option maxHeartbeats 4000000
open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u

/-- A fixed reciprocal weight floor bounds the number of indexed edges. -/
theorem subtwo_card_edges_le_of_weight_floor
    (G : WeightedMultigraph.{u}) (S : ℕ) (hS : 0 < S)
    (hlower : ∀ e, (1 : ℝ)/S ≤ G.weight e) {n : ℕ}
    (hlocal : G.LocallyPacksInto n) :
    Fintype.card G.E ≤ Fintype.card G.V * (n*S) := by
  classical
  calc
    Fintype.card G.E = ∑ v : G.V,
        ((Finset.univ : Finset G.E).filter fun e => G.fst e=v).card := by
      simpa using (card_eq_sum_card_filter_fiber (Finset.univ : Finset G.E) G.fst)
    _ ≤ ∑ _v : G.V, n*S := by
      apply Finset.sum_le_sum
      intro v _
      have hsub : ((Finset.univ : Finset G.E).filter fun e => G.fst e=v) ⊆
          Finset.univ.filter (G.Inc v) := by
        intro e he
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (Finset.mem_filter.mp he).2⟩
      exact (Finset.card_le_card hsub).trans
        (G.degreeOn_univ_le_mul_of_reciprocal_weight_floor hS hlower hlocal v)
    _ = _ := by simp

namespace SubtwoLinearGrouping

/-- Fixed grouping and pattern-floor loss for an at-most-five-vertex block. -/
def fixedSmallBlockError (S M : ℕ) : ℝ :=
  25*M + 150*M*S*((S+1)^(25*M) : ℕ)

theorem fixedSmallBlockError_nonneg (S M : ℕ) : 0 ≤ fixedSmallBlockError S M := by
  unfold fixedSmallBlockError
  positivity

theorem smallBlockGroupingError_le
    (G : WeightedMultigraph.{u}) (S M : ℕ) (hM : 0 < M)
    (hV : Fintype.card G.V ≤ 5) {n : ℕ}
    (hcard : Fintype.card G.E ≤ Fintype.card G.V*(n*S)) :
    2*(Fintype.card G.E : ℝ)/M + ((Fintype.card G.V)^2 : ℕ)*M +
      ((Fintype.card G.V)^2*M : ℕ)*((Fintype.card G.V : ℝ)+1)*
        ((S+1)^((Fintype.card G.V)^2*M) : ℕ)*S ≤
      10*S*n/M + fixedSmallBlockError S M := by
  have hvR : (Fintype.card G.V : ℝ) ≤ 5 := by exact_mod_cast hV
  have hcardR : (Fintype.card G.E : ℝ) ≤ 5*(n : ℝ)*S := by
    calc
      _ ≤ (Fintype.card G.V : ℝ)*((n : ℝ)*S) := by exact_mod_cast hcard
      _ ≤ 5*((n : ℝ)*S) := mul_le_mul_of_nonneg_right hvR (by positivity)
      _ = _ := by ring
  have hpow : (Fintype.card G.V)^2*M ≤ 25*M := by
    have hsq : (Fintype.card G.V)^2 ≤ 25 := by nlinarith
    exact Nat.mul_le_mul_right M hsq
  have hp : (((S+1)^((Fintype.card G.V)^2*M) : ℕ) : ℝ) ≤
      ((S+1)^(25*M) : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < S+1) hpow
  have hsqR : (((Fintype.card G.V)^2 : ℕ) : ℝ) ≤ 25 := by
    exact_mod_cast (show (Fintype.card G.V)^2 ≤ 25 by nlinarith)
  have hterm1 : 2*(Fintype.card G.E : ℝ)/M ≤ 10*S*n/M := by
    exact div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg M)
  have hterm2 : (((Fintype.card G.V)^2 : ℕ) : ℝ)*M ≤ 25*(M : ℝ) := by gcongr
  have hterm3 : (((Fintype.card G.V)^2*M : ℕ) : ℝ)*((Fintype.card G.V : ℝ)+1)*
      ((S+1)^((Fintype.card G.V)^2*M) : ℕ)*S ≤
      150*(M : ℝ)*S*((S+1)^(25*M) : ℕ) := by
    calc
      _ ≤ (25*(M : ℝ))*6*((S+1)^(25*M) : ℕ)*S := by
        push_cast
        gcongr <;> nlinarith
      _ = _ := by ring
  unfold fixedSmallBlockError
  linarith

/-- The width and threshold precede the arbitrary graph and its multiplicity. -/
theorem exists_uniform_smallBlockGroupingParameters
    (S : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ M N : ℕ, 0 < M ∧ 0 < N ∧
      ∀ (G : WeightedMultigraph.{u}) (n : ℕ), N ≤ n →
        Fintype.card G.V ≤ 5 →
        Fintype.card G.E ≤ Fintype.card G.V*(n*S) →
        2*(Fintype.card G.E : ℝ)/M + ((Fintype.card G.V)^2 : ℕ)*M +
          ((Fintype.card G.V)^2*M : ℕ)*((Fintype.card G.V : ℝ)+1)*
            ((S+1)^((Fintype.card G.V)^2*M) : ℕ)*S ≤ η*n := by
  let M : ℕ := max 1 (Nat.ceil (20*(S : ℝ)/η))
  have hM : 0 < M := by dsimp [M]; omega
  have hMbound : 20*(S : ℝ)/η ≤ M :=
    (Nat.le_ceil _).trans (by
      dsimp only [M]
      exact_mod_cast le_max_right 1 (Nat.ceil (20*(S : ℝ)/η)))
  have hscale : 10*(S : ℝ) ≤ (η/2)*M := by
    have h := (div_le_iff₀ hη).mp hMbound
    nlinarith
  let N : ℕ := max 1 (Nat.ceil (2*fixedSmallBlockError S M/η))
  have hN : 0 < N := by dsimp [N]; omega
  refine ⟨M,N,hM,hN,?_⟩
  intro G n hn hV hcard
  have hfixed : fixedSmallBlockError S M ≤ (η/2)*n := by
    have hNbound : 2*fixedSmallBlockError S M/η ≤ (n : ℝ) := by
      calc
        _ ≤ (Nat.ceil (2*fixedSmallBlockError S M/η) : ℝ) := Nat.le_ceil _
        _ ≤ (N : ℝ) := by exact_mod_cast le_max_right 1 (Nat.ceil (2*fixedSmallBlockError S M/η))
        _ ≤ n := by exact_mod_cast hn
    have h := (div_le_iff₀ hη).mp hNbound
    nlinarith
  have hlinear : 10*(S : ℝ)*n/M ≤ (η/2)*n := by
    apply (div_le_iff₀ (by exact_mod_cast hM : (0 : ℝ)<M)).mpr
    have h := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg n)
    nlinarith
  have h := smallBlockGroupingError_le G S M hM hV hcard
  linarith

end SubtwoLinearGrouping
end
end WeightedEdgeColoring.WeightedMultigraph
