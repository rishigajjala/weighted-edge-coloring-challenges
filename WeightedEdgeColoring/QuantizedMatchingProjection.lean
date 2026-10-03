import WeightedEdgeColoring.QuantizedOptions

/-!
# Projecting a matching of labelled copies

Floor replication replaces each fractional option by labelled copies.  A
partial matching can never contain two labels of the same base option, since
they have the same owner.  Hence forgetting labels preserves the matching.
-/

namespace WeightedEdgeColoring

noncomputable section

namespace RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Base options occurring in a finite set of labelled quantized copies. -/
def baseOptionSet (N : ℕ) (x : Option → ℝ)
    (M : Finset (QuantizedCopy N x)) : Finset Option :=
  M.image Sigma.fst

@[simp] theorem mem_baseOptionSet_iff
    (N : ℕ) (x : Option → ℝ) (M : Finset (QuantizedCopy N x))
    (o : Option) :
    o ∈ baseOptionSet N x M ↔ ∃ q ∈ M, q.1 = o := by
  simp [baseOptionSet]

/-- Forgetting copy labels preserves pairwise slot-disjointness and owner
injectivity. -/
theorem baseOptionSet_isPartialMatching
    (N : ℕ) (x : Option → ℝ) (M : Finset (QuantizedCopy N x))
    (hM : (H.quantized N x).IsPartialMatching M) :
    H.IsPartialMatching (baseOptionSet N x M) := by
  constructor
  · intro o ho p hp hop
    rcases (mem_baseOptionSet_iff N x M o).mp ho with ⟨qo, hqoM, rfl⟩
    rcases (mem_baseOptionSet_iff N x M p).mp hp with ⟨qp, hqpM, rfl⟩
    have hcopy : qo ≠ qp := by
      intro h
      exact hop (congrArg Sigma.fst h)
    exact hM.1 hqoM hqpM hcopy
  · intro o ho p hp howner
    rcases (mem_baseOptionSet_iff N x M o).mp ho with ⟨qo, hqoM, rfl⟩
    rcases (mem_baseOptionSet_iff N x M p).mp hp with ⟨qp, hqpM, rfl⟩
    have hcopy : qo = qp := hM.2 hqoM hqpM howner
    exact congrArg Sigma.fst hcopy

/-- Forgetting copy labels preserves exactly which jobs are covered. -/
theorem covers_baseOptionSet_iff
    (N : ℕ) (x : Option → ℝ) (M : Finset (QuantizedCopy N x))
    (j : Job) :
    H.Covers (baseOptionSet N x M) j ↔
      (H.quantized N x).Covers M j := by
  constructor
  · rintro ⟨o, ho, howner⟩
    rcases (mem_baseOptionSet_iff N x M o).mp ho with ⟨q, hq, hqval⟩
    refine ⟨q, hq, ?_⟩
    simpa [quantized] using hqval ▸ howner
  · rintro ⟨q, hq, howner⟩
    refine ⟨q.1, (mem_baseOptionSet_iff N x M q.1).mpr ⟨q, hq, rfl⟩, ?_⟩
    simpa [quantized] using howner

/-- The mass of the base option under every existing quantized copy is
strictly positive. -/
theorem quantizedCopy_mass_pos
    (N : ℕ) (x : Option → ℝ)
    (q : QuantizedCopy N x) :
    0 < x q.1 := by
  have hmult : 0 < quantizedMultiplicity N (x q.1) :=
    Nat.zero_lt_of_lt q.2.isLt
  have hscaled : (1 : ℝ) ≤ (N : ℝ) * x q.1 := by
    exact Nat.floor_pos.mp hmult
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith

/-- Every base option represented in a selected copy set has positive mass. -/
theorem baseOptionSet_mass_pos
    (N : ℕ) (x : Option → ℝ)
    (M : Finset (QuantizedCopy N x)) {o : Option}
    (ho : o ∈ baseOptionSet N x M) :
    0 < x o := by
  rcases (mem_baseOptionSet_iff N x M o).mp ho with ⟨q, _hqM, rfl⟩
  exact quantizedCopy_mass_pos N x q

end RankThreeOptionSystem

end

end WeightedEdgeColoring
