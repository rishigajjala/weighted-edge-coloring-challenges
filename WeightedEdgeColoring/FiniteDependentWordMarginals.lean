import WeightedEdgeColoring.FiniteDependentWordPadding

/-!
# Coordinate marginals of finite dependent product words

The padded full-word law is used as one categorical state at each graph
vertex.  Capacity estimates, however, concern one colour coordinate at a
time.  These identities reduce integration of a one-coordinate statistic
under the full product word law to the original atom law.  The second form
includes padding and the total decoder.
-/

namespace WeightedEdgeColoring.FiniteDependentWordPadding

open scoped BigOperators

noncomputable section

universe u₁ u₂ u₃

variable {Source : Type u₁} {Color : Type u₂}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype Color] [DecidableEq Color]
variable (Atom : Source → Type u₃)
variable [∀ i, Fintype (Atom i)] [∀ i, DecidableEq (Atom i)]

/-- A statistic of one coordinate has its atom-law expectation under the
full independent product word law. -/
theorem sum_wordMass_mul_coordinate
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) (c : Color) (f : Atom i → ℝ) :
    (∑ word : Color → Atom i,
      wordMass Atom atomProb i word * f (word c)) =
      ∑ z, atomProb i z * f z := by
  classical
  let g : Color → ℝ := fun d ↦
    ∑ z : Atom i, atomProb i z * (if d = c then f z else 1)
  calc
    (∑ word : Color → Atom i,
        wordMass Atom atomProb i word * f (word c)) =
        ∑ word : Color → Atom i,
          ∏ d, atomProb i (word d) *
            (if d = c then f (word d) else 1) := by
      apply Finset.sum_congr rfl
      intro word _hword
      unfold wordMass
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ d, ∑ z : Atom i,
          atomProb i z * (if d = c then f z else 1) := by
      exact (Fintype.prod_sum
        (fun d z ↦ atomProb i z *
          (if d = c then f z else 1))).symm
    _ = ∏ d, g d := by rfl
    _ = ∑ z, atomProb i z * f z := by
      rw [← Finset.prod_erase_mul (Finset.univ : Finset Color) g
        (Finset.mem_univ c)]
      have hrest : ∏ d ∈ (Finset.univ : Finset Color).erase c, g d = 1 := by
        apply Finset.prod_eq_one
        intro d hd
        have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
        simp [g, hdc, hatomSum i]
      rw [hrest, one_mul]
      simp [g]

/-- Padding a product word law by zero and decoding it does not change any
one-coordinate expectation. -/
theorem sum_paddedWordProbability_mul_decode_coordinate
    {M : ℕ} (E : Encoding Atom M) (fallback : ∀ i, Atom i)
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) (c : Color) (f : Atom i → ℝ) :
    (∑ a : PackedWordState (Color := Color) M,
      paddedWordProbability Atom E atomProb i a *
        f (decodePackedWord Atom (Color := Color) E fallback i a c)) =
      ∑ z, atomProb i z * f z := by
  rw [sum_paddedWordProbability_mul_decode Atom E fallback atomProb i
    (fun word ↦ f (word c))]
  exact sum_wordMass_mul_coordinate Atom atomProb hatomSum i c f

end

end WeightedEdgeColoring.FiniteDependentWordPadding
