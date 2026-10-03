import WeightedEdgeColoring.FiniteDependentWordMarginals

/-!
# Exact moments of finite product words

This file supplies the algebra needed when one categorical source chooses a
whole fixed-size color block.  Coordinates of the word are independent.  We
prove exact one- and two-coordinate expectations, exact additivity of the
variance of a centered coordinate sum, and the elementary bound

`E[(X - E X)^2] ≤ U * E X`

for `0 ≤ X ≤ U`.  Every identity is also transferred to the padded common
state type from `FiniteDependentWordPadding`; padding-only states have zero
mass, so no error is introduced.
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

/-- The common packed categorical state for a block of exactly `k`
coordinates, each using `M` codes. -/
abbrev PackedBlockState (k M : ℕ) :=
  PackedWordState (Color := Fin k) M

@[simp] theorem packedBlockState_card (k M : ℕ) :
    Fintype.card (PackedBlockState k M) = M ^ k := by
  change Fintype.card (Fin (Fintype.card (Fin k → Fin M))) = M ^ k
  rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]

/-- The unpadded finite product word law is normalized. -/
theorem sum_wordMass
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) :
    (∑ word : Color → Atom i, wordMass Atom atomProb i word) = 1 := by
  unfold wordMass
  rw [← Fintype.prod_sum]
  simp [hatomSum i]

/-- The expectation of a sum of coordinate statistics is the sum of their
one-coordinate expectations. -/
theorem sum_wordMass_mul_sum_coordinates
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) (value : Color → Atom i → ℝ) :
    (∑ word : Color → Atom i,
      wordMass Atom atomProb i word * ∑ c, value c (word c)) =
      ∑ c, ∑ z, atomProb i z * value c z := by
  calc
    (∑ word : Color → Atom i,
        wordMass Atom atomProb i word * ∑ c, value c (word c)) =
        ∑ word : Color → Atom i, ∑ c,
          wordMass Atom atomProb i word * value c (word c) := by
      apply Finset.sum_congr rfl
      intro word _hword
      rw [Finset.mul_sum]
    _ = ∑ c, ∑ word : Color → Atom i,
          wordMass Atom atomProb i word * value c (word c) := by
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ z, atomProb i z * value c z := by
      apply Finset.sum_congr rfl
      intro c _hc
      exact sum_wordMass_mul_coordinate Atom atomProb hatomSum i c (value c)

/-- The same sum-of-coordinate expectation under the padded common state
law. -/
theorem sum_paddedWordProbability_mul_decode_sum_coordinates
    {M : ℕ} (E : Encoding Atom M) (fallback : ∀ i, Atom i)
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) (value : Color → Atom i → ℝ) :
    (∑ a : PackedWordState (Color := Color) M,
      paddedWordProbability Atom E atomProb i a *
        ∑ c, value c
          (decodePackedWord Atom (Color := Color) E fallback i a c)) =
      ∑ c, ∑ z, atomProb i z * value c z := by
  rw [sum_paddedWordProbability_mul_decode Atom E fallback atomProb i
    (fun word ↦ ∑ c, value c (word c))]
  exact sum_wordMass_mul_sum_coordinates Atom atomProb hatomSum i value

/-- Two distinct coordinates of a product word have the product of their
one-coordinate expectations. -/
theorem sum_wordMass_mul_two_coordinates
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) (c d : Color) (hcd : c ≠ d)
    (f g : Atom i → ℝ) :
    (∑ word : Color → Atom i,
      wordMass Atom atomProb i word * (f (word c) * g (word d))) =
      (∑ z, atomProb i z * f z) *
        ∑ z, atomProb i z * g z := by
  classical
  let coordFactor : Color → ℝ := fun e ↦
    ∑ z : Atom i, atomProb i z *
      (if e = c then f z else if e = d then g z else 1)
  calc
    (∑ word : Color → Atom i,
        wordMass Atom atomProb i word * (f (word c) * g (word d))) =
        ∑ word : Color → Atom i,
          ∏ e, atomProb i (word e) *
            (if e = c then f (word e)
              else if e = d then g (word e) else 1) := by
      apply Finset.sum_congr rfl
      intro word _hword
      unfold wordMass
      have hfactor :
          (∏ e : Color,
            (if e = c then f (word e)
              else if e = d then g (word e) else 1)) =
            f (word c) * g (word d) := by
        calc
          (∏ e : Color,
              (if e = c then f (word e)
                else if e = d then g (word e) else 1)) =
              ∏ e : Color,
                ((if e = c then f (word e) else 1) *
                  (if e = d then g (word e) else 1)) := by
            apply Finset.prod_congr rfl
            intro e _he
            by_cases hec : e = c
            · subst e
              simp [hcd]
            · by_cases hed : e = d <;> simp [hec, hed, hcd.symm]
          _ = (∏ e : Color, if e = c then f (word e) else 1) *
                ∏ e : Color, if e = d then g (word e) else 1 := by
            rw [Finset.prod_mul_distrib]
          _ = f (word c) * g (word d) := by
            rw [Fintype.prod_ite_eq', Fintype.prod_ite_eq']
      rw [Finset.prod_mul_distrib]
      rw [hfactor]
    _ = ∏ e, ∑ z : Atom i, atomProb i z *
          (if e = c then f z else if e = d then g z else 1) := by
      exact (Fintype.prod_sum
        (fun e z ↦ atomProb i z *
          (if e = c then f z else if e = d then g z else 1))).symm
    _ = ∏ e, coordFactor e := by rfl
    _ = (∑ z, atomProb i z * f z) *
          ∑ z, atomProb i z * g z := by
      rw [← Finset.prod_erase_mul (Finset.univ : Finset Color) coordFactor
        (Finset.mem_univ c)]
      have hdmem : d ∈ (Finset.univ : Finset Color).erase c := by
        exact Finset.mem_erase.mpr ⟨hcd.symm, Finset.mem_univ d⟩
      rw [← Finset.prod_erase_mul
        ((Finset.univ : Finset Color).erase c) coordFactor hdmem]
      have hrest :
          ∏ e ∈ ((Finset.univ : Finset Color).erase c).erase d,
            coordFactor e = 1 := by
        apply Finset.prod_eq_one
        intro e he
        have hec : e ≠ c := by
          exact (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).1
        have hed : e ≠ d := (Finset.mem_erase.mp he).1
        simp [coordFactor, hec, hed, hatomSum i]
      rw [hrest, one_mul]
      simp [coordFactor, hcd, hcd.symm, mul_comm]

/-- Padded product words retain exact two-coordinate expectations. -/
theorem sum_paddedWordProbability_mul_decode_two_coordinates
    {M : ℕ} (E : Encoding Atom M) (fallback : ∀ i, Atom i)
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) (c d : Color) (hcd : c ≠ d)
    (f g : Atom i → ℝ) :
    (∑ a : PackedWordState (Color := Color) M,
      paddedWordProbability Atom E atomProb i a *
        (f (decodePackedWord Atom (Color := Color) E fallback i a c) *
          g (decodePackedWord Atom (Color := Color) E fallback i a d))) =
      (∑ z, atomProb i z * f z) *
        ∑ z, atomProb i z * g z := by
  rw [sum_paddedWordProbability_mul_decode Atom E fallback atomProb i
    (fun word ↦ f (word c) * g (word d))]
  exact sum_wordMass_mul_two_coordinates Atom atomProb hatomSum i c d hcd f g

/-- Centering by the exact mean gives expectation zero. -/
theorem sum_atomProb_mul_sub_mean
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) (value : Atom i → ℝ) (mean : ℝ)
    (hmean : ∑ z, atomProb i z * value z = mean) :
    (∑ z, atomProb i z * (value z - mean)) = 0 := by
  calc
    (∑ z, atomProb i z * (value z - mean)) =
        ∑ z, (atomProb i z * value z - atomProb i z * mean) := by
      apply Finset.sum_congr rfl
      intro z _hz
      ring
    _ = (∑ z, atomProb i z * value z) -
          (∑ z, atomProb i z) * mean := by
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = 0 := by rw [hmean, hatomSum i]; ring

/-- The elementary one-coordinate variance identity. -/
theorem sum_atomProb_mul_sub_mean_sq
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) (value : Atom i → ℝ) (mean : ℝ)
    (hmean : ∑ z, atomProb i z * value z = mean) :
    (∑ z, atomProb i z * (value z - mean) ^ 2) =
      (∑ z, atomProb i z * (value z) ^ 2) - mean ^ 2 := by
  calc
    (∑ z, atomProb i z * (value z - mean) ^ 2) =
        (∑ z, atomProb i z * (value z) ^ 2) -
          2 * mean * (∑ z, atomProb i z * value z) +
          (∑ z, atomProb i z) * mean ^ 2 := by
      rw [Finset.mul_sum, Finset.sum_mul]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _hz
      ring
    _ = (∑ z, atomProb i z * (value z) ^ 2) - mean ^ 2 := by
      rw [hmean, hatomSum i]
      ring

/-- Distinct centered coordinates have zero cross moment. -/
theorem sum_wordMass_mul_centered_cross
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) (c d : Color) (hcd : c ≠ d)
    (value : Color → Atom i → ℝ) (mean : Color → ℝ)
    (hmean : ∀ e, ∑ z, atomProb i z * value e z = mean e) :
    (∑ word : Color → Atom i,
      wordMass Atom atomProb i word *
        ((value c (word c) - mean c) *
          (value d (word d) - mean d))) = 0 := by
  rw [sum_wordMass_mul_two_coordinates Atom atomProb hatomSum i c d hcd
    (fun z ↦ value c z - mean c) (fun z ↦ value d z - mean d)]
  rw [sum_atomProb_mul_sub_mean Atom atomProb hatomSum i
      (value c) (mean c) (hmean c),
    sum_atomProb_mul_sub_mean Atom atomProb hatomSum i
      (value d) (mean d) (hmean d)]
  ring

/-- Expanding a weighted square of a finite sum and exchanging the three
finite sums. -/
private theorem sum_mass_mul_sum_sq_eq
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    (mass : Sample → ℝ) (term : Sample → Color → ℝ) :
    (∑ sample : Sample,
      mass sample * (∑ c, term sample c) ^ 2) =
      ∑ c, ∑ d, ∑ sample : Sample,
        mass sample * (term sample c * term sample d) := by
  have hpoint : ∀ sample : Sample,
      mass sample * (∑ c, term sample c) ^ 2 =
        ∑ c, ∑ d,
          mass sample * (term sample c * term sample d) := by
    intro sample
    calc
      mass sample * (∑ c, term sample c) ^ 2 =
          mass sample * ((∑ c, term sample c) *
            ∑ d, term sample d) := by rw [pow_two]
      _ = mass sample *
          (∑ c, term sample c *
            ∑ d, term sample d) := by rw [Finset.sum_mul]
      _ = ∑ c, mass sample *
          (term sample c * ∑ d, term sample d) := by
        rw [Finset.mul_sum]
      _ = ∑ c, ∑ d,
          mass sample * (term sample c * term sample d) := by
        apply Finset.sum_congr rfl
        intro c _hc
        calc
          mass sample *
              (term sample c * ∑ d, term sample d) =
              (mass sample * term sample c) *
                ∑ d, term sample d := by ring
          _ = ∑ d, (mass sample * term sample c) *
                term sample d := by rw [Finset.mul_sum]
          _ = ∑ d, mass sample *
                (term sample c * term sample d) := by
            apply Finset.sum_congr rfl
            intro d _hd
            ring
  calc
    (∑ sample : Sample,
        mass sample * (∑ c, term sample c) ^ 2) =
        ∑ sample : Sample, ∑ c, ∑ d,
          mass sample * (term sample c * term sample d) := by
      apply Finset.sum_congr rfl
      intro sample _hsample
      exact hpoint sample
    _ = ∑ c, ∑ sample : Sample, ∑ d,
          mass sample * (term sample c * term sample d) := by
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ sample : Sample,
          mass sample * (term sample c * term sample d) := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [Finset.sum_comm]

/-- For independent word coordinates, the variance of a centered sum is the
sum of the coordinate variances. -/
theorem sum_wordMass_mul_centered_sum_sq
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) (value : Color → Atom i → ℝ) (mean : Color → ℝ)
    (hmean : ∀ c, ∑ z, atomProb i z * value c z = mean c) :
    (∑ word : Color → Atom i,
      wordMass Atom atomProb i word *
        (∑ c, (value c (word c) - mean c)) ^ 2) =
      ∑ c, ∑ z, atomProb i z * (value c z - mean c) ^ 2 := by
  rw [sum_mass_mul_sum_sq_eq
    (wordMass Atom atomProb i)
    (fun word c ↦ value c (word c) - mean c)]
  apply Finset.sum_congr rfl
  intro c _hc
  calc
    (∑ d, ∑ word : Color → Atom i,
        wordMass Atom atomProb i word *
          ((value c (word c) - mean c) *
            (value d (word d) - mean d))) =
        ∑ d, if c = d then
          (∑ z, atomProb i z * (value c z - mean c) ^ 2) else 0 := by
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hcd : c = d
      · rw [if_pos hcd]
        subst d
        simpa only [pow_two] using
          (sum_wordMass_mul_coordinate Atom atomProb hatomSum i c
            (fun z ↦
              (value c z - mean c) * (value c z - mean c)))
      · rw [if_neg hcd]
        exact sum_wordMass_mul_centered_cross Atom atomProb hatomSum i c d
          hcd value mean hmean
    _ = ∑ z, atomProb i z * (value c z - mean c) ^ 2 := by
      simp

/-- Exact centered-sum variance under the common padded state law. -/
theorem sum_paddedWordProbability_mul_decode_centered_sum_sq
    {M : ℕ} (E : Encoding Atom M) (fallback : ∀ i, Atom i)
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) (value : Color → Atom i → ℝ) (mean : Color → ℝ)
    (hmean : ∀ c, ∑ z, atomProb i z * value c z = mean c) :
    (∑ a : PackedWordState (Color := Color) M,
      paddedWordProbability Atom E atomProb i a *
        (∑ c, (value c
          (decodePackedWord Atom (Color := Color) E fallback i a c) -
            mean c)) ^ 2) =
      ∑ c, ∑ z, atomProb i z * (value c z - mean c) ^ 2 := by
  rw [sum_paddedWordProbability_mul_decode Atom E fallback atomProb i
    (fun word ↦ (∑ c, (value c (word c) - mean c)) ^ 2)]
  exact sum_wordMass_mul_centered_sum_sq Atom atomProb hatomSum i
    value mean hmean

/-! ## Two independent endpoint words -/

/-- Exact expectation of a statistic of one coordinate in two independently
sampled words. -/
theorem sum_twoWordMass_mul_coordinate
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i j : Source) (c : Color) (value : Atom i → Atom j → ℝ) :
    (∑ left : Color → Atom i,
      wordMass Atom atomProb i left *
        ∑ right : Color → Atom j,
          wordMass Atom atomProb j right * value (left c) (right c)) =
      ∑ x, atomProb i x * ∑ y, atomProb j y * value x y := by
  calc
    (∑ left : Color → Atom i,
      wordMass Atom atomProb i left *
        ∑ right : Color → Atom j,
          wordMass Atom atomProb j right * value (left c) (right c)) =
        ∑ left : Color → Atom i,
          wordMass Atom atomProb i left *
            ∑ y, atomProb j y * value (left c) y := by
      apply Finset.sum_congr rfl
      intro left _hleft
      congr 1
      exact sum_wordMass_mul_coordinate Atom atomProb hatomSum j c
        (value (left c))
    _ = ∑ x, atomProb i x * ∑ y, atomProb j y * value x y := by
      exact sum_wordMass_mul_coordinate Atom atomProb hatomSum i c
        (fun x ↦ ∑ y, atomProb j y * value x y)

/-- Statistics on two distinct coordinates factor under two independently
sampled product words. -/
theorem sum_twoWordMass_mul_two_coordinates
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i j : Source) (c d : Color) (hcd : c ≠ d)
    (f g : Atom i → Atom j → ℝ) :
    (∑ left : Color → Atom i,
      wordMass Atom atomProb i left *
        ∑ right : Color → Atom j,
          wordMass Atom atomProb j right *
            (f (left c) (right c) * g (left d) (right d))) =
      (∑ x, atomProb i x * ∑ y, atomProb j y * f x y) *
        ∑ x, atomProb i x * ∑ y, atomProb j y * g x y := by
  calc
    (∑ left : Color → Atom i,
      wordMass Atom atomProb i left *
        ∑ right : Color → Atom j,
          wordMass Atom atomProb j right *
            (f (left c) (right c) * g (left d) (right d))) =
        ∑ left : Color → Atom i,
          wordMass Atom atomProb i left *
            ((∑ y, atomProb j y * f (left c) y) *
              ∑ y, atomProb j y * g (left d) y) := by
      apply Finset.sum_congr rfl
      intro left _hleft
      congr 1
      exact sum_wordMass_mul_two_coordinates Atom atomProb hatomSum j c d
        hcd (f (left c)) (g (left d))
    _ = (∑ x, atomProb i x * ∑ y, atomProb j y * f x y) *
        ∑ x, atomProb i x * ∑ y, atomProb j y * g x y := by
      exact sum_wordMass_mul_two_coordinates Atom atomProb hatomSum i c d hcd
        (fun x ↦ ∑ y, atomProb j y * f x y)
        (fun x ↦ ∑ y, atomProb j y * g x y)

/-- Centering a statistic under the product of two atom laws gives
expectation zero. -/
theorem sum_twoAtomProb_mul_sub_mean
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i j : Source) (value : Atom i → Atom j → ℝ) (mean : ℝ)
    (hmean : ∑ x, atomProb i x *
      ∑ y, atomProb j y * value x y = mean) :
    (∑ x, atomProb i x *
      ∑ y, atomProb j y * (value x y - mean)) = 0 := by
  calc
    (∑ x, atomProb i x *
      ∑ y, atomProb j y * (value x y - mean)) =
        ∑ x, atomProb i x *
          ((∑ y, atomProb j y * value x y) - mean) := by
      apply Finset.sum_congr rfl
      intro x _hx
      congr 1
      calc
        (∑ y, atomProb j y * (value x y - mean)) =
            ∑ y, (atomProb j y * value x y - atomProb j y * mean) := by
          apply Finset.sum_congr rfl
          intro y _hy
          ring
        _ = (∑ y, atomProb j y * value x y) -
              (∑ y, atomProb j y) * mean := by
          rw [Finset.sum_sub_distrib, Finset.sum_mul]
        _ = (∑ y, atomProb j y * value x y) - mean := by
          rw [hatomSum j]
          ring
    _ = (∑ x, atomProb i x *
          ∑ y, atomProb j y * value x y) - mean := by
      calc
        (∑ x, atomProb i x *
          ((∑ y, atomProb j y * value x y) - mean)) =
            ∑ x, (atomProb i x *
              (∑ y, atomProb j y * value x y) -
                atomProb i x * mean) := by
          apply Finset.sum_congr rfl
          intro x _hx
          ring
        _ = (∑ x, atomProb i x *
              ∑ y, atomProb j y * value x y) -
              (∑ x, atomProb i x) * mean := by
          rw [Finset.sum_sub_distrib, Finset.sum_mul]
        _ = (∑ x, atomProb i x *
              ∑ y, atomProb j y * value x y) - mean := by
          rw [hatomSum i]
          ring
    _ = 0 := by rw [hmean]; ring

/-- Distinct coordinate pairs have zero cross moment after centering by
their exact joint means. -/
theorem sum_twoWordMass_mul_centered_cross
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i j : Source) (c d : Color) (hcd : c ≠ d)
    (value : Color → Atom i → Atom j → ℝ) (mean : Color → ℝ)
    (hmean : ∀ e, ∑ x, atomProb i x *
      ∑ y, atomProb j y * value e x y = mean e) :
    (∑ left : Color → Atom i,
      wordMass Atom atomProb i left *
        ∑ right : Color → Atom j,
          wordMass Atom atomProb j right *
            ((value c (left c) (right c) - mean c) *
              (value d (left d) (right d) - mean d))) = 0 := by
  rw [sum_twoWordMass_mul_two_coordinates Atom atomProb hatomSum i j c d hcd
    (fun x y ↦ value c x y - mean c)
    (fun x y ↦ value d x y - mean d)]
  rw [sum_twoAtomProb_mul_sub_mean Atom atomProb hatomSum i j
      (value c) (mean c) (hmean c),
    sum_twoAtomProb_mul_sub_mean Atom atomProb hatomSum i j
      (value d) (mean d) (hmean d)]
  ring

/-- Exact variance additivity for a coordinate sum formed from two
independent product words. -/
theorem sum_twoWordMass_mul_centered_sum_sq
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i j : Source) (value : Color → Atom i → Atom j → ℝ)
    (mean : Color → ℝ)
    (hmean : ∀ c, ∑ x, atomProb i x *
      ∑ y, atomProb j y * value c x y = mean c) :
    (∑ left : Color → Atom i,
      wordMass Atom atomProb i left *
        ∑ right : Color → Atom j,
          wordMass Atom atomProb j right *
            (∑ c, (value c (left c) (right c) - mean c)) ^ 2) =
      ∑ c, ∑ x, atomProb i x * ∑ y, atomProb j y *
        (value c x y - mean c) ^ 2 := by
  have hexpand := sum_mass_mul_sum_sq_eq
    (Color := Color)
    (mass := fun pair : (Color → Atom i) × (Color → Atom j) ↦
      wordMass Atom atomProb i pair.1 * wordMass Atom atomProb j pair.2)
    (term := fun pair c ↦ value c (pair.1 c) (pair.2 c) - mean c)
  simp only [Fintype.sum_prod_type, Prod.fst, Prod.snd] at hexpand
  have hexpand' :
      (∑ left : Color → Atom i,
        wordMass Atom atomProb i left *
          ∑ right : Color → Atom j,
            wordMass Atom atomProb j right *
              (∑ c, (value c (left c) (right c) - mean c)) ^ 2) =
        ∑ c, ∑ d, ∑ left : Color → Atom i,
          wordMass Atom atomProb i left *
            ∑ right : Color → Atom j,
              wordMass Atom atomProb j right *
                ((value c (left c) (right c) - mean c) *
                  (value d (left d) (right d) - mean d)) := by
    calc
      (∑ left : Color → Atom i,
        wordMass Atom atomProb i left *
          ∑ right : Color → Atom j,
            wordMass Atom atomProb j right *
              (∑ c, (value c (left c) (right c) - mean c)) ^ 2) =
          ∑ left : Color → Atom i, ∑ right : Color → Atom j,
            (wordMass Atom atomProb i left *
              wordMass Atom atomProb j right) *
                (∑ c, (value c (left c) (right c) - mean c)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro left _hleft
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro right _hright
        ring
      _ = ∑ c, ∑ d, ∑ left : Color → Atom i,
          ∑ right : Color → Atom j,
            (wordMass Atom atomProb i left *
              wordMass Atom atomProb j right) *
                ((value c (left c) (right c) - mean c) *
                  (value d (left d) (right d) - mean d)) := hexpand
      _ = ∑ c, ∑ d, ∑ left : Color → Atom i,
          wordMass Atom atomProb i left *
            ∑ right : Color → Atom j,
              wordMass Atom atomProb j right *
                ((value c (left c) (right c) - mean c) *
                  (value d (left d) (right d) - mean d)) := by
        apply Finset.sum_congr rfl
        intro c _hc
        apply Finset.sum_congr rfl
        intro d _hd
        apply Finset.sum_congr rfl
        intro left _hleft
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro right _hright
        ring
  rw [hexpand']
  apply Finset.sum_congr rfl
  intro c _hc
  calc
    (∑ d, ∑ left : Color → Atom i,
      wordMass Atom atomProb i left *
        ∑ right : Color → Atom j,
          wordMass Atom atomProb j right *
            ((value c (left c) (right c) - mean c) *
              (value d (left d) (right d) - mean d))) =
        ∑ d, if c = d then
          (∑ x, atomProb i x * ∑ y, atomProb j y *
            (value c x y - mean c) ^ 2) else 0 := by
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hcd : c = d
      · rw [if_pos hcd]
        subst d
        simpa only [pow_two] using
          (sum_twoWordMass_mul_coordinate Atom atomProb hatomSum i j c
            (fun x y ↦
              (value c x y - mean c) * (value c x y - mean c)))
      · rw [if_neg hcd]
        exact sum_twoWordMass_mul_centered_cross Atom atomProb hatomSum
          i j c d hcd value mean hmean
    _ = ∑ x, atomProb i x * ∑ y, atomProb j y *
        (value c x y - mean c) ^ 2 := by
      simp

/-- The preceding joint variance identity also holds after independently
padding both endpoint words into their common categorical state spaces. -/
theorem sum_twoPaddedWordProbability_mul_decode_centered_sum_sq
    {M : ℕ} (E : Encoding Atom M) (fallback : ∀ i, Atom i)
    (atomProb : ∀ i, Atom i → ℝ)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i j : Source) (value : Color → Atom i → Atom j → ℝ)
    (mean : Color → ℝ)
    (hmean : ∀ c, ∑ x, atomProb i x *
      ∑ y, atomProb j y * value c x y = mean c) :
    (∑ left : PackedWordState (Color := Color) M,
      paddedWordProbability Atom E atomProb i left *
        ∑ right : PackedWordState (Color := Color) M,
          paddedWordProbability Atom E atomProb j right *
            (∑ c, (value c
              (decodePackedWord Atom (Color := Color) E fallback i left c)
              (decodePackedWord Atom (Color := Color) E fallback j right c) -
                mean c)) ^ 2) =
      ∑ c, ∑ x, atomProb i x * ∑ y, atomProb j y *
        (value c x y - mean c) ^ 2 := by
  calc
    (∑ left : PackedWordState (Color := Color) M,
      paddedWordProbability Atom E atomProb i left *
        ∑ right : PackedWordState (Color := Color) M,
          paddedWordProbability Atom E atomProb j right *
            (∑ c, (value c
              (decodePackedWord Atom (Color := Color) E fallback i left c)
              (decodePackedWord Atom (Color := Color) E fallback j right c) -
                mean c)) ^ 2) =
        ∑ left : PackedWordState (Color := Color) M,
          paddedWordProbability Atom E atomProb i left *
            ∑ rightWord : Color → Atom j,
              wordMass Atom atomProb j rightWord *
                (∑ c, (value c
                  (decodePackedWord Atom (Color := Color) E fallback i left c)
                  (rightWord c) - mean c)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro left _hleft
      congr 1
      exact sum_paddedWordProbability_mul_decode Atom E fallback atomProb j
        (fun rightWord ↦
          (∑ c, (value c
            (decodePackedWord Atom (Color := Color) E fallback i left c)
            (rightWord c) - mean c)) ^ 2)
    _ = ∑ leftWord : Color → Atom i,
          wordMass Atom atomProb i leftWord *
            ∑ rightWord : Color → Atom j,
              wordMass Atom atomProb j rightWord *
                (∑ c, (value c (leftWord c) (rightWord c) - mean c)) ^ 2 := by
      exact sum_paddedWordProbability_mul_decode Atom E fallback atomProb i
        (fun leftWord ↦
          ∑ rightWord : Color → Atom j,
            wordMass Atom atomProb j rightWord *
              (∑ c, (value c (leftWord c) (rightWord c) - mean c)) ^ 2)
    _ = ∑ c, ∑ x, atomProb i x * ∑ y, atomProb j y *
        (value c x y - mean c) ^ 2 :=
      sum_twoWordMass_mul_centered_sum_sq Atom atomProb hatomSum i j
        value mean hmean

/-- Variance identity for an arbitrary normalized finite mass function.  No
positivity assumption is needed for this algebraic identity. -/
theorem finite_sum_mul_sub_mean_sq
    {A : Type*} [Fintype A] [DecidableEq A]
    (prob value : A → ℝ) (mean : ℝ)
    (hprobSum : ∑ a, prob a = 1)
    (hmean : ∑ a, prob a * value a = mean) :
    (∑ a, prob a * (value a - mean) ^ 2) =
      (∑ a, prob a * (value a) ^ 2) - mean ^ 2 := by
  calc
    (∑ a, prob a * (value a - mean) ^ 2) =
        (∑ a, prob a * (value a) ^ 2) -
          2 * mean * (∑ a, prob a * value a) +
          (∑ a, prob a) * mean ^ 2 := by
      rw [Finset.mul_sum, Finset.sum_mul]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = (∑ a, prob a * (value a) ^ 2) - mean ^ 2 := by
      rw [hmean, hprobSum]
      ring

/-- A normalized finite nonnegative mass and a variable in `[0,U]` satisfy
`Var(X) ≤ U E[X]`. -/
theorem finite_sum_mul_sub_mean_sq_le_mul
    {A : Type*} [Fintype A] [DecidableEq A]
    (prob value : A → ℝ) (mean U : ℝ)
    (hprob0 : ∀ a, 0 ≤ prob a)
    (hprobSum : ∑ a, prob a = 1)
    (hvalue0 : ∀ a, 0 ≤ value a)
    (hvalueU : ∀ a, value a ≤ U)
    (hmean : ∑ a, prob a * value a = mean) :
    (∑ a, prob a * (value a - mean) ^ 2) ≤ U * mean := by
  have hsecond :
      (∑ a, prob a * (value a) ^ 2) ≤
        U * (∑ a, prob a * value a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _ha
    have hsq : (value a) ^ 2 ≤ U * value a := by
      nlinarith [hvalue0 a, hvalueU a]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left hsq (hprob0 a))
  rw [finite_sum_mul_sub_mean_sq prob value mean hprobSum hmean]
  rw [hmean] at hsecond
  exact (sub_le_sub_right hsecond (mean ^ 2)).trans
    (sub_le_self (U * mean) (sq_nonneg mean))

/-- The joint atom law at two endpoints satisfies the same bounded-variance
estimate. -/
theorem sum_twoAtomProb_mul_sub_mean_sq_le_mul
    (atomProb : ∀ i, Atom i → ℝ)
    (hatom0 : ∀ i z, 0 ≤ atomProb i z)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i j : Source) (value : Atom i → Atom j → ℝ) (mean U : ℝ)
    (hvalue0 : ∀ x y, 0 ≤ value x y)
    (hvalueU : ∀ x y, value x y ≤ U)
    (hmean : ∑ x, atomProb i x *
      ∑ y, atomProb j y * value x y = mean) :
    (∑ x, atomProb i x *
      ∑ y, atomProb j y * (value x y - mean) ^ 2) ≤ U * mean := by
  let pairProb : Atom i × Atom j → ℝ :=
    fun z ↦ atomProb i z.1 * atomProb j z.2
  let pairValue : Atom i × Atom j → ℝ := fun z ↦ value z.1 z.2
  have hpair0 : ∀ z, 0 ≤ pairProb z := by
    intro z
    exact mul_nonneg (hatom0 i z.1) (hatom0 j z.2)
  have hpairSum : ∑ z, pairProb z = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [pairProb]
    calc
      (∑ x, ∑ y, atomProb i x * atomProb j y) =
          ∑ x, atomProb i x * ∑ y, atomProb j y := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [Finset.mul_sum]
      _ = 1 := by simp [hatomSum]
  have hpairMean : ∑ z, pairProb z * pairValue z = mean := by
    rw [Fintype.sum_prod_type]
    simp only [pairProb, pairValue]
    calc
      (∑ x, ∑ y,
        (atomProb i x * atomProb j y) * value x y) =
          ∑ x, atomProb i x * ∑ y, atomProb j y * value x y := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _hy
        ring
      _ = mean := hmean
  have h := finite_sum_mul_sub_mean_sq_le_mul pairProb pairValue mean U
    hpair0 hpairSum
    (fun z ↦ hvalue0 z.1 z.2) (fun z ↦ hvalueU z.1 z.2) hpairMean
  rw [Fintype.sum_prod_type] at h
  calc
    (∑ x, atomProb i x *
      ∑ y, atomProb j y * (value x y - mean) ^ 2) =
        ∑ x, ∑ y, (atomProb i x * atomProb j y) *
          (value x y - mean) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      ring
    _ ≤ U * mean := by simpa [pairProb, pairValue] using h

/-- Summed joint variance bound for two endpoint words. -/
theorem sum_twoWordMass_mul_centered_sum_sq_le
    (atomProb : ∀ i, Atom i → ℝ)
    (hatom0 : ∀ i z, 0 ≤ atomProb i z)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i j : Source) (value : Color → Atom i → Atom j → ℝ)
    (mean upper : Color → ℝ)
    (hvalue0 : ∀ c x y, 0 ≤ value c x y)
    (hvalueUpper : ∀ c x y, value c x y ≤ upper c)
    (hmean : ∀ c, ∑ x, atomProb i x *
      ∑ y, atomProb j y * value c x y = mean c) :
    (∑ left : Color → Atom i,
      wordMass Atom atomProb i left *
        ∑ right : Color → Atom j,
          wordMass Atom atomProb j right *
            (∑ c, (value c (left c) (right c) - mean c)) ^ 2) ≤
      ∑ c, upper c * mean c := by
  rw [sum_twoWordMass_mul_centered_sum_sq Atom atomProb hatomSum i j
    value mean hmean]
  exact Finset.sum_le_sum fun c _hc ↦
    sum_twoAtomProb_mul_sub_mean_sq_le_mul Atom atomProb hatom0 hatomSum
      i j (value c) (mean c) (upper c) (hvalue0 c) (hvalueUpper c) (hmean c)

/-- The summed joint variance bound after padding both endpoint words. -/
theorem sum_twoPaddedWordProbability_mul_decode_centered_sum_sq_le
    {M : ℕ} (E : Encoding Atom M) (fallback : ∀ i, Atom i)
    (atomProb : ∀ i, Atom i → ℝ)
    (hatom0 : ∀ i z, 0 ≤ atomProb i z)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i j : Source) (value : Color → Atom i → Atom j → ℝ)
    (mean upper : Color → ℝ)
    (hvalue0 : ∀ c x y, 0 ≤ value c x y)
    (hvalueUpper : ∀ c x y, value c x y ≤ upper c)
    (hmean : ∀ c, ∑ x, atomProb i x *
      ∑ y, atomProb j y * value c x y = mean c) :
    (∑ left : PackedWordState (Color := Color) M,
      paddedWordProbability Atom E atomProb i left *
        ∑ right : PackedWordState (Color := Color) M,
          paddedWordProbability Atom E atomProb j right *
            (∑ c, (value c
              (decodePackedWord Atom (Color := Color) E fallback i left c)
              (decodePackedWord Atom (Color := Color) E fallback j right c) -
                mean c)) ^ 2) ≤
      ∑ c, upper c * mean c := by
  rw [sum_twoPaddedWordProbability_mul_decode_centered_sum_sq Atom E fallback
    atomProb hatomSum i j value mean hmean]
  exact Finset.sum_le_sum fun c _hc ↦
    sum_twoAtomProb_mul_sub_mean_sq_le_mul Atom atomProb hatom0 hatomSum
      i j (value c) (mean c) (upper c) (hvalue0 c) (hvalueUpper c) (hmean c)

/-- Constant-mean form used for a block of `k` identically distributed
color coordinates. -/
theorem sum_twoPaddedWordProbability_mul_decode_block_sum_sub_card_sq_le
    {M : ℕ} (E : Encoding Atom M) (fallback : ∀ i, Atom i)
    (atomProb : ∀ i, Atom i → ℝ)
    (hatom0 : ∀ i z, 0 ≤ atomProb i z)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i j : Source) (value : Color → Atom i → Atom j → ℝ)
    (mean upper : ℝ)
    (hvalue0 : ∀ c x y, 0 ≤ value c x y)
    (hvalueUpper : ∀ c x y, value c x y ≤ upper)
    (hmean : ∀ c, ∑ x, atomProb i x *
      ∑ y, atomProb j y * value c x y = mean) :
    (∑ left : PackedWordState (Color := Color) M,
      paddedWordProbability Atom E atomProb i left *
        ∑ right : PackedWordState (Color := Color) M,
          paddedWordProbability Atom E atomProb j right *
            ((∑ c, value c
              (decodePackedWord Atom (Color := Color) E fallback i left c)
              (decodePackedWord Atom (Color := Color) E fallback j right c)) -
                (Fintype.card Color : ℝ) * mean) ^ 2) ≤
      (Fintype.card Color : ℝ) * upper * mean := by
  have h := sum_twoPaddedWordProbability_mul_decode_centered_sum_sq_le
    Atom E fallback atomProb hatom0 hatomSum i j value
    (fun _c ↦ mean) (fun _c ↦ upper) hvalue0 hvalueUpper hmean
  simpa [Finset.sum_sub_distrib, mul_assoc] using h

/-- A bounded nonnegative variable has variance at most `U` times its mean.
No sign condition on the stated mean is needed; it follows from the other
hypotheses. -/
theorem sum_atomProb_mul_sub_mean_sq_le_mul
    (atomProb : ∀ i, Atom i → ℝ)
    (hatom0 : ∀ i z, 0 ≤ atomProb i z)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) (value : Atom i → ℝ) (mean U : ℝ)
    (hvalue0 : ∀ z, 0 ≤ value z)
    (hvalueU : ∀ z, value z ≤ U)
    (hmean : ∑ z, atomProb i z * value z = mean) :
    (∑ z, atomProb i z * (value z - mean) ^ 2) ≤ U * mean := by
  have hsecond :
      (∑ z, atomProb i z * (value z) ^ 2) ≤
        U * (∑ z, atomProb i z * value z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z _hz
    have hsq : (value z) ^ 2 ≤ U * value z := by
      nlinarith [hvalue0 z, hvalueU z]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left hsq (hatom0 i z))
  rw [sum_atomProb_mul_sub_mean_sq Atom atomProb hatomSum i value mean hmean]
  rw [hmean] at hsecond
  exact (sub_le_sub_right hsecond (mean ^ 2)).trans
    (sub_le_self (U * mean) (sq_nonneg mean))

/-- The variance bound summed across all independent coordinates. -/
theorem sum_wordMass_mul_centered_sum_sq_le
    (atomProb : ∀ i, Atom i → ℝ)
    (hatom0 : ∀ i z, 0 ≤ atomProb i z)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) (value : Color → Atom i → ℝ)
    (mean upper : Color → ℝ)
    (hvalue0 : ∀ c z, 0 ≤ value c z)
    (hvalueUpper : ∀ c z, value c z ≤ upper c)
    (hmean : ∀ c, ∑ z, atomProb i z * value c z = mean c) :
    (∑ word : Color → Atom i,
      wordMass Atom atomProb i word *
        (∑ c, (value c (word c) - mean c)) ^ 2) ≤
      ∑ c, upper c * mean c := by
  rw [sum_wordMass_mul_centered_sum_sq Atom atomProb hatomSum i
    value mean hmean]
  exact Finset.sum_le_sum fun c _hc ↦
    sum_atomProb_mul_sub_mean_sq_le_mul Atom atomProb hatom0 hatomSum i
      (value c) (mean c) (upper c) (hvalue0 c) (hvalueUpper c) (hmean c)

/-- Padded common states satisfy the same summed variance bound. -/
theorem sum_paddedWordProbability_mul_decode_centered_sum_sq_le
    {M : ℕ} (E : Encoding Atom M) (fallback : ∀ i, Atom i)
    (atomProb : ∀ i, Atom i → ℝ)
    (hatom0 : ∀ i z, 0 ≤ atomProb i z)
    (hatomSum : ∀ i, ∑ z, atomProb i z = 1)
    (i : Source) (value : Color → Atom i → ℝ)
    (mean upper : Color → ℝ)
    (hvalue0 : ∀ c z, 0 ≤ value c z)
    (hvalueUpper : ∀ c z, value c z ≤ upper c)
    (hmean : ∀ c, ∑ z, atomProb i z * value c z = mean c) :
    (∑ a : PackedWordState (Color := Color) M,
      paddedWordProbability Atom E atomProb i a *
        (∑ c, (value c
          (decodePackedWord Atom (Color := Color) E fallback i a c) -
            mean c)) ^ 2) ≤
      ∑ c, upper c * mean c := by
  rw [sum_paddedWordProbability_mul_decode Atom E fallback atomProb i
    (fun word ↦ (∑ c, (value c (word c) - mean c)) ^ 2)]
  exact sum_wordMass_mul_centered_sum_sq_le Atom atomProb hatom0 hatomSum i
    value mean upper hvalue0 hvalueUpper hmean

end

end WeightedEdgeColoring.FiniteDependentWordPadding
