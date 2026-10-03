import WeightedEdgeColoring.FiniteDependentWordBlockMoments

/-!
# Variance of words with coordinate-dependent atom types

Each coordinate may have its own finite state type and law.  The two endpoint
words are independent, and coordinates inside each word are independent.
-/

namespace WeightedEdgeColoring.FiniteCoordinateDependentWordMoments

open scoped BigOperators

noncomputable section

universe u v w

variable {Color : Type u} [Fintype Color] [DecidableEq Color]
variable (Left : Color → Type v) (Right : Color → Type w)
variable [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
variable [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]

def wordMass (prob : ∀ c, Left c → ℝ)
    (word : ∀ c, Left c) : ℝ := ∏ c, prob c (word c)

theorem sum_wordMass
    (prob : ∀ c, Left c → ℝ)
    (hprob : ∀ c, ∑ z, prob c z = 1) :
    (∑ word : ∀ c, Left c, wordMass Left prob word) = 1 := by
  unfold wordMass
  rw [← Fintype.prod_sum]
  simp [hprob]

theorem sum_wordMass_mul_coordinate
    (prob : ∀ c, Left c → ℝ)
    (hprob : ∀ c, ∑ z, prob c z = 1)
    (c : Color) (f : Left c → ℝ) :
    (∑ word : ∀ d, Left d,
      wordMass Left prob word * f (word c)) =
      ∑ z, prob c z * f z := by
  classical
  let factor : ∀ d, Left d → ℝ := fun d z ↦
    if h : d = c then f (h ▸ z) else 1
  calc
    (∑ word : ∀ d, Left d,
      wordMass Left prob word * f (word c)) =
      ∑ word : ∀ d, Left d,
        ∏ d, prob d (word d) * factor d (word d) := by
          apply Finset.sum_congr rfl
          intro word _hword
          unfold wordMass
          rw [Finset.prod_mul_distrib]
          have : (∏ d, factor d (word d)) = f (word c) := by
            rw [← Finset.prod_erase_mul (Finset.univ : Finset Color)
              (fun d ↦ factor d (word d)) (Finset.mem_univ c)]
            simp [factor]
          rw [this]
    _ = ∏ d, ∑ z, prob d z * factor d z := by
      exact (Fintype.prod_sum
        (fun d (z : Left d) ↦ prob d z * factor d z)).symm
    _ = ∑ z, prob c z * f z := by
      rw [← Finset.prod_erase_mul (Finset.univ : Finset Color)
        (fun d ↦ ∑ z, prob d z * factor d z) (Finset.mem_univ c)]
      have hrest : (∏ d ∈ (Finset.univ : Finset Color).erase c,
          ∑ z, prob d z * factor d z) = 1 := by
        apply Finset.prod_eq_one
        intro d hd
        have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
        simp [factor, hdc, hprob d]
      rw [hrest, one_mul]
      simp [factor]

theorem sum_wordMass_mul_two_coordinates
    (prob : ∀ c, Left c → ℝ)
    (hprob : ∀ c, ∑ z, prob c z = 1)
    (c d : Color) (hcd : c ≠ d)
    (f : Left c → ℝ) (g : Left d → ℝ) :
    (∑ word : ∀ e, Left e,
      wordMass Left prob word * (f (word c) * g (word d))) =
      (∑ x, prob c x * f x) * ∑ y, prob d y * g y := by
  classical
  let factor : ∀ e, Left e → ℝ := fun e z ↦
    if h : e = c then f (h ▸ z)
    else if h : e = d then g (h ▸ z) else 1
  calc
    (∑ word : ∀ e, Left e,
      wordMass Left prob word * (f (word c) * g (word d))) =
      ∑ word : ∀ e, Left e,
        ∏ e, prob e (word e) * factor e (word e) := by
          apply Finset.sum_congr rfl
          intro word _hword
          unfold wordMass
          rw [Finset.prod_mul_distrib]
          have hfactor : (∏ e, factor e (word e)) =
              f (word c) * g (word d) := by
            rw [← Finset.prod_erase_mul (Finset.univ : Finset Color)
              (fun e ↦ factor e (word e)) (Finset.mem_univ c)]
            rw [← Finset.prod_erase_mul
              ((Finset.univ : Finset Color).erase c)
              (fun e ↦ factor e (word e))
              (Finset.mem_erase.mpr ⟨hcd.symm, Finset.mem_univ d⟩)]
            have hrest :
                (∏ e ∈ ((Finset.univ : Finset Color).erase c).erase d,
                  factor e (word e)) = 1 := by
              apply Finset.prod_eq_one
              intro e he
              have hed : e ≠ d := (Finset.mem_erase.mp he).1
              have hec : e ≠ c :=
                (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).1
              simp [factor, hec, hed]
            rw [hrest]
            simp [factor, hcd, hcd.symm, mul_comm]
          rw [hfactor]
    _ = ∏ e, ∑ z, prob e z * factor e z := by
      exact (Fintype.prod_sum
        (fun e (z : Left e) ↦ prob e z * factor e z)).symm
    _ = (∑ x, prob c x * f x) * ∑ y, prob d y * g y := by
      rw [← Finset.prod_erase_mul (Finset.univ : Finset Color)
        (fun e ↦ ∑ z, prob e z * factor e z) (Finset.mem_univ c)]
      rw [← Finset.prod_erase_mul
        ((Finset.univ : Finset Color).erase c)
        (fun e ↦ ∑ z, prob e z * factor e z)
        (Finset.mem_erase.mpr ⟨hcd.symm, Finset.mem_univ d⟩)]
      have hrest : (∏ e ∈ ((Finset.univ : Finset Color).erase c).erase d,
          ∑ z, prob e z * factor e z) = 1 := by
        apply Finset.prod_eq_one
        intro e he
        have hec : e ≠ c :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).1
        have hed : e ≠ d := (Finset.mem_erase.mp he).1
        simp [factor, hec, hed, hprob e]
      rw [hrest, one_mul]
      simp [factor, hcd, hcd.symm, mul_comm]

/-- Expanding a weighted square of a finite sum and exchanging the finite
sums. -/
private theorem sum_mass_mul_sum_sq_eq
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    (mass : Sample → ℝ) (term : Sample → Color → ℝ) :
    (∑ sample : Sample, mass sample * (∑ c, term sample c) ^ 2) =
      ∑ c, ∑ d, ∑ sample : Sample,
        mass sample * (term sample c * term sample d) := by
  have hpoint : ∀ sample : Sample,
      mass sample * (∑ c, term sample c) ^ 2 =
        ∑ c, ∑ d, mass sample * (term sample c * term sample d) := by
    intro sample
    calc
      mass sample * (∑ c, term sample c) ^ 2 =
          mass sample * ((∑ c, term sample c) * ∑ d, term sample d) := by
        rw [pow_two]
      _ = mass sample *
          (∑ c, term sample c * ∑ d, term sample d) := by
        rw [Finset.sum_mul]
      _ = ∑ c, mass sample *
          (term sample c * ∑ d, term sample d) := by
        rw [Finset.mul_sum]
      _ = ∑ c, ∑ d,
          mass sample * (term sample c * term sample d) := by
        apply Finset.sum_congr rfl
        intro c _hc
        calc
          mass sample * (term sample c * ∑ d, term sample d) =
              (mass sample * term sample c) * ∑ d, term sample d := by
            ring
          _ = ∑ d, (mass sample * term sample c) * term sample d := by
            rw [Finset.mul_sum]
          _ = ∑ d, mass sample * (term sample c * term sample d) := by
            apply Finset.sum_congr rfl
            intro d _hd
            ring
  calc
    (∑ sample : Sample, mass sample * (∑ c, term sample c) ^ 2) =
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

/-- Exact variance additivity for two independent coordinate-dependent
product words. -/
theorem sum_twoWordMass_mul_centered_sum_sq
    (leftProb : ∀ c, Left c → ℝ)
    (rightProb : ∀ c, Right c → ℝ)
    (hleft : ∀ c, ∑ z, leftProb c z = 1)
    (hright : ∀ c, ∑ z, rightProb c z = 1)
    (value : ∀ c, Left c → Right c → ℝ)
    (mean : Color → ℝ)
    (hmean : ∀ c, ∑ x, leftProb c x *
      ∑ y, rightProb c y * value c x y = mean c) :
    (∑ left : ∀ c, Left c,
      wordMass Left leftProb left *
        ∑ right : ∀ c, Right c,
          wordMass Right rightProb right *
            (∑ c, (value c (left c) (right c) - mean c)) ^ 2) =
      ∑ c, ∑ x, leftProb c x * ∑ y, rightProb c y *
        (value c x y - mean c) ^ 2 := by
  classical
  have hcenter : ∀ c,
      (∑ x, leftProb c x * ∑ y, rightProb c y *
        (value c x y - mean c)) = 0 := by
    intro c
    calc
      (∑ x, leftProb c x * ∑ y, rightProb c y *
          (value c x y - mean c)) =
          ∑ x, leftProb c x *
            ((∑ y, rightProb c y * value c x y) - mean c) := by
        apply Finset.sum_congr rfl
        intro x _hx
        congr 1
        calc
          (∑ y, rightProb c y * (value c x y - mean c)) =
              ∑ y, (rightProb c y * value c x y -
                rightProb c y * mean c) := by
            apply Finset.sum_congr rfl
            intro y _hy
            ring
          _ = (∑ y, rightProb c y * value c x y) -
                (∑ y, rightProb c y) * mean c := by
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
          _ = (∑ y, rightProb c y * value c x y) - mean c := by
            rw [hright c]
            ring
      _ = (∑ x, leftProb c x * ∑ y, rightProb c y * value c x y) -
          mean c := by
        calc
          (∑ x, leftProb c x *
              ((∑ y, rightProb c y * value c x y) - mean c)) =
              ∑ x, (leftProb c x *
                (∑ y, rightProb c y * value c x y) -
                  leftProb c x * mean c) := by
            apply Finset.sum_congr rfl
            intro x _hx
            ring
          _ = (∑ x, leftProb c x * ∑ y, rightProb c y * value c x y) -
                (∑ x, leftProb c x) * mean c := by
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
          _ = (∑ x, leftProb c x * ∑ y, rightProb c y * value c x y) -
                mean c := by
            rw [hleft c]
            ring
      _ = 0 := by rw [hmean c]; ring
  have hcross : ∀ c d, c ≠ d →
      (∑ left : ∀ e, Left e, wordMass Left leftProb left *
        ∑ right : ∀ e, Right e, wordMass Right rightProb right *
          ((value c (left c) (right c) - mean c) *
            (value d (left d) (right d) - mean d))) = 0 := by
    intro c d hcd
    calc
      (∑ left : ∀ e, Left e, wordMass Left leftProb left *
        ∑ right : ∀ e, Right e, wordMass Right rightProb right *
          ((value c (left c) (right c) - mean c) *
            (value d (left d) (right d) - mean d))) =
        ∑ left : ∀ e, Left e, wordMass Left leftProb left *
          ((∑ y, rightProb c y *
              (value c (left c) y - mean c)) *
            (∑ y, rightProb d y *
              (value d (left d) y - mean d))) := by
          apply Finset.sum_congr rfl
          intro left _hleft
          congr 1
          exact sum_wordMass_mul_two_coordinates Right rightProb hright
            c d hcd
            (fun y ↦ value c (left c) y - mean c)
            (fun y ↦ value d (left d) y - mean d)
      _ =
        (∑ x, leftProb c x * ∑ y, rightProb c y *
          (value c x y - mean c)) *
        (∑ x, leftProb d x * ∑ y, rightProb d y *
          (value d x y - mean d)) := by
          exact sum_wordMass_mul_two_coordinates Left leftProb hleft
            c d hcd
            (fun x ↦ ∑ y, rightProb c y *
              (value c x y - mean c))
            (fun x ↦ ∑ y, rightProb d y *
              (value d x y - mean d))
      _ = 0 := by rw [hcenter c, hcenter d]; ring
  have hexpand := sum_mass_mul_sum_sq_eq
    (Color := Color)
    (mass := fun pair : (∀ c, Left c) × (∀ c, Right c) ↦
      wordMass Left leftProb pair.1 * wordMass Right rightProb pair.2)
    (term := fun pair c ↦ value c (pair.1 c) (pair.2 c) - mean c)
  simp only [Fintype.sum_prod_type, Prod.fst, Prod.snd] at hexpand
  have hexpand' :
      (∑ left : ∀ c, Left c,
        wordMass Left leftProb left *
          ∑ right : ∀ c, Right c,
            wordMass Right rightProb right *
              (∑ c, (value c (left c) (right c) - mean c)) ^ 2) =
        ∑ c, ∑ d, ∑ left : ∀ c, Left c,
          wordMass Left leftProb left *
            ∑ right : ∀ c, Right c,
              wordMass Right rightProb right *
                ((value c (left c) (right c) - mean c) *
                  (value d (left d) (right d) - mean d)) := by
    calc
      (∑ left : ∀ c, Left c,
        wordMass Left leftProb left *
          ∑ right : ∀ c, Right c,
            wordMass Right rightProb right *
              (∑ c, (value c (left c) (right c) - mean c)) ^ 2) =
          ∑ left : ∀ c, Left c, ∑ right : ∀ c, Right c,
            (wordMass Left leftProb left * wordMass Right rightProb right) *
              (∑ c, (value c (left c) (right c) - mean c)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro left _hleft
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro right _hright
        ring
      _ = ∑ c, ∑ d, ∑ left : ∀ c, Left c,
          ∑ right : ∀ c, Right c,
            (wordMass Left leftProb left * wordMass Right rightProb right) *
              ((value c (left c) (right c) - mean c) *
                (value d (left d) (right d) - mean d)) := hexpand
      _ = ∑ c, ∑ d, ∑ left : ∀ c, Left c,
          wordMass Left leftProb left *
            ∑ right : ∀ c, Right c,
              wordMass Right rightProb right *
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
    (∑ d, ∑ left : ∀ e, Left e,
      wordMass Left leftProb left *
        ∑ right : ∀ e, Right e,
          wordMass Right rightProb right *
            ((value c (left c) (right c) - mean c) *
              (value d (left d) (right d) - mean d))) =
      ∑ d, if c = d then
        (∑ x, leftProb c x * ∑ y, rightProb c y *
          (value c x y - mean c) ^ 2) else 0 := by
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hcd : c = d
      · subst d
        rw [if_pos rfl]
        calc
          (∑ left : ∀ e, Left e,
            wordMass Left leftProb left *
              ∑ right : ∀ e, Right e,
                wordMass Right rightProb right *
                  ((value c (left c) (right c) - mean c) *
                    (value c (left c) (right c) - mean c))) =
              ∑ left : ∀ e, Left e,
                wordMass Left leftProb left *
                  ∑ y, rightProb c y *
                    ((value c (left c) y - mean c) *
                      (value c (left c) y - mean c)) := by
            apply Finset.sum_congr rfl
            intro left _hleft
            congr 1
            exact sum_wordMass_mul_coordinate Right rightProb hright c
              (fun y ↦ (value c (left c) y - mean c) *
                (value c (left c) y - mean c))
          _ = ∑ x, leftProb c x * ∑ y, rightProb c y *
              ((value c x y - mean c) * (value c x y - mean c)) := by
            exact sum_wordMass_mul_coordinate Left leftProb hleft c
              (fun x ↦ ∑ y, rightProb c y *
                ((value c x y - mean c) * (value c x y - mean c)))
          _ = ∑ x, leftProb c x * ∑ y, rightProb c y *
              (value c x y - mean c) ^ 2 := by
            simp [pow_two]
      · rw [if_neg hcd]
        exact hcross c d hcd
    _ = _ := by simp

/-- A bounded nonnegative coordinate has variance at most upper times mean;
summation and independence then give the block estimate. -/
theorem sum_twoWordMass_mul_centered_sum_sq_le
    (leftProb : ∀ c, Left c → ℝ)
    (rightProb : ∀ c, Right c → ℝ)
    (hleft0 : ∀ c x, 0 ≤ leftProb c x)
    (hright0 : ∀ c y, 0 ≤ rightProb c y)
    (hleft : ∀ c, ∑ z, leftProb c z = 1)
    (hright : ∀ c, ∑ z, rightProb c z = 1)
    (value : ∀ c, Left c → Right c → ℝ)
    (mean upper : Color → ℝ)
    (hvalue0 : ∀ c x y, 0 ≤ value c x y)
    (hvalueUpper : ∀ c x y, value c x y ≤ upper c)
    (hmean : ∀ c, ∑ x, leftProb c x *
      ∑ y, rightProb c y * value c x y = mean c) :
    (∑ left : ∀ c, Left c,
      wordMass Left leftProb left *
        ∑ right : ∀ c, Right c,
          wordMass Right rightProb right *
            (∑ c, (value c (left c) (right c) - mean c)) ^ 2) ≤
      ∑ c, upper c * mean c := by
  rw [sum_twoWordMass_mul_centered_sum_sq Left Right leftProb rightProb
    hleft hright value mean hmean]
  apply Finset.sum_le_sum
  intro c _hc
  let pairProb : Left c × Right c → ℝ :=
    fun z ↦ leftProb c z.1 * rightProb c z.2
  let pairValue : Left c × Right c → ℝ :=
    fun z ↦ value c z.1 z.2
  have hpair0 : ∀ z, 0 ≤ pairProb z := by
    intro z
    exact mul_nonneg (hleft0 c z.1) (hright0 c z.2)
  have hpairSum : ∑ z, pairProb z = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [pairProb]
    calc
      (∑ x, ∑ y, leftProb c x * rightProb c y) =
          ∑ x, leftProb c x * ∑ y, rightProb c y := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [Finset.mul_sum]
      _ = 1 := by simp [hleft c, hright c]
  have hpairMean : ∑ z, pairProb z * pairValue z = mean c := by
    rw [Fintype.sum_prod_type]
    simp only [pairProb, pairValue]
    calc
      (∑ x, ∑ y,
        (leftProb c x * rightProb c y) * value c x y) =
          ∑ x, leftProb c x * ∑ y, rightProb c y * value c x y := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _hy
        ring
      _ = mean c := hmean c
  have h :=
    WeightedEdgeColoring.FiniteDependentWordPadding.finite_sum_mul_sub_mean_sq_le_mul
      pairProb pairValue (mean c) (upper c) hpair0 hpairSum
      (fun z ↦ hvalue0 c z.1 z.2)
      (fun z ↦ hvalueUpper c z.1 z.2) hpairMean
  rw [Fintype.sum_prod_type] at h
  calc
    (∑ x, leftProb c x * ∑ y, rightProb c y *
        (value c x y - mean c) ^ 2) =
      ∑ x, ∑ y, (leftProb c x * rightProb c y) *
        (value c x y - mean c) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _hy
        ring
    _ ≤ upper c * mean c := by
      simpa [pairProb, pairValue] using h

end

end WeightedEdgeColoring.FiniteCoordinateDependentWordMoments
