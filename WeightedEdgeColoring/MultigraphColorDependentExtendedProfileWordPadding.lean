import WeightedEdgeColoring.MultigraphExtendedProfileWordPadding
import WeightedEdgeColoring.FiniteDependentWordMarginals

/-!
# Common padding for color-dependent extended-profile words

Here the local realization depends on both a vertex and a color.  Thus the
atom in coordinate `c` of the word at `v` is the extended state built from
`R v c`; its type may vary with `c`.  Every `(v,c)` atom still injects into
the same finite code range.  We encode the dependent word coordinatewise
and pad its product law by zero in one common finite state type.

The last two identities say that padding preserves integration exactly and
that every decoded coordinate has precisely its original marginal law.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})
variable {Color : Type w} [Fintype Color] [DecidableEq Color]
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable {proposal : G.E → Color → ℝ}
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- The extended state at the vertex--color source `(v,c)`. -/
abbrev ColorDependentExtendedProfileState (v : G.V) (c : Color) :=
  Sum {P // P ∈ G.roundedProfileMenu (R v c).law hβ hr} (Fin 3)

theorem colorDependentExtendedProfileState_card_le (v : G.V) (c : Color) :
    Fintype.card (G.ColorDependentExtendedProfileState R v c) ≤
      extendedProfileStateBound β q r := by
  have hmenu : Fintype.card {P // P ∈
      G.roundedProfileMenu (R v c).law hβ hr} ≤
      Fintype.card (G.RoundedProfileIndex (R v c).law hβ hr) := by
    simp [RoundedProfileIndex]
  have hprofile : Fintype.card {P // P ∈
      G.roundedProfileMenu (R v c).law hβ hr} ≤
      profileStateBound β q r :=
    hmenu.trans
      (G.roundedProfileIndex_card_le_parameters (R v c).law hβ hr)
  simpa [ColorDependentExtendedProfileState, extendedProfileStateBound] using
    Nat.add_le_add_right hprofile 3

/-- A single color-dependent atom encoded in the common state range. -/
def colorDependentExtendedProfileStateCode (v : G.V) (c : Color) :
    G.ColorDependentExtendedProfileState R v c →
      Fin (extendedProfileStateBound β q r) :=
  fun z ↦ Fin.castLE (G.colorDependentExtendedProfileState_card_le R v c)
    (Fintype.equivFin (G.ColorDependentExtendedProfileState R v c) z)

theorem colorDependentExtendedProfileStateCode_injective
    (v : G.V) (c : Color) :
    Function.Injective
      (G.colorDependentExtendedProfileStateCode R v c) := by
  intro left right h
  unfold colorDependentExtendedProfileStateCode at h
  apply (Fintype.equivFin
    (G.ColorDependentExtendedProfileState R v c)).injective
  apply Fin.ext
  simpa using congrArg Fin.val h

/-- The common atom encoding, indexed by the full source `(vertex,color)`. -/
def colorDependentExtendedProfileStateEncoding :
    FiniteDependentWordPadding.Encoding
      (fun src : G.V × Color ↦
        G.ColorDependentExtendedProfileState R src.1 src.2)
      (extendedProfileStateBound β q r) where
  code := fun src ↦
    G.colorDependentExtendedProfileStateCode R src.1 src.2
  code_injective := fun src ↦
    G.colorDependentExtendedProfileStateCode_injective R src.1 src.2

/-- A genuine word at `v`; its atom type is allowed to vary with the color
coordinate. -/
abbrev ColorDependentExtendedProfileWord (v : G.V) :=
  ∀ c : Color, G.ColorDependentExtendedProfileState R v c

/-- The common packed type used for a color-dependent word at every vertex. -/
abbrev ColorDependentExtendedProfilePackedWordState
    (_G : WeightedMultigraph.{u}) :=
  FiniteDependentWordPadding.PackedWordState
    (Color := Color) (extendedProfileStateBound β q r)

/-- Coordinatewise encoding of a genuine color-dependent word. -/
def encodeColorDependentExtendedProfileWord (v : G.V)
    (word : G.ColorDependentExtendedProfileWord R v) :
    G.ColorDependentExtendedProfilePackedWordState
      (Color := Color) (β := β) (q := q) (r := r) :=
  Fintype.equivFin
      (FiniteDependentWordPadding.WordState
        (Color := Color) (extendedProfileStateBound β q r))
    (fun c ↦
      (G.colorDependentExtendedProfileStateEncoding R).code (v, c) (word c))

theorem encodeColorDependentExtendedProfileWord_injective (v : G.V) :
    Function.Injective
      (G.encodeColorDependentExtendedProfileWord R v) := by
  intro left right h
  have hword :=
    (Fintype.equivFin
      (FiniteDependentWordPadding.WordState
        (Color := Color) (extendedProfileStateBound β q r))).injective h
  funext c
  exact (G.colorDependentExtendedProfileStateEncoding R).code_injective
    (v, c) (congrFun hword c)

/-- The inactive state used only to totalize decoding of padding codes. -/
def inactiveColorDependentExtendedProfileState
    (src : G.V × Color) :
    G.ColorDependentExtendedProfileState R src.1 src.2 :=
  Sum.inr ⟨2, by decide⟩

/-- Decode a common packed state at a specified vertex. -/
def decodeColorDependentExtendedProfileWord (v : G.V)
    (a : G.ColorDependentExtendedProfilePackedWordState
      (Color := Color) (β := β) (q := q) (r := r)) :
    G.ColorDependentExtendedProfileWord R v :=
  fun c ↦ FiniteDependentWordPadding.decodeAtom
    (fun src : G.V × Color ↦
      G.ColorDependentExtendedProfileState R src.1 src.2)
    (G.colorDependentExtendedProfileStateEncoding R)
    (G.inactiveColorDependentExtendedProfileState R) (v, c)
    ((Fintype.equivFin
      (FiniteDependentWordPadding.WordState
        (Color := Color) (extendedProfileStateBound β q r))).symm a c)

@[simp] theorem decode_encodeColorDependentExtendedProfileWord
    (v : G.V) (word : G.ColorDependentExtendedProfileWord R v) :
    G.decodeColorDependentExtendedProfileWord R v
      (G.encodeColorDependentExtendedProfileWord R v word) = word := by
  funext c
  simp [decodeColorDependentExtendedProfileWord,
    encodeColorDependentExtendedProfileWord,
    FiniteDependentWordPadding.decodeAtom_code]

/-- The unsmoothed extended-state law at a vertex--color source. -/
def colorDependentExtendedProfileProbability (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c) : ℝ :=
  match z with
  | Sum.inl P => s * G.roundedProfileMass (R v c).law hβ hr P.1
  | Sum.inr k =>
      if k.1 = 0 then s * q
      else if k.1 = 1 then s * r
      else 1 - s * (1 + q + r)

theorem colorDependentExtendedProfileProbability_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c) :
    0 ≤ G.colorDependentExtendedProfileProbability R v c z := by
  cases z with
  | inl P =>
      exact mul_nonneg hs
        (G.roundedProfileMass_nonneg (R v c).law hβ hr P.1)
  | inr k =>
      by_cases hk0 : k.1 = 0
      · simp [colorDependentExtendedProfileProbability, hk0,
          mul_nonneg hs hq]
      · by_cases hk1 : k.1 = 1
        · simp [colorDependentExtendedProfileProbability, hk0, hk1,
            mul_nonneg hs hr0]
        · simpa [colorDependentExtendedProfileProbability, hk0, hk1]
            using hleft

theorem sum_colorDependentExtendedProfileProbability
    (v : G.V) (c : Color) :
    ∑ z : G.ColorDependentExtendedProfileState R v c,
      G.colorDependentExtendedProfileProbability R v c z = 1 := by
  classical
  have hmenu :
      (∑ P : {P // P ∈ G.roundedProfileMenu (R v c).law hβ hr},
        G.roundedProfileMass (R v c).law hβ hr P.1) = 1 := by
    calc
      _ = ∑ P ∈ G.roundedProfileMenu (R v c).law hβ hr,
          G.roundedProfileMass (R v c).law hβ hr P := by
        symm
        exact Finset.sum_subtype _ (fun _ ↦ Iff.rfl) _
      _ = 1 := G.sum_roundedProfileMass (R v c).law hβ hr
  rw [Fintype.sum_sum_type]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  simp only [colorDependentExtendedProfileProbability, Fin.val_zero, if_pos,
    Fin.val_succ, Nat.succ_ne_zero, if_false, Nat.reduceAdd, zero_add]
  rw [← Finset.mul_sum, hmenu]
  norm_num
  ring

/-- Uniform smoothing of the color-dependent extended-state law. -/
def smoothedColorDependentExtendedProfileProbability
    (omega : ℝ) (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c) : ℝ :=
  (1 - omega) * G.colorDependentExtendedProfileProbability R v c z +
    omega / Fintype.card (G.ColorDependentExtendedProfileState R v c)

theorem sum_smoothedColorDependentExtendedProfileProbability
    (omega : ℝ) (v : G.V) (c : Color) :
    ∑ z : G.ColorDependentExtendedProfileState R v c,
      G.smoothedColorDependentExtendedProfileProbability R omega v c z = 1 := by
  classical
  unfold smoothedColorDependentExtendedProfileProbability
  have hcard : Fintype.card
      (G.ColorDependentExtendedProfileState R v c) ≠ 0 := by
    simp [ColorDependentExtendedProfileState]
  have huniform :
      (∑ _z : G.ColorDependentExtendedProfileState R v c,
        omega / Fintype.card
          (G.ColorDependentExtendedProfileState R v c)) = omega := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcardR : (Fintype.card
        (G.ColorDependentExtendedProfileState R v c) : ℝ) ≠ 0 := by
      exact_mod_cast hcard
    field_simp [hcardR]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    G.sum_colorDependentExtendedProfileProbability R v c, huniform]
  ring

theorem smoothedColorDependentExtendedProfileProbability_pos
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c) :
    0 < G.smoothedColorDependentExtendedProfileProbability R omega v c z := by
  unfold smoothedColorDependentExtendedProfileProbability
  have hbase := G.colorDependentExtendedProfileProbability_nonneg R
    hs hq hr0 hleft v c z
  have hfirst :
      0 ≤ (1 - omega) * G.colorDependentExtendedProfileProbability R v c z :=
    mul_nonneg (sub_nonneg.mpr homega1) hbase
  have hcard : 0 < (Fintype.card
      (G.ColorDependentExtendedProfileState R v c) : ℝ) := by
    positivity
  have hsecond : 0 < omega /
      Fintype.card (G.ColorDependentExtendedProfileState R v c) :=
    div_pos homega0 hcard
  linarith

/-- Product mass of one genuine color-dependent word. -/
def colorDependentExtendedProfileWordMass (omega : ℝ) (v : G.V)
    (word : G.ColorDependentExtendedProfileWord R v) : ℝ :=
  ∏ c, G.smoothedColorDependentExtendedProfileProbability
    R omega v c (word c)

/-- Push the dependent product law into the common packed state, with zero
mass on padding-only codes. -/
def paddedColorDependentExtendedProfileWordProbability
    (omega : ℝ) (v : G.V)
    (a : G.ColorDependentExtendedProfilePackedWordState
      (Color := Color) (β := β) (q := q) (r := r)) : ℝ :=
  ∑ word : G.ColorDependentExtendedProfileWord R v,
    if G.encodeColorDependentExtendedProfileWord R v word = a then
      G.colorDependentExtendedProfileWordMass R omega v word else 0

theorem paddedColorDependentExtendedProfileWordProbability_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V)
    (a : G.ColorDependentExtendedProfilePackedWordState
      (Color := Color) (β := β) (q := q) (r := r)) :
    0 ≤ G.paddedColorDependentExtendedProfileWordProbability R omega v a := by
  apply Finset.sum_nonneg
  intro word _hword
  split
  · exact Finset.prod_nonneg fun c _hc ↦
      (G.smoothedColorDependentExtendedProfileProbability_pos R
        hs hq hr0 hleft homega0 homega1 v c (word c)).le
  · exact le_rfl

/-- The mass at the code of a genuine word is exactly its product mass. -/
theorem paddedColorDependentExtendedProfileWordProbability_at_encode
    (omega : ℝ) (v : G.V)
    (word : G.ColorDependentExtendedProfileWord R v) :
    G.paddedColorDependentExtendedProfileWordProbability R omega v
        (G.encodeColorDependentExtendedProfileWord R v word) =
      G.colorDependentExtendedProfileWordMass R omega v word := by
  classical
  unfold paddedColorDependentExtendedProfileWordProbability
  have hinj := G.encodeColorDependentExtendedProfileWord_injective R v
  simp only [hinj.eq_iff]
  simp

/-- Padding preserves normalization of the color-dependent product law. -/
theorem sum_paddedColorDependentExtendedProfileWordProbability
    (omega : ℝ) (v : G.V) :
    ∑ a, G.paddedColorDependentExtendedProfileWordProbability R omega v a =
      1 := by
  classical
  unfold paddedColorDependentExtendedProfileWordProbability
    colorDependentExtendedProfileWordMass
  rw [Finset.sum_comm]
  calc
    (∑ word : G.ColorDependentExtendedProfileWord R v,
        ∑ a, if G.encodeColorDependentExtendedProfileWord R v word = a then
          ∏ c, G.smoothedColorDependentExtendedProfileProbability
            R omega v c (word c) else 0) =
      ∑ word : G.ColorDependentExtendedProfileWord R v,
        ∏ c, G.smoothedColorDependentExtendedProfileProbability
          R omega v c (word c) := by
        apply Finset.sum_congr rfl
        intro word _hword
        simp
    _ = ∏ c : Color,
        ∑ z : G.ColorDependentExtendedProfileState R v c,
          G.smoothedColorDependentExtendedProfileProbability
            R omega v c z := by
      exact (Fintype.prod_sum
        (fun c (z : G.ColorDependentExtendedProfileState R v c) ↦
          G.smoothedColorDependentExtendedProfileProbability
            R omega v c z)).symm
    _ = 1 := by
      simp [G.sum_smoothedColorDependentExtendedProfileProbability]

/-- Exact integration formula: padding and total decoding introduce no
error for any statistic of the full dependent word. -/
theorem sum_paddedColorDependentProbability_mul_decode
    (omega : ℝ) (v : G.V)
    (f : G.ColorDependentExtendedProfileWord R v → ℝ) :
    (∑ a,
      G.paddedColorDependentExtendedProfileWordProbability R omega v a *
        f (G.decodeColorDependentExtendedProfileWord R v a)) =
      ∑ word : G.ColorDependentExtendedProfileWord R v,
        G.colorDependentExtendedProfileWordMass R omega v word * f word := by
  classical
  unfold paddedColorDependentExtendedProfileWordProbability
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro word _hword
  simp [G.decode_encodeColorDependentExtendedProfileWord R v word]

/-- Exact one-coordinate marginal under the padded product law. -/
theorem sum_paddedColorDependentProbability_mul_decode_coordinate
    (omega : ℝ) (v : G.V) (c : Color)
    (f : G.ColorDependentExtendedProfileState R v c → ℝ) :
    (∑ a,
      G.paddedColorDependentExtendedProfileWordProbability R omega v a *
        f (G.decodeColorDependentExtendedProfileWord R v a c)) =
      ∑ z : G.ColorDependentExtendedProfileState R v c,
        G.smoothedColorDependentExtendedProfileProbability
          R omega v c z * f z := by
  rw [G.sum_paddedColorDependentProbability_mul_decode R omega v
    (fun word ↦ f (word c))]
  classical
  let atomProb : ∀ d : Color,
      G.ColorDependentExtendedProfileState R v d → ℝ :=
    fun d z ↦ G.smoothedColorDependentExtendedProfileProbability
      R omega v d z
  let coordFactor : ∀ d : Color,
      G.ColorDependentExtendedProfileState R v d → ℝ :=
    fun d z ↦
      if h : d = c then f (by subst d; exact z) else 1
  let g : Color → ℝ := fun d ↦
    ∑ z, atomProb d z * coordFactor d z
  calc
    (∑ word : G.ColorDependentExtendedProfileWord R v,
        G.colorDependentExtendedProfileWordMass R omega v word *
          f (word c)) =
      ∑ word : G.ColorDependentExtendedProfileWord R v,
        ∏ d, atomProb d (word d) *
          coordFactor d (word d) := by
        apply Finset.sum_congr rfl
        intro word _hword
        unfold colorDependentExtendedProfileWordMass atomProb
        rw [Finset.prod_mul_distrib]
        simp [coordFactor]
    _ = ∏ d, ∑ z, atomProb d z * coordFactor d z := by
      exact (Fintype.prod_sum
        (fun d z ↦ atomProb d z * coordFactor d z)).symm
    _ = ∏ d, g d := by rfl
    _ = ∑ z, atomProb c z * f z := by
      rw [← Finset.prod_erase_mul (Finset.univ : Finset Color) g
        (Finset.mem_univ c)]
      have hrest :
          ∏ d ∈ (Finset.univ : Finset Color).erase c, g d = 1 := by
        apply Finset.prod_eq_one
        intro d hd
        have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
        simp [g, atomProb, coordFactor, hdc,
          G.sum_smoothedColorDependentExtendedProfileProbability]
      rw [hrest, one_mul]
      simp [g, coordFactor]
    _ = ∑ z : G.ColorDependentExtendedProfileState R v c,
        G.smoothedColorDependentExtendedProfileProbability
          R omega v c z * f z := by rfl

/-- Positive padded mass always names a genuine dependent word of positive
product mass. -/
theorem exists_colorDependentExtendedProfileWord_of_padded_pos
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V)
    (a : G.ColorDependentExtendedProfilePackedWordState
      (Color := Color) (β := β) (q := q) (r := r))
    (ha : 0 <
      G.paddedColorDependentExtendedProfileWordProbability R omega v a) :
    ∃ word : G.ColorDependentExtendedProfileWord R v,
      G.encodeColorDependentExtendedProfileWord R v word = a ∧
        0 < G.colorDependentExtendedProfileWordMass R omega v word := by
  classical
  unfold paddedColorDependentExtendedProfileWordProbability at ha
  have hterm0 : ∀ word : G.ColorDependentExtendedProfileWord R v,
      0 ≤ (if G.encodeColorDependentExtendedProfileWord R v word = a then
        G.colorDependentExtendedProfileWordMass R omega v word else 0) := by
    intro word
    split
    · exact Finset.prod_nonneg fun c _hc ↦
        (G.smoothedColorDependentExtendedProfileProbability_pos R
          hs hq hr0 hleft homega0 homega1 v c (word c)).le
    · exact le_rfl
  rcases (Finset.sum_pos_iff_of_nonneg
      (fun word _hword ↦ hterm0 word)).mp ha with
    ⟨word, _hword, hword⟩
  by_cases hcode : G.encodeColorDependentExtendedProfileWord R v word = a
  · exact ⟨word, hcode, by simpa [hcode] using hword⟩
  · simp [hcode] at hword

end WeightedMultigraph

end

end WeightedEdgeColoring
