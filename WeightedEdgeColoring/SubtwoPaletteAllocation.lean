import WeightedEdgeColoring.SubtwoPaletteSeparation

/-!
# Finite labelled pattern palettes

A label has a nonnegative mass budget.  It can split that mass fractionally
among finitely many patterns.  Each pattern contributes a nonnegative amount
to every demand coordinate.  The attainable demands are the nonnegative
vectors covered coordinatewise by some feasible allocation.

This is a finite convex model for the local palette step.  No assertion is
made here that such a local allocation assembles into a global edge coloring.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo

variable {I L P : Type*}
  [Fintype I] [DecidableEq I]
  [Fintype L] [DecidableEq L]
  [Fintype P] [DecidableEq P]

/-- Contribution of a labelled pattern allocation to one demand coordinate. -/
def paletteCoverage (pattern : L → P → I → ℝ) (a : L × P → ℝ) (i : I) : ℝ :=
  ∑ l : L, ∑ p : P, a (l, p) * pattern l p i

/-- Nonnegative fractional allocations respecting each label's mass budget. -/
def PaletteFeasible (budget : L → ℝ) (a : L × P → ℝ) : Prop :=
  (∀ lp, 0 ≤ a lp) ∧
    ∀ l, (∑ p : P, a (l, p)) ≤ budget l

/-- Nonnegative demands that one feasible allocation covers coordinatewise. -/
def PaletteAttainable (budget : L → ℝ) (pattern : L → P → I → ℝ) :
    Set (I → ℝ) :=
  {d | (∀ i, 0 ≤ d i) ∧
    ∃ a : L × P → ℝ, PaletteFeasible budget a ∧
      ∀ i, d i ≤ paletteCoverage pattern a i}

/-- Coordinatewise deletion preserves attainable demand. -/
theorem paletteAttainable_downward (budget : L → ℝ) (pattern : L → P → I → ℝ) :
    NonnegativeDownwardClosed (PaletteAttainable budget pattern) := by
  constructor
  · intro d hd i
    exact hd.1 i
  · intro d hd e he0 hed
    obtain ⟨a, ha, hcover⟩ := hd.2
    exact ⟨he0, a, ha, fun i => (hed i).trans (hcover i)⟩

/-- Every attainable demand passes every nonnegative price test, witnessed
by the same concrete allocation's coverage vector. -/
theorem paletteAttainable_price_bound
    (budget : L → ℝ) (pattern : L → P → I → ℝ)
    {d : I → ℝ} (hd : d ∈ PaletteAttainable budget pattern)
    (price : I → ℝ) (hprice : ∀ i, 0 ≤ price i) :
    ∃ a : L × P → ℝ, PaletteFeasible budget a ∧
      (∑ i, price i * d i) ≤
        ∑ i, price i * paletteCoverage pattern a i := by
  obtain ⟨a, ha, hcover⟩ := hd.2
  refine ⟨a, ha, ?_⟩
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (hcover i) (hprice i)

/-- Coverage depends linearly on the allocation. -/
theorem paletteCoverage_affine
    (pattern : L → P → I → ℝ) (a b : L × P → ℝ)
    (s t : ℝ) (i : I) :
    paletteCoverage pattern (fun lp => s * a lp + t * b lp) i =
      s * paletteCoverage pattern a i +
        t * paletteCoverage pattern b i := by
  simp [paletteCoverage, add_mul, mul_assoc, Finset.sum_add_distrib,
    Finset.mul_sum]

/-- Feasible allocations are closed under convex mixing. -/
theorem paletteFeasible_convexMix
    (budget : L → ℝ) (a b : L × P → ℝ)
    (ha : PaletteFeasible budget a) (hb : PaletteFeasible budget b)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    PaletteFeasible budget (fun lp => s * a lp + t * b lp) := by
  constructor
  · intro lp
    exact add_nonneg (mul_nonneg hs (ha.1 lp)) (mul_nonneg ht (hb.1 lp))
  · intro l
    have hsum :
        (∑ p : P, (s * a (l, p) + t * b (l, p))) =
          s * (∑ p : P, a (l, p)) + t * (∑ p : P, b (l, p)) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsum]
    calc
      s * (∑ p : P, a (l, p)) + t * (∑ p : P, b (l, p)) ≤
          s * budget l + t * budget l :=
        add_le_add (mul_le_mul_of_nonneg_left (ha.2 l) hs)
          (mul_le_mul_of_nonneg_left (hb.2 l) ht)
      _ = budget l := by rw [← add_mul, hst, one_mul]

/-- The attainable demand set is convex. -/
theorem paletteAttainable_convex
    (budget : L → ℝ) (pattern : L → P → I → ℝ) :
    Convex ℝ (PaletteAttainable budget pattern) := by
  intro d hd e he s t hs ht hst
  obtain ⟨a, ha, hda⟩ := hd.2
  obtain ⟨b, hb, heb⟩ := he.2
  let mix : L × P → ℝ := fun lp => s * a lp + t * b lp
  change (fun i => s * d i + t * e i) ∈ PaletteAttainable budget pattern
  refine ⟨?_, mix, paletteFeasible_convexMix budget a b ha hb hs ht hst, ?_⟩
  · intro i
    exact add_nonneg (mul_nonneg hs (hd.1 i)) (mul_nonneg ht (he.1 i))
  · intro i
    rw [show paletteCoverage pattern mix i =
      s * paletteCoverage pattern a i +
        t * paletteCoverage pattern b i from
      paletteCoverage_affine pattern a b s t i]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hda i) hs)
      (mul_le_mul_of_nonneg_left (heb i) ht)

/-- Exchange the price sum with the label and pattern sums. -/
theorem palettePrice_eq_patternScores
    (pattern : L → P → I → ℝ) (a : L × P → ℝ) (price : I → ℝ) :
    (∑ i : I, price i * paletteCoverage pattern a i) =
      ∑ l : L, ∑ p : P,
        a (l, p) * (∑ i : I, price i * pattern l p i) := by
  simp only [paletteCoverage, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A label-specific per-pattern price cap gives an upper bound on the
price of any attainable demand. -/
theorem paletteAttainable_price_le_budget_mul
    (budget : L → ℝ) (pattern : L → P → I → ℝ)
    {d : I → ℝ} (hd : d ∈ PaletteAttainable budget pattern)
    (price : I → ℝ) (hprice : ∀ i, 0 ≤ price i)
    (M : L → ℝ) (hM : ∀ l, 0 ≤ M l)
    (hscore : ∀ (l : L) (p : P),
      (∑ i : I, price i * pattern l p i) ≤ M l) :
    (∑ i : I, price i * d i) ≤ ∑ l : L, budget l * M l := by
  obtain ⟨a, ha, hcover⟩ := hd.2
  calc
    (∑ i : I, price i * d i) ≤
        ∑ i : I, price i * paletteCoverage pattern a i :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hcover i) (hprice i)
    _ = ∑ l : L, ∑ p : P,
        a (l, p) * (∑ i : I, price i * pattern l p i) :=
      palettePrice_eq_patternScores pattern a price
    _ ≤ ∑ l : L, (∑ p : P, a (l, p)) * M l := by
      apply Finset.sum_le_sum
      intro l _
      calc
        (∑ p : P, a (l, p) * (∑ i : I, price i * pattern l p i)) ≤
            ∑ p : P, a (l, p) * M l :=
          Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_left (hscore l p) (ha.1 (l, p))
        _ = (∑ p : P, a (l, p)) * M l := by rw [Finset.sum_mul]
    _ ≤ ∑ l : L, budget l * M l :=
      Finset.sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_right (ha.2 l) (hM l)

/-- The finite allocation constraints form a closed polytope. -/
theorem paletteFeasible_isClosed (budget : L → ℝ) :
    IsClosed {a : L × P → ℝ | PaletteFeasible budget a} := by
  have hnonneg : IsClosed {a : L × P → ℝ | ∀ lp, 0 ≤ a lp} := by
    have heq : {a : L × P → ℝ | ∀ lp, 0 ≤ a lp} =
        ⋂ lp : L × P, {a | (0 : ℝ) ≤ a lp} := by
      ext a
      simp
    rw [heq]
    apply isClosed_iInter
    intro lp
    exact isClosed_le continuous_const (continuous_apply lp)
  have hrow : IsClosed {a : L × P → ℝ |
      ∀ l : L, (∑ p : P, a (l, p)) ≤ budget l} := by
    have heq : {a : L × P → ℝ |
        ∀ l : L, (∑ p : P, a (l, p)) ≤ budget l} =
        ⋂ l : L,
          {a | (∑ p : P, a (l, p)) ≤ budget l} := by
      ext a
      simp
    rw [heq]
    apply isClosed_iInter
    intro l
    apply isClosed_le _ continuous_const
    apply continuous_finset_sum
    intro p _
    exact continuous_apply (l, p)
  have heq : {a : L × P → ℝ | PaletteFeasible budget a} =
      {a | ∀ lp, 0 ≤ a lp} ∩
        {a | ∀ l : L, (∑ p : P, a (l, p)) ≤ budget l} := by
    ext a
    rfl
  rw [heq]
  exact hnonneg.inter hrow

/-- Feasible allocations occupy a compact coordinate box.  This is the
finite-dimensional attainment input for later palette separation. -/
theorem paletteFeasible_isCompact
    (budget : L → ℝ) :
    IsCompact {a : L × P → ℝ | PaletteFeasible budget a} := by
  apply IsCompact.of_isClosed_subset isCompact_Icc
    (paletteFeasible_isClosed budget)
  intro a ha
  constructor
  · exact ha.1
  · intro lp
    have hsingle : a lp ≤ ∑ p : P, a (lp.1, p) := by
      exact Finset.single_le_sum
        (fun p _ => ha.1 (lp.1, p)) (Finset.mem_univ lp.2)
    exact hsingle.trans (ha.2 lp.1)

/-- A coordinatewise bound depending only on the label budgets and the
pattern contributions. -/
def paletteCoordinateBound (budget : L → ℝ)
    (pattern : L → P → I → ℝ) (i : I) : ℝ :=
  ∑ l : L, ∑ p : P, budget l * pattern l p i

theorem paletteCoverage_le_coordinateBound
    (budget : L → ℝ) (pattern : L → P → I → ℝ)
    (hpattern : ∀ l p i, 0 ≤ pattern l p i)
    (a : L × P → ℝ) (ha : PaletteFeasible budget a) (i : I) :
    paletteCoverage pattern a i ≤
      paletteCoordinateBound budget pattern i := by
  unfold paletteCoverage paletteCoordinateBound
  apply Finset.sum_le_sum
  intro l _
  apply Finset.sum_le_sum
  intro p _
  have hap : a (l, p) ≤ budget l := by
    have hsingle : a (l, p) ≤ ∑ q : P, a (l, q) :=
      Finset.single_le_sum
        (fun q _ => ha.1 (l, q)) (Finset.mem_univ p)
    exact hsingle.trans (ha.2 l)
  exact mul_le_mul_of_nonneg_right hap (hpattern l p i)

/-- Coverage is continuous in the finite coefficient array. -/
theorem continuous_paletteCoverage
    (pattern : L → P → I → ℝ) (i : I) :
    Continuous (fun a : L × P → ℝ => paletteCoverage pattern a i) := by
  unfold paletteCoverage
  apply continuous_finset_sum
  intro l _
  apply continuous_finset_sum
  intro p _
  exact (continuous_apply (l, p)).mul continuous_const

/-- The concrete allocation and the demand vector it covers. -/
def paletteWitnessPairs (budget : L → ℝ) (pattern : L → P → I → ℝ) :
    Set ((L × P → ℝ) × (I → ℝ)) :=
  {z | PaletteFeasible budget z.1 ∧
    ∀ i, 0 ≤ z.2 i ∧ z.2 i ≤ paletteCoverage pattern z.1 i}

theorem paletteWitnessPairs_isClosed
    (budget : L → ℝ) (pattern : L → P → I → ℝ) :
    IsClosed (paletteWitnessPairs budget pattern) := by
  have hfeas : IsClosed {z : (L × P → ℝ) × (I → ℝ) |
      PaletteFeasible budget z.1} :=
    (paletteFeasible_isClosed budget).preimage continuous_fst
  have hnonneg : IsClosed {z : (L × P → ℝ) × (I → ℝ) |
      ∀ i : I, 0 ≤ z.2 i} := by
    have heq : {z : (L × P → ℝ) × (I → ℝ) |
        ∀ i : I, 0 ≤ z.2 i} =
        ⋂ i : I, {z | (0 : ℝ) ≤ z.2 i} := by
      ext z
      simp
    rw [heq]
    apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const
      ((continuous_apply i).comp continuous_snd)
  have hcover : IsClosed {z : (L × P → ℝ) × (I → ℝ) |
      ∀ i : I, z.2 i ≤ paletteCoverage pattern z.1 i} := by
    have heq : {z : (L × P → ℝ) × (I → ℝ) |
        ∀ i : I, z.2 i ≤ paletteCoverage pattern z.1 i} =
        ⋂ i : I,
          {z | z.2 i ≤ paletteCoverage pattern z.1 i} := by
      ext z
      simp
    rw [heq]
    apply isClosed_iInter
    intro i
    exact isClosed_le ((continuous_apply i).comp continuous_snd)
      ((continuous_paletteCoverage pattern i).comp continuous_fst)
  have heq : paletteWitnessPairs budget pattern =
      {z | PaletteFeasible budget z.1} ∩
      {z | ∀ i : I, 0 ≤ z.2 i} ∩
        {z | ∀ i : I, z.2 i ≤ paletteCoverage pattern z.1 i} := by
    ext z
    constructor
    · intro hz
      exact ⟨⟨hz.1, fun i => (hz.2 i).1⟩, fun i => (hz.2 i).2⟩
    · intro hz
      exact ⟨hz.1.1, fun i => ⟨hz.1.2 i, hz.2 i⟩⟩
  rw [heq]
  exact (hfeas.inter hnonneg).inter hcover

/-- The feasible allocation-demand pairs lie in a compact product box. -/
theorem paletteWitnessPairs_isCompact
    (budget : L → ℝ) (pattern : L → P → I → ℝ)
    (hpattern : ∀ l p i, 0 ≤ pattern l p i) :
    IsCompact (paletteWitnessPairs budget pattern) := by
  let lo : (L × P → ℝ) × (I → ℝ) :=
    (fun _ => 0, fun _ => 0)
  let hi : (L × P → ℝ) × (I → ℝ) :=
    (fun lp => budget lp.1, paletteCoordinateBound budget pattern)
  have hbox : IsCompact (Set.Icc lo hi) := isCompact_Icc
  apply IsCompact.of_isClosed_subset hbox
    (paletteWitnessPairs_isClosed budget pattern)
  intro z hz
  change lo ≤ z ∧ z ≤ hi
  constructor
  · constructor
    · exact hz.1.1
    · intro i
      exact (hz.2 i).1
  · constructor
    · intro lp
      have hsingle : z.1 lp ≤ ∑ p : P, z.1 (lp.1, p) :=
        Finset.single_le_sum
          (fun p _ => hz.1.1 (lp.1, p)) (Finset.mem_univ lp.2)
      exact hsingle.trans (hz.1.2 lp.1)
    · intro i
      exact (hz.2 i).2.trans
        (paletteCoverage_le_coordinateBound budget pattern hpattern z.1 hz.1 i)

/-- Finite labelled pattern palettes have compact attainable-demand sets. -/
theorem paletteAttainable_isCompact
    (budget : L → ℝ) (pattern : L → P → I → ℝ)
    (hpattern : ∀ l p i, 0 ≤ pattern l p i) :
    IsCompact (PaletteAttainable budget pattern) := by
  have heq : PaletteAttainable budget pattern =
      Prod.snd '' paletteWitnessPairs budget pattern := by
    ext d
    constructor
    · intro hd
      obtain ⟨a, ha, hcover⟩ := hd.2
      exact ⟨(a, d), ⟨ha, fun i => ⟨hd.1 i, hcover i⟩⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨fun i => (hz.2 i).1, z.1, hz.1,
        fun i => (hz.2 i).2⟩
  rw [heq]
  exact (paletteWitnessPairs_isCompact budget pattern hpattern).image continuous_snd

theorem paletteAttainable_isClosed
    (budget : L → ℝ) (pattern : L → P → I → ℝ)
    (hpattern : ∀ l p i, 0 ≤ pattern l p i) :
    IsClosed (PaletteAttainable budget pattern) :=
  (paletteAttainable_isCompact budget pattern hpattern).isClosed

/-- For finite nonnegative pattern palettes, all nonnegative price tests are
equivalent to a feasible fractional allocation covering the demand.  The
existential allocation in each test may depend on the price; separation
produces one allocation satisfying all demand coordinates at once. -/
theorem paletteAttainable_iff_priceTests
    (budget : L → ℝ) (pattern : L → P → I → ℝ)
    (hpattern : ∀ l p i, 0 ≤ pattern l p i)
    {d : I → ℝ} (hd : ∀ i, 0 ≤ d i) :
    d ∈ PaletteAttainable budget pattern ↔
      ∀ price : I → ℝ, (∀ i, 0 ≤ price i) →
        ∃ a : L × P → ℝ, PaletteFeasible budget a ∧
          (∑ i : I, price i * d i) ≤
            ∑ i : I, price i * paletteCoverage pattern a i := by
  constructor
  · intro h price hprice
    exact paletteAttainable_price_bound budget pattern h price hprice
  · intro hprice
    apply mem_of_nonnegative_price_tests
      (paletteAttainable_convex budget pattern)
      (paletteAttainable_isClosed budget pattern hpattern)
      (paletteAttainable_downward budget pattern) hd
    intro price hp
    obtain ⟨a, ha, hscore⟩ := hprice price hp
    have hcoverage : ∀ i, 0 ≤ paletteCoverage pattern a i := by
      intro i
      unfold paletteCoverage
      apply Finset.sum_nonneg
      intro l _
      apply Finset.sum_nonneg
      intro p _
      exact mul_nonneg (ha.1 (l, p)) (hpattern l p i)
    exact ⟨paletteCoverage pattern a,
      ⟨hcoverage, a, ha, fun _ => le_rfl⟩, hscore⟩

/-- Put the entire budget of each label on one chosen pattern. -/
def oneHotPaletteAllocation (budget : L → ℝ) (chosen : L → P) :
    L × P → ℝ :=
  fun lp => if lp.2 = chosen lp.1 then budget lp.1 else 0

theorem oneHotPaletteAllocation_feasible
    (budget : L → ℝ) (hbudget : ∀ l, 0 ≤ budget l)
    (chosen : L → P) :
    PaletteFeasible budget (oneHotPaletteAllocation budget chosen) := by
  classical
  constructor
  · intro lp
    simp only [oneHotPaletteAllocation]
    split_ifs
    · exact hbudget lp.1
    · exact le_rfl
  · intro l
    simp [oneHotPaletteAllocation]

/-- A one-hot allocation realizes exactly the sum of the chosen pattern
scores, weighted by the label budgets. -/
theorem oneHotPaletteAllocation_price_eq
    (budget : L → ℝ) (pattern : L → P → I → ℝ)
    (chosen : L → P) (price : I → ℝ) :
    (∑ i : I,
        price i * paletteCoverage pattern
          (oneHotPaletteAllocation budget chosen) i) =
      ∑ l : L, budget l *
        (∑ i : I, price i * pattern l (chosen l) i) := by
  classical
  rw [palettePrice_eq_patternScores]
  apply Finset.sum_congr rfl
  intro l _
  simp [oneHotPaletteAllocation]

/-- When each label's price cap is attained by one pattern, the scalar
support inequality yields a single allocation covering every coordinate.
The chosen maximizer may depend on the price; the resulting covering
allocation does not. -/
theorem paletteAttainable_of_attained_priceCaps
    (budget : L → ℝ) (hbudget : ∀ l, 0 ≤ budget l)
    (pattern : L → P → I → ℝ)
    (hpattern : ∀ l p i, 0 ≤ pattern l p i)
    {d : I → ℝ} (hd : ∀ i, 0 ≤ d i)
    (hcap : ∀ price : I → ℝ, (∀ i, 0 ≤ price i) →
      ∃ M : L → ℝ,
        (∀ l p, (∑ i : I, price i * pattern l p i) ≤ M l) ∧
        (∀ l, ∃ p : P,
          M l = ∑ i : I, price i * pattern l p i) ∧
        (∑ i : I, price i * d i) ≤
          ∑ l : L, budget l * M l) :
    d ∈ PaletteAttainable budget pattern := by
  apply (paletteAttainable_iff_priceTests budget pattern hpattern hd).2
  intro price hp
  obtain ⟨M, _hupper, hmax, hbound⟩ := hcap price hp
  classical
  let chosen : L → P := fun l => Classical.choose (hmax l)
  have hchosen : ∀ l, M l =
      ∑ i : I, price i * pattern l (chosen l) i := by
    intro l
    exact Classical.choose_spec (hmax l)
  refine ⟨oneHotPaletteAllocation budget chosen,
    oneHotPaletteAllocation_feasible budget hbudget chosen, ?_⟩
  calc
    (∑ i : I, price i * d i) ≤
        ∑ l : L, budget l * M l := hbound
    _ = ∑ l : L, budget l *
          (∑ i : I, price i * pattern l (chosen l) i) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [hchosen l]
    _ = ∑ i : I, price i *
          paletteCoverage pattern
            (oneHotPaletteAllocation budget chosen) i :=
      (oneHotPaletteAllocation_price_eq budget pattern chosen price).symm

/-- A maximizing pattern for one label and one price vector exists because
the pattern family is finite and nonempty. -/
noncomputable def paletteMaximizer [Nonempty P]
    (pattern : L → P → I → ℝ) (price : I → ℝ) (l : L) : P := by
  classical
  have hne : (Finset.univ : Finset P).Nonempty :=
    ⟨Classical.choice (inferInstance : Nonempty P), Finset.mem_univ _⟩
  exact Classical.choose <|
    Finset.exists_max_image (Finset.univ : Finset P)
      (fun p => ∑ i : I, price i * pattern l p i) hne

noncomputable def paletteMaxScore [Nonempty P]
    (pattern : L → P → I → ℝ) (price : I → ℝ) (l : L) : ℝ :=
  ∑ i : I, price i * pattern l (paletteMaximizer pattern price l) i

theorem patternPrice_le_paletteMaxScore [Nonempty P]
    (pattern : L → P → I → ℝ) (price : I → ℝ)
    (l : L) (p : P) :
    (∑ i : I, price i * pattern l p i) ≤
      paletteMaxScore pattern price l := by
  classical
  have hne : (Finset.univ : Finset P).Nonempty :=
    ⟨Classical.choice (inferInstance : Nonempty P), Finset.mem_univ _⟩
  have hs := Classical.choose_spec <|
    Finset.exists_max_image (Finset.univ : Finset P)
      (fun p => ∑ i : I, price i * pattern l p i) hne
  exact hs.2 p (Finset.mem_univ p)

theorem paletteMaxScore_nonneg [Nonempty P]
    (pattern : L → P → I → ℝ)
    (hpattern : ∀ l p i, 0 ≤ pattern l p i)
    (price : I → ℝ) (hprice : ∀ i, 0 ≤ price i)
    (l : L) : 0 ≤ paletteMaxScore pattern price l := by
  unfold paletteMaxScore
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hprice i) (hpattern l (paletteMaximizer pattern price l) i)

theorem oneHotPaletteAllocation_maxScore_price_eq [Nonempty P]
    (budget : L → ℝ) (pattern : L → P → I → ℝ)
    (price : I → ℝ) :
    (∑ i : I, price i * paletteCoverage pattern
      (oneHotPaletteAllocation budget
        (paletteMaximizer pattern price)) i) =
      ∑ l : L, budget l * paletteMaxScore pattern price l := by
  exact oneHotPaletteAllocation_price_eq budget pattern
    (paletteMaximizer pattern price) price

/-- The explicit finite maximum support inequalities are sufficient for a
fractional labelled-palette allocation covering the demand. -/
theorem paletteAttainable_of_maxScoreInequalities [Nonempty P]
    (budget : L → ℝ) (hbudget : ∀ l, 0 ≤ budget l)
    (pattern : L → P → I → ℝ)
    (hpattern : ∀ l p i, 0 ≤ pattern l p i)
    {d : I → ℝ} (hd : ∀ i, 0 ≤ d i)
    (hprice : ∀ price : I → ℝ, (∀ i, 0 ≤ price i) →
      (∑ i : I, price i * d i) ≤
        ∑ l : L, budget l * paletteMaxScore pattern price l) :
    d ∈ PaletteAttainable budget pattern := by
  apply paletteAttainable_of_attained_priceCaps budget hbudget pattern hpattern hd
  intro price hp
  refine ⟨paletteMaxScore pattern price, ?_, ?_, hprice price hp⟩
  · intro l p
    exact patternPrice_le_paletteMaxScore pattern price l p
  · intro l
    exact ⟨paletteMaximizer pattern price l, rfl⟩

section ReservedClasses

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The unrestricted palette is `none`; `some v` is the palette reserved at
vertex `v`. -/
def reservedPaletteBudget (κ : ℝ) (q : V → ℝ) : Option V → ℝ
  | none => κ - ∑ v : V, q v
  | some v => q v

def reservedPalettePattern (full : P → I → ℝ)
    (avoiding : V → P → I → ℝ) : Option V → P → I → ℝ
  | none => full
  | some v => avoiding v

theorem reservedPaletteBudget_nonneg
    (κ : ℝ) (q : V → ℝ) (hq : ∀ v, 0 ≤ q v)
    (hsum : (∑ v : V, q v) ≤ κ) :
    ∀ o : Option V, 0 ≤ reservedPaletteBudget κ q o := by
  intro o
  cases o with
  | none => simp [reservedPaletteBudget, sub_nonneg, hsum]
  | some v => simpa [reservedPaletteBudget] using hq v

/-- Exact support sum of the unrestricted and vertex-reserved classes. -/
theorem reservedPaletteSupport_eq [Nonempty P]
    (κ : ℝ) (q : V → ℝ)
    (pattern : Option V → P → I → ℝ) (price : I → ℝ) :
    (∑ o : Option V,
        reservedPaletteBudget κ q o *
          paletteMaxScore pattern price o) =
      (κ - ∑ v : V, q v) * paletteMaxScore pattern price none +
        ∑ v : V, q v * paletteMaxScore pattern price (some v) := by
  simp [Fintype.sum_option, reservedPaletteBudget]

/-- The reserved-class price test in the `C + Σ q_v (R-r_v)` form. -/
theorem reservedPalettePrice_iff
    (κ C R : ℝ) (q r : V → ℝ) :
    C ≤ (κ - ∑ v : V, q v) * R + ∑ v : V, q v * r v ↔
      C + ∑ v : V, q v * (R - r v) ≤ κ * R := by
  have hsum :
      (∑ v : V, q v * (R - r v)) =
        (∑ v : V, q v) * R - ∑ v : V, q v * r v := by
    simp [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hsum]
  constructor <;> intro h <;> nlinarith

/-- A five-vertex charge inequality, if proved for every nonnegative price,
supplies the finite labelled-palette allocation.  The two price maxima are
the unrestricted patterns and the patterns allowed in each reserved class.
No graph inequality is asserted by this reduction. -/
theorem reservedPaletteAttainable_of_chargeInequalities [Nonempty P]
    (κ : ℝ) (q : V → ℝ) (hq : ∀ v, 0 ≤ q v)
    (hsum : (∑ v : V, q v) ≤ κ)
    (full : P → I → ℝ) (avoiding : V → P → I → ℝ)
    (hfull : ∀ p i, 0 ≤ full p i)
    (havoiding : ∀ v p i, 0 ≤ avoiding v p i)
    {d : I → ℝ} (hd : ∀ i, 0 ≤ d i)
    (hcharge : ∀ price : I → ℝ, (∀ i, 0 ≤ price i) →
      let pat := reservedPalettePattern full avoiding
      let R := paletteMaxScore pat price none
      let r : V → ℝ := fun v => paletteMaxScore pat price (some v)
      (∑ i : I, price i * d i) +
          (∑ v : V, q v * (R - r v)) ≤ κ * R) :
    d ∈ PaletteAttainable (reservedPaletteBudget κ q)
      (reservedPalettePattern full avoiding) := by
  let pat := reservedPalettePattern full avoiding
  have hpat : ∀ o p i, 0 ≤ pat o p i := by
    intro o p i
    cases o with
    | none => exact hfull p i
    | some v => exact havoiding v p i
  apply paletteAttainable_of_maxScoreInequalities
    (reservedPaletteBudget κ q)
    (reservedPaletteBudget_nonneg κ q hq hsum)
    pat hpat hd
  intro price hp
  let R := paletteMaxScore pat price none
  let r : V → ℝ := fun v => paletteMaxScore pat price (some v)
  have hc : (∑ i : I, price i * d i) +
      (∑ v : V, q v * (R - r v)) ≤ κ * R :=
    hcharge price hp
  have hsmall : (∑ i : I, price i * d i) ≤
      (κ - ∑ v : V, q v) * R + ∑ v : V, q v * r v :=
    (reservedPalettePrice_iff κ (∑ i : I, price i * d i) R q r).2 hc
  rw [reservedPaletteSupport_eq κ q pat price]
  exact hsmall

/-- Exact local dual interface for the `none` unrestricted palette and the
`some v` reserved palettes.  It is an equivalence for the finite fractional
allocation model; proving the right side for a graph remains separate. -/
theorem reservedPaletteAttainable_iff_chargeInequalities [Nonempty P]
    (κ : ℝ) (q : V → ℝ) (hq : ∀ v, 0 ≤ q v)
    (hsum : (∑ v : V, q v) ≤ κ)
    (full : P → I → ℝ) (avoiding : V → P → I → ℝ)
    (hfull : ∀ p i, 0 ≤ full p i)
    (havoiding : ∀ v p i, 0 ≤ avoiding v p i)
    {d : I → ℝ} (hd : ∀ i, 0 ≤ d i) :
    d ∈ PaletteAttainable (reservedPaletteBudget κ q)
      (reservedPalettePattern full avoiding) ↔
      ∀ price : I → ℝ, (∀ i, 0 ≤ price i) →
        let pat := reservedPalettePattern full avoiding
        let R := paletteMaxScore pat price none
        let r : V → ℝ := fun v => paletteMaxScore pat price (some v)
        (∑ i : I, price i * d i) +
          (∑ v : V, q v * (R - r v)) ≤ κ * R := by
  constructor
  · intro halloc price hp
    let pat := reservedPalettePattern full avoiding
    let R := paletteMaxScore pat price none
    let r : V → ℝ := fun v => paletteMaxScore pat price (some v)
    have hpat : ∀ o p i, 0 ≤ pat o p i := by
      intro o p i
      cases o with
      | none => exact hfull p i
      | some v => exact havoiding v p i
    have hmax0 : ∀ o, 0 ≤ paletteMaxScore pat price o :=
      paletteMaxScore_nonneg pat hpat price hp
    have hbound : (∑ i : I, price i * d i) ≤
        ∑ o : Option V,
          reservedPaletteBudget κ q o * paletteMaxScore pat price o :=
      paletteAttainable_price_le_budget_mul
        (reservedPaletteBudget κ q) pat halloc price hp
        (paletteMaxScore pat price) hmax0
        (fun o p => patternPrice_le_paletteMaxScore pat price o p)
    rw [reservedPaletteSupport_eq κ q pat price] at hbound
    exact (reservedPalettePrice_iff κ
      (∑ i : I, price i * d i) R q r).1 hbound
  · exact reservedPaletteAttainable_of_chargeInequalities
      κ q hq hsum full avoiding hfull havoiding hd

end ReservedClasses

end WeightedEdgeColoring.Subtwo
