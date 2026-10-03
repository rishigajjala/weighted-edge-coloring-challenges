import WeightedEdgeColoring.SubtwoPaletteAllocation
import WeightedEdgeColoring.BPGeneralPacketCompletion
import WeightedEdgeColoring.GeneralDeficitAwareBoundedMultiplicityWholeEdgeRounding

/-!
# Integer rounding of labelled local palettes

The local separation theorem supplies a real mass for every *labelled*
pattern.  Flooring those masses after scaling by the local bin number keeps
the label of every resulting color.  This file quantifies the loss in each
demand coordinate and the number of colors in every label class.  It is a
finite arithmetic bridge; assigning the resulting colors to physical edges
still requires the graph-facing completion argument.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo

variable {I L P : Type*}
  [Fintype I] [DecidableEq I]
  [Fintype L] [DecidableEq L]
  [Fintype P] [DecidableEq P]

/-- Integer copies of a particular labelled pattern after scaling. -/
noncomputable def roundedPaletteCount (n : ℕ) (a : L × P → ℝ)
    (lp : L × P) : ℕ := Nat.floor ((n : ℝ) * a lp)

/-- The actual integer colors available in one label class.  The pattern
coordinate is retained, so a color can be decoded back to its local pattern. -/
noncomputable abbrev RoundedLabelColors (n : ℕ) (a : L × P → ℝ) (l : L) : Type _ :=
  Σ p : P, Fin (roundedPaletteCount n a (l, p))

/-- Integer copies, still carrying their class label and pattern. -/
noncomputable abbrev RoundedPaletteColors (n : ℕ) (a : L × P → ℝ) : Type _ :=
  Σ l : L, RoundedLabelColors n a l

theorem card_roundedLabelColors (n : ℕ) (a : L × P → ℝ) (l : L) :
    Fintype.card (RoundedLabelColors n a l) =
      ∑ p : P, roundedPaletteCount n a (l, p) := by
  classical
  simp [RoundedLabelColors, Fintype.card_sigma]

theorem card_roundedPaletteColors (n : ℕ) (a : L × P → ℝ) :
    Fintype.card (RoundedPaletteColors n a) =
      ∑ l : L, ∑ p : P, roundedPaletteCount n a (l, p) := by
  classical
  simp [RoundedPaletteColors, Fintype.card_sigma, card_roundedLabelColors]

/-- The number of colors in each label class respects the scaled budget,
with no accumulation of rounding loss across the patterns of that class. -/
theorem roundedLabelColors_le_budget
    (n : ℕ) (budget : L → ℝ) (a : L × P → ℝ)
    (ha : PaletteFeasible budget a) (l : L) :
    Fintype.card (RoundedLabelColors n a l) ≤
      Nat.floor ((n : ℝ) * budget l) := by
  rw [card_roundedLabelColors]
  apply Nat.le_floor
  rw [Nat.cast_sum]
  calc
    (∑ p : P, (roundedPaletteCount n a (l, p) : ℝ)) ≤
        ∑ p : P, (n : ℝ) * a (l, p) := by
      apply Finset.sum_le_sum
      intro p _
      exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (ha.1 (l, p)))
    _ = (n : ℝ) * ∑ p : P, a (l, p) := by rw [Finset.mul_sum]
    _ ≤ (n : ℝ) * budget l :=
      mul_le_mul_of_nonneg_left (ha.2 l) (Nat.cast_nonneg n)

/-- Coverage by the integer copies of labelled patterns. -/
noncomputable def roundedPaletteCoverage (n : ℕ) (pattern : L → P → I → ℝ)
    (a : L × P → ℝ) (i : I) : ℝ :=
  ∑ l : L, ∑ p : P,
    (roundedPaletteCount n a (l, p) : ℝ) * pattern l p i

/-- A universal, finite error budget for a demand coordinate.  It depends
on the menu of patterns, not on the fractional allocation or on `n`. -/
def roundedPaletteError (pattern : L → P → I → ℝ) (i : I) : ℝ :=
  ∑ l : L, ∑ p : P, pattern l p i

/-- Every labelled pattern loses less than one copy under flooring.  Thus
the scaled demand is covered by the rounded copies plus the fixed menu error.
The proof uses the actual allocation witness supplied by separation. -/
theorem roundedPaletteCoverage_with_error
    (n : ℕ) (pattern : L → P → I → ℝ)
    (hpattern : ∀ l p i, 0 ≤ pattern l p i)
    (a : L × P → ℝ) (i : I) :
    (n : ℝ) * paletteCoverage pattern a i ≤
      roundedPaletteCoverage n pattern a i + roundedPaletteError pattern i := by
  unfold paletteCoverage roundedPaletteCoverage roundedPaletteError
  rw [Finset.mul_sum]
  calc
    (∑ l : L, (n : ℝ) * ∑ p : P, a (l, p) * pattern l p i) =
        ∑ l : L, ∑ p : P, ((n : ℝ) * a (l, p)) * pattern l p i := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ ∑ l : L, ∑ p : P,
          ((roundedPaletteCount n a (l, p) : ℝ) * pattern l p i +
            pattern l p i) := by
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro p _
      have hf := Nat.lt_floor_add_one ((n : ℝ) * a (l, p))
      have hm := mul_le_mul_of_nonneg_right hf.le (hpattern l p i)
      dsimp [roundedPaletteCount] at hm ⊢
      nlinarith
    _ = (∑ l : L, ∑ p : P,
          (roundedPaletteCount n a (l, p) : ℝ) * pattern l p i) +
          (∑ l : L, ∑ p : P, pattern l p i) := by
      simp only [Finset.sum_add_distrib]

/-- The usable form for a nonnegative demand covered by a feasible
fractional labelled allocation.  Both the label counts and the coordinate
error hold for the same integer collection of colors. -/
theorem exists_roundedPaletteColors_of_attainable
    (n : ℕ) (budget : L → ℝ) (pattern : L → P → I → ℝ)
    (hpattern : ∀ l p i, 0 ≤ pattern l p i)
    {d : I → ℝ} (hd : d ∈ PaletteAttainable budget pattern) :
    ∃ a : L × P → ℝ, PaletteFeasible budget a ∧
      (∀ l, Fintype.card (RoundedLabelColors n a l) ≤
        Nat.floor ((n : ℝ) * budget l)) ∧
      (∀ i, (n : ℝ) * d i ≤
        roundedPaletteCoverage n pattern a i + roundedPaletteError pattern i) := by
  obtain ⟨a, ha, hcover⟩ := hd.2
  refine ⟨a, ha, roundedLabelColors_le_budget n budget a ha, ?_⟩
  intro i
  exact (mul_le_mul_of_nonneg_left (hcover i) (Nat.cast_nonneg n)).trans
    (roundedPaletteCoverage_with_error n pattern hpattern a i)

/-- Number of integral slots for one internal type after pattern rounding. -/
noncomputable def roundedPaletteSlotCount (n : ℕ)
    (pattern : L → P → I → ℕ) (a : L × P → ℝ) (i : I) : ℕ :=
  ∑ l : L, ∑ p : P,
    roundedPaletteCount n a (l, p) * pattern l p i

/-- Fixed upper bound on the unfilled objects of one internal type. -/
def roundedPaletteErrorCount (pattern : L → P → I → ℕ) (i : I) : ℕ :=
  ∑ l : L, ∑ p : P, pattern l p i

theorem roundedPaletteSlotCount_cast (n : ℕ)
    (pattern : L → P → I → ℕ) (a : L × P → ℝ) (i : I) :
    (roundedPaletteSlotCount n pattern a i : ℝ) =
      roundedPaletteCoverage n (fun l p j => (pattern l p j : ℝ)) a i := by
  simp [roundedPaletteSlotCount, roundedPaletteCoverage, Nat.cast_sum,
    Nat.cast_mul]

theorem roundedPaletteErrorCount_cast
    (pattern : L → P → I → ℕ) (i : I) :
    (roundedPaletteErrorCount pattern i : ℝ) =
      roundedPaletteError (fun l p j => (pattern l p j : ℝ)) i := by
  simp [roundedPaletteErrorCount, roundedPaletteError, Nat.cast_sum]

/-- Every slot remembers its palette label, pattern, color copy, and
position within that pattern for the chosen internal type. -/
noncomputable abbrev RoundedTypeSlots (n : ℕ)
    (pattern : L → P → I → ℕ) (a : L × P → ℝ) (i : I) : Type _ :=
  Σ l : L, Σ p : P,
    Fin (roundedPaletteCount n a (l, p)) × Fin (pattern l p i)

theorem card_roundedTypeSlots (n : ℕ)
    (pattern : L → P → I → ℕ) (a : L × P → ℝ) (i : I) :
    Fintype.card (RoundedTypeSlots n pattern a i) =
      roundedPaletteSlotCount n pattern a i := by
  simp [RoundedTypeSlots, roundedPaletteSlotCount, Fintype.card_sigma,
    Fintype.card_prod]

/-- Any initial segment of the objects that fits in the rounded pattern
slots has an injective assignment to actual labelled slots. -/
theorem exists_injective_roundedTypeSlotAssignment (n : ℕ)
    (pattern : L → P → I → ℕ) (a : L × P → ℝ) (i : I)
    (D : ℕ) (hD : D ≤ roundedPaletteSlotCount n pattern a i) :
    ∃ assign : Fin D ↪ RoundedTypeSlots n pattern a i, True := by
  let equiv := Fintype.equivFinOfCardEq
    (card_roundedTypeSlots n pattern a i)
  let assign : Fin D ↪ RoundedTypeSlots n pattern a i :=
    ⟨fun j => equiv.symm (Fin.castLE hD j),
      equiv.symm.injective.comp (Fin.castLE_injective hD)⟩
  exact ⟨assign, trivial⟩

/-- For actual integral type demands, the rounded color copies leave at
most a fixed number of objects of each type.  This bound is independent of
the scale `n`; each copy contributes its pattern's integer slot count. -/
theorem exists_roundedPaletteSlots_of_attainable
    (n : ℕ) (budget : L → ℝ) (pattern : L → P → I → ℕ)
    {d : I → ℝ}
    (hd : d ∈ PaletteAttainable budget
      (fun l p i => (pattern l p i : ℝ)))
    (D : I → ℕ) (hD : ∀ i, (D i : ℝ) ≤ (n : ℝ) * d i) :
    ∃ a : L × P → ℝ, PaletteFeasible budget a ∧
      (∀ l, Fintype.card (RoundedLabelColors n a l) ≤
        Nat.floor ((n : ℝ) * budget l)) ∧
      ∀ i, D i ≤ roundedPaletteSlotCount n pattern a i +
        roundedPaletteErrorCount pattern i := by
  obtain ⟨a, ha, hlabels, hcoverage⟩ :=
    exists_roundedPaletteColors_of_attainable n budget
      (fun l p i => (pattern l p i : ℝ))
      (fun _ _ _ => Nat.cast_nonneg _) hd
  refine ⟨a, ha, hlabels, ?_⟩
  intro i
  have hreal : (D i : ℝ) ≤
      (roundedPaletteSlotCount n pattern a i : ℝ) +
        (roundedPaletteErrorCount pattern i : ℝ) := by
    rw [roundedPaletteSlotCount_cast, roundedPaletteErrorCount_cast]
    exact (hD i).trans (hcoverage i)
  exact_mod_cast hreal

/-- The same rounded allocation admits concrete injections of the colored
objects into labelled slots.  The remaining object count is bounded by the
fixed pattern-menu error for each type. -/
theorem exists_roundedPaletteSlotAssignments_of_attainable
    (n : ℕ) (budget : L → ℝ) (pattern : L → P → I → ℕ)
    {d : I → ℝ}
    (hd : d ∈ PaletteAttainable budget
      (fun l p i => (pattern l p i : ℝ)))
    (D : I → ℕ) (hD : ∀ i, (D i : ℝ) ≤ (n : ℝ) * d i) :
    ∃ a : L × P → ℝ, PaletteFeasible budget a ∧
      (∀ l, Fintype.card (RoundedLabelColors n a l) ≤
        Nat.floor ((n : ℝ) * budget l)) ∧
      ∀ i,
        D i - roundedPaletteSlotCount n pattern a i ≤
          roundedPaletteErrorCount pattern i ∧
        ∃ assign : Fin (min (D i) (roundedPaletteSlotCount n pattern a i)) ↪
          RoundedTypeSlots n pattern a i, True := by
  obtain ⟨a, ha, hlabels, hslots⟩ :=
    exists_roundedPaletteSlots_of_attainable n budget pattern hd D hD
  refine ⟨a, ha, hlabels, ?_⟩
  intro i
  constructor
  · have h := hslots i
    omega
  · exact exists_injective_roundedTypeSlotAssignment n pattern a i
      _ (Nat.min_le_right _ _)

section ReservedClasses

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In the reserved-palette model, integer rounding retains the endpoint
label: the `some v` class has at most `⌊n qᵥ⌋` colors, while the common class
has at most `⌊n(κ - Σ qᵥ)⌋` colors. -/
theorem roundedReservedPalette_class_bounds
    (n : ℕ) (κ : ℝ) (q : V → ℝ) (P : Type*)
    [Fintype P] [DecidableEq P]
    (a : Option V × P → ℝ)
    (ha : PaletteFeasible (reservedPaletteBudget κ q) a) :
    Fintype.card (RoundedLabelColors n a none) ≤
        Nat.floor ((n : ℝ) * (κ - ∑ v : V, q v)) ∧
      ∀ v, Fintype.card (RoundedLabelColors n a (some v)) ≤
        Nat.floor ((n : ℝ) * q v) := by
  constructor
  · simpa [reservedPaletteBudget] using
      roundedLabelColors_le_budget n (reservedPaletteBudget κ q) a ha none
  · intro v
    simpa [reservedPaletteBudget] using
      roundedLabelColors_le_budget n (reservedPaletteBudget κ q) a ha (some v)

/-- The checked finite price inequality yields actual integer copies of
reserved and unrestricted patterns, with an explicit fixed rounding error.
This is the direct interface from fractional palette separation to local
integer restoration; no graph-facing charge inequality is assumed here. -/
theorem exists_roundedReservedPalette_of_chargeInequalities
    [Nonempty P]
    (n : ℕ) (κ : ℝ) (q : V → ℝ)
    (hq : ∀ v, 0 ≤ q v) (hsum : (∑ v : V, q v) ≤ κ)
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
    ∃ a : Option V × P → ℝ,
      PaletteFeasible (reservedPaletteBudget κ q) a ∧
      Fintype.card (RoundedLabelColors n a none) ≤
        Nat.floor ((n : ℝ) * (κ - ∑ v : V, q v)) ∧
      (∀ v, Fintype.card (RoundedLabelColors n a (some v)) ≤
        Nat.floor ((n : ℝ) * q v)) ∧
      ∀ i, (n : ℝ) * d i ≤
        roundedPaletteCoverage n (reservedPalettePattern full avoiding) a i +
          roundedPaletteError (reservedPalettePattern full avoiding) i := by
  let pat := reservedPalettePattern full avoiding
  have hpat : ∀ o p i, 0 ≤ pat o p i := by
    intro o p i
    cases o with
    | none => exact hfull p i
    | some v => exact havoiding v p i
  have hattain :
      d ∈ PaletteAttainable (reservedPaletteBudget κ q) pat :=
    reservedPaletteAttainable_of_chargeInequalities
      κ q hq hsum full avoiding hfull havoiding hd hcharge
  obtain ⟨a, ha, _, hcover⟩ :=
    exists_roundedPaletteColors_of_attainable n
      (reservedPaletteBudget κ q) pat hpat hattain
  obtain ⟨hcommon, hreserved⟩ :=
    roundedReservedPalette_class_bounds n κ q P a ha
  exact ⟨a, ha, hcommon, hreserved, hcover⟩

end ReservedClasses

section DisjointBlockAssembly

/-- Colors may be reused across vertex-disjoint blocks.  `blockE` records
which block owns a physical edge; the incidence condition ensures every edge
touching a vertex belongs to that vertex's block.  Therefore the global
load at a vertex is exactly its local block load. -/
theorem feasibleOn_of_blockwise_feasible
    {G : WeightedEdgeColoring.WeightedMultigraph} {B : Type*} [DecidableEq B]
    {K : ℕ} (F : Finset G.E)
    (blockV : G.V → B) (blockE : G.E → B)
    (hinc : ∀ e ∈ F, ∀ v, G.Inc v e → blockE e = blockV v)
    (color : B → G.E → Fin K)
    (hlocal : ∀ b, G.IsFeasibleOn (F.filter fun e => blockE e = b)
      (color b)) :
    G.IsFeasibleOn F (fun e => color (blockE e) e) := by
  classical
  intro v c
  have hload :
      G.colorLoadOn F (fun e => color (blockE e) e) v c =
        G.colorLoadOn (F.filter fun e => blockE e = blockV v)
          (color (blockV v)) v c := by
    unfold WeightedEdgeColoring.WeightedMultigraph.colorLoadOn
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e heF
    by_cases hv : G.Inc v e
    · have hb := hinc e heF v hv
      simp [hv, hb]
    · simp [hv]
  rw [hload]
  exact hlocal (blockV v) v c

end DisjointBlockAssembly

section BoundaryLabelTransfer

universe u

/-- The used color names assigned to one boundary label in one block. -/
noncomputable def usedBoundaryLabelColors
    {G : WeightedEdgeColoring.WeightedMultigraph} {B L : Type*}
    [DecidableEq L] {K : ℕ}
    (P : Finset G.E) (color : G.E → Fin K)
    (touches : B → G.E → Prop) (label : B → G.E → L)
    (b : B) (l : L) : Finset (Fin K) := by
  classical
  exact (P.filter fun e => touches b e ∧ label b e = l).image color

/-- Proposal support is enough to transfer a prescribed class for each
boundary label through a whole-edge rounding theorem.  The conclusion is
an actual bound on distinct color names at a block, not merely an expected
number of chosen edges. -/
theorem usedBoundaryLabelColors_card_le_allowed
    {G : WeightedEdgeColoring.WeightedMultigraph} {B L : Type*}
    [DecidableEq L] {K : ℕ}
    (P : Finset G.E) (color : G.E → Fin K)
    (x : G.E → Fin K → ℝ)
    (hselected : ∀ e ∈ P, 0 < x e (color e))
    (touches : B → G.E → Prop) (label : B → G.E → L)
    (allowed : B → L → Finset (Fin K))
    (hsupport : ∀ e c b, 0 < x e c → touches b e →
      c ∈ allowed b (label b e))
    (b : B) (l : L) :
    (usedBoundaryLabelColors P color touches label b l).card ≤
      (allowed b l).card := by
  classical
  apply Finset.card_le_card
  intro c hc
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨heP, ht, hl⟩ := Finset.mem_filter.mp he
  simpa [hl] using hsupport e (color e) b (hselected e heP) ht

/-- Disjoint allowed classes ensure one rounded color at a block cannot
carry two different endpoint labels. -/
theorem selectedBoundaryColor_label_unique
    {G : WeightedEdgeColoring.WeightedMultigraph} {B L : Type*}
    [DecidableEq L] {K : ℕ}
    (P : Finset G.E) (color : G.E → Fin K)
    (x : G.E → Fin K → ℝ)
    (hselected : ∀ e ∈ P, 0 < x e (color e))
    (touches : B → G.E → Prop) (label : B → G.E → L)
    (allowed : B → L → Finset (Fin K))
    (hsupport : ∀ e c b, 0 < x e c → touches b e →
      c ∈ allowed b (label b e))
    (hdisj : ∀ b l l', l ≠ l' → Disjoint (allowed b l) (allowed b l'))
    (b : B) (e f : G.E)
    (he : e ∈ P) (hf : f ∈ P)
    (hte : touches b e) (htf : touches b f)
    (hcolor : color e = color f) : label b e = label b f := by
  by_contra hne
  have hce : color e ∈ allowed b (label b e) :=
    hsupport e (color e) b (hselected e he) hte
  have hcf : color f ∈ allowed b (label b f) :=
    hsupport f (color f) b (hselected f hf) htf
  exact Finset.disjoint_left.mp (hdisj b _ _ hne) hce (hcolor ▸ hcf)

/-- The existing whole-edge theorem automatically preserves preassigned
endpoint-label palettes.  Its positive-support conclusion transfers both
the per-label count and uniqueness of the label at each block/color.
Constructing the disjoint allowed sets and a locally feasible proposal with
this support is a separate, earlier step. -/
theorem exists_labelControlled_partialColoring_of_generalDeficitAware
    {B L : Type*} [DecidableEq L]
    (hround : WeightedEdgeColoring.GeneralDeficitAwareBoundedMultiplicityWholeEdgeUniformRounding.{u})
    (Lmult : ℕ) (C0 C1 trim eta : ℝ)
    (hC0 : 0 < C0) (hC1 : 0 < C1) (hC1four : C1 < 4)
    (htrim0 : 0 < trim) (htrim1 : trim < 1)
    (htrimEta : 64 * trim < eta) (heta : 0 < eta) :
    ∃ N : ℕ,
      ∀ (G : WeightedEdgeColoring.WeightedMultigraph.{u}) (n q : ℕ)
        (x : G.E → Fin q → ℝ)
        (touches : B → G.E → Prop) (label : B → G.E → L)
        (allowed : B → L → Finset (Fin q)),
        N ≤ n → 0 < q → G.PairMultiplicityAtMost Lmult →
        (∀ v, G.starWeight v ≤ n) →
        (q : ℝ) ≤ C1 * n →
        (∀ e c, 0 ≤ x e c ∧ x e c ≤ C0 / n) →
        (∀ e, ∑ c, x e c ≤ 1) →
        (∀ v c, G.IsAverageOfStarFeasibleSets v
          (fun se => x se.1 c)) →
        (∀ e c b, 0 < x e c → touches b e →
          c ∈ allowed b (label b e)) →
        (∀ b l l', l ≠ l' → Disjoint (allowed b l) (allowed b l')) →
        ∃ (P : Finset G.E) (color : G.E → Fin q),
          G.IsFeasibleOn P color ∧
          (∀ e ∈ P, 0 < x e (color e)) ∧
          (∀ b l, (usedBoundaryLabelColors P color touches label b l).card ≤
            (allowed b l).card) ∧
          (∀ b e f, e ∈ P → f ∈ P → touches b e → touches b f →
            color e = color f → label b e = label b f) ∧
          ∀ v, (∑ e ∈ Finset.univ \ P,
            if G.Inc v e then G.weight e else 0) ≤
            G.proposalDeficit x v / trim + eta * n := by
  obtain ⟨N, hN⟩ := hround Lmult C0 C1 trim eta hC0 hC1 hC1four
    htrim0 htrim1 htrimEta heta
  refine ⟨N, ?_⟩
  intro G n q x touches label allowed hn hq hmult hstar hpalette hx
    hmass havg hsupport hdisj
  obtain ⟨P, color, hfeasible, hselected, hloss⟩ :=
    hN G n q x hn hq hmult hstar hpalette hx hmass havg
  refine ⟨P, color, hfeasible, hselected, ?_, ?_, hloss⟩
  · intro b l
    exact usedBoundaryLabelColors_card_le_allowed P color x hselected
      touches label allowed hsupport b l
  · intro b e f he hf hte htf hc
    exact selectedBoundaryColor_label_unique P color x hselected
      touches label allowed hsupport hdisj b e f he hf hte htf hc

end BoundaryLabelTransfer

end WeightedEdgeColoring.Subtwo
