import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic

/-!
# One-dimensional bin packing

This file records a finite, indexed version of bin packing.  Items are indexed
rather than identified with their weights, so two different items may have the
same weight.  Integral packings are represented by explicit bin assignments.

The patterns used by the fractional relaxation are integer vectors.  In
particular, a pattern is allowed to use an item index with multiplicity greater
than one, as in the usual configuration LP.  A fractional cover itself has
finite support, even though the type of all integer patterns need not be
presented as a finite type.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

universe u

/-- A finite indexed family of items, each having a weight in `(0, 1]`. -/
structure BinPackingInstance where
  Item : Type u
  instFintypeItem : Fintype Item
  instDecidableEqItem : DecidableEq Item
  weight : Item → ℝ
  weight_pos : ∀ i, 0 < weight i
  weight_le_one : ∀ i, weight i ≤ 1

attribute [instance]
  BinPackingInstance.instFintypeItem
  BinPackingInstance.instDecidableEqItem

namespace BinPackingInstance

variable (B : BinPackingInstance)

/-- The sum of the weights of all indexed items. -/
def totalWeight : ℝ := ∑ i : B.Item, B.weight i

theorem weight_nonneg (i : B.Item) : 0 ≤ B.weight i := (B.weight_pos i).le

/-- The load of bin `j` under an assignment to `n` labelled bins. -/
def binLoad {n : ℕ} (bin : B.Item → Fin n) (j : Fin n) : ℝ :=
  ∑ i : B.Item, if bin i = j then B.weight i else 0

/-- An explicit certificate that all items fit into `n` unit-capacity bins. -/
structure PackingCertificate (n : ℕ) where
  bin : B.Item → Fin n
  load_le_one : ∀ j, B.binLoad bin j ≤ 1

/-- The items admit an integral packing into `n` bins. -/
def PacksInto (n : ℕ) : Prop := Nonempty (B.PackingCertificate n)

/-- Giving every indexed item its own bin always produces a packing. -/
theorem packsInto_card : B.PacksInto (Fintype.card B.Item) := by
  let bin : B.Item → Fin (Fintype.card B.Item) := Fintype.equivFin B.Item
  refine ⟨⟨bin, ?_⟩⟩
  intro j
  rw [binLoad, ← Finset.sum_filter]
  have hinj : Function.Injective bin := (Fintype.equivFin B.Item).injective
  have hcard : (Finset.univ.filter fun i : B.Item => bin i = j).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    exact hinj ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  calc
    (∑ i ∈ Finset.univ.filter fun i : B.Item => bin i = j, B.weight i)
        ≤ ∑ _i ∈ Finset.univ.filter fun i : B.Item => bin i = j, (1 : ℝ) := by
          exact Finset.sum_le_sum fun i _hi => B.weight_le_one i
    _ = ((Finset.univ.filter fun i : B.Item => bin i = j).card : ℝ) := by simp
    _ ≤ 1 := by
      have hcast := (Nat.cast_le.2 hcard :
        ((Finset.univ.filter fun i : B.Item => bin i = j).card : ℝ) ≤ ((1 : ℕ) : ℝ))
      simpa only [Nat.cast_one] using hcast

/-- There is always some number of bins into which the items pack. -/
theorem exists_packsInto : ∃ n, B.PacksInto n :=
  ⟨Fintype.card B.Item, B.packsInto_card⟩

/-- The minimum number of unit bins needed by the instance. -/
noncomputable def binPackingNumber : ℕ := by
  classical
  exact Nat.find B.exists_packsInto

theorem packsInto_binPackingNumber : B.PacksInto B.binPackingNumber :=
  by
    classical
    exact Nat.find_spec B.exists_packsInto

theorem binPackingNumber_le_of_packsInto {n : ℕ} (h : B.PacksInto n) :
    B.binPackingNumber ≤ n := by
  classical
  exact Nat.find_min' B.exists_packsInto h

/-- The total item weight is at most the number of bins in any packing. -/
theorem totalWeight_le_of_packsInto {n : ℕ} (h : B.PacksInto n) :
    B.totalWeight ≤ n := by
  rcases h with ⟨P⟩
  calc
    B.totalWeight = ∑ j : Fin n, B.binLoad P.bin j := by
      simp only [totalWeight, binLoad]
      rw [Finset.sum_comm]
      simp only [Fintype.sum_ite_eq]
    _ ≤ ∑ _j : Fin n, (1 : ℝ) := by
      exact Finset.sum_le_sum fun j _hj => P.load_le_one j
    _ = n := by simp

/-- In particular, total weight is bounded by the optimum integral cost. -/
theorem totalWeight_le_binPackingNumber :
    B.totalWeight ≤ B.binPackingNumber :=
  B.totalWeight_le_of_packsInto B.packsInto_binPackingNumber

/--
An integer configuration (or pattern) for one unit bin.  Multiplicities are
unrestricted natural numbers; feasibility alone limits their weighted sum.
-/
structure Pattern where
  multiplicity : B.Item → ℕ
  capacity : ∑ i : B.Item, (multiplicity i : ℝ) * B.weight i ≤ 1

namespace Pattern

variable {B}

/-- The total number of copies of item index `i` in a pattern. -/
abbrev count (p : B.Pattern) (i : B.Item) : ℕ := p.multiplicity i

end Pattern

/--
A finite-support fractional cover by feasible integer patterns.  The cover
constraint is coordinatewise: every indexed item is covered to extent at
least one.
-/
structure FractionalPatternCover where
  coeff : B.Pattern →₀ ℝ
  coeff_nonneg : ∀ p, 0 ≤ coeff p
  covers : ∀ i : B.Item,
    1 ≤ ∑ p ∈ coeff.support, coeff p * (p.multiplicity i : ℝ)

namespace FractionalPatternCover

variable {B}

/-- The fractional amount by which `C` covers item coordinate `i`. -/
def coverage (C : B.FractionalPatternCover) (i : B.Item) : ℝ :=
  ∑ p ∈ C.coeff.support, C.coeff p * (p.multiplicity i : ℝ)

/-- The objective value of a finite-support fractional pattern cover. -/
def cost (C : B.FractionalPatternCover) : ℝ :=
  ∑ p ∈ C.coeff.support, C.coeff p

theorem one_le_coverage (C : B.FractionalPatternCover) (i : B.Item) :
    1 ≤ C.coverage i :=
  C.covers i

theorem cost_nonneg (C : B.FractionalPatternCover) : 0 ≤ C.cost := by
  exact Finset.sum_nonneg fun p _hp => C.coeff_nonneg p

/-- Every fractional pattern cover costs at least the total item weight. -/
theorem totalWeight_le_cost (C : B.FractionalPatternCover) :
    B.totalWeight ≤ C.cost := by
  calc
    B.totalWeight = ∑ i : B.Item, B.weight i * 1 := by
      simp [BinPackingInstance.totalWeight]
    _ ≤ ∑ i : B.Item, B.weight i * C.coverage i := by
      exact Finset.sum_le_sum fun i _hi =>
        mul_le_mul_of_nonneg_left (C.one_le_coverage i) (B.weight_nonneg i)
    _ = ∑ p ∈ C.coeff.support,
        C.coeff p * (∑ i : B.Item, (p.multiplicity i : ℝ) * B.weight i) := by
      simp only [coverage, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro i hi
      simp only [mul_assoc, mul_left_comm, mul_comm]
    _ ≤ ∑ p ∈ C.coeff.support, C.coeff p * 1 := by
      exact Finset.sum_le_sum fun p _hp =>
        mul_le_mul_of_nonneg_left p.capacity (C.coeff_nonneg p)
    _ = C.cost := by simp [cost]

end FractionalPatternCover

/-- The configuration LP has a feasible cover of objective value at most `F`. -/
def HasFractionalPatternCoverCostAtMost (F : ℝ) : Prop :=
  ∃ C : B.FractionalPatternCover, C.cost ≤ F

/-- A fractional objective upper bound also bounds the total item weight. -/
theorem totalWeight_le_of_hasFractionalPatternCoverCostAtMost {F : ℝ}
    (h : B.HasFractionalPatternCoverCostAtMost F) : B.totalWeight ≤ F := by
  rcases h with ⟨C, hC⟩
  exact C.totalWeight_le_cost.trans hC

end BinPackingInstance

/--
The assertion called *Elementary Grouping* (Lemma 4.1) in the paper.

The upper bound `weight ≤ 1` is part of `BinPackingInstance`.  The additional
hypothesis says that every item has weight at least `τ`.  This definition
names a proposition; it does not assert the proposition or introduce an axiom.
-/
def ElementaryGrouping : Prop :=
  ∀ (B : BinPackingInstance.{u}) (τ θ F : ℝ),
    0 < τ →
    (∀ i : B.Item, τ ≤ B.weight i) →
    0 < θ →
    θ < 1 →
    1 ≤ θ * F →
    B.HasFractionalPatternCoverCostAtMost F →
    (B.binPackingNumber : ℝ) ≤ (1 + θ) * F + 1 / (θ * τ) + 3

end WeightedEdgeColoring
