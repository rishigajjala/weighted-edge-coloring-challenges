import WeightedEdgeColoring.BinPacking
import Mathlib.Tactic

/-!
# Greedy packing for uniformly small items

Assign each item, in an arbitrary finite order, to a currently least-loaded
bin.  With `m > 0` bins, every final load is at most the average total load
plus the largest item.  This gives a clean `n + O(delta*n) + 1` bound when
all item weights are at most `delta ≤ 1/2`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance

universe u

/-- Finite-list-scheduling estimate: `m` positive bins suffice with maximum
load at most the average plus the maximum item size. -/
theorem exists_assignment_load_le_average_add
    {X : Type u} [Fintype X] [DecidableEq X]
    (weight : X → ℝ) (delta : ℝ)
    (hdelta0 : 0 ≤ delta)
    (hweight0 : ∀ x, 0 ≤ weight x)
    (hweightDelta : ∀ x, weight x ≤ delta)
    (F : Finset X) (m : ℕ) (hm : 0 < m) :
    ∃ bin : X → Fin m, ∀ j,
      (∑ x ∈ F, if bin x = j then weight x else 0) ≤
        (∑ x ∈ F, weight x) / (m : ℝ) + delta := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      let j0 : Fin m := ⟨0, hm⟩
      refine ⟨fun _ ↦ j0, ?_⟩
      intro j
      simpa using hdelta0
  | @insert a S ha ih =>
      obtain ⟨bin, hbin⟩ := ih
      let load : Fin m → ℝ := fun j ↦
        ∑ x ∈ S, if bin x = j then weight x else 0
      have hsum_load : (∑ j : Fin m, load j) = ∑ x ∈ S, weight x := by
        simp only [load]
        rw [Finset.sum_comm]
        simp
      have havg : ∃ j : Fin m,
          load j ≤ (∑ x ∈ S, weight x) / (m : ℝ) := by
        by_contra hnone
        push_neg at hnone
        let j0 : Fin m := ⟨0, hm⟩
        have hlt :
            (∑ _j : Fin m, (∑ x ∈ S, weight x) / (m : ℝ)) <
              ∑ j : Fin m, load j := by
          apply Finset.sum_lt_sum_of_nonempty
          · exact ⟨j0, Finset.mem_univ _⟩
          · intro j _hj
            exact hnone j
        have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
        have hconst :
            (∑ _j : Fin m, (∑ x ∈ S, weight x) / (m : ℝ)) =
              ∑ x ∈ S, weight x := by
          simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
          exact mul_div_cancel₀ _ hmreal
        rw [hconst, hsum_load] at hlt
        exact (lt_irrefl _) hlt
      obtain ⟨least, hleast⟩ := havg
      let newBin : X → Fin m := Function.update bin a least
      have hload (j : Fin m) :
          (∑ x ∈ insert a S,
              if newBin x = j then weight x else 0) =
            (if least = j then weight a else 0) + load j := by
        rw [Finset.sum_insert ha]
        have hrest :
            (∑ x ∈ S, if newBin x = j then weight x else 0) = load j := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxa : x ≠ a := fun h ↦ ha (h ▸ hx)
          simp [newBin, hxa]
        rw [hrest]
        simp [newBin]
      refine ⟨newBin, ?_⟩
      intro j
      rw [hload j, Finset.sum_insert ha]
      by_cases hj : least = j
      · subst j
        simp only [if_pos]
        have hwa := hweightDelta a
        have hwa0 := hweight0 a
        have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
        have hdivmono :
            (∑ x ∈ S, weight x) / (m : ℝ) ≤
              (weight a + ∑ x ∈ S, weight x) / (m : ℝ) := by
          exact (div_le_div_iff_of_pos_right hmreal).2 (by linarith)
        linarith
      · simp only [if_neg hj]
        have hwa0 := hweight0 a
        have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
        have hdivmono :
            (∑ x ∈ S, weight x) / (m : ℝ) ≤
              (weight a + ∑ x ∈ S, weight x) / (m : ℝ) := by
          exact (div_le_div_iff_of_pos_right hmreal).2 (by linarith)
        simpa [load] using
          (hbin j).trans (add_le_add_left hdivmono delta)

variable (B : BinPackingInstance.{u})

/-- If average load plus the item-size cap is at most one, greedy balancing
produces a valid packing. -/
theorem packsInto_of_average_add_max_le_one
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (m : ℕ) (hm : 0 < m)
    (hsmall : ∀ x, B.weight x ≤ delta)
    (hcapacity : B.totalWeight / (m : ℝ) + delta ≤ 1) :
    B.PacksInto m := by
  classical
  obtain ⟨bin, hbin⟩ := exists_assignment_load_le_average_add
    B.weight delta hdelta0 B.weight_nonneg hsmall Finset.univ m hm
  refine ⟨⟨bin, ?_⟩⟩
  intro j
  calc
    B.binLoad bin j ≤ B.totalWeight / (m : ℝ) + delta := by
      simpa [binLoad, totalWeight] using hbin j
    _ ≤ 1 := hcapacity

/-- Concrete small-item bound.  For `delta ≤ 1/2`, total weight at most `n`
packs into `n + ceil (2*delta*n) + 1` bins. -/
theorem packsInto_nat_add_ceil_two_mul
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdeltahalf : delta ≤ 1 / 2)
    (n : ℕ) (htotal : B.totalWeight ≤ n)
    (hsmall : ∀ x, B.weight x ≤ delta) :
    B.PacksInto (n + Nat.ceil (2 * delta * n) + 1) := by
  let m : ℕ := n + Nat.ceil (2 * delta * n) + 1
  have hm : 0 < m := by
    dsimp [m]
    omega
  apply B.packsInto_of_average_add_max_le_one delta hdelta0 m hm hsmall
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hceil : 2 * delta * (n : ℝ) ≤ (Nat.ceil (2 * delta * n) : ℕ) :=
    Nat.le_ceil _
  have hmLower :
      (n : ℝ) + 2 * delta * n ≤ (m : ℝ) := by
    dsimp [m]
    push_cast
    linarith
  have hgap : 0 ≤ delta * (n : ℝ) * (1 - 2 * delta) := by
    exact mul_nonneg (mul_nonneg hdelta0 (Nat.cast_nonneg n)) (by linarith)
  have hbase :
      (n : ℝ) ≤ (1 - delta) * ((n : ℝ) + 2 * delta * n) := by
    nlinarith
  have hone : 0 ≤ 1 - delta := by linarith
  have hprod : (n : ℝ) ≤ (1 - delta) * (m : ℝ) :=
    hbase.trans (mul_le_mul_of_nonneg_left hmLower hone)
  have hdiv : (n : ℝ) / (m : ℝ) ≤ 1 - delta := by
    apply (div_le_iff₀ hmreal).2
    simpa [mul_comm] using hprod
  have htotalDiv : B.totalWeight / (m : ℝ) ≤ (n : ℝ) / (m : ℝ) := by
    exact (div_le_div_iff_of_pos_right hmreal).2 htotal
  linarith

end BinPackingInstance
end WeightedEdgeColoring
