import WeightedEdgeColoring.SmallItemGreedyPacking

/-!
# Greedy packing above fixed initial loads

The ordinary least-loaded-bin proof also works when the bins already contain
fixed items.  Provided those initial loads are feasible, greedily inserting
small remaining items succeeds whenever the average final load plus the
largest inserted item is at most one.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance

universe u

/-- The numerical capacity inequality used by both the empty-bin and seeded
versions of the small-item argument. -/
theorem nat_div_nat_add_ceil_two_mul_add_le_one
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdeltahalf : delta ≤ 1 / 2)
    (n : ℕ) :
    let m := n + Nat.ceil (2 * delta * n) + 1
    (n : ℝ) / (m : ℝ) + delta ≤ 1 := by
  let m : ℕ := n + Nat.ceil (2 * delta * n) + 1
  have hm : 0 < m := by
    dsimp [m]
    omega
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hceil : 2 * delta * (n : ℝ) ≤
      (Nat.ceil (2 * delta * n) : ℕ) := Nat.le_ceil _
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
  dsimp only
  linarith

/-- Least-loaded insertion above arbitrary feasible initial loads.  Only the
items in `F` are assigned by the returned map; its values outside `F` are
irrelevant. -/
theorem exists_assignment_above_initial_loads
    {X : Type u} [Fintype X] [DecidableEq X]
    (weight : X → ℝ) (delta : ℝ)
    (hweight0 : ∀ x, 0 ≤ weight x)
    (F : Finset X) (m : ℕ) (hm : 0 < m)
    (hweightDelta : ∀ x, x ∈ F → weight x ≤ delta)
    (initial : Fin m → ℝ)
    (hinitial : ∀ j, initial j ≤ 1)
    (hcapacity :
      ((∑ j : Fin m, initial j) + ∑ x ∈ F, weight x) / (m : ℝ) +
          delta ≤ 1) :
    ∃ bin : X → Fin m, ∀ j,
      initial j +
          (∑ x ∈ F, if bin x = j then weight x else 0) ≤ 1 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      let j0 : Fin m := ⟨0, hm⟩
      refine ⟨fun _ ↦ j0, ?_⟩
      intro j
      simpa using hinitial j
  | @insert a S ha ih =>
      have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
      have hsumS :
          (∑ j : Fin m, initial j) + ∑ x ∈ S, weight x ≤
            (∑ j : Fin m, initial j) +
              ∑ x ∈ insert a S, weight x := by
        rw [Finset.sum_insert ha]
        linarith [hweight0 a]
      have hcapacityS :
          ((∑ j : Fin m, initial j) + ∑ x ∈ S, weight x) /
                (m : ℝ) + delta ≤ 1 := by
        have hdiv := (div_le_div_iff_of_pos_right hmreal).2 hsumS
        linarith
      obtain ⟨bin, hbin⟩ := ih
        (fun x hx ↦ hweightDelta x (Finset.mem_insert_of_mem hx))
        hcapacityS
      let load : Fin m → ℝ := fun j ↦
        initial j + ∑ x ∈ S, if bin x = j then weight x else 0
      have hsum_load :
          (∑ j : Fin m, load j) =
            (∑ j : Fin m, initial j) + ∑ x ∈ S, weight x := by
        simp only [load, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
        simp
      have havg : ∃ j : Fin m,
          load j ≤
            ((∑ i : Fin m, initial i) + ∑ x ∈ S, weight x) /
              (m : ℝ) := by
        by_contra hnone
        push_neg at hnone
        let j0 : Fin m := ⟨0, hm⟩
        have hlt :
            (∑ _j : Fin m,
                ((∑ i : Fin m, initial i) + ∑ x ∈ S, weight x) /
                  (m : ℝ)) <
              ∑ j : Fin m, load j := by
          apply Finset.sum_lt_sum_of_nonempty
          · exact ⟨j0, Finset.mem_univ _⟩
          · intro j _hj
            exact hnone j
        have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmreal
        have hconst :
            (∑ _j : Fin m,
                ((∑ i : Fin m, initial i) + ∑ x ∈ S, weight x) /
                  (m : ℝ)) =
              (∑ i : Fin m, initial i) + ∑ x ∈ S, weight x := by
          simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
          exact mul_div_cancel₀ _ hmne
        rw [hconst, hsum_load] at hlt
        exact (lt_irrefl _) hlt
      obtain ⟨least, hleast⟩ := havg
      let newBin : X → Fin m := Function.update bin a least
      have hload (j : Fin m) :
          initial j +
              (∑ x ∈ insert a S,
                if newBin x = j then weight x else 0) =
            (if least = j then weight a else 0) + load j := by
        rw [Finset.sum_insert ha]
        have hrest :
            (∑ x ∈ S, if newBin x = j then weight x else 0) =
              ∑ x ∈ S, if bin x = j then weight x else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxa : x ≠ a := fun h ↦ ha (h ▸ hx)
          simp [newBin, hxa]
        rw [hrest]
        simp [newBin, load, add_assoc, add_left_comm, add_comm]
      refine ⟨newBin, ?_⟩
      intro j
      rw [hload j]
      by_cases hj : least = j
      · subst j
        simp only [if_pos]
        have hdiv :
            ((∑ i : Fin m, initial i) + ∑ x ∈ S, weight x) /
                (m : ℝ) ≤
              ((∑ i : Fin m, initial i) +
                ∑ x ∈ insert a S, weight x) / (m : ℝ) :=
          (div_le_div_iff_of_pos_right hmreal).2 hsumS
        have hw := hweightDelta a (Finset.mem_insert_self a S)
        linarith
      · simp only [if_neg hj]
        simpa [load] using hbin j

/-- A packed left family may be kept fixed while a uniformly small right
family is inserted greedily.  This is the exact scalar form used for mixed
singleton/packet stars. -/
theorem exists_sum_assignment_of_left_packing_and_small_right
    {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (leftWeight : A → ℝ) (rightWeight : B → ℝ)
    (hleft0 : ∀ a, 0 ≤ leftWeight a)
    (hright0 : ∀ b, 0 ≤ rightWeight b)
    (delta : ℝ) (hrightSmall : ∀ b, rightWeight b ≤ delta)
    {n m : ℕ} (hnm : n ≤ m) (hm : 0 < m)
    (leftBin : A → Fin n)
    (hleftBin : ∀ i,
      (∑ a : A, if leftBin a = i then leftWeight a else 0) ≤ 1)
    (htotal : (∑ a : A, leftWeight a) + ∑ b : B, rightWeight b ≤ n)
    (hcapacity : (n : ℝ) / (m : ℝ) + delta ≤ 1) :
    ∃ bin : A ⊕ B → Fin m, ∀ j,
      (∑ x : A ⊕ B,
        if bin x = j then Sum.elim leftWeight rightWeight x else 0) ≤ 1 := by
  classical
  let paddedLeftBin : A → Fin m := fun a ↦ Fin.castLE hnm (leftBin a)
  let initial : Fin m → ℝ := fun j ↦
    ∑ a : A, if paddedLeftBin a = j then leftWeight a else 0
  have hinitial : ∀ j, initial j ≤ 1 := by
    intro j
    by_cases hj : ∃ i : Fin n, Fin.castLE hnm i = j
    · obtain ⟨i, rfl⟩ := hj
      simpa only [initial, paddedLeftBin, Fin.castLE_inj] using hleftBin i
    · have hne : ∀ a : A, paddedLeftBin a ≠ j := by
        intro a ha
        exact hj ⟨leftBin a, ha⟩
      simp [initial, hne]
  have hsumInitial :
      (∑ j : Fin m, initial j) = ∑ a : A, leftWeight a := by
    simp only [initial]
    rw [Finset.sum_comm]
    simp
  have hgreedyCapacity :
      ((∑ j : Fin m, initial j) + ∑ b : B, rightWeight b) /
            (m : ℝ) + delta ≤ 1 := by
    rw [hsumInitial]
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
    have hdiv := (div_le_div_iff_of_pos_right hmreal).2 htotal
    linarith
  obtain ⟨rightBin, hrightBin⟩ :=
    exists_assignment_above_initial_loads
      rightWeight delta hright0 Finset.univ m hm
      (fun b _hb ↦ hrightSmall b) initial hinitial (by
        simpa using hgreedyCapacity)
  let bin : A ⊕ B → Fin m
    | Sum.inl a => paddedLeftBin a
    | Sum.inr b => rightBin b
  refine ⟨bin, ?_⟩
  intro j
  have hsplit :
      (∑ x : A ⊕ B,
          if bin x = j then Sum.elim leftWeight rightWeight x else 0) =
        initial j +
          ∑ b : B, if rightBin b = j then rightWeight b else 0 := by
    simp [bin, initial]
  rw [hsplit]
  simpa using hrightBin j

end BinPackingInstance
end WeightedEdgeColoring
