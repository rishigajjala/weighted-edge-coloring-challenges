import WeightedEdgeColoring.SubtwoK6SupportFinite
import WeightedEdgeColoring.SubtwoK6MatchingDeficits
import Mathlib.Data.Nat.Bitwise

namespace WeightedEdgeColoring.Subtwo.K6SupportBridge
open K6MatchingDeficits K6SupportFinite

def maskList : List Bool → Nat
  | [] => 0
  | b :: bs => Nat.bit b (maskList bs)

theorem maskList_lt_two_pow (bs : List Bool) : maskList bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [maskList]
  | cons b bs ih =>
      cases b <;> simp [maskList, Nat.bit, pow_succ] at * <;> omega

theorem maskList_testBit (bs : List Bool) (i : Fin bs.length) :
    (maskList bs).testBit i.val = bs[i.val] := by
  induction bs with
  | nil => exact Fin.elim0 i
  | cons b bs ih =>
      cases i using Fin.cases with
      | zero => simp [maskList, Nat.testBit_bit_zero]
      | succ j =>
          simp only [maskList, Fin.val_succ, Nat.testBit_bit_succ]
          simpa using ih j

def supportMask (b : Edge → Bool) : Fin 32768 :=
  ⟨maskList (List.ofFn b), by simpa using maskList_lt_two_pow (List.ofFn b)⟩

theorem supportMask_testBit (b : Edge → Bool) (e : Edge) :
    (supportMask b).val.testBit e.val = b e := by
  let i : Fin (List.ofFn b).length := ⟨e.val, by simpa using e.isLt⟩
  have hi := maskList_testBit (List.ofFn b) i
  simp only [List.getElem_ofFn] at hi
  simpa only [supportMask, i] using hi

theorem contains_iff_bits (s m : Nat) :
    contains s m = true ↔ ∀ i : Nat, m.testBit i = true → s.testBit i = true := by
  simp only [contains, beq_iff_eq]
  constructor
  · intro h i hi
    have hh := congrArg (fun n : Nat => n.testBit i) h
    change (s &&& m).testBit i = m.testBit i at hh
    rw [Nat.testBit_land, hi] at hh
    simpa using hh
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    change (s &&& m).testBit i = m.testBit i
    rw [Nat.testBit_land]
    cases hm : m.testBit i
    · simp [hm]
    · simp [hm, h i hm]

theorem contains_supportMask_iff (b : Edge → Bool) (m : Nat) (hm : m < 32768) :
    contains (supportMask b).val m = true ↔
      ∀ e : Edge, m.testBit e.val = true → b e = true := by
  rw [contains_iff_bits]
  constructor
  · intro h e he
    simpa only [supportMask_testBit] using h e.val he
  · intro h i hi
    by_cases hil : i < 15
    · let e : Edge := ⟨i, hil⟩
      have he := h e hi
      have hb := supportMask_testBit b e
      simpa only [e] using hb.trans he
    · have hpow : 2 ^ 15 ≤ 2 ^ i :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hf : m.testBit i = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm hpow)
      simp [hf] at hi

theorem degree_pair_cover : ∀ v : Vertex, ∀ e f : Edge,
    e ≠ f → v ∈ ends e → v ∈ ends f →
    ∃ k ∈ degreePairMasks[v.val],
      k < 32768 ∧ k.testBit e.val = true ∧ k.testBit f.val = true := by
  decide +kernel

theorem degree_pair_cover_pair_bits : ∀ v : Vertex, ∀ e f : Edge, ∀ k : Nat,
    k ∈ degreePairMasks[v.val] → e ≠ f → v ∈ ends e → v ∈ ends f →
    k.testBit e.val = true → k.testBit f.val = true →
    ∀ z : Edge, z ≠ e → z ≠ f → k.testBit z.val = false := by
  decide +kernel

theorem minDegreeTwo_of_support (b : Edge → Bool)
    (h : ∀ v : Vertex, ∃ e f : Edge,
      e ≠ f ∧ v ∈ ends e ∧ v ∈ ends f ∧ b e = true ∧ b f = true) :
    minDegreeTwo (supportMask b).val = true := by
  apply Array.all_eq_true.mpr
  intro i hi
  have hiv : i < 6 := by simpa [degreePairMasks] using hi
  let v : Vertex := ⟨i, hiv⟩
  obtain ⟨e, f, hef, hve, hvf, hbe, hbf⟩ := h v
  obtain ⟨k, hk, hkl, hke, hkf⟩ := degree_pair_cover v e f hef hve hvf
  apply Array.any_eq_true.mpr
  obtain ⟨j, hj, hkj⟩ := Array.mem_iff_getElem.mp hk
  refine ⟨j, hj, ?_⟩
  have hcontains : contains (supportMask b).val k = true := by
    apply (contains_supportMask_iff b k hkl).2
    intro z hz
    by_cases hze : z = e
    · simpa [hze] using hbe
    by_cases hzf : z = f
    · simpa [hzf] using hbf
    have hz_other : k.testBit z.val = false := by
      exact degree_pair_cover_pair_bits v e f k hk hef hve hvf hke hkf z hze hzf
    simp [hz_other] at hz
  simpa [v, hkj] using hcontains


def triangleSets : Array (Finset Vertex) := #[
  {0, 1, 2},
  {0, 1, 3},
  {0, 1, 4},
  {0, 1, 5},
  {0, 2, 3},
  {0, 2, 4},
  {0, 2, 5},
  {0, 3, 4},
  {0, 3, 5},
  {0, 4, 5},
  {1, 2, 3},
  {1, 2, 4},
  {1, 2, 5},
  {1, 3, 4},
  {1, 3, 5},
  {1, 4, 5},
  {2, 3, 4},
  {2, 3, 5},
  {2, 4, 5},
  {3, 4, 5}]

theorem triangleSets_card : ∀ t : Fin 20, triangleSets[t].card = 3 := by
  decide +kernel

theorem triangleSets_complete : ∀ S : Finset Vertex, S.card = 3 →
    ∃ t : Fin 20, triangleSets[t] = S := by
  decide +kernel

def Crosses (S : Finset Vertex) (e : Edge) : Prop :=
  (ends e ∩ S).card = 1

theorem triangleCuts_size : ∀ t : Fin 20, (triangleCuts[t]).2.size = 36 := by
  decide +kernel

def trianglePair (t : Fin 20) (j : Fin 36) : Nat :=
  (triangleCuts[t]).2[j.val]'(by rw [triangleCuts_size]; exact j.isLt)

theorem triangle_cross_pair_cover : ∀ t : Fin 20, ∀ e f : Edge,
    e ≠ f → Crosses triangleSets[t] e → Crosses triangleSets[t] f →
    ∃ j : Fin 36, let k := trianglePair t j;
      k < 32768 ∧ k.testBit e.val = true ∧ k.testBit f.val = true := by
  unfold Crosses
  decide +kernel

def pairBits (k : Nat) : Finset Edge :=
  Finset.univ.filter (fun e => k.testBit e.val = true)

theorem trianglePair_bits_card : ∀ t : Fin 20, ∀ j : Fin 36,
    (pairBits (trianglePair t j)).card = 2 := by
  decide +kernel

theorem triangle_pair_only_bits (t : Fin 20) (j : Fin 36) (e f z : Edge)
    (hef : e ≠ f) (he : (trianglePair t j).testBit e.val = true)
    (hf : (trianglePair t j).testBit f.val = true)
    (hze : z ≠ e) (hzf : z ≠ f) :
    (trianglePair t j).testBit z.val = false := by
  have hsubset : ({e, f} : Finset Edge) ⊆ pairBits (trianglePair t j) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl <;> simp [pairBits, he, hf]
  have hcard : (pairBits (trianglePair t j)).card ≤ ({e, f} : Finset Edge).card := by
    rw [trianglePair_bits_card t j]
    simp [hef]
  have heq := Finset.eq_of_subset_of_card_le hsubset hcard
  have hz : z ∉ pairBits (trianglePair t j) := by
    rw [← heq]
    simp [hze, hzf]
  have hfz : (trianglePair t j).testBit z.val ≠ true := by
    simpa [pairBits] using hz
  exact Bool.eq_false_iff.mpr hfz

theorem hasNarrowTriangle_witness (b : Edge → Bool)
    (h : hasNarrowTriangle (supportMask b).val = true) :
    ∃ t : Fin 20, ∀ e f : Edge,
      e ≠ f → Crosses triangleSets[t] e → Crosses triangleSets[t] f →
      b e = true → b f = true → False := by
  obtain ⟨i, hi, hc⟩ := Array.any_eq_true.mp h
  have hit : i < 20 := by simpa [triangleCuts] using hi
  let t : Fin 20 := ⟨i, hit⟩
  have hcut : ((triangleCuts[t]).2).all
      (fun pair => !contains (supportMask b).val pair) = true := by
    have hrow : (contains (supportMask b).val (triangleCuts[t]).1 &&
      (triangleCuts[t]).2.all (fun pair => !contains (supportMask b).val pair)) = true := by
      simpa [hasNarrowTriangle, t] using hc
    exact (Bool.and_eq_true_iff.mp hrow).2
  refine ⟨t, ?_⟩
  intro e f hef hce hcf hbe hbf
  obtain ⟨j, hkl, hke, hkf⟩ := triangle_cross_pair_cover t e f hef hce hcf
  let k : Nat := trianglePair t j
  have hcontains : contains (supportMask b).val k = true := by
    apply (contains_supportMask_iff b k hkl).2
    intro z hz
    by_cases hze : z = e
    · simpa [hze] using hbe
    by_cases hzf : z = f
    · simpa [hzf] using hbf
    have hz_other := triangle_pair_only_bits t j e f z hef hke hkf hze hzf
    simp [k, hz_other] at hz
  have hj : j.val < (triangleCuts[t]).2.size := by rw [triangleCuts_size]; exact j.isLt
  have hno := (Array.all_eq_true.mp hcut) j.val hj
  change (!contains (supportMask b).val k) = true at hno
  simp [hcontains] at hno

end WeightedEdgeColoring.Subtwo.K6SupportBridge
