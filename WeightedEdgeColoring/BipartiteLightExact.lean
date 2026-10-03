import WeightedEdgeColoring.BipartitePackets
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Finset.Prod

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable {G : WeightedMultigraph.{u}}

/-! The relation used in the block-cloning proof.  The second coordinate is
only a deterministic tie breaker; sorting by this relation gives
nonincreasing weight. -/

private def decreasingWeightRel (G : WeightedMultigraph.{u})
    (e f : G.E) : Prop :=
  G.weight f < G.weight e ∨
    (G.weight e = G.weight f ∧
      Fintype.equivFin G.E e ≤ Fintype.equivFin G.E f)

private instance (G : WeightedMultigraph.{u}) :
    IsTrans G.E G.decreasingWeightRel := ⟨by
  intro e f g hef hfg
  rcases hef with hef | ⟨hef, hidxef⟩ <;>
    rcases hfg with hfg | ⟨hfg, hidxfg⟩
  · exact Or.inl (hfg.trans hef)
  · exact Or.inl (hfg ▸ hef)
  · exact Or.inl (hef ▸ hfg)
  · exact Or.inr ⟨hef.trans hfg, hidxef.trans hidxfg⟩⟩

private instance (G : WeightedMultigraph.{u}) :
    Std.Antisymm G.decreasingWeightRel := ⟨by
  intro e f hef hfe
  rcases hef with hef | ⟨hef, hidxef⟩ <;>
    rcases hfe with hfe | ⟨hfe, hidxfe⟩
  · exact (lt_asymm hef hfe).elim
  · rw [hfe] at hef; exact (lt_irrefl _ hef).elim
  · rw [hef] at hfe; exact (lt_irrefl _ hfe).elim
  · apply (Fintype.equivFin G.E).injective
    exact le_antisymm hidxef hidxfe⟩

private instance (G : WeightedMultigraph.{u}) :
    Std.Total G.decreasingWeightRel := ⟨by
  intro e f
  rcases lt_trichotomy (G.weight e) (G.weight f) with h | h | h
  · exact Or.inr (Or.inl h)
  · by_cases hij : Fintype.equivFin G.E e ≤ Fintype.equivFin G.E f
    · exact Or.inl (Or.inr ⟨h, hij⟩)
    · exact Or.inr (Or.inr ⟨h.symm, le_of_not_ge hij⟩)
  · exact Or.inl (Or.inl h)⟩

/-- The zero-based position of an incident edge in the nonincreasing ordering
of the star at `v`.  Its value away from the star is irrelevant and chosen to
be zero. -/
noncomputable def decreasingStarRank (G : WeightedMultigraph.{u})
    (v : G.V) (e : G.E) : ℕ := by
  classical
  let S : Finset G.E := Finset.univ.filter (G.Inc v)
  exact (S.sort G.decreasingWeightRel).idxOf e

theorem decreasingStarRank_lt_degreeOn
    (G : WeightedMultigraph.{u}) {v : G.V} {e : G.E}
    (he : G.Inc v e) :
    G.decreasingStarRank v e < G.degreeOn Finset.univ v := by
  classical
  let S : Finset G.E := Finset.univ.filter (G.Inc v)
  have heS : e ∈ S := by simp [S, he]
  change (S.sort G.decreasingWeightRel).idxOf e < S.card
  rw [← Finset.length_sort G.decreasingWeightRel,
    List.idxOf_lt_length_iff]
  exact (Finset.mem_sort G.decreasingWeightRel).2 heS

theorem decreasingStarRank_injective_on_inc
    (G : WeightedMultigraph.{u}) (v : G.V) :
    Set.InjOn (G.decreasingStarRank v) {e | G.Inc v e} := by
  classical
  intro e he f hf hrank
  let S : Finset G.E := Finset.univ.filter (G.Inc v)
  have heS : e ∈ S := by simpa [S] using he
  have hfS : f ∈ S := by simpa [S] using hf
  let L := S.sort G.decreasingWeightRel
  have heL : e ∈ L := (Finset.mem_sort G.decreasingWeightRel).2 heS
  have hfL : f ∈ L := (Finset.mem_sort G.decreasingWeightRel).2 hfS
  change L.idxOf e = L.idxOf f at hrank
  exact (List.idxOf_inj heL).mp hrank

/-- The decreasing rank is a genuine enumeration of every indexed star. -/
noncomputable def decreasingStarEquiv (G : WeightedMultigraph.{u}) (v : G.V) :
    G.StarEdge v ≃ Fin (G.degreeOn Finset.univ v) := by
  classical
  let rank : G.StarEdge v → Fin (G.degreeOn Finset.univ v) := fun e ↦
    ⟨G.decreasingStarRank v e.1,
      G.decreasingStarRank_lt_degreeOn e.2⟩
  apply Equiv.ofBijective rank
  apply (Fintype.bijective_iff_injective_and_card rank).2
  constructor
  · intro e f h
    apply Subtype.ext
    apply G.decreasingStarRank_injective_on_inc v e.2 f.2
    exact congrArg Fin.val h
  · rw [Fintype.card_fin]
    change Fintype.card (G.StarEdge v) =
      (Finset.univ.filter (G.Inc v)).card
    rw [Fintype.card_subtype]

@[simp] theorem decreasingStarEquiv_apply_val
    (G : WeightedMultigraph.{u}) (v : G.V) (e : G.StarEdge v) :
    (G.decreasingStarEquiv v e).val = G.decreasingStarRank v e.1 := by
  rfl

theorem weight_anti_of_decreasingStarRank_le
    (G : WeightedMultigraph.{u}) {v : G.V} {e f : G.E}
    (he : G.Inc v e) (hf : G.Inc v f)
    (hrank : G.decreasingStarRank v e ≤ G.decreasingStarRank v f) :
    G.weight f ≤ G.weight e := by
  classical
  let S : Finset G.E := Finset.univ.filter (G.Inc v)
  have heS : e ∈ S := by simp [S, he]
  have hfS : f ∈ S := by simp [S, hf]
  by_cases hef : e = f
  · subst f; exact le_rfl
  have hranklt : G.decreasingStarRank v e < G.decreasingStarRank v f :=
    lt_of_le_of_ne hrank (fun h ↦ hef
      (G.decreasingStarRank_injective_on_inc v he hf h))
  let L := S.sort G.decreasingWeightRel
  have heL : e ∈ L := (Finset.mem_sort G.decreasingWeightRel).2 heS
  have hfL : f ∈ L := (Finset.mem_sort G.decreasingWeightRel).2 hfS
  have heget := List.getElem_idxOf ((List.idxOf_lt_length_iff).2 heL)
  have hfget := List.getElem_idxOf ((List.idxOf_lt_length_iff).2 hfL)
  have hrel := (List.pairwise_iff_getElem.mp
    (Finset.pairwise_sort S G.decreasingWeightRel))
      (L.idxOf e) (L.idxOf f)
      ((List.idxOf_lt_length_iff).2 heL)
      ((List.idxOf_lt_length_iff).2 hfL) (by simpa [decreasingStarRank, S, L] using hranklt)
  rw [heget, hfget] at hrel
  rcases hrel with h | ⟨h, _⟩
  · exact h.le
  · exact h.ge

/-- At most `q` ranks lie in any quotient block of width `q`. -/
theorem card_filter_rank_div_eq_le
    (G : WeightedMultigraph.{u}) (v : G.V) (q : ℕ) (hq : 0 < q) (k : ℕ) :
    ((Finset.univ.filter (G.Inc v)).filter
      (fun e ↦ G.decreasingStarRank v e / q = k)).card ≤ q := by
  classical
  let T := (Finset.univ.filter (G.Inc v)).filter
    (fun e ↦ G.decreasingStarRank v e / q = k)
  have hcard := Finset.card_le_card_of_injOn
    (s := T) (t := (Finset.univ : Finset (Fin q)))
    (fun e : G.E ↦ (⟨G.decreasingStarRank v e % q,
      Nat.mod_lt _ hq⟩ : Fin q))
    (by
      intro e _he
      exact Finset.mem_univ
        (⟨G.decreasingStarRank v e % q, Nat.mod_lt _ hq⟩ : Fin q))
    (by
      intro e he f hf hmod
      have heinc : G.Inc v e := (Finset.mem_filter.mp
        (Finset.mem_filter.mp he).1).2
      have hfinc : G.Inc v f := (Finset.mem_filter.mp
        (Finset.mem_filter.mp hf).1).2
      have hdiv : G.decreasingStarRank v e / q =
          G.decreasingStarRank v f / q :=
        (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
      have hmod' : G.decreasingStarRank v e % q =
          G.decreasingStarRank v f % q := congrArg Fin.val hmod
      apply G.decreasingStarRank_injective_on_inc v heinc hfinc
      calc
        G.decreasingStarRank v e =
            q * (G.decreasingStarRank v e / q) +
              G.decreasingStarRank v e % q :=
          (Nat.div_add_mod _ _).symm
        _ = q * (G.decreasingStarRank v f / q) +
              G.decreasingStarRank v f % q := by rw [hdiv, hmod']
        _ = G.decreasingStarRank v f := Nat.div_add_mod _ _)
  simpa [T] using hcard

/-- The analytic core of the block-cloning argument.  For a nonincreasing
nonnegative sequence, a set containing at most one index from every block of
`q` consecutive indices has weight at most the first term plus `1/q` of the
total weight. -/
theorem sum_le_head_add_average_of_div_inj
    (n q : ℕ) (hq : 0 < q) (w : Fin n → ℝ)
    (hw0 : ∀ i, 0 ≤ w i)
    (hanti : ∀ i j : Fin n, i ≤ j → w j ≤ w i)
    (S : Finset (Fin n))
    (hinj : ∀ i ∈ S, ∀ j ∈ S, i.val / q = j.val / q → i = j) :
    ∑ i ∈ S, w i ≤
      (if hn : 0 < n then w ⟨0, hn⟩ else 0) +
        (∑ i : Fin n, w i) / q := by
  classical
  by_cases hn : 0 < n
  · let S0 := S.filter (fun i ↦ i.val / q = 0)
    let Sp := S.filter (fun i ↦ i.val / q ≠ 0)
    have hsplit : S0 ∪ Sp = S := by
      ext i
      simp only [S0, Sp, Finset.mem_union, Finset.mem_filter]
      tauto
    have hdisj : Disjoint S0 Sp := by
      rw [Finset.disjoint_left]
      intro i hi0 hip
      exact (Finset.mem_filter.mp hip).2 (Finset.mem_filter.mp hi0).2
    have hcard0 : S0.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro i hi j hj
      exact hinj i (Finset.mem_filter.mp hi).1 j
        (Finset.mem_filter.mp hj).1
        ((Finset.mem_filter.mp hi).2.trans
          (Finset.mem_filter.mp hj).2.symm)
    have hsum0 : ∑ i ∈ S0, w i ≤ w ⟨0, hn⟩ := by
      calc
        ∑ i ∈ S0, w i ≤ ∑ _i ∈ S0, w ⟨0, hn⟩ := by
          apply Finset.sum_le_sum
          intro i hi
          apply hanti ⟨0, hn⟩ i
          exact Nat.zero_le i.val
        _ = (S0.card : ℝ) * w ⟨0, hn⟩ := by simp
        _ ≤ 1 * w ⟨0, hn⟩ := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hcard0
          · exact hw0 ⟨0, hn⟩
        _ = w ⟨0, hn⟩ := one_mul _
    let charge : Fin n × Fin q → Fin n := fun x ↦
      if hk : 0 < x.1.val / q then
        ⟨q * (x.1.val / q - 1) + x.2.val, by
          obtain ⟨k, hkval⟩ := Nat.exists_eq_succ_of_ne_zero
            (Nat.ne_of_gt hk)
          have ht : q * k + x.2.val < q * k + q :=
            Nat.add_lt_add_left x.2.isLt (q * k)
          have hle : q * (x.1.val / q) ≤ x.1.val := by
            simpa [Nat.mul_comm] using Nat.div_mul_le_self x.1.val q
          rw [hkval] at hle ⊢
          exact (by
            have := (lt_of_lt_of_le ht hle).trans x.1.isLt
            simpa [Nat.mul_succ] using this)⟩
      else x.1
    let T : Finset (Fin n × Fin q) := Sp.product Finset.univ
    have hcharge_lt (x : Fin n × Fin q) (hx : x ∈ T) :
        (charge x).val < x.1.val := by
      have hxSp : x.1 ∈ Sp := (Finset.mem_product.mp hx).1
      have hk : 0 < x.1.val / q := Nat.pos_of_ne_zero
        (Finset.mem_filter.mp hxSp).2
      simp only [charge, dif_pos hk]
      obtain ⟨k, hkval⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hk)
      have ht : q * k + x.2.val < q * k + q :=
        Nat.add_lt_add_left x.2.isLt (q * k)
      have hle : q * (x.1.val / q) ≤ x.1.val := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self x.1.val q
      rw [hkval] at hle ⊢
      simpa [Nat.mul_succ] using ht.trans_le hle
    have hcharge_inj : Set.InjOn charge T := by
      intro x hx y hy hxy
      have hxSp : x.1 ∈ Sp := (Finset.mem_product.mp hx).1
      have hySp : y.1 ∈ Sp := (Finset.mem_product.mp hy).1
      have hkx : 0 < x.1.val / q := Nat.pos_of_ne_zero
        (Finset.mem_filter.mp hxSp).2
      have hky : 0 < y.1.val / q := Nat.pos_of_ne_zero
        (Finset.mem_filter.mp hySp).2
      have hval := congrArg Fin.val hxy
      simp only [charge, dif_pos hkx, dif_pos hky] at hval
      have hmod : x.2.val = y.2.val := by
        have := congrArg (fun z : ℕ ↦ z % q) hval
        simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt x.2.isLt,
          Nat.mod_eq_of_lt y.2.isLt] using this
      have hdivsub : x.1.val / q - 1 = y.1.val / q - 1 := by
        have := congrArg (fun z : ℕ ↦ z / q) hval
        simpa [Nat.mul_add_div hq, Nat.div_eq_of_lt x.2.isLt,
          Nat.div_eq_of_lt y.2.isLt] using this
      have hdiv : x.1.val / q = y.1.val / q := by omega
      have hfirst : x.1 = y.1 := hinj x.1
        (Finset.mem_filter.mp hxSp).1 y.1
        (Finset.mem_filter.mp hySp).1 hdiv
      have hsecond : x.2 = y.2 := Fin.ext hmod
      exact Prod.ext hfirst hsecond
    have hcharged : q * (∑ i ∈ Sp, w i) ≤ ∑ i : Fin n, w i := by
      calc
        q * (∑ i ∈ Sp, w i) =
            ∑ i ∈ Sp, ∑ _j : Fin q, w i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          simp
        _ = ∑ x ∈ T, w x.1 := by
          simp [T, Finset.sum_product]
        _ ≤ ∑ x ∈ T, w (charge x) := by
          apply Finset.sum_le_sum
          intro x hx
          exact hanti (charge x) x.1 (Nat.le_of_lt (hcharge_lt x hx))
        _ = ∑ i ∈ T.image charge, w i := by
          rw [Finset.sum_image hcharge_inj]
        _ ≤ ∑ i : Fin n, w i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro i _hi _hnot
          exact hw0 i
    have hsp : ∑ i ∈ Sp, w i ≤ (∑ i : Fin n, w i) / q := by
      have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
      rw [le_div_iff₀ hqreal]
      simpa [Nat.cast_ofNat, mul_comm] using hcharged
    rw [← hsplit, Finset.sum_union hdisj]
    rw [dif_pos hn]
    exact (add_le_add hsum0 hsp)
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hS : S = ∅ := by
      ext i
      exact Fin.elim0 i
    simp [hS]

/-- A coloring whose equal-colored incident edges occupy different rank
blocks has the standard `largest item + average` load bound. -/
theorem colorLoad_le_half_add_average_of_block_injective
    (G : WeightedMultigraph.{u}) (q : ℕ) (hq : 0 < q)
    (color : G.E → Fin q) (v : G.V)
    (hhalf : ∀ e, G.weight e ≤ (1 / 2 : ℝ))
    (hblock : ∀ e f, G.Inc v e → G.Inc v f →
      color e = color f →
      G.decreasingStarRank v e / q = G.decreasingStarRank v f / q →
      e = f) :
    ∀ i, G.colorLoad color v i ≤
      (1 / 2 : ℝ) + G.starWeight v / q := by
  classical
  intro i
  let d := G.degreeOn Finset.univ v
  let E := G.decreasingStarEquiv v
  let w : Fin d → ℝ := fun j ↦ G.weight (E.symm j).1
  let S : Finset (Fin d) := Finset.univ.filter fun j ↦
    color (E.symm j).1 = i
  have hw0 : ∀ j, 0 ≤ w j := fun j ↦ G.weight_nonneg _
  have hanti : ∀ a b : Fin d, a ≤ b → w b ≤ w a := by
    intro a b hab
    apply G.weight_anti_of_decreasingStarRank_le
      (E.symm a).2 (E.symm b).2
    have ha := congrArg Fin.val (E.apply_symm_apply a)
    have hb := congrArg Fin.val (E.apply_symm_apply b)
    have ha' : G.decreasingStarRank v (E.symm a).1 = a.val := by
      simpa only [E, decreasingStarEquiv_apply_val] using ha
    have hb' : G.decreasingStarRank v (E.symm b).1 = b.val := by
      simpa only [E, decreasingStarEquiv_apply_val] using hb
    omega
  have hSinj : ∀ a ∈ S, ∀ b ∈ S,
      a.val / q = b.val / q → a = b := by
    intro a ha b hb hab
    have hca : color (E.symm a).1 = i := (Finset.mem_filter.mp ha).2
    have hcb : color (E.symm b).1 = i := (Finset.mem_filter.mp hb).2
    have hra := congrArg Fin.val (E.apply_symm_apply a)
    have hrb := congrArg Fin.val (E.apply_symm_apply b)
    have hra' : G.decreasingStarRank v (E.symm a).1 = a.val := by
      simpa only [E, decreasingStarEquiv_apply_val] using hra
    have hrb' : G.decreasingStarRank v (E.symm b).1 = b.val := by
      simpa only [E, decreasingStarEquiv_apply_val] using hrb
    apply E.symm.injective
    apply Subtype.ext
    apply hblock (E.symm a).1 (E.symm b).1
      (E.symm a).2 (E.symm b).2 (hca.trans hcb.symm)
    rw [hra', hrb']
    exact hab
  have hseq := sum_le_head_add_average_of_div_inj d q hq w hw0 hanti S hSinj
  have hselected : G.colorLoad color v i = ∑ j ∈ S, w j := by
    unfold colorLoad
    calc
      (∑ e : G.StarEdge v,
          if color e.1 = i then G.weight e.1 else 0) =
          ∑ j : Fin d,
            if color (E.symm j).1 = i then G.weight (E.symm j).1 else 0 := by
        simpa [E, d] using (E.symm.sum_comp
          (fun e : G.StarEdge v ↦
            if color e.1 = i then G.weight e.1 else 0)).symm
      _ = ∑ j ∈ S, w j := by simp [S, w, Finset.sum_filter]
  have htotal : (∑ j : Fin d, w j) = G.starWeight v := by
    unfold starWeight
    simpa [w, E, d] using E.symm.sum_comp
      (fun e : G.StarEdge v ↦ G.weight e.1)
  rw [← hselected, htotal] at hseq
  by_cases hd : 0 < d
  · rw [dif_pos hd] at hseq
    have hhead : w ⟨0, hd⟩ ≤ (1 / 2 : ℝ) := hhalf _
    linarith
  · rw [dif_neg hd] at hseq
    linarith

/-- The clone number of an edge at one endpoint: its decreasing rank divided
by the desired palette size. -/
noncomputable def rankCloneIndex (G : WeightedMultigraph.{u})
    (q : ℕ) (v : G.V) (e : G.E) (he : G.Inc v e) :
    Fin (Fintype.card G.E + 1) := by
  classical
  refine ⟨G.decreasingStarRank v e / q, ?_⟩
  have hrank := G.decreasingStarRank_lt_degreeOn he
  have hdegree : G.degreeOn Finset.univ v ≤ Fintype.card G.E := by
    unfold degreeOn
    calc
      (Finset.univ.filter (G.Inc v)).card ≤ Finset.univ.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = Fintype.card G.E := Finset.card_univ
  have hle : G.decreasingStarRank v e / q ≤
      G.decreasingStarRank v e := Nat.div_le_self _ _
  omega

noncomputable def rankCloneLeft (G : WeightedMultigraph.{u})
    (b : G.Bipartition) (q : ℕ) (e : G.E) :
    G.V × Fin (Fintype.card G.E + 1) :=
  (b.leftEndpoint e,
    G.rankCloneIndex q (b.leftEndpoint e) e (b.leftEndpoint_inc e))

noncomputable def rankCloneRight (G : WeightedMultigraph.{u})
    (b : G.Bipartition) (q : ℕ) (e : G.E) :
    G.V × Fin (Fintype.card G.E + 1) :=
  (b.rightEndpoint e,
    G.rankCloneIndex q (b.rightEndpoint e) e (b.rightEndpoint_inc e))

theorem card_filter_rankCloneLeft_eq_le
    (G : WeightedMultigraph.{u}) (b : G.Bipartition)
    (q : ℕ) (hq : 0 < q)
    (x : G.V × Fin (Fintype.card G.E + 1)) :
    ((Finset.univ : Finset G.E).filter
      (fun e ↦ G.rankCloneLeft b q e = x)).card ≤ q := by
  classical
  let T := ((Finset.univ : Finset G.E).filter
    (G.Inc x.1)).filter
      (fun e ↦ G.decreasingStarRank x.1 e / q = x.2.val)
  calc
    ((Finset.univ : Finset G.E).filter
        (fun e ↦ G.rankCloneLeft b q e = x)).card ≤ T.card := by
      apply Finset.card_le_card
      intro e he
      have heq := (Finset.mem_filter.mp he).2
      have hv : b.leftEndpoint e = x.1 := congrArg Prod.fst heq
      have hk := congrArg (fun y ↦ y.2.val) heq
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [← hv]
        exact b.leftEndpoint_inc e
      · simpa [rankCloneLeft, rankCloneIndex, hv] using hk
    _ ≤ q := G.card_filter_rank_div_eq_le x.1 q hq x.2.val

theorem card_filter_rankCloneRight_eq_le
    (G : WeightedMultigraph.{u}) (b : G.Bipartition)
    (q : ℕ) (hq : 0 < q)
    (x : G.V × Fin (Fintype.card G.E + 1)) :
    ((Finset.univ : Finset G.E).filter
      (fun e ↦ G.rankCloneRight b q e = x)).card ≤ q := by
  classical
  let T := ((Finset.univ : Finset G.E).filter
    (G.Inc x.1)).filter
      (fun e ↦ G.decreasingStarRank x.1 e / q = x.2.val)
  calc
    ((Finset.univ : Finset G.E).filter
        (fun e ↦ G.rankCloneRight b q e = x)).card ≤ T.card := by
      apply Finset.card_le_card
      intro e he
      have heq := (Finset.mem_filter.mp he).2
      have hv : b.rightEndpoint e = x.1 := congrArg Prod.fst heq
      have hk := congrArg (fun y ↦ y.2.val) heq
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [← hv]
        exact b.rightEndpoint_inc e
      · simpa [rankCloneRight, rankCloneIndex, hv] using hk
    _ ≤ q := G.card_filter_rank_div_eq_le x.1 q hq x.2.val

/-- Kőnig coloring of the rank-block clone graph.  Equal-colored incident
edges at an original vertex necessarily lie in different rank blocks. -/
theorem exists_color_block_injective
    (G : WeightedMultigraph.{u}) (b : G.Bipartition)
    (q : ℕ) (hq : 0 < q) :
    ∃ color : G.E → Fin q, ∀ v e f,
      G.Inc v e → G.Inc v f → color e = color f →
      G.decreasingStarRank v e / q = G.decreasingStarRank v f / q →
      e = f := by
  classical
  obtain ⟨color, hproper⟩ :=
    OrdinaryEdgeColoring.exists_finProperColoring_of_bimap_degree_le
      (G.rankCloneLeft b q) (G.rankCloneRight b q)
      Finset.univ q hq
      (G.card_filter_rankCloneLeft_eq_le b q hq)
      (G.card_filter_rankCloneRight_eq_le b q hq)
  refine ⟨color, ?_⟩
  intro v e f he hf hcolor hblock
  by_contra hef
  apply (hproper e (Finset.mem_univ _) f (Finset.mem_univ _) hef ?_) hcolor
  cases hv : b.side v with
  | false =>
      apply Or.inl
      apply Prod.ext
      · exact (b.leftEndpoint_eq_of_inc_of_side_eq_false he hv).trans
          (b.leftEndpoint_eq_of_inc_of_side_eq_false hf hv).symm
      · apply Fin.ext
        simpa [rankCloneLeft, rankCloneIndex,
          b.leftEndpoint_eq_of_inc_of_side_eq_false he hv,
          b.leftEndpoint_eq_of_inc_of_side_eq_false hf hv] using hblock
  | true =>
      apply Or.inr
      apply Prod.ext
      · exact (b.rightEndpoint_eq_of_inc_of_side_eq_true he hv).trans
          (b.rightEndpoint_eq_of_inc_of_side_eq_true hf hv).symm
      · apply Fin.ext
        simpa [rankCloneRight, rankCloneIndex,
          b.rightEndpoint_eq_of_inc_of_side_eq_true he hv,
          b.rightEndpoint_eq_of_inc_of_side_eq_true hf hv] using hblock

/-- The exact coefficient-two bound for the light-edge regime.  Sorting each
star into blocks of `2 * ceil Δ_w` edges and properly coloring the bipartite
clone graph makes every color choose at most one edge per block.  The block
load estimate is then at most `1/2 + Δ_w / (2 * ceil Δ_w) ≤ 1`. -/
theorem chiW_le_two_ceil_of_le_half
    (G : WeightedMultigraph.{u}) (hbip : G.IsBipartite)
    (hhalf : ∀ e, G.weight e ≤ (1 / 2 : ℝ)) :
    G.chiW ≤ 2 * Nat.ceil G.deltaW := by
  let n := Nat.ceil G.deltaW
  have hdelta : G.deltaW ≤ n := Nat.le_ceil G.deltaW
  by_cases hn0 : n = 0
  · have hzero : G.deltaW = 0 := by
      apply le_antisymm
      · simpa [n, hn0] using hdelta
      · exact G.deltaW_nonneg
    have hz := G.hasWeightedColoring_zero_of_deltaW_eq_zero hzero
    have hchi : G.chiW ≤ 0 := G.chiW_le_of_hasWeightedColoring hz
    simpa [n, hn0] using hchi
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hq : 0 < 2 * n := Nat.mul_pos (by decide) hn
    rcases hbip with ⟨b⟩
    obtain ⟨color, hblock⟩ :=
      G.exists_color_block_injective b (2 * n) hq
    have hweighted : G.IsWeightedColoring color := by
      intro v i
      have hload := G.colorLoad_le_half_add_average_of_block_injective
        (2 * n) hq color v hhalf (hblock v) i
      have hstar : G.starWeight v ≤ n :=
        (G.starWeight_le_deltaW v).trans hdelta
      have hqreal : (0 : ℝ) < (2 * n : ℕ) := by exact_mod_cast hq
      have havg : G.starWeight v / (2 * n : ℕ) ≤ (1 / 2 : ℝ) := by
        rw [div_le_iff₀ hqreal]
        calc
          G.starWeight v ≤ (n : ℝ) := hstar
          _ = (1 / 2 : ℝ) * (2 * n : ℕ) := by
            push_cast
            ring
      linarith
    apply G.chiW_le_of_hasWeightedColoring
    simpa [n] using (show G.HasWeightedColoring (2 * n) from
      ⟨color, hweighted⟩)

end WeightedMultigraph
end WeightedEdgeColoring
