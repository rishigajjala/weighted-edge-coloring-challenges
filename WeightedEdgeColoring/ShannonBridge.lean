import WeightedEdgeColoring.GeneralThree
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators
open Function

namespace OrdinaryEdgeColoring

theorem exists_equiv_of_regular_relation
    {L R : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (adj : L → R → Prop) [DecidableRel adj]
    (k : ℕ) (hk : 0 < k)
    (hL : ∀ l, (Finset.univ.filter (adj l)).card = k)
    (hR : ∀ r, (Finset.univ.filter (fun l ↦ adj l r)).card = k) :
    ∃ f : L ≃ R, ∀ l, adj l (f l) := by
  classical
  let t : L → Finset R := fun l ↦ Finset.univ.filter (adj l)
  have hHall : ∀ s : Finset L, s.card ≤ (s.biUnion t).card := by
    intro s
    let N : Finset R := s.biUnion t
    have hdouble :
        ∑ l ∈ s, (t l).card =
          ∑ r ∈ N, (s.filter (fun l ↦ adj l r)).card := by
      calc
        ∑ l ∈ s, (t l).card =
            ∑ l ∈ s, ∑ r ∈ N, if adj l r then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro l hls
              have hfilter : N.filter (adj l) = t l := by
                ext r
                simp only [N, t, Finset.mem_filter, Finset.mem_biUnion,
                  Finset.mem_univ, true_and]
                constructor
                · exact fun h ↦ h.2
                · exact fun h ↦ ⟨⟨l, hls, h⟩, h⟩
              rw [← hfilter]
              simp
        _ = ∑ r ∈ N, ∑ l ∈ s, if adj l r then 1 else 0 := by
              rw [Finset.sum_comm]
        _ = ∑ r ∈ N, (s.filter (fun l ↦ adj l r)).card := by
              apply Finset.sum_congr rfl
              intro r hr
              simp
    have hleft : ∑ l ∈ s, (t l).card = s.card * k := by
      simp [t, hL]
    have hright :
        ∑ r ∈ N, (s.filter (fun l ↦ adj l r)).card ≤ N.card * k := by
      calc
        ∑ r ∈ N, (s.filter (fun l ↦ adj l r)).card ≤
            ∑ _r ∈ N, k := by
              apply Finset.sum_le_sum
              intro r hr
              calc
                (s.filter (fun l ↦ adj l r)).card ≤
                    (Finset.univ.filter (fun l ↦ adj l r)).card := by
                      apply Finset.card_le_card
                      exact Finset.filter_subset_filter _ (Finset.subset_univ _)
                _ = k := hR r
        _ = N.card * k := by simp
    have hmul : s.card * k ≤ N.card * k := by
      rw [← hleft, hdouble]
      exact hright
    exact Nat.le_of_mul_le_mul_right hmul hk
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall
  have hcard : Fintype.card L = Fintype.card R := by
    have hsumL : Fintype.card L * k =
        ∑ l : L, (Finset.univ.filter (adj l)).card := by simp [hL]
    have hsumR : Fintype.card R * k =
        ∑ r : R, (Finset.univ.filter (fun l ↦ adj l r)).card := by simp [hR]
    have hdouble :
        ∑ l : L, (Finset.univ.filter (adj l)).card =
          ∑ r : R, (Finset.univ.filter (fun l ↦ adj l r)).card := by
      calc
        ∑ l : L, (Finset.univ.filter (adj l)).card =
            ∑ l : L, ∑ r : R, if adj l r then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro l hl
              simp
        _ = ∑ r : R, ∑ l : L, if adj l r then 1 else 0 := by
              rw [Finset.sum_comm]
        _ = ∑ r : R, (Finset.univ.filter (fun l ↦ adj l r)).card := by
              apply Finset.sum_congr rfl
              intro r hr
              simp
    apply Nat.eq_of_mul_eq_mul_right hk
    rw [hsumL, hdouble, ← hsumR]
  have hf_bij : Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, hcard⟩
  let e : L ≃ R := Equiv.ofBijective f hf_bij
  exact ⟨e, fun l ↦ by simpa [e, t] using hf_mem l⟩

/-- A positive regular indexed bipartite multigraph has a perfect matching.
Parallel edge indices are retained in `F`. -/
theorem exists_perfectMatching_of_regular_bimap
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (left right : E → V) (F : Finset E)
    (k : ℕ) (hk : 0 < k)
    (hleft : ∀ v, (F.filter (fun e ↦ left e = v)).card = k)
    (hright : ∀ v, (F.filter (fun e ↦ right e = v)).card = k) :
    ∃ M : Finset E, M ⊆ F ∧
      (∀ v, (M.filter (fun e ↦ left e = v)).card = 1) ∧
      (∀ v, (M.filter (fun e ↦ right e = v)).card = 1) := by
  classical
  let t : V → Finset V := fun v ↦
    Finset.univ.filter (fun w ↦ ∃ e ∈ F, left e = v ∧ right e = w)
  have hHall : ∀ s : Finset V, s.card ≤ (s.biUnion t).card := by
    intro s
    let N : Finset V := s.biUnion t
    let O : Finset E := F.filter (fun e ↦ left e ∈ s)
    have hOleft : O.card = s.card * k := by
      calc
        O.card = ∑ e ∈ F, if left e ∈ s then 1 else 0 := by
          simp [O]
        _ = ∑ e ∈ F, ∑ v ∈ s, if left e = v then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro e he
          simp
        _ = ∑ v ∈ s, ∑ e ∈ F, if left e = v then 1 else 0 := by
          rw [Finset.sum_comm]
        _ = ∑ v ∈ s, (F.filter (fun e ↦ left e = v)).card := by
          apply Finset.sum_congr rfl
          intro v hv
          simp
        _ = s.card * k := by simp [hleft]
    have hOright : O.card ≤ N.card * k := by
      calc
        O.card = ∑ e ∈ O, ∑ w ∈ N, if right e = w then 1 else 0 := by
          rw [Finset.card_eq_sum_ones]
          apply Finset.sum_congr rfl
          intro e heO
          have heO' := Finset.mem_filter.mp heO
          have heN : right e ∈ N := by
            apply Finset.mem_biUnion.mpr
            refine ⟨left e, heO'.2, ?_⟩
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_univ _, ⟨e, heO'.1, rfl, rfl⟩⟩
          simp [heN]
        _ = ∑ w ∈ N, ∑ e ∈ O, if right e = w then 1 else 0 := by
          rw [Finset.sum_comm]
        _ = ∑ w ∈ N, (O.filter (fun e ↦ right e = w)).card := by
          apply Finset.sum_congr rfl
          intro w hw
          simp
        _ ≤ ∑ _w ∈ N, k := by
          apply Finset.sum_le_sum
          intro w hw
          calc
            (O.filter (fun e ↦ right e = w)).card ≤
                (F.filter (fun e ↦ right e = w)).card := by
                  apply Finset.card_le_card
                  exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
            _ = k := hright w
        _ = N.card * k := by simp
    have hmul : s.card * k ≤ N.card * k := by
      rw [← hOleft]
      exact hOright
    exact Nat.le_of_mul_le_mul_right hmul hk
  obtain ⟨mate, hmate_inj, hmate_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall
  have hedge_exists (v : V) :
      ∃ e ∈ F, left e = v ∧ right e = mate v := by
    simpa [t] using hmate_mem v
  choose edge hedgeF hedgeleft hedgeright using hedge_exists
  have hedge_inj : Injective edge := by
    intro u v huv
    simpa [hedgeleft] using congrArg left huv
  let M : Finset E := Finset.univ.image edge
  refine ⟨M, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_image.mp he with ⟨v, _hv, rfl⟩
    exact hedgeF v
  · intro v
    have hset : M.filter (fun e ↦ left e = v) = {edge v} := by
      ext e
      simp only [M, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
        true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨u, rfl⟩, hu⟩
        have : u = v := by simpa [hedgeleft] using hu
        simpa [this]
      · rintro rfl
        exact ⟨⟨v, rfl⟩, hedgeleft v⟩
    rw [hset]
    simp
  · intro v
    have hsurj : Surjective mate :=
      hmate_inj.surjective_of_finite (Equiv.refl V)
    obtain ⟨u, rfl⟩ := hsurj v
    have hset : M.filter (fun e ↦ right e = mate u) = {edge u} := by
      ext e
      simp only [M, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
        true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨z, rfl⟩, hz⟩
        have : z = u := hmate_inj (by simpa [hedgeright] using hz)
        simpa [this]
      · rintro rfl
        exact ⟨⟨u, rfl⟩, hedgeright u⟩
    rw [hset]
    simp

/-- `c` is a proper edge coloring of the indexed bipartite multigraph
described by `left` and `right`, restricted to the physical edge set `F`. -/
def BimapProperOn
    {V E C : Type*} (left right : E → V) (F : Finset E) (c : E → C) : Prop :=
  ∀ e, e ∈ F → ∀ f, f ∈ F → e ≠ f →
    (left e = left f ∨ right e = right f) → c e ≠ c f

/-- Every finite `k`-regular indexed bipartite multigraph has a proper
`k`-edge-coloring.  The colors are first represented by natural numbers
strictly below `k`; this makes the empty induction case independent of edges
outside `F`. -/
theorem exists_natProperColoring_of_regular_bimap
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (left right : E → V) (F : Finset E) (k : ℕ)
    (hleft : ∀ v, (F.filter (fun e ↦ left e = v)).card = k)
    (hright : ∀ v, (F.filter (fun e ↦ right e = v)).card = k) :
    ∃ c : E → ℕ, (∀ e ∈ F, c e < k) ∧ BimapProperOn left right F c := by
  classical
  induction k generalizing F with
  | zero =>
      have hF : F = ∅ := by
        ext e
        constructor
        · intro heF
          have he : e ∈ F.filter (fun x ↦ left x = left e) :=
            Finset.mem_filter.mpr ⟨heF, rfl⟩
          have hz := hleft (left e)
          rw [Finset.card_eq_zero] at hz
          simpa [hz] using he
        · simp
      refine ⟨fun _ ↦ 0, ?_, ?_⟩
      · intro e he
        simpa [hF] using he
      · simp [BimapProperOn, hF]
  | succ k ih =>
      obtain ⟨M, hMF, hMleft, hMright⟩ :=
        exists_perfectMatching_of_regular_bimap left right F (k + 1)
          (Nat.zero_lt_succ k) hleft hright
      let R : Finset E := F \ M
      have hRleft : ∀ v, (R.filter (fun e ↦ left e = v)).card = k := by
        intro v
        have hset :
            R.filter (fun e ↦ left e = v) =
              (F.filter (fun e ↦ left e = v)) \
                (M.filter (fun e ↦ left e = v)) := by
          ext e
          simp only [Finset.mem_filter, R, Finset.mem_sdiff]
          constructor
          · rintro ⟨⟨heF, heM⟩, hp⟩
            exact ⟨⟨heF, hp⟩, fun h ↦ heM h.1⟩
          · rintro ⟨⟨heF, hp⟩, hnot⟩
            exact ⟨⟨heF, fun heM ↦ hnot ⟨heM, hp⟩⟩, hp⟩
        have hsub :
            M.filter (fun e ↦ left e = v) ⊆
              F.filter (fun e ↦ left e = v) :=
          Finset.filter_subset_filter _ hMF
        rw [hset, Finset.card_sdiff_of_subset hsub, hleft v, hMleft v]
        simp
      have hRright : ∀ v, (R.filter (fun e ↦ right e = v)).card = k := by
        intro v
        have hset :
            R.filter (fun e ↦ right e = v) =
              (F.filter (fun e ↦ right e = v)) \
                (M.filter (fun e ↦ right e = v)) := by
          ext e
          simp only [Finset.mem_filter, R, Finset.mem_sdiff]
          constructor
          · rintro ⟨⟨heF, heM⟩, hp⟩
            exact ⟨⟨heF, hp⟩, fun h ↦ heM h.1⟩
          · rintro ⟨⟨heF, hp⟩, hnot⟩
            exact ⟨⟨heF, fun heM ↦ hnot ⟨heM, hp⟩⟩, hp⟩
        have hsub :
            M.filter (fun e ↦ right e = v) ⊆
              F.filter (fun e ↦ right e = v) :=
          Finset.filter_subset_filter _ hMF
        rw [hset, Finset.card_sdiff_of_subset hsub, hright v, hMright v]
        simp
      obtain ⟨cR, hcRbound, hcRproper⟩ := ih R hRleft hRright
      let c : E → ℕ := fun e ↦ if e ∈ M then k else cR e
      have hleft_unique : ∀ e f, e ∈ M → f ∈ M →
          left e = left f → e = f := by
        intro e f he hf hef
        apply (Finset.card_le_one.mp (by rw [hMleft (left e)])) e
        · exact Finset.mem_filter.mpr ⟨he, rfl⟩
        · exact Finset.mem_filter.mpr ⟨hf, hef.symm⟩
      have hright_unique : ∀ e f, e ∈ M → f ∈ M →
          right e = right f → e = f := by
        intro e f he hf hef
        apply (Finset.card_le_one.mp (by rw [hMright (right e)])) e
        · exact Finset.mem_filter.mpr ⟨he, rfl⟩
        · exact Finset.mem_filter.mpr ⟨hf, hef.symm⟩
      refine ⟨c, ?_, ?_⟩
      · intro e heF
        by_cases heM : e ∈ M
        · simp [c, heM]
        · have heR : e ∈ R := by simp [R, heF, heM]
          exact Nat.lt.step (by simpa [c, heM] using hcRbound e heR)
      · intro e heF f hfF hef hconflict
        by_cases heM : e ∈ M
        · by_cases hfM : f ∈ M
          · exfalso
            apply hef
            rcases hconflict with hleftEq | hrightEq
            · exact hleft_unique e f heM hfM hleftEq
            · exact hright_unique e f heM hfM hrightEq
          · have hfR : f ∈ R := by simp [R, hfF, hfM]
            have hlt : cR f < k := hcRbound f hfR
            simp [c, heM, hfM, Nat.ne_of_gt hlt]
        · by_cases hfM : f ∈ M
          · have heR : e ∈ R := by simp [R, heF, heM]
            have hlt : cR e < k := hcRbound e heR
            simp [c, heM, hfM, Nat.ne_of_lt hlt]
          · have heR : e ∈ R := by simp [R, heF, heM]
            have hfR : f ∈ R := by simp [R, hfF, hfM]
            simpa [c, heM, hfM] using hcRproper e heR f hfR hef hconflict

/-- Finite-type form of bipartite one-factorization. -/
theorem exists_finProperColoring_of_regular_bimap
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (left right : E → V) (F : Finset E) (k : ℕ) (hk : 0 < k)
    (hleft : ∀ v, (F.filter (fun e ↦ left e = v)).card = k)
    (hright : ∀ v, (F.filter (fun e ↦ right e = v)).card = k) :
    ∃ c : E → Fin k, BimapProperOn left right F c := by
  classical
  obtain ⟨c, hcbound, hcproper⟩ :=
    exists_natProperColoring_of_regular_bimap left right F k hleft hright
  let cFin : E → Fin k := fun e ↦
    if he : e ∈ F then ⟨c e, hcbound e he⟩ else ⟨0, hk⟩
  refine ⟨cFin, ?_⟩
  intro e heF f hfF hef hconflict hEq
  apply hcproper e heF f hfF hef hconflict
  have hval := congrArg (fun z : Fin k ↦ z.val) hEq
  simpa [cFin, heF, hfF] using hval

theorem card_slot_neighbors_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (a b : V) (hab : a ≠ b) :
    ((Finset.univ : Finset (V × Fin r)).filter
      (fun s ↦ a = s.1 ∨ b = s.1)).card = 2 * r := by
  have hset :
      (Finset.univ : Finset (V × Fin r)).filter
        (fun s ↦ a = s.1 ∨ b = s.1) =
      ({a, b} : Finset V) ×ˢ (Finset.univ : Finset (Fin r)) := by
    ext x
    simp [eq_comm]
  rw [hset, Finset.card_product]
  simp [hab]

theorem card_equiv_symm_fst_fiber
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (r : ℕ) (f : (V × Fin r) ≃ E) (v : V) :
    ((Finset.univ : Finset E).filter
      (fun e ↦ (f.symm e).1 = v)).card = r := by
  let S : Finset E := Finset.univ.filter (fun e ↦ (f.symm e).1 = v)
  calc
    S.card = (Finset.univ : Finset (Fin r)).card := by
      apply Finset.card_bij (fun e _he ↦ (f.symm e).2)
      · intro e he
        simp
      · intro e he e' he' hsecond
        apply f.symm.injective
        apply Prod.ext
        · exact (Finset.mem_filter.mp he).2.trans
            (Finset.mem_filter.mp he').2.symm
        · exact hsecond
      · intro i hi
        refine ⟨f (v, i), ?_, ?_⟩
        · simp [S]
        · simp
    _ = r := by simp

/-- A loopless `2r`-regular indexed multigraph admits an orientation with
indegree and outdegree both `r`.  The proof assigns its physical edges to
`r` slots at each vertex by Hall's theorem. -/
theorem exists_balanced_orientation_of_even_regular
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (a b : E → V) (r : ℕ) (hr : 0 < r)
    (hloop : ∀ e, a e ≠ b e)
    (hreg : ∀ v, ((Finset.univ : Finset E).filter
      (fun e ↦ a e = v ∨ b e = v)).card = 2 * r) :
    ∃ tail head : E → V,
      (∀ e, (tail e = a e ∧ head e = b e) ∨
        (tail e = b e ∧ head e = a e)) ∧
      (∀ v, ((Finset.univ : Finset E).filter
        (fun e ↦ head e = v)).card = r) ∧
      (∀ v, ((Finset.univ : Finset E).filter
        (fun e ↦ tail e = v)).card = r) := by
  classical
  let adj : (V × Fin r) → E → Prop := fun s e ↦
    a e = s.1 ∨ b e = s.1
  have hslot : ∀ s, ((Finset.univ : Finset E).filter
      (adj s)).card = 2 * r := by
    intro s
    exact hreg s.1
  have hedge : ∀ e, ((Finset.univ : Finset (V × Fin r)).filter
      (fun s ↦ adj s e)).card = 2 * r := by
    intro e
    exact card_slot_neighbors_of_ne r (a e) (b e) (hloop e)
  obtain ⟨f, hf⟩ := exists_equiv_of_regular_relation adj (2 * r)
    (Nat.mul_pos (by decide) hr) hslot hedge
  let head : E → V := fun e ↦ (f.symm e).1
  let tail : E → V := fun e ↦
    if head e = a e then b e else a e
  have hinc : ∀ e, a e = head e ∨ b e = head e := by
    intro e
    simpa [adj, head] using hf (f.symm e)
  have hendpoints : ∀ e, (tail e = a e ∧ head e = b e) ∨
      (tail e = b e ∧ head e = a e) := by
    intro e
    by_cases ha : head e = a e
    · exact Or.inr ⟨by simp [tail, ha], ha⟩
    · have hb : head e = b e := by
        exact (hinc e).resolve_left (Ne.symm ha) |>.symm
      exact Or.inl ⟨by simp [tail, ha], hb⟩
  have hhead : ∀ v, ((Finset.univ : Finset E).filter
      (fun e ↦ head e = v)).card = r := by
    intro v
    exact card_equiv_symm_fst_fiber r f v
  have htail_iff : ∀ e v, tail e = v ↔
      (a e = v ∨ b e = v) ∧ head e ≠ v := by
    intro e v
    by_cases ha : head e = a e
    · constructor
      · intro htv
        have hbv : b e = v := by simpa [tail, ha] using htv
        refine ⟨Or.inr hbv, ?_⟩
        intro hhv
        apply hloop e
        exact ha.symm.trans (hhv.trans hbv.symm)
      · rintro ⟨hav | hbv, hhv⟩
        · exact (hhv (ha.trans hav)).elim
        · simpa [tail, ha] using hbv
    · have hb : head e = b e := by
        exact (hinc e).resolve_left (Ne.symm ha) |>.symm
      constructor
      · intro htv
        have hav : a e = v := by simpa [tail, ha] using htv
        refine ⟨Or.inl hav, ?_⟩
        intro hhv
        apply hloop e
        exact hav.trans (hhv.symm.trans hb)
      · rintro ⟨hav | hbv, hhv⟩
        · simpa [tail, ha] using hav
        · exact (hhv (hb.trans hbv)).elim
  have htail : ∀ v, ((Finset.univ : Finset E).filter
      (fun e ↦ tail e = v)).card = r := by
    intro v
    let I : Finset E := Finset.univ.filter
      (fun e ↦ a e = v ∨ b e = v)
    let H : Finset E := Finset.univ.filter (fun e ↦ head e = v)
    have hsub : H ⊆ I := by
      intro e heH
      have hev := (Finset.mem_filter.mp heH).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hinc e with hae | hbe
      · exact Or.inl (hae.trans hev)
      · exact Or.inr (hbe.trans hev)
    have hset : (Finset.univ : Finset E).filter
        (fun e ↦ tail e = v) = I \ H := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_sdiff, I, H]
      exact htail_iff e v
    rw [hset, Finset.card_sdiff_of_subset hsub]
    change I.card - H.card = r
    rw [show I.card = 2 * r by exact hreg v,
      show H.card = r by exact hhead v]
    simp [two_mul]
  exact ⟨tail, head, hendpoints, hhead, htail⟩

def ConflictProperOn
    {A C : Type*} (conflict : A → A → Prop)
    (S : Finset A) (c : A → C) : Prop :=
  ∀ e, e ∈ S → ∀ f, f ∈ S → e ≠ f →
    conflict e f → c e ≠ c f

/-- A finite conflict graph of maximum degree at most two is 3-colorable.
This is the exact small greedy lemma needed for each base-color layer in
Shannon's construction. -/
theorem exists_fin3_coloring_of_conflict_degree_le_two
    {A : Type*} [Fintype A] [DecidableEq A]
    (conflict : A → A → Prop) [DecidableRel conflict]
    (hsymm : Symmetric conflict)
    (hdeg : ∀ a, ((Finset.univ : Finset A).filter
      (conflict a)).card ≤ 2) :
    ∃ c : A → Fin 3, ConflictProperOn conflict Finset.univ c := by
  classical
  have hpartial : ∀ S : Finset A, ∃ c : A → Fin 3,
      ConflictProperOn conflict S c := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        exact ⟨fun _ ↦ 0, by simp [ConflictProperOn]⟩
    | @insert a S ha ih =>
        obtain ⟨c, hc⟩ := ih
        let forbidden : Finset (Fin 3) :=
          (S.filter (conflict a)).image c
        have hforbidden : forbidden.card ≤ 2 := by
          calc
            forbidden.card ≤ (S.filter (conflict a)).card :=
              Finset.card_image_le
            _ ≤ ((Finset.univ : Finset A).filter
                (conflict a)).card := by
              apply Finset.card_le_card
              exact Finset.filter_subset_filter _ (Finset.subset_univ S)
            _ ≤ 2 := hdeg a
        have hex : ∃ x : Fin 3, x ∉ forbidden := by
          by_contra hnone
          push_neg at hnone
          have hsub : (Finset.univ : Finset (Fin 3)) ⊆ forbidden := by
            intro x hx
            exact hnone x
          have hthree : 3 ≤ forbidden.card := by
            simpa using Finset.card_le_card hsub
          exact (by decide : ¬ (3 : ℕ) ≤ 2) (hthree.trans hforbidden)
        obtain ⟨x, hx⟩ := hex
        let c' : A → Fin 3 := fun e ↦ if e = a then x else c e
        refine ⟨c', ?_⟩
        intro e he f hf hef heconf
        simp only [Finset.mem_insert] at he hf
        rcases he with hea | heS
        · subst e
          have hfa : f ≠ a := by
            intro hfa
            apply hef
            exact hfa.symm
          have hfS : f ∈ S := hf.resolve_left hfa
          have hcf : c f ∈ forbidden := by
            apply Finset.mem_image.mpr
            exact ⟨f, Finset.mem_filter.mpr ⟨hfS, heconf⟩, rfl⟩
          simp only [c', if_pos, if_neg hfa]
          exact fun hxc ↦ hx (hxc ▸ hcf)
        · rcases hf with hfa | hfS
          · subst f
            have hea : e ≠ a := by
              intro hea
              apply hef
              exact hea
            have hce : c e ∈ forbidden := by
              apply Finset.mem_image.mpr
              exact ⟨e, Finset.mem_filter.mpr ⟨heS, hsymm heconf⟩, rfl⟩
            simp only [c', if_neg hea, if_pos]
            exact fun hcx ↦ hx (hcx.symm ▸ hce)
          · have hea : e ≠ a := by
              intro hea
              exact ha (hea ▸ heS)
            have hfa : f ≠ a := by
              intro hfa
              exact ha (hfa ▸ hfS)
            simpa [c', hea, hfa] using hc e heS f hfS hef heconf
  exact hpartial Finset.univ

theorem card_univ_subtype_filter
    {A : Type*} [Fintype A] [DecidableEq A]
    (F : Finset A) (p : A → Prop) [DecidablePred p] :
    ((Finset.univ : Finset {a // a ∈ F}).filter
      (fun a ↦ p a.1)).card = (F.filter p).card := by
  apply Finset.card_bij (fun a _ha ↦ a.1)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨a.2, (Finset.mem_filter.mp ha).2⟩
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro a ha
    refine ⟨⟨a, (Finset.mem_filter.mp ha).1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩

theorem card_univ_sigma_fst_fiber
    {A : Type*} [Fintype A] [DecidableEq A]
    (D : A → ℕ) (a : A) :
    ((Finset.univ : Finset (Σ x, Fin (D x))).filter
      (fun x ↦ x.1 = a)).card = D a := by
  calc
    ((Finset.univ : Finset (Σ x, Fin (D x))).filter
      (fun x ↦ x.1 = a)).card =
        ∑ x : (Σ y, Fin (D y)), if x.1 = a then 1 else 0 := by
          rw [Finset.card_filter]
    _ = ∑ y : A, ∑ _i : Fin (D y), if y = a then 1 else 0 := by
          rw [Fintype.sum_sigma]
    _ = D a := by simp

theorem card_univ_sum_filter
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (p : Sum A B → Prop) [DecidablePred p] :
    ((Finset.univ : Finset (Sum A B)).filter p).card =
      ((Finset.univ : Finset A).filter (fun a ↦ p (.inl a))).card +
      ((Finset.univ : Finset B).filter (fun b ↦ p (.inr b))).card := by
  have hset : (Finset.univ : Finset (Sum A B)).filter p =
      ((Finset.univ : Finset A).filter (fun a ↦ p (.inl a))).disjSum
      ((Finset.univ : Finset B).filter (fun b ↦ p (.inr b))) := by
    ext x
    cases x <;> simp
  rw [hset]
  simp

abbrev ShareEndpoint {V E : Type*} (tail head : E → V) (e f : E) : Prop :=
  tail f = tail e ∨ head f = tail e ∨
    tail f = head e ∨ head f = head e

abbrev SameLayerConflict
    {V E C : Type*} (tail head : E → V) (base : E → C)
    (e f : E) : Prop :=
  e ≠ f ∧ base f = base e ∧ ShareEndpoint tail head e f

theorem sameLayerConflict_degree_le_two
    {V E C : Type*} [Fintype E]
    [DecidableEq V] [DecidableEq E] [DecidableEq C]
    (tail head : E → V) (base : E → C)
    (hproper : BimapProperOn tail head Finset.univ base) :
    ∀ e, ((Finset.univ : Finset E).filter
      (SameLayerConflict tail head base e)).card ≤ 2 := by
  classical
  intro e
  let S : Finset E := (Finset.univ : Finset E).filter
    (SameLayerConflict tail head base e)
  let side : E → Fin 2 := fun f ↦
    if tail f = tail e ∨ head f = tail e then 0 else 1
  have hinj : Set.InjOn side (S : Set E) := by
    intro f hf g hg hside
    have hfdata := (Finset.mem_filter.mp hf).2
    have hgdata := (Finset.mem_filter.mp hg).2
    rcases hfdata with ⟨hfne, hfcolor, hfshare⟩
    rcases hgdata with ⟨hgne, hgcolor, hgshare⟩
    by_cases hffirst : tail f = tail e ∨ head f = tail e
    · have hgfirst : tail g = tail e ∨ head g = tail e := by
        by_contra hgnfirst
        simpa [side, hffirst, hgnfirst] using hside
      have hfhead : head f = tail e := by
        rcases hffirst with hftail | hfhead
        · exact (hproper f (Finset.mem_univ _) e (Finset.mem_univ _)
            (Ne.symm hfne) (Or.inl hftail) hfcolor).elim
        · exact hfhead
      have hghead : head g = tail e := by
        rcases hgfirst with hgtail | hghead
        · exact (hproper g (Finset.mem_univ _) e (Finset.mem_univ _)
            (Ne.symm hgne) (Or.inl hgtail) hgcolor).elim
        · exact hghead
      by_contra hfg
      have hneq := hproper f (Finset.mem_univ _) g (Finset.mem_univ _)
        hfg (Or.inr (hfhead.trans hghead.symm))
      exact hneq (hfcolor.trans hgcolor.symm)
    · have hgnfirst : ¬ (tail g = tail e ∨ head g = tail e) := by
        intro hgfirst
        simpa [side, hffirst, hgfirst] using hside
      have hftail : tail f = head e := by
        rcases hfshare with hft | hfh | hft | hfh
        · exact (hffirst (Or.inl hft)).elim
        · exact (hffirst (Or.inr hfh)).elim
        · exact hft
        · exact (hproper f (Finset.mem_univ _) e (Finset.mem_univ _)
            (Ne.symm hfne) (Or.inr hfh) hfcolor).elim
      have hgtail : tail g = head e := by
        rcases hgshare with hgt | hgh | hgt | hgh
        · exact (hgnfirst (Or.inl hgt)).elim
        · exact (hgnfirst (Or.inr hgh)).elim
        · exact hgt
        · exact (hproper g (Finset.mem_univ _) e (Finset.mem_univ _)
            (Ne.symm hgne) (Or.inr hgh) hgcolor).elim
      by_contra hfg
      have hneq := hproper f (Finset.mem_univ _) g (Finset.mem_univ _)
        hfg (Or.inl (hftail.trans hgtail.symm))
      exact hneq (hfcolor.trans hgcolor.symm)
  have hcard : (S.image side).card = S.card :=
    Finset.card_image_iff.mpr hinj
  calc
    S.card = (S.image side).card := hcard.symm
    _ ≤ (Finset.univ : Finset (Fin 2)).card := by
      exact Finset.card_le_card (Finset.subset_univ _)
    _ = 2 := by simp

def DegreeOn {V E : Type*} [DecidableEq V] [DecidableEq E]
    (a b : E → V) (F : Finset E) (v : V) : ℕ :=
  (F.filter (fun e ↦ a e = v ∨ b e = v)).card

def EndpointProperOn {V E C : Type*}
    (a b : E → V) (F : Finset E) (c : E → C) : Prop :=
  ∀ e, e ∈ F → ∀ f, f ∈ F → e ≠ f →
    (a f = a e ∨ b f = a e ∨ a f = b e ∨ b f = b e) →
    c e ≠ c f

/-- Shannon's `3Δ/2` construction for a finite loopless indexed
multigraph, in the even-degree form needed by the weighted packet proof.
Parallel physical edges remain distinct throughout. -/
theorem exists_endpointProper_fin_three_mul_of_degreeOn_le_two_mul
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (a b : E → V) (F : Finset E) (n : ℕ) (hn : 0 < n)
    (hloop : ∀ e ∈ F, a e ≠ b e)
    (hdeg : ∀ v, DegreeOn a b F v ≤ 2 * n) :
    ∃ c : E → Fin (3 * n), EndpointProperOn a b F c := by
  classical
  let d : V → ℕ := fun v ↦ DegreeOn a b F v
  let OE : Type _ := {e // e ∈ F} × Fin 2
  let DE : Type _ := Σ v, Fin (2 * n - d v)
  let HV : Type _ := V × Fin 2
  let HE : Type _ := Sum OE DE
  let A : HE → HV := Sum.elim
    (fun x ↦ (a x.1.1, x.2))
    (fun x ↦ (x.1, 0))
  let B : HE → HV := Sum.elim
    (fun x ↦ (b x.1.1, x.2))
    (fun x ↦ (x.1, 1))
  have hloopH : ∀ e : HE, A e ≠ B e := by
    intro e
    cases e with
    | inl x =>
        intro hab
        exact hloop x.1.1 x.1.2 (congrArg Prod.fst hab)
    | inr x =>
        intro hab
        have h01 := congrArg Prod.snd hab
        simpa [A, B] using h01
  have hregH : ∀ x : HV,
      ((Finset.univ : Finset HE).filter
        (fun e ↦ A e = x ∨ B e = x)).card = 2 * n := by
    intro x
    rcases x with ⟨v, i⟩
    rw [card_univ_sum_filter]
    have horig :
        ((Finset.univ : Finset OE).filter
          (fun e ↦ A (.inl e) = (v, i) ∨ B (.inl e) = (v, i))).card =
          d v := by
      have hset :
          (Finset.univ : Finset OE).filter
            (fun e ↦ A (.inl e) = (v, i) ∨ B (.inl e) = (v, i)) =
          ((Finset.univ : Finset {e // e ∈ F}).filter
            (fun e ↦ a e.1 = v ∨ b e.1 = v)) ×ˢ
              ({i} : Finset (Fin 2)) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product, Finset.mem_singleton, A, B, OE,
          Sum.elim_inl, Prod.mk.injEq]
        aesop
      rw [hset, Finset.card_product]
      simp only [Finset.card_singleton, mul_one]
      simpa [d, DegreeOn] using card_univ_subtype_filter F
        (fun e ↦ a e = v ∨ b e = v)
    have hdummy :
        ((Finset.univ : Finset DE).filter
          (fun e ↦ A (.inr e) = (v, i) ∨ B (.inr e) = (v, i))).card =
          2 * n - d v := by
      have hset :
          (Finset.univ : Finset DE).filter
            (fun e ↦ A (.inr e) = (v, i) ∨ B (.inr e) = (v, i)) =
          (Finset.univ : Finset DE).filter (fun e ↦ e.1 = v) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          A, B, DE, Sum.elim_inr, Prod.mk.injEq]
        constructor
        · aesop
        · intro hyv
          rcases Fin.eq_zero_or_eq_succ i with hi | ⟨q, hi⟩
          · exact Or.inl (Prod.ext hyv hi.symm)
          · have hq : q = 0 := Fin.eq_zero q
            subst q
            exact Or.inr (Prod.ext hyv hi.symm)
      rw [hset]
      exact card_univ_sigma_fst_fiber (fun w ↦ 2 * n - d w) v
    rw [horig, hdummy]
    exact Nat.add_sub_of_le (hdeg v)
  obtain ⟨tail, head, hendpoints, hhead, htail⟩ :=
    exists_balanced_orientation_of_even_regular A B n hn hloopH hregH
  obtain ⟨base, hbase⟩ :=
    exists_finProperColoring_of_regular_bimap tail head Finset.univ n hn
      htail hhead
  let conflict : HE → HE → Prop :=
    SameLayerConflict tail head base
  have hconflict_symm : Symmetric conflict := by
    intro e f hef
    rcases hef with ⟨hne, hcolor, hshare⟩
    refine ⟨Ne.symm hne, hcolor.symm, ?_⟩
    rcases hshare with h | h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inr h.symm))
  have hconflict_deg : ∀ e,
      ((Finset.univ : Finset HE).filter (conflict e)).card ≤ 2 := by
    exact sameLayerConflict_degree_le_two tail head base hbase
  obtain ⟨shade, hshade⟩ :=
    exists_fin3_coloring_of_conflict_degree_le_two conflict
      hconflict_symm hconflict_deg
  have horient_share : ∀ e f,
      (A f = A e ∨ B f = A e ∨ A f = B e ∨ B f = B e) →
      ShareEndpoint tail head e f := by
    intro e f hshare
    rcases hendpoints e with ⟨het, heh⟩ | ⟨het, heh⟩
    · rcases hendpoints f with ⟨hft, hfh⟩ | ⟨hft, hfh⟩
      · simp only [ShareEndpoint]
        rw [het, heh, hft, hfh]
        exact hshare
      · simp only [ShareEndpoint]
        rw [het, heh, hft, hfh]
        rcases hshare with h | h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inl h))
    · rcases hendpoints f with ⟨hft, hfh⟩ | ⟨hft, hfh⟩
      · simp only [ShareEndpoint]
        rw [het, heh, hft, hfh]
        rcases hshare with h | h | h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · simp only [ShareEndpoint]
        rw [het, heh, hft, hfh]
        rcases hshare with h | h | h | h
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
  let pack : (Fin 3 × Fin n) ≃ Fin (3 * n) := by
    simpa using Fintype.equivFin (Fin 3 × Fin n)
  let hcolor : HE → Fin (3 * n) := fun e ↦
    pack (shade e, base e)
  have hHproper : EndpointProperOn A B Finset.univ hcolor := by
    intro e he f hf hef hshare hsame
    have hpairs : (shade e, base e) = (shade f, base f) :=
      pack.injective hsame
    have hshadeEq : shade e = shade f := congrArg Prod.fst hpairs
    have hbaseEq : base e = base f := congrArg Prod.snd hpairs
    have hconf : conflict e f :=
      ⟨hef, hbaseEq.symm, horient_share e f hshare⟩
    exact (hshade e (Finset.mem_univ _) f (Finset.mem_univ _)
      hef hconf) hshadeEq
  let embed : {e // e ∈ F} → HE := fun e ↦
    Sum.inl (e, (0 : Fin 2))
  have h3n : 0 < 3 * n := Nat.mul_pos (by decide) hn
  let c : E → Fin (3 * n) := fun e ↦
    if he : e ∈ F then hcolor (embed ⟨e, he⟩) else ⟨0, h3n⟩
  refine ⟨c, ?_⟩
  intro e heF f hfF hef hshare hsame
  have hembed : embed ⟨e, heF⟩ ≠ embed ⟨f, hfF⟩ := by
    intro heq
    apply hef
    change (Sum.inl (⟨e, heF⟩, (0 : Fin 2)) : HE) =
      Sum.inl (⟨f, hfF⟩, (0 : Fin 2)) at heq
    have hp := Sum.inl.inj heq
    exact congrArg (fun x : OE ↦ x.1.1) hp
  have hshareH :
      A (embed ⟨f, hfF⟩) = A (embed ⟨e, heF⟩) ∨
      B (embed ⟨f, hfF⟩) = A (embed ⟨e, heF⟩) ∨
      A (embed ⟨f, hfF⟩) = B (embed ⟨e, heF⟩) ∨
      B (embed ⟨f, hfF⟩) = B (embed ⟨e, heF⟩) := by
    rcases hshare with h | h | h | h
    · apply Or.inl
      change (a f, (0 : Fin 2)) = (a e, (0 : Fin 2))
      exact Prod.ext h rfl
    · apply Or.inr; apply Or.inl
      change (b f, (0 : Fin 2)) = (a e, (0 : Fin 2))
      exact Prod.ext h rfl
    · apply Or.inr; apply Or.inr; apply Or.inl
      change (a f, (0 : Fin 2)) = (b e, (0 : Fin 2))
      exact Prod.ext h rfl
    · apply Or.inr; apply Or.inr; apply Or.inr
      change (b f, (0 : Fin 2)) = (b e, (0 : Fin 2))
      exact Prod.ext h rfl
  have hsameH : hcolor (embed ⟨e, heF⟩) =
      hcolor (embed ⟨f, hfF⟩) := by
    simpa [c, heF, hfF] using hsame
  exact (hHproper (embed ⟨e, heF⟩) (Finset.mem_univ _)
    (embed ⟨f, hfF⟩) (Finset.mem_univ _) hembed hshareH) hsameH

end OrdinaryEdgeColoring

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- The abstract two-copy Shannon construction, specialized to the indexed
weighted multigraph interface used by the manuscript. -/
theorem exists_isProperOn_three_of_degreeOn_le
    (F : Finset G.E) (n : ℕ) (hn : 0 < n)
    (hdegree : ∀ v, G.degreeOn F v ≤ 2 * n) :
    ∃ color : G.E → Fin (3 * n), G.IsProperOn F color := by
  have hdegree' : ∀ v,
      OrdinaryEdgeColoring.DegreeOn G.fst G.snd F v ≤ 2 * n := by
    intro v
    simpa only [OrdinaryEdgeColoring.DegreeOn, degreeOn, Inc] using hdegree v
  obtain ⟨color, hcolor⟩ :=
    OrdinaryEdgeColoring.exists_endpointProper_fin_three_mul_of_degreeOn_le_two_mul
      G.fst G.snd F n hn (fun e _he ↦ G.noLoop e) hdegree'
  refine ⟨color, ?_⟩
  intro v e he f hf hsame
  have heF : e ∈ F := (Finset.mem_filter.mp he).1
  have hfF : f ∈ F := (Finset.mem_filter.mp hf).1
  have heInc : G.Inc v e := (Finset.mem_filter.mp he).2
  have hfInc : G.Inc v f := (Finset.mem_filter.mp hf).2
  by_contra hne
  have hshare :
      G.fst f = G.fst e ∨ G.snd f = G.fst e ∨
      G.fst f = G.snd e ∨ G.snd f = G.snd e := by
    rcases heInc with he | he <;> rcases hfInc with hf | hf
    · exact Or.inl (hf.trans he.symm)
    · exact Or.inr (Or.inl (hf.trans he.symm))
    · exact Or.inr (Or.inr (Or.inl (hf.trans he.symm)))
    · exact Or.inr (Or.inr (Or.inr (hf.trans he.symm)))
  exact (hcolor e heF f hfF hne hshare) hsame

/-- The canonical greedy skeleton has a proper ordinary `3n` coloring for
every positive `n`. -/
theorem hasColoredHeavySkeleton_shannon
    (n : ℕ) (hn : 0 < n) :
    G.HasColoredHeavySkeleton n := by
  let F := G.greedySkeleton n
  obtain ⟨base, hproper⟩ :=
    G.exists_isProperOn_three_of_degreeOn_le F n hn
      (G.degreeOn_greedySkeleton_le n)
  exact ⟨F, base, G.greedySkeleton_hasHeavyWitnesses n, hproper⟩

/-- Exact general-multigraph weighted bound, with no unproved Shannon axiom. -/
theorem generalMultigraphThreeCeil_proved :
    GeneralMultigraphThreeCeil.{u} := by
  apply generalMultigraphThreeCeil_of_coloredHeavySkeletons
  intro H n hn _hdelta
  exact H.hasColoredHeavySkeleton_shannon n hn

/-- A real-valued form of the exact ceiling theorem.  It makes explicit
that the only additive loss is the strict constant coming from rounding the
real maximum load up to an integer. -/
theorem chiW_lt_three_deltaW_add_three :
    (G.chiW : ℝ) < 3 * G.deltaW + 3 := by
  have hceilNat : G.chiW ≤ 3 * Nat.ceil G.deltaW :=
    generalMultigraphThreeCeil_proved G
  have hceilReal : (G.chiW : ℝ) ≤ 3 * (Nat.ceil G.deltaW : ℝ) := by
    exact_mod_cast hceilNat
  calc
    (G.chiW : ℝ) ≤ 3 * (Nat.ceil G.deltaW : ℝ) := hceilReal
    _ < 3 * (G.deltaW + 1) := by
      gcongr
      exact Nat.ceil_lt_add_one G.deltaW_nonneg
    _ = 3 * G.deltaW + 3 := by ring

/-- Uniform asymptotic statement obtained from the exact ceiling bound. -/
theorem generalMultigraphDeltaAsymptotic_proved :
    GeneralMultigraphDeltaAsymptotic.{u} :=
  generalMultigraphDeltaAsymptotic_of_threeCeil
    generalMultigraphThreeCeil_proved

end WeightedMultigraph
end WeightedEdgeColoring
