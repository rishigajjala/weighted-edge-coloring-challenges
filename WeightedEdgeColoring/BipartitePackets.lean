import WeightedEdgeColoring.ShannonBridge

open scoped BigOperators
open Function

namespace OrdinaryEdgeColoring

/-- Kőnig's line-coloring theorem for an indexed bipartite multigraph.

The two endpoint maps use the same ambient finite vertex type; vertices that
occur on only one shore simply have degree zero for the other endpoint map.
Parallel physical edges are retained in `F`.  We first add dummy edges to
make both endpoint degrees exactly `k`, apply the regular one-factorization
theorem, and then discard the dummy edges. -/
theorem exists_finProperColoring_of_bimap_degree_le
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (left right : E → V) (F : Finset E) (k : ℕ) (hk : 0 < k)
    (hleft : ∀ v, (F.filter (fun e ↦ left e = v)).card ≤ k)
    (hright : ∀ v, (F.filter (fun e ↦ right e = v)).card ≤ k) :
    ∃ c : E → Fin k, BimapProperOn left right F c := by
  classical
  let dl : V → ℕ := fun v ↦ (F.filter (fun e ↦ left e = v)).card
  let dr : V → ℕ := fun v ↦ (F.filter (fun e ↦ right e = v)).card
  let DL : Type _ := Σ v, Fin (k - dl v)
  let DR : Type _ := Σ v, Fin (k - dr v)
  have hsum_left : ∑ v, dl v = F.card := by
    calc
      ∑ v, dl v = ∑ v : V, ∑ e ∈ F, if left e = v then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro v _hv
        simp [dl]
      _ = ∑ e ∈ F, ∑ v : V, if left e = v then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = F.card := by simp
  have hsum_right : ∑ v, dr v = F.card := by
    calc
      ∑ v, dr v = ∑ v : V, ∑ e ∈ F, if right e = v then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro v _hv
        simp [dr]
      _ = ∑ e ∈ F, ∑ v : V, if right e = v then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = F.card := by simp
  have hcard_deficit : Fintype.card DL = Fintype.card DR := by
    simp only [DL, DR, Fintype.card_sigma, Fintype.card_fin]
    have hdl : ∑ v : V, (k - dl v) =
        (∑ _v : V, k) - ∑ v : V, dl v := by
      exact Finset.sum_tsub_distrib Finset.univ
        (fun v _hv ↦ hleft v)
    have hdr : ∑ v : V, (k - dr v) =
        (∑ _v : V, k) - ∑ v : V, dr v := by
      exact Finset.sum_tsub_distrib Finset.univ
        (fun v _hv ↦ hright v)
    calc
      ∑ v, (k - dl v) = Fintype.card V * k - ∑ v, dl v := by
        rw [hdl]
        simp
      _ = Fintype.card V * k - F.card := by rw [hsum_left]
      _ = Fintype.card V * k - ∑ v, dr v := by rw [hsum_right]
      _ = ∑ v, (k - dr v) := by
        rw [hdr]
        simp
  let matchDeficit : DL ≃ DR := Fintype.equivOfCardEq hcard_deficit
  let OE : Type _ := {e // e ∈ F}
  let HE : Type _ := Sum OE DL
  let A : HE → V := Sum.elim (fun e ↦ left e.1) (fun x ↦ x.1)
  let B : HE → V := Sum.elim (fun e ↦ right e.1)
    (fun x ↦ (matchDeficit x).1)
  have hleft_regular : ∀ v,
      ((Finset.univ : Finset HE).filter (fun e ↦ A e = v)).card = k := by
    intro v
    rw [card_univ_sum_filter]
    have horig :
        ((Finset.univ : Finset OE).filter
          (fun e ↦ A (.inl e) = v)).card = dl v := by
      simpa [A, OE, dl] using
        card_univ_subtype_filter F (fun e ↦ left e = v)
    have hdummy :
        ((Finset.univ : Finset DL).filter
          (fun e ↦ A (.inr e) = v)).card = k - dl v := by
      simpa [A, DL] using card_univ_sigma_fst_fiber (fun w ↦ k - dl w) v
    rw [horig, hdummy]
    exact Nat.add_sub_of_le (hleft v)
  have hright_dummy : ∀ v,
      ((Finset.univ : Finset DL).filter
        (fun x ↦ (matchDeficit x).1 = v)).card = k - dr v := by
    intro v
    let S : Finset DL := (Finset.univ : Finset DL).filter
      (fun x ↦ (matchDeficit x).1 = v)
    let T : Finset DR := (Finset.univ : Finset DR).filter
      (fun y ↦ y.1 = v)
    have hcardST : S.card = T.card := by
      apply Finset.card_bij (fun x _hx ↦ matchDeficit x)
      · intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hx).2⟩
      · intro x hx y hy hxy
        exact matchDeficit.injective hxy
      · intro y hy
        refine ⟨matchDeficit.symm y, ?_, by simp⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          simpa using (Finset.mem_filter.mp hy).2⟩
    calc
      ((Finset.univ : Finset DL).filter
          (fun x ↦ (matchDeficit x).1 = v)).card = S.card := rfl
      _ = T.card := hcardST
      _ = k - dr v := by
        simpa [T, DR] using card_univ_sigma_fst_fiber (fun w ↦ k - dr w) v
  have hright_regular : ∀ v,
      ((Finset.univ : Finset HE).filter (fun e ↦ B e = v)).card = k := by
    intro v
    rw [card_univ_sum_filter]
    have horig :
        ((Finset.univ : Finset OE).filter
          (fun e ↦ B (.inl e) = v)).card = dr v := by
      simpa [B, OE, dr] using
        card_univ_subtype_filter F (fun e ↦ right e = v)
    have hdummy :
        ((Finset.univ : Finset DL).filter
          (fun e ↦ B (.inr e) = v)).card = k - dr v := by
      simpa [B] using hright_dummy v
    rw [horig, hdummy]
    exact Nat.add_sub_of_le (hright v)
  obtain ⟨cH, hcH⟩ :=
    exists_finProperColoring_of_regular_bimap A B Finset.univ k hk
      hleft_regular hright_regular
  let fallback : Fin k := ⟨0, hk⟩
  let embed : OE → HE := Sum.inl
  let c : E → Fin k := fun e ↦
    if he : e ∈ F then cH (embed ⟨e, he⟩) else fallback
  refine ⟨c, ?_⟩
  intro e heF f hfF hef hconflict
  have hembed : embed ⟨e, heF⟩ ≠ embed ⟨f, hfF⟩ := by
    intro h
    apply hef
    have h' := Sum.inl_injective h
    exact congrArg Subtype.val h'
  have hconflictH :
      A (embed ⟨e, heF⟩) = A (embed ⟨f, hfF⟩) ∨
        B (embed ⟨e, heF⟩) = B (embed ⟨f, hfF⟩) := by
    simpa [A, B, embed] using hconflict
  have hne := hcH (embed ⟨e, heF⟩) (Finset.mem_univ _)
    (embed ⟨f, hfF⟩) (Finset.mem_univ _) hembed hconflictH
  simpa [c, heF, hfF, embed] using hne

end OrdinaryEdgeColoring

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable {G : WeightedMultigraph.{u}}

namespace Bipartition

/-- Orient an edge from the `false` shore to the `true` shore. -/
def leftEndpoint (b : G.Bipartition) (e : G.E) : G.V :=
  if b.side (G.fst e) = false then G.fst e else G.snd e

/-- The endpoint on the `true` shore. -/
def rightEndpoint (b : G.Bipartition) (e : G.E) : G.V :=
  if b.side (G.fst e) = false then G.snd e else G.fst e

theorem leftEndpoint_inc (b : G.Bipartition) (e : G.E) :
    G.Inc (b.leftEndpoint e) e := by
  unfold leftEndpoint Inc
  split <;> simp

theorem rightEndpoint_inc (b : G.Bipartition) (e : G.E) :
    G.Inc (b.rightEndpoint e) e := by
  unfold rightEndpoint Inc
  split <;> simp

@[simp] theorem side_leftEndpoint (b : G.Bipartition) (e : G.E) :
    b.side (b.leftEndpoint e) = false := by
  unfold leftEndpoint
  split
  · assumption
  · rename_i hfalse
    have hop := b.opposite e
    cases hfst : b.side (G.fst e) <;>
      cases hsnd : b.side (G.snd e) <;> simp_all

@[simp] theorem side_rightEndpoint (b : G.Bipartition) (e : G.E) :
    b.side (b.rightEndpoint e) = true := by
  unfold rightEndpoint
  split
  · rename_i hfalse
    have hop := b.opposite e
    cases hfst : b.side (G.fst e) <;>
      cases hsnd : b.side (G.snd e) <;> simp_all
  · rename_i hnotfalse
    cases hfst : b.side (G.fst e) <;> simp_all

theorem leftEndpoint_eq_of_inc_of_side_eq_false
    (b : G.Bipartition) {v : G.V} {e : G.E}
    (hinc : G.Inc v e) (hv : b.side v = false) :
    b.leftEndpoint e = v := by
  rcases hinc with hfst | hsnd
  · subst v
    simp [leftEndpoint, hv]
  · have hop := b.opposite e
    rw [hsnd, hv] at hop
    have hfst : b.side (G.fst e) = true := by
      cases h : b.side (G.fst e) <;> simp_all
    simp [leftEndpoint, hfst, hsnd]

theorem rightEndpoint_eq_of_inc_of_side_eq_true
    (b : G.Bipartition) {v : G.V} {e : G.E}
    (hinc : G.Inc v e) (hv : b.side v = true) :
    b.rightEndpoint e = v := by
  rcases hinc with hfst | hsnd
  · subst v
    simp [rightEndpoint, hv]
  · have hop := b.opposite e
    rw [hsnd, hv] at hop
    have hfst : b.side (G.fst e) = false := by
      cases h : b.side (G.fst e) <;> simp_all
    simp [rightEndpoint, hfst, hsnd]

/-- Two edges meeting at a vertex meet on the same oriented shore. -/
theorem oriented_conflict_of_common_inc
    (b : G.Bipartition) {v : G.V} {e f : G.E}
    (he : G.Inc v e) (hf : G.Inc v f) :
    b.leftEndpoint e = b.leftEndpoint f ∨
      b.rightEndpoint e = b.rightEndpoint f := by
  cases hv : b.side v with
  | false =>
      exact Or.inl ((b.leftEndpoint_eq_of_inc_of_side_eq_false he hv).trans
        (b.leftEndpoint_eq_of_inc_of_side_eq_false hf hv).symm)
  | true =>
      exact Or.inr ((b.rightEndpoint_eq_of_inc_of_side_eq_true he hv).trans
        (b.rightEndpoint_eq_of_inc_of_side_eq_true hf hv).symm)

end Bipartition

/-- Kőnig's exact edge-coloring theorem, specialized to the indexed
multigraph representation used by the weighted development. -/
theorem exists_isProperOn_bipartite_of_degreeOn_le
    (b : G.Bipartition) (F : Finset G.E) (k : ℕ) (hk : 0 < k)
    (hdegree : ∀ v, G.degreeOn F v ≤ k) :
    ∃ color : G.E → Fin k, G.IsProperOn F color := by
  classical
  let left : G.E → G.V := b.leftEndpoint
  let right : G.E → G.V := b.rightEndpoint
  have hleft : ∀ v,
      (F.filter (fun e ↦ left e = v)).card ≤ k := by
    intro v
    calc
      (F.filter (fun e ↦ left e = v)).card ≤
          (F.filter (G.Inc v)).card := by
        apply Finset.card_le_card
        intro e he
        have he' := Finset.mem_filter.mp he
        apply Finset.mem_filter.mpr
        refine ⟨he'.1, ?_⟩
        rw [← he'.2]
        exact b.leftEndpoint_inc e
      _ = G.degreeOn F v := rfl
      _ ≤ k := hdegree v
  have hright : ∀ v,
      (F.filter (fun e ↦ right e = v)).card ≤ k := by
    intro v
    calc
      (F.filter (fun e ↦ right e = v)).card ≤
          (F.filter (G.Inc v)).card := by
        apply Finset.card_le_card
        intro e he
        have he' := Finset.mem_filter.mp he
        apply Finset.mem_filter.mpr
        refine ⟨he'.1, ?_⟩
        rw [← he'.2]
        exact b.rightEndpoint_inc e
      _ = G.degreeOn F v := rfl
      _ ≤ k := hdegree v
  obtain ⟨color, hcolor⟩ :=
    OrdinaryEdgeColoring.exists_finProperColoring_of_bimap_degree_le
      left right F k hk hleft hright
  refine ⟨color, ?_⟩
  intro v e he f hf hsame
  by_contra hne
  have heF : e ∈ F := (Finset.mem_filter.mp he).1
  have hfF : f ∈ F := (Finset.mem_filter.mp hf).1
  have hconflict : left e = left f ∨ right e = right f :=
    b.oriented_conflict_of_common_inc
      (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2
  exact (hcolor e heF f hfF hne hconflict) hsame

/-- Colors not used by the selected proper edge coloring at `v`. -/
def missingColorsAt {q : ℕ} (F : Finset G.E) (color : G.E → Fin q)
    (v : G.V) : Finset (Fin q) :=
  Finset.univ \ (F.filter (G.Inc v)).image color

/-- In a proper coloring, the number of missing colors is the palette size
minus the selected ordinary degree. -/
theorem card_missingColorsAt
    {q : ℕ} (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (v : G.V) :
    (G.missingColorsAt F color v).card = q - G.degreeOn F v := by
  classical
  unfold missingColorsAt
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [Finset.card_image_iff.mpr (hproper v)]
  rfl

/-- A residual edge may use only a color missing at both endpoints of the
already colored edge set. -/
def UsesOnlyCommonMissing
    {q : ℕ} (F R : Finset G.E) (base residual : G.E → Fin q) : Prop :=
  ∀ e ∈ R,
    residual e ∈ G.missingColorsAt F base (G.fst e) ∧
      residual e ∈ G.missingColorsAt F base (G.snd e)

theorem mem_missingColorsAt_of_commonMissing_of_inc
    {q : ℕ} {F R : Finset G.E} {base residual : G.E → Fin q}
    (hmissing : G.UsesOnlyCommonMissing F R base residual)
    {e : G.E} (heR : e ∈ R) {v : G.V} (hinc : G.Inc v e) :
    residual e ∈ G.missingColorsAt F base v := by
  rcases hmissing e heR with ⟨hfst, hsnd⟩
  rcases hinc with h | h
  · simpa [h] using hfst
  · simpa [h] using hsnd

/-- A color used by an edge at `v` is not missing at `v`. -/
theorem not_mem_missingColorsAt_of_used
    {q : ℕ} {F : Finset G.E} {base : G.E → Fin q}
    {f : G.E} (hfF : f ∈ F) {v : G.V} (hfinc : G.Inc v f) :
    base f ∉ G.missingColorsAt F base v := by
  classical
  simp only [missingColorsAt, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image]
  push_neg
  exact ⟨f, Finset.mem_filter.mpr ⟨hfF, hfinc⟩, rfl⟩

/-- Merge two disjoint partial colorings in the same palette when every
residual edge uses a color missing at both endpoints of the first coloring.
This is the exact deterministic compatibility step after palette mixing and
whole-edge rounding. -/
theorem merge_feasibleOn_samePalette_of_commonMissing
    {q : ℕ} (F R : Finset G.E) (hdisj : Disjoint F R)
    (base residual : G.E → Fin q)
    (hbase : G.IsFeasibleOn F base)
    (hresidual : G.IsFeasibleOn R residual)
    (hmissing : G.UsesOnlyCommonMissing F R base residual) :
    ∃ color : G.E → Fin q, G.IsFeasibleOn (F ∪ R) color := by
  classical
  let color : G.E → Fin q := fun e ↦
    if e ∈ F then base e else residual e
  refine ⟨color, ?_⟩
  intro v i
  have hload :
      G.colorLoadOn (F ∪ R) color v i =
        G.colorLoadOn F base v i + G.colorLoadOn R residual v i := by
    unfold colorLoadOn
    rw [Finset.sum_union hdisj]
    congr 1
    · apply Finset.sum_congr rfl
      intro e heF
      simp [color, heF]
    · apply Finset.sum_congr rfl
      intro e heR
      have heNF : e ∉ F := fun heF ↦
        Finset.disjoint_left.mp hdisj heF heR
      simp [color, heNF]
  rw [hload]
  by_cases hused : ∃ f ∈ F, G.Inc v f ∧ base f = i
  · have hRzero : G.colorLoadOn R residual v i = 0 := by
      unfold colorLoadOn
      apply Finset.sum_eq_zero
      intro e heR
      by_cases heinc : G.Inc v e
      · have hemiss :=
          G.mem_missingColorsAt_of_commonMissing_of_inc hmissing heR heinc
        obtain ⟨f, hfF, hfinc, hfi⟩ := hused
        have hnot := G.not_mem_missingColorsAt_of_used
          (base := base) hfF hfinc
        have hne : residual e ≠ i := by
          intro hei
          apply hnot
          rw [hfi, ← hei]
          exact hemiss
        simp [heinc, hne]
      · simp [heinc]
    rw [hRzero, add_zero]
    exact hbase v i
  · have hFzero : G.colorLoadOn F base v i = 0 := by
      unfold colorLoadOn
      apply Finset.sum_eq_zero
      intro f hfF
      by_cases hfinc : G.Inc v f
      · have hne : base f ≠ i := by
          intro hfi
          exact hused ⟨f, hfF, hfinc, hfi⟩
        simp [hfinc, hne]
      · simp [hfinc]
    rw [hFzero, zero_add]
    exact hresidual v i

/-- Half-unit lower bounds turn weighted degree into ordinary degree.  This
is the deterministic counting fact behind the heavy-packet palette. -/
theorem degreeOn_cast_le_two_mul_restrictedWeight
    (F : Finset G.E)
    (hhalf : ∀ e ∈ F, (1 / 2 : ℝ) ≤ G.weight e) (v : G.V) :
    (G.degreeOn F v : ℝ) ≤
      2 * (∑ e ∈ F, if G.Inc v e then G.weight e else 0) := by
  classical
  let S := F.filter (G.Inc v)
  have hsum : ∑ e ∈ S, (1 / 2 : ℝ) ≤ ∑ e ∈ S, G.weight e := by
    exact Finset.sum_le_sum fun e he ↦
      hhalf e (Finset.mem_filter.mp he).1
  have hload :
      (∑ e ∈ F, if G.Inc v e then G.weight e else 0) =
        ∑ e ∈ S, G.weight e := by
    simp [S, Finset.sum_filter]
  have hcard :
      ∑ _e ∈ S, (1 / 2 : ℝ) = (S.card : ℝ) / 2 := by
    simp
    ring
  rw [hcard, ← hload] at hsum
  change (S.card : ℝ) ≤ _
  nlinarith

/-- The edges heavier than one half.  In a packet graph these are exactly
the heavy packets. -/
noncomputable def heavyEdges : Finset G.E :=
  Finset.univ.filter fun e ↦ (1 / 2 : ℝ) < G.weight e

theorem degreeOn_heavyEdges_le_two_mul
    (n : ℕ) (hdelta : G.deltaW ≤ n) (v : G.V) :
    G.degreeOn G.heavyEdges v ≤ 2 * n := by
  have hhalf : ∀ e ∈ G.heavyEdges, (1 / 2 : ℝ) ≤ G.weight e := by
    intro e he
    exact (Finset.mem_filter.mp he).2.le
  have hweighted := G.degreeOn_cast_le_two_mul_restrictedWeight
    G.heavyEdges hhalf v
  have hrestricted := G.restrictedStarWeight_le_starWeight G.heavyEdges v
  have hstar := (G.starWeight_le_deltaW v).trans hdelta
  have hreal : (G.degreeOn G.heavyEdges v : ℝ) ≤ (2 * n : ℕ) := by
    push_cast
    nlinarith
  exact_mod_cast hreal

/-- Heavy packets in a bipartite graph have a proper `2n`-coloring. -/
theorem exists_heavyEdges_properColoring_bipartite
    (b : G.Bipartition) (n : ℕ) (hn : 0 < n)
    (hdelta : G.deltaW ≤ n) :
    ∃ color : G.E → Fin (2 * n), G.IsProperOn G.heavyEdges color := by
  apply G.exists_isProperOn_bipartite_of_degreeOn_le b G.heavyEdges
    (2 * n) (Nat.mul_pos (by decide) hn)
  exact G.degreeOn_heavyEdges_le_two_mul n hdelta

/-- The exact palette-slack inequality used before moment mixing.

`F` is the heavy packet set and `R` is the light residual.  If the two
restricted loads add to at most `n`, every heavy edge has weight at least
one half, and the palette has at least `(2+tau)n` colors, then the number of
colors missing at a vertex is at least `tau*n + 2*load(R,v)`. -/
theorem missingColorsAt_lowerBound
    {q : ℕ} (F R : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color)
    (hhalf : ∀ e ∈ F, (1 / 2 : ℝ) ≤ G.weight e)
    (n τ : ℝ)
    (hpalette : (2 + τ) * n ≤ q)
    (htotal : ∀ v,
      (∑ e ∈ F, if G.Inc v e then G.weight e else 0) +
        (∑ e ∈ R, if G.Inc v e then G.weight e else 0) ≤ n) :
    ∀ v,
      τ * n + 2 * (∑ e ∈ R,
        if G.Inc v e then G.weight e else 0) ≤
      (G.missingColorsAt F color v).card := by
  classical
  intro v
  let d : ℕ := G.degreeOn F v
  let f : ℕ := (G.missingColorsAt F color v).card
  let WF : ℝ := ∑ e ∈ F, if G.Inc v e then G.weight e else 0
  let WR : ℝ := ∑ e ∈ R, if G.Inc v e then G.weight e else 0
  have hdq : d ≤ q := by
    have himage : (F.filter (G.Inc v)).image color ⊆
        (Finset.univ : Finset (Fin q)) := Finset.subset_univ _
    have hcardImage := Finset.card_le_card himage
    rw [Finset.card_image_iff.mpr (hproper v)] at hcardImage
    simpa only [d, degreeOn, Finset.card_univ, Fintype.card_fin] using hcardImage
  have hf : f = q - d := by
    simpa [f, d] using G.card_missingColorsAt F color hproper v
  have hcastf : (f : ℝ) = (q : ℝ) - (d : ℝ) := by
    rw [hf, Nat.cast_sub hdq]
  have hdweight : (d : ℝ) ≤ 2 * WF := by
    simpa [d, WF] using
      G.degreeOn_cast_le_two_mul_restrictedWeight F hhalf v
  have htotalv : WF + WR ≤ n := by
    simpa [WF, WR] using htotal v
  change τ * n + 2 * WR ≤ (f : ℝ)
  rw [hcastf]
  norm_num at hpalette
  nlinarith

/-- Rewrite a star weight as an unrestricted finite sum with an incidence
indicator. -/
theorem starWeight_eq_inc_sum (v : G.V) :
    G.starWeight v =
      ∑ e : G.E, if G.Inc v e then G.weight e else 0 := by
  classical
  unfold starWeight
  calc
    (∑ e : {e : G.E // G.Inc v e}, G.weight e.1) =
        ∑ e ∈ (Finset.univ : Finset G.E).filter (G.Inc v), G.weight e := by
      symm
      exact Finset.sum_subtype
        ((Finset.univ : Finset G.E).filter (G.Inc v)) (by simp) G.weight
    _ = _ := by rw [Finset.sum_filter]

/-- Rewrite one color load as an unrestricted finite sum. -/
theorem colorLoad_eq_inc_sum {q : ℕ} (color : G.E → Fin q)
    (v : G.V) (i : Fin q) :
    G.colorLoad color v i =
      ∑ e : G.E,
        if G.Inc v e ∧ color e = i then G.weight e else 0 := by
  classical
  unfold colorLoad
  calc
    (∑ e : {e : G.E // G.Inc v e},
        if color e.1 = i then G.weight e.1 else 0) =
        ∑ e ∈ (Finset.univ : Finset G.E).filter (G.Inc v),
          if color e = i then G.weight e else 0 := by
      symm
      exact Finset.sum_subtype
        ((Finset.univ : Finset G.E).filter (G.Inc v)) (by simp)
        (fun e ↦ if color e = i then G.weight e else 0)
    _ = ∑ e : G.E,
        if G.Inc v e then
          (if color e = i then G.weight e else 0) else 0 := by
      rw [Finset.sum_filter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hinc : G.Inc v e <;>
        by_cases hc : color e = i <;> simp [hinc, hc]

/-- Weight assigned to one tentative packet label. -/
def packetLabelWeight {C : Type*} [DecidableEq C]
    (a : G.E → C) (c : C) : ℝ :=
  ∑ e : G.E, if a e = c then G.weight e else 0

/-- Labels actually used by an assignment. -/
def usedPacketLabels {C : Type*} [Fintype C] [DecidableEq C]
    (a : G.E → C) : Finset C :=
  Finset.univ.image a

/-- A tentative packet assignment respects oriented endpoint pairs and gives
every label total weight at most one. -/
def IsValidPacketAssignment {C : Type*} [Fintype C] [DecidableEq C]
    (b : G.Bipartition) (a : G.E → C) : Prop :=
  (∀ e f, a e = a f →
      b.leftEndpoint e = b.leftEndpoint f ∧
        b.rightEndpoint e = b.rightEndpoint f) ∧
    ∀ c, G.packetLabelWeight a c ≤ 1

/-- Giving every edge its own label is a valid packet assignment. -/
theorem isValidPacketAssignment_equivFin
    (b : G.Bipartition) :
    G.IsValidPacketAssignment b (Fintype.equivFin G.E) := by
  classical
  constructor
  · intro e f hef
    have : e = f := (Fintype.equivFin G.E).injective hef
    subst f
    exact ⟨rfl, rfl⟩
  · intro c
    let a : G.E → Fin (Fintype.card G.E) := Fintype.equivFin G.E
    let S : Finset G.E := Finset.univ.filter fun e ↦ a e = c
    have hcard : S.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro e he f hf
      apply (Fintype.equivFin G.E).injective
      exact (Finset.mem_filter.mp he).2.trans
        (Finset.mem_filter.mp hf).2.symm
    calc
      G.packetLabelWeight a c = ∑ e ∈ S, G.weight e := by
        simp [packetLabelWeight, S, Finset.sum_filter]
      _ ≤ ∑ _e ∈ S, (1 : ℝ) := by
        exact Finset.sum_le_sum fun e _he ↦ G.weight_le_one e
      _ = (S.card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hcard

/-- Among all valid assignments to the fixed finite label set, one uses a
minimum number of labels. -/
theorem exists_minimal_validPacketAssignment
    (b : G.Bipartition) :
    ∃ a : G.E → Fin (Fintype.card G.E),
      G.IsValidPacketAssignment b a ∧
      ∀ a' : G.E → Fin (Fintype.card G.E),
        G.IsValidPacketAssignment b a' →
        (G.usedPacketLabels a).card ≤ (G.usedPacketLabels a').card := by
  classical
  let C := Fin (Fintype.card G.E)
  let candidates : Finset (G.E → C) :=
    Finset.univ.filter (G.IsValidPacketAssignment b)
  have hnonempty : candidates.Nonempty := by
    refine ⟨Fintype.equivFin G.E, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, G.isValidPacketAssignment_equivFin b⟩
  obtain ⟨a, ha, hmin⟩ := candidates.exists_min_image
    (fun x ↦ (G.usedPacketLabels x).card) hnonempty
  refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
  intro a' ha'
  exact hmin a' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha'⟩)

/-- Merge label `q` into label `p`. -/
def mergePacketLabels {C : Type*} [DecidableEq C]
    (a : G.E → C) (p q : C) : G.E → C :=
  fun e ↦ if a e = q then p else a e

theorem packetLabelWeight_merge_self
    {C : Type*} [Fintype C] [DecidableEq C]
    (a : G.E → C) {p q : C} (hpq : p ≠ q) :
    G.packetLabelWeight (G.mergePacketLabels a p q) p =
      G.packetLabelWeight a p + G.packetLabelWeight a q := by
  classical
  unfold packetLabelWeight mergePacketLabels
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases heq : a e = q
  · have hnep : a e ≠ p := by
      intro hep
      exact hpq (hep.symm.trans heq)
    simp [heq, hnep, hpq, Ne.symm hpq]
  · by_cases hep : a e = p <;> simp [heq, hep, hpq, Ne.symm hpq]

theorem packetLabelWeight_merge_old
    {C : Type*} [Fintype C] [DecidableEq C]
    (a : G.E → C) {p q r : C} (hrp : r ≠ p) (hrq : r ≠ q) :
    G.packetLabelWeight (G.mergePacketLabels a p q) r =
      G.packetLabelWeight a r := by
  classical
  unfold packetLabelWeight mergePacketLabels
  apply Finset.sum_congr rfl
  intro e _he
  by_cases heq : a e = q
  · simp [heq, Ne.symm hrp, Ne.symm hrq]
  · simp [heq]

theorem isValidPacketAssignment_merge
    {C : Type*} [Fintype C] [DecidableEq C]
    (b : G.Bipartition) (a : G.E → C)
    (ha : G.IsValidPacketAssignment b a)
    {p q : C} (hpq : p ≠ q)
    (hcross : ∀ e f, a e = p → a f = q →
      b.leftEndpoint e = b.leftEndpoint f ∧
        b.rightEndpoint e = b.rightEndpoint f)
    (hpweight : G.packetLabelWeight a p ≤ (1 / 2 : ℝ))
    (hqweight : G.packetLabelWeight a q ≤ (1 / 2 : ℝ)) :
    G.IsValidPacketAssignment b (G.mergePacketLabels a p q) := by
  constructor
  · intro e f hef
    by_cases heq : a e = q <;> by_cases hfq : a f = q
    · exact ha.1 e f (heq.trans hfq.symm)
    · have hfp : a f = p := by
        simpa [mergePacketLabels, heq, hfq] using hef.symm
      exact (hcross f e hfp heq) |>.imp Eq.symm Eq.symm
    · have hep : a e = p := by
        simpa [mergePacketLabels, heq, hfq] using hef
      exact hcross e f hep hfq
    · apply ha.1 e f
      simpa [mergePacketLabels, heq, hfq] using hef
  · intro r
    by_cases hrp : r = p
    · subst r
      rw [G.packetLabelWeight_merge_self a hpq]
      nlinarith
    · by_cases hrq : r = q
      · subst r
        have hzero :
            G.packetLabelWeight (G.mergePacketLabels a p q) q = 0 := by
          unfold packetLabelWeight mergePacketLabels
          apply Finset.sum_eq_zero
          intro e _he
          by_cases heq : a e = q
          · simp [heq, hpq]
          · simp [heq]
        rw [hzero]
        norm_num
      · rw [G.packetLabelWeight_merge_old a hrp hrq]
        exact ha.2 r

theorem usedPacketLabels_merge_subset
    {C : Type*} [Fintype C] [DecidableEq C]
    (a : G.E → C) {p q : C} (hpq : p ≠ q)
    (hpused : p ∈ G.usedPacketLabels a) :
    G.usedPacketLabels (G.mergePacketLabels a p q) ⊆
      G.usedPacketLabels a \ {q} := by
  classical
  intro r hr
  rcases Finset.mem_image.mp hr with ⟨e, _he, rfl⟩
  by_cases heq : a e = q
  · simp only [mergePacketLabels, if_pos heq, Finset.mem_sdiff,
      Finset.mem_singleton]
    exact ⟨hpused, hpq⟩
  · simp only [mergePacketLabels, if_neg heq, Finset.mem_sdiff,
      Finset.mem_singleton]
    exact ⟨Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩, heq⟩

theorem card_usedPacketLabels_merge_lt
    {C : Type*} [Fintype C] [DecidableEq C]
    (a : G.E → C) {p q : C} (hpq : p ≠ q)
    (hpused : p ∈ G.usedPacketLabels a)
    (hqused : q ∈ G.usedPacketLabels a) :
    (G.usedPacketLabels (G.mergePacketLabels a p q)).card <
      (G.usedPacketLabels a).card := by
  classical
  have hsub := G.usedPacketLabels_merge_subset a hpq hpused
  have hle := Finset.card_le_card hsub
  have hsingle : ({q} : Finset C) ⊆ G.usedPacketLabels a := by
    simpa using hqused
  rw [Finset.card_sdiff_of_subset hsingle] at hle
  simp only [Finset.card_singleton] at hle
  have hpos : 0 < (G.usedPacketLabels a).card :=
    Finset.card_pos.mpr ⟨q, hqused⟩
  omega

/-- Minimality forbids two distinct light labels with the same oriented
endpoint pair. -/
theorem no_mergeable_labels_of_minimal
    {C : Type*} [Fintype C] [DecidableEq C]
    (b : G.Bipartition) (a : G.E → C)
    (ha : G.IsValidPacketAssignment b a)
    (hminimal : ∀ a' : G.E → C,
      G.IsValidPacketAssignment b a' →
      (G.usedPacketLabels a).card ≤ (G.usedPacketLabels a').card)
    {p q : C} (hpq : p ≠ q)
    (hpused : p ∈ G.usedPacketLabels a)
    (hqused : q ∈ G.usedPacketLabels a)
    (hcross : ∀ e f, a e = p → a f = q →
      b.leftEndpoint e = b.leftEndpoint f ∧
        b.rightEndpoint e = b.rightEndpoint f)
    (hpweight : G.packetLabelWeight a p ≤ (1 / 2 : ℝ))
    (hqweight : G.packetLabelWeight a q ≤ (1 / 2 : ℝ)) : False := by
  let a' := G.mergePacketLabels a p q
  have hvalid : G.IsValidPacketAssignment b a' :=
    G.isValidPacketAssignment_merge b a ha hpq hcross hpweight hqweight
  have hle := hminimal a' hvalid
  have hlt := G.card_usedPacketLabels_merge_lt a hpq hpused hqused
  have hle' : (G.usedPacketLabels a).card ≤
      (G.usedPacketLabels (G.mergePacketLabels a p q)).card := by
    simpa [a'] using hle
  exact (not_le_of_gt hlt) hle'

/-- A partition of the original physical edges into bipartite packets.
All members of a packet have the same oriented endpoint pair, every packet
is nonempty, and its total weight is at most one. -/
structure BipartitePacketization (G : WeightedMultigraph.{u})
    (b : G.Bipartition) where
  Packet : Type u
  instFintypePacket : Fintype Packet
  instDecidableEqPacket : DecidableEq Packet
  packetOf : G.E → Packet
  tail : Packet → G.V
  head : Packet → G.V
  endpoints : ∀ e,
    b.leftEndpoint e = tail (packetOf e) ∧
      b.rightEndpoint e = head (packetOf e)
  onto : Function.Surjective packetOf
  weight_le_one : ∀ p,
    (∑ e : G.E, if packetOf e = p then G.weight e else 0) ≤ 1

attribute [instance]
  BipartitePacketization.instFintypePacket
  BipartitePacketization.instDecidableEqPacket

namespace BipartitePacketization

variable {b : G.Bipartition} (P : G.BipartitePacketization b)

/-- Total weight of the original edges in one packet. -/
def packetWeight (p : P.Packet) : ℝ :=
  ∑ e : G.E, if P.packetOf e = p then G.weight e else 0

theorem packetWeight_pos (p : P.Packet) : 0 < P.packetWeight p := by
  classical
  obtain ⟨e, he⟩ := P.onto p
  calc
    0 < G.weight e := G.weight_pos e
    _ = (if P.packetOf e = p then G.weight e else 0) := by simp [he]
    _ ≤ ∑ x : G.E,
        if P.packetOf x = p then G.weight x else 0 := by
      change (if P.packetOf e = p then G.weight e else 0) ≤
        ∑ x ∈ (Finset.univ : Finset G.E),
          if P.packetOf x = p then G.weight x else 0
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset G.E))
        (f := fun x ↦ if P.packetOf x = p then G.weight x else 0)
        (fun x _hx ↦ by
          by_cases hx : P.packetOf x = p
          · simp [hx, G.weight_nonneg]
          · simp [hx])
        (Finset.mem_univ e)

theorem packetWeight_le_one (p : P.Packet) : P.packetWeight p ≤ 1 :=
  P.weight_le_one p

theorem tail_side (p : P.Packet) : b.side (P.tail p) = false := by
  obtain ⟨e, he⟩ := P.onto p
  rw [← he, ← (P.endpoints e).1]
  exact b.side_leftEndpoint e

theorem head_side (p : P.Packet) : b.side (P.head p) = true := by
  obtain ⟨e, he⟩ := P.onto p
  rw [← he, ← (P.endpoints e).2]
  exact b.side_rightEndpoint e

theorem tail_ne_head (p : P.Packet) : P.tail p ≠ P.head p := by
  intro h
  have hs := congrArg b.side h
  rw [P.tail_side p, P.head_side p] at hs
  contradiction

/-- The grouped graph: every packet becomes one physical weighted edge. -/
noncomputable def groupedGraph : WeightedMultigraph.{u} where
  V := G.V
  E := P.Packet
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := inferInstance
  fst := P.tail
  snd := P.head
  noLoop := P.tail_ne_head
  weight := P.packetWeight
  weight_pos := P.packetWeight_pos
  weight_le_one := P.packetWeight_le_one

/-- The packet graph inherits the original bipartition. -/
noncomputable def groupedBipartition : P.groupedGraph.Bipartition where
  side := b.side
  opposite := by
    intro p
    change b.side (P.tail p) ≠ b.side (P.head p)
    rw [P.tail_side p, P.head_side p]
    decide

/-- Incidence is unchanged when an original edge is replaced by its packet. -/
theorem groupedGraph_inc_packetOf (v : G.V) (e : G.E) :
    P.groupedGraph.Inc v (P.packetOf e) ↔ G.Inc v e := by
  change P.tail (P.packetOf e) = v ∨ P.head (P.packetOf e) = v ↔
    G.fst e = v ∨ G.snd e = v
  rw [← (P.endpoints e).1, ← (P.endpoints e).2]
  unfold Bipartition.leftEndpoint Bipartition.rightEndpoint
  split <;> simp [or_comm]

/-- A color of packets expands canonically to a color of original edges. -/
def expandColor {q : ℕ} (color : P.Packet → Fin q) : G.E → Fin q :=
  fun e ↦ color (P.packetOf e)

/-- Original physical edges belonging to a chosen packet set. -/
def originalEdgesOfPackets (S : Finset P.Packet) : Finset G.E :=
  Finset.univ.filter fun e ↦ P.packetOf e ∈ S

theorem originalEdgesOfPackets_compl (S : Finset P.Packet) :
    P.originalEdgesOfPackets (Finset.univ \ S) =
      Finset.univ \ P.originalEdgesOfPackets S := by
  classical
  ext e
  simp [originalEdgesOfPackets]

/-- Restricted star weight is preserved by expanding a packet set. -/
theorem restrictedWeight_originalEdgesOfPackets
    (S : Finset P.Packet) (v : G.V) :
    (∑ e ∈ P.originalEdgesOfPackets S,
      if G.Inc v e then G.weight e else 0) =
    ∑ p ∈ S,
      if P.groupedGraph.Inc v p then P.packetWeight p else 0 := by
  classical
  change
    (∑ e ∈ Finset.univ.filter (fun e ↦ P.packetOf e ∈ S),
      if G.Inc v e then G.weight e else 0) = _
  rw [Finset.sum_filter]
  calc
    (∑ e : G.E,
      if P.packetOf e ∈ S then
        (if G.Inc v e then G.weight e else 0) else 0) =
      ∑ p ∈ S, ∑ e : G.E,
        if P.packetOf e = p ∧ P.groupedGraph.Inc v p
          then G.weight e else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases heS : P.packetOf e ∈ S
      · rw [Finset.sum_eq_single (P.packetOf e)]
        · have hinc := P.groupedGraph_inc_packetOf v e
          by_cases heinc : G.Inc v e
          · have hpinc : P.groupedGraph.Inc v (P.packetOf e) := hinc.mpr heinc
            simp [heS, heinc, hpinc]
          · have hpinc : ¬ P.groupedGraph.Inc v (P.packetOf e) :=
              fun h ↦ heinc (hinc.mp h)
            simp [heS, heinc, hpinc]
        · intro p _hpS hp
          simp [Ne.symm hp]
        · intro hnot
          exact (hnot heS).elim
      · have hzero :
          (∑ p ∈ S, if P.packetOf e = p ∧ P.groupedGraph.Inc v p
            then G.weight e else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro p hpS
          have hne : P.packetOf e ≠ p := fun h ↦ heS (h ▸ hpS)
          simp [hne]
        rw [hzero]
        simp [heS]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hpinc : P.groupedGraph.Inc v p
      · simp [packetWeight, hpinc, and_comm]
      · simp [hpinc]

/-- Restricted color loads are preserved by expanding a packet set. -/
theorem colorLoadOn_originalEdgesOfPackets
    {q : ℕ} (S : Finset P.Packet) (color : P.Packet → Fin q)
    (v : G.V) (i : Fin q) :
    G.colorLoadOn (P.originalEdgesOfPackets S) (P.expandColor color) v i =
      P.groupedGraph.colorLoadOn S color v i := by
  classical
  unfold WeightedMultigraph.colorLoadOn
  change
    (∑ e ∈ Finset.univ.filter (fun e ↦ P.packetOf e ∈ S),
      if G.Inc v e ∧ color (P.packetOf e) = i
        then G.weight e else 0) = _
  rw [Finset.sum_filter]
  change
    (∑ e : G.E,
      if P.packetOf e ∈ S then
        (if G.Inc v e ∧ color (P.packetOf e) = i
          then G.weight e else 0) else 0) =
    ∑ p ∈ S,
      if P.groupedGraph.Inc v p ∧ color p = i
        then P.packetWeight p else 0
  calc
    _ = ∑ p ∈ S, ∑ e : G.E,
        if P.packetOf e = p ∧
            (P.groupedGraph.Inc v p ∧ color p = i)
          then G.weight e else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases heS : P.packetOf e ∈ S
      · rw [Finset.sum_eq_single (P.packetOf e)]
        · have hinc := P.groupedGraph_inc_packetOf v e
          by_cases heinc : G.Inc v e
          · have hpinc : P.groupedGraph.Inc v (P.packetOf e) := hinc.mpr heinc
            simp [heS, heinc, hpinc]
          · have hpinc : ¬ P.groupedGraph.Inc v (P.packetOf e) :=
              fun h ↦ heinc (hinc.mp h)
            simp [heS, heinc, hpinc]
        · intro p _hpS hp
          simp [Ne.symm hp]
        · intro hnot
          exact (hnot heS).elim
      · have hzero :
          (∑ p ∈ S,
            if P.packetOf e = p ∧
                (P.groupedGraph.Inc v p ∧ color p = i)
              then G.weight e else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro p hpS
          have hne : P.packetOf e ≠ p := fun h ↦ heS (h ▸ hpS)
          simp [hne]
        rw [hzero]
        simp [heS]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hpi : P.groupedGraph.Inc v p ∧ color p = i
      · simp [packetWeight, hpi, and_assoc]
      · simp [hpi]

theorem isFeasibleOn_originalEdgesOfPackets
    {q : ℕ} (S : Finset P.Packet) (color : P.Packet → Fin q)
    (hcolor : P.groupedGraph.IsFeasibleOn S color) :
    G.IsFeasibleOn (P.originalEdgesOfPackets S) (P.expandColor color) := by
  intro v i
  rw [P.colorLoadOn_originalEdgesOfPackets S color v i]
  exact hcolor v i

/-- Expanding packets preserves every vertex-color load exactly. -/
theorem groupedGraph_colorLoad_expandColor
    {q : ℕ} (color : P.Packet → Fin q) (v : G.V) (i : Fin q) :
    P.groupedGraph.colorLoad color v i =
      G.colorLoad (P.expandColor color) v i := by
  classical
  rw [P.groupedGraph.colorLoad_eq_inc_sum,
    G.colorLoad_eq_inc_sum]
  change
    (∑ p : P.Packet,
      if P.groupedGraph.Inc v p ∧ color p = i then
        P.packetWeight p else 0) =
    ∑ e : G.E,
      if G.Inc v e ∧ color (P.packetOf e) = i then G.weight e else 0
  calc
    _ = ∑ p : P.Packet, ∑ e : G.E,
        if (P.groupedGraph.Inc v p ∧ color p = i) ∧
            P.packetOf e = p then G.weight e else 0 := by
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hpi : P.groupedGraph.Inc v p ∧ color p = i
      · simp [packetWeight, hpi]
      · simp [hpi]
    _ = ∑ e : G.E, ∑ p : P.Packet,
        if (P.groupedGraph.Inc v p ∧ color p = i) ∧
            P.packetOf e = p then G.weight e else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [Fintype.sum_eq_single (P.packetOf e)]
      · have hinc := P.groupedGraph_inc_packetOf v e
        by_cases heinc : G.Inc v e
        · have hpinc : P.groupedGraph.Inc v (P.packetOf e) := hinc.mpr heinc
          simp [hpinc, heinc]
        · have hpinc : ¬ P.groupedGraph.Inc v (P.packetOf e) :=
            fun h ↦ heinc (hinc.mp h)
          simp [hpinc, heinc]
      · intro p hp
        simp [Ne.symm hp]

/-- Any feasible coloring of the grouped graph expands to a feasible coloring
of all original edges with the same palette. -/
theorem isWeightedColoring_expandColor
    {q : ℕ} (color : P.Packet → Fin q)
    (hcolor : P.groupedGraph.IsWeightedColoring color) :
    G.IsWeightedColoring (P.expandColor color) := by
  intro v i
  rw [← P.groupedGraph_colorLoad_expandColor color v i]
  exact hcolor v i

theorem hasWeightedColoring_of_groupedGraph
    {q : ℕ} (h : P.groupedGraph.HasWeightedColoring q) :
    G.HasWeightedColoring q := by
  rcases h with ⟨color, hcolor⟩
  exact ⟨P.expandColor color, P.isWeightedColoring_expandColor color hcolor⟩

/-- Packet grouping preserves the total incident weight at every vertex. -/
theorem groupedGraph_starWeight (v : G.V) :
    P.groupedGraph.starWeight v = G.starWeight v := by
  classical
  rw [P.groupedGraph.starWeight_eq_inc_sum,
    G.starWeight_eq_inc_sum]
  change
    (∑ p : P.Packet,
      if P.groupedGraph.Inc v p then P.packetWeight p else 0) =
    ∑ e : G.E, if G.Inc v e then G.weight e else 0
  calc
    _ = ∑ p : P.Packet, ∑ e : G.E,
        if P.groupedGraph.Inc v p ∧ P.packetOf e = p
          then G.weight e else 0 := by
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hpi : P.groupedGraph.Inc v p
      · simp [packetWeight, hpi]
      · simp [hpi]
    _ = ∑ e : G.E, ∑ p : P.Packet,
        if P.groupedGraph.Inc v p ∧ P.packetOf e = p
          then G.weight e else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [Fintype.sum_eq_single (P.packetOf e)]
      · have hinc := P.groupedGraph_inc_packetOf v e
        by_cases heinc : G.Inc v e
        · have hpinc : P.groupedGraph.Inc v (P.packetOf e) := hinc.mpr heinc
          simp [hpinc, heinc]
        · have hpinc : ¬ P.groupedGraph.Inc v (P.packetOf e) :=
            fun h ↦ heinc (hinc.mp h)
          simp [hpinc, heinc]
      · intro p hp
        simp [Ne.symm hp]

/-- Packet grouping preserves the maximum weighted degree exactly. -/
theorem groupedGraph_deltaW : P.groupedGraph.deltaW = G.deltaW := by
  apply le_antisymm
  · apply (P.groupedGraph.deltaW_le_iff).2
    refine ⟨G.deltaW_nonneg, ?_⟩
    intro v
    rw [P.groupedGraph_starWeight v]
    exact G.starWeight_le_deltaW v
  · apply (G.deltaW_le_iff).2
    refine ⟨P.groupedGraph.deltaW_nonneg, ?_⟩
    intro v
    rw [← P.groupedGraph_starWeight v]
    exact P.groupedGraph.starWeight_le_deltaW v

/-- The light packets, with the manuscript's threshold `1/2`. -/
noncomputable def lightPackets : Finset P.Packet :=
  Finset.univ \ P.groupedGraph.heavyEdges

/-- The heavy packets. -/
noncomputable def heavyPackets : Finset P.Packet :=
  P.groupedGraph.heavyEdges

theorem heavyPackets_eq_groupedGraph_heavyEdges :
    P.heavyPackets = P.groupedGraph.heavyEdges := by
  rfl

theorem lightPackets_union_heavyPackets :
    P.lightPackets ∪ P.heavyPackets = Finset.univ := by
  classical
  unfold lightPackets heavyPackets
  exact Finset.sdiff_union_of_subset (Finset.subset_univ _)

theorem lightPackets_disjoint_heavyPackets :
    Disjoint P.lightPackets P.heavyPackets := by
  classical
  simp [lightPackets, heavyPackets, Finset.disjoint_left]

theorem packetWeight_le_half_of_mem_lightPackets
    {p : P.Packet} (hp : p ∈ P.lightPackets) :
    P.packetWeight p ≤ (1 / 2 : ℝ) := by
  classical
  have hp' : p ∈
      (Finset.univ \ P.groupedGraph.heavyEdges : Finset P.Packet) := hp
  have hnotheavy := (Finset.mem_sdiff.mp hp').2
  have hnlt : ¬ ((1 / 2 : ℝ) < P.packetWeight p) := by
    intro hlt
    apply hnotheavy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
  exact le_of_not_gt hnlt

/-- The light packet graph is simple precisely when no two light packets
have the same unordered endpoint pair. -/
def LightIsSimple : Prop :=
  Function.Injective
    (fun p : {p : P.Packet // p ∈ P.lightPackets} ↦
      s(P.tail p.1, P.head p.1))

/-- The simple weighted graph formed by the light packets. -/
noncomputable def lightGraph (hsimple : P.LightIsSimple) : WeightedSimpleGraph.{u} where
  V := G.V
  E := {p : P.Packet // p ∈ P.lightPackets}
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := inferInstance
  fst p := P.tail p.1
  snd p := P.head p.1
  noLoop p := P.tail_ne_head p.1
  simple := hsimple
  weight p := P.packetWeight p.1
  weight_pos p := P.packetWeight_pos p.1
  weight_le_one p := by
    have hhalf := P.packetWeight_le_half_of_mem_lightPackets p.2
    nlinarith

/-- The heavy packet graph has a proper `2n`-coloring whenever the original
maximum weighted degree is at most `n`. -/
theorem exists_heavyPackets_properColoring
    (n : ℕ) (hn : 0 < n) (hdelta : G.deltaW ≤ n) :
    ∃ color : P.Packet → Fin (2 * n),
      P.groupedGraph.IsProperOn P.heavyPackets color := by
  have hdelta' : P.groupedGraph.deltaW ≤ n := by
    rw [P.groupedGraph_deltaW]
    exact hdelta
  rw [P.heavyPackets_eq_groupedGraph_heavyEdges]
  exact P.groupedGraph.exists_heavyEdges_properColoring_bipartite
    P.groupedBipartition n hn hdelta'

end BipartitePacketization

/-- Every finite bipartite weighted multigraph admits the manuscript's
parallel-edge grouping: packets have weight at most one, and the packets of
weight at most one half form a simple graph.

We choose, among all feasible endpoint-respecting assignments to a fixed
finite label set, one using the fewest labels.  Two light packets on the same
endpoint pair could be merged, contradicting minimality. -/
theorem exists_bipartitePacketization
    (b : G.Bipartition) :
    ∃ P : G.BipartitePacketization b, P.LightIsSimple := by
  classical
  obtain ⟨a, ha, hminimal⟩ := G.exists_minimal_validPacketAssignment b
  let U : Type u := ULift.{u}
    {c : Fin (Fintype.card G.E) // c ∈ G.usedPacketLabels a}
  have hex (p : U) : ∃ e : G.E, a e = p.down.1 := by
    rcases Finset.mem_image.mp p.down.2 with ⟨e, _he, h⟩
    exact ⟨e, h⟩
  choose repr hre using hex
  let packetOf : G.E → U := fun e ↦
    ULift.up ⟨a e, Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩⟩
  have hpacket_eq (e : G.E) (p : U) :
      packetOf e = p ↔ a e = p.down.1 := by
    constructor
    · intro h
      exact congrArg (fun z : U ↦ z.down.1) h
    · intro h
      apply ULift.ext
      apply Subtype.ext
      exact h
  let tail : U → G.V := fun p ↦ b.leftEndpoint (repr p)
  let head : U → G.V := fun p ↦ b.rightEndpoint (repr p)
  let P : G.BipartitePacketization b := {
    Packet := U
    instFintypePacket := inferInstance
    instDecidableEqPacket := inferInstance
    packetOf := packetOf
    tail := tail
    head := head
    endpoints := by
      intro e
      have hlabel : a e = a (repr (packetOf e)) := by
        exact (hre (packetOf e)).symm
      have hends := ha.1 e (repr (packetOf e)) hlabel
      simpa [tail, head] using hends
    onto := by
      intro p
      refine ⟨repr p, ?_⟩
      apply ULift.ext
      apply Subtype.ext
      exact hre p
    weight_le_one := by
      intro p
      change (∑ e : G.E,
        if packetOf e = p then G.weight e else 0) ≤ 1
      calc
        _ = G.packetLabelWeight a p.down.1 := by
          unfold packetLabelWeight
          apply Finset.sum_congr rfl
          intro e _he
          by_cases h : packetOf e = p
          · have h' : a e = p.down.1 := (hpacket_eq e p).mp h
            simp [h, h']
          · have h' : a e ≠ p.down.1 := fun heq ↦
              h ((hpacket_eq e p).mpr heq)
            simp [h, h']
        _ ≤ 1 := ha.2 p.down.1
  }
  refine ⟨P, ?_⟩
  have hweight (p : P.Packet) :
      P.packetWeight p = G.packetLabelWeight a p.down.1 := by
    unfold BipartitePacketization.packetWeight packetLabelWeight
    apply Finset.sum_congr rfl
    intro e _he
    change (if packetOf e = p then G.weight e else 0) =
      if a e = p.down.1 then G.weight e else 0
    by_cases h : packetOf e = p
    · have h' : a e = p.down.1 := (hpacket_eq e p).mp h
      simp [h, h']
    · have h' : a e ≠ p.down.1 := fun heq ↦
        h ((hpacket_eq e p).mpr heq)
      simp [h, h']
  intro p q hpqEndpoints
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  by_contra hpqLabel
  have horiented :
      P.tail p.1 = P.tail q.1 ∧ P.head p.1 = P.head q.1 := by
    rcases Sym2.eq_iff.mp hpqEndpoints with hdirect | hswap
    · exact hdirect
    · exfalso
      have hs := congrArg b.side hswap.1
      rw [P.tail_side p.1, P.head_side q.1] at hs
      contradiction
  have hpweight :
      G.packetLabelWeight a p.1.down.1 ≤ (1 / 2 : ℝ) := by
    rw [← hweight p.1]
    exact P.packetWeight_le_half_of_mem_lightPackets p.2
  have hqweight :
      G.packetLabelWeight a q.1.down.1 ≤ (1 / 2 : ℝ) := by
    rw [← hweight q.1]
    exact P.packetWeight_le_half_of_mem_lightPackets q.2
  have hcross : ∀ e f, a e = p.1.down.1 → a f = q.1.down.1 →
      b.leftEndpoint e = b.leftEndpoint f ∧
        b.rightEndpoint e = b.rightEndpoint f := by
    intro e f hep hfq
    have heP := ha.1 e (repr p.1) (hep.trans (hre p.1).symm)
    have hfQ := ha.1 f (repr q.1) (hfq.trans (hre q.1).symm)
    refine ⟨?_, ?_⟩
    · exact heP.1.trans (horiented.1.trans hfQ.1.symm)
    · exact heP.2.trans (horiented.2.trans hfQ.2.symm)
  exact (G.no_mergeable_labels_of_minimal b a ha hminimal hpqLabel
    p.1.down.2 q.1.down.2 hcross hpweight hqweight).elim

end WeightedMultigraph
end WeightedEdgeColoring
