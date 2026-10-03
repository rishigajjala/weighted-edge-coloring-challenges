import WeightedEdgeColoring.BPOrdinaryCriticalChainThree
import WeightedEdgeColoring.BPOrdinaryCriticalTriangleCertificate

/-!
# Critical chains at the seven-sixths degree threshold

The quotient in the coefficient-1.999 proof needs less than the full
near-fractional ordinary edge-coloring theorem.  Andersen's `m = 7`
theorem suffices, since `(7/6) * 1.691031 < 1.999`.

This module proves the chain-length restriction used in that theorem.
It does not assert the subsequent five-vertex saturation argument.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Successive witnesses of a simple two-color path have different colors. -/
theorem path_witness_colors_ne
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    (hproper : G.IsProperOn F color) {a b : Fin k} {x y : G.V}
    (p : (G.twoColorGraph F color a b).Path x y)
    (i : ℕ) (hi : i + 1 < p.1.length)
    {g r : G.E} (hgF : g ∈ F) (hrF : r ∈ F)
    (hgi : G.Inc (p.1.getVert i) g)
    (hgi1 : G.Inc (p.1.getVert (i + 1)) g)
    (hri1 : G.Inc (p.1.getVert (i + 1)) r)
    (hri2 : G.Inc (p.1.getVert (i + 2)) r) :
    color g ≠ color r := by
  have h01 : p.1.getVert (i + 1) ≠ p.1.getVert i :=
    (p.1.adj_getVert_succ (i := i) (by omega)).ne.symm
  have h12 : p.1.getVert (i + 1) ≠ p.1.getVert (i + 2) := by
    simpa [Nat.add_assoc] using
      (p.1.adj_getVert_succ (i := i + 1) hi).ne
  have h02 : p.1.getVert i ≠ p.1.getVert (i + 2) := by
    intro h
    have hidx := p.property.getVert_injOn
      (show i ∈ Set.Iic p.1.length by simp only [Set.mem_Iic]; omega)
      (show i + 2 ∈ Set.Iic p.1.length by simp only [Set.mem_Iic]; omega) h
    omega
  exact G.color_ne_of_isProperOn_of_incident_otherEndpoints_ne hproper
    h01 h12 h02 hgF hrF hgi1 hgi hri1 hri2

/-- An alternating list starting with `b` ends with `a` only at even length. -/
private theorem even_length_of_alternating
    {α : Type*} {a b : α} (hab : a ≠ b) (n : ℕ) (hn : 0 < n)
    (f : Fin n → α) (hfirst : f ⟨0, hn⟩ = b)
    (hlast : f ⟨n - 1, by omega⟩ = a)
    (hvalues : ∀ i, f i = a ∨ f i = b)
    (hnext : ∀ (i : ℕ) (hi : i + 1 < n),
      f ⟨i, by omega⟩ ≠ f ⟨i + 1, hi⟩) : Even n := by
  have halt : ∀ (i : ℕ) (hi : i < n),
      f ⟨i, hi⟩ = if i % 2 = 0 then b else a := by
    intro i
    induction i with
    | zero => intro hi; simpa using hfirst
    | succ i ih =>
        intro hi
        have hprev := ih (by omega)
        have hdiff := hnext i hi
        have hval := hvalues ⟨i + 1, hi⟩
        split_ifs at hprev ⊢ with hp hc
        · omega
        · rcases hval with hval | hval
          · exact False.elim (hdiff (hprev.trans hval.symm))
          · exact hval
        · rcases hval with hval | hval
          · exact hval
          · exact False.elim (hdiff (hprev.trans hval.symm))
        · omega
  have hlast' := halt (n - 1) (by omega)
  have hoddLast : (n - 1) % 2 ≠ 0 := by
    intro h
    rw [if_pos h] at hlast'
    exact hab (hlast.symm.trans hlast')
  rw [Nat.even_iff]
  omega

/-- A critical endpoint chain has even edge length. This uses only
properness and the two endpoint-missing colors, not a degree threshold. -/
theorem criticalPath_even_length
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) : Even p.1.length := by
  classical
  have hn : 0 < p.1.length := by
    by_contra h
    have hz : p.1.length = 0 := by omega
    exact G.noLoop e (SimpleGraph.Walk.eq_of_length_eq_zero hz)
  have hwitness (i : Fin p.1.length) := G.exists_twoColorWitnessEdge
    (F.erase e) color a b (p.1.adj_getVert_succ i.isLt)
  choose edge hedgeF hedgeLeft hedgeRight hedgeColor using hwitness
  have hfirst : color (edge ⟨0, hn⟩) = b := by
    apply (hedgeColor ⟨0, hn⟩).resolve_left
    apply G.color_ne_of_mem_missingColorsAt (F.erase e) color (G.fst e) a ha
      (hedgeF ⟨0, hn⟩)
    simpa using hedgeLeft ⟨0, hn⟩
  have hlast : color (edge ⟨p.1.length - 1, by omega⟩) = a := by
    apply (hedgeColor ⟨p.1.length - 1, by omega⟩).resolve_right
    apply G.color_ne_of_mem_missingColorsAt (F.erase e) color (G.snd e) b hb
      (hedgeF ⟨p.1.length - 1, by omega⟩)
    have hend : p.1.length - 1 + 1 = p.1.length := by omega
    simpa [hend] using hedgeRight ⟨p.1.length - 1, by omega⟩
  apply even_length_of_alternating
    (G.critical_endpoint_missingColors_ne hcritical heF hproper ha hb)
    p.1.length hn (fun i ↦ color (edge i)) hfirst hlast hedgeColor
  intro i hi
  exact G.path_witness_colors_ne hproper p i hi
    (hedgeF ⟨i, by omega⟩) (hedgeF ⟨i + 1, hi⟩)
    (hedgeLeft ⟨i, by omega⟩) (hedgeRight ⟨i, by omega⟩)
    (hedgeLeft ⟨i + 1, hi⟩) (hedgeRight ⟨i + 1, hi⟩)

/-- Andersen's palette count at an arbitrary integer threshold. -/
theorem criticalPath_support_card_lt_threshold
    {F : Finset G.E} {k d m : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hdk : d < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : k < m * (k - d) + 2) :
    p.1.support.toFinset.card < m := by
  have hcount := G.criticalPath_card_mul_sub_add_two_le
    hcritical heF hproper ha hb p hdk hdegree
  by_contra hnot
  have hm : m ≤ p.1.support.toFinset.card := by omega
  have hmul := Nat.mul_le_mul_right (k - d) hm
  omega

/-- The precise chain restriction needed for Andersen's `m = 7` step. -/
theorem criticalPath_support_card_eq_three_or_five
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hdk : d < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2) :
    p.1.support.toFinset.card = 3 ∨ p.1.support.toFinset.card = 5 := by
  have hcard := G.criticalPath_support_card_lt_threshold
    hcritical heF hproper ha hb p hdk hdegree
    (m := 7) (by omega)
  have hcardLength : p.1.support.toFinset.card = p.1.length + 1 := by
    rw [List.toFinset_card_of_nodup p.property.support_nodup,
      p.1.length_support]
  have hpositive : 0 < p.1.length := by
    by_contra h
    have hz : p.1.length = 0 := by omega
    exact G.noLoop e (SimpleGraph.Walk.eq_of_length_eq_zero hz)
  obtain ⟨r, hr⟩ := G.criticalPath_even_length hcritical heF hproper ha hb p
  omega

/-- Counting all color fibers counts each internal edge exactly once. -/
theorem palette_mul_le_of_internal_color_fibers
    {F : Finset G.E} {S : Finset G.V} {k r : ℕ}
    (color : G.E → Fin k)
    (hall : ∀ c : Fin k,
      r ≤ ((G.internalEdges F S).filter (fun g ↦ color g = c)).card) :
    k * r ≤ (G.internalEdges F S).card := by
  classical
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
    (fun c _ ↦ hall c)
  have hfibers :
      (∑ c : Fin k,
        ((G.internalEdges F S).filter (fun g ↦ color g = c)).card) =
      (G.internalEdges F S).card := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter
      (G.internalEdges F S) (Finset.univ : Finset (Fin k)) color
  simpa [hfibers, Nat.mul_comm] using hsum

/-- Saturating each palette color on an odd set gives the strict density
certificate after restoring the omitted edge. Properness is needed only
to establish saturation, not for this counting implication. -/
theorem oddSetCertificate_of_saturated_internal_color_fibers
    {F : Finset G.E} {S : Finset G.V} {e : G.E} {k r : ℕ}
    (color : G.E → Fin k) (hr : 0 < r) (hS : S.card = 2 * r + 1)
    (heF : e ∈ F) (heS : G.fst e ∈ S ∧ G.snd e ∈ S)
    (hall : ∀ c : Fin k,
      r ≤ ((G.internalEdges (F.erase e) S).filter
        (fun g ↦ color g = c)).card) :
    Odd S.card ∧ 3 ≤ S.card ∧
      (k : ℝ) * ((S.card : ℝ) - 1) <
        (2 : ℝ) * (G.internalEdges F S).card := by
  have hcount := G.palette_mul_le_of_internal_color_fibers color hall
  have hrestore := G.card_internalEdges_erase_add_one_le heF heS
  have hstrict : k * r < (G.internalEdges F S).card := by omega
  have hreal : (k : ℝ) * r < (G.internalEdges F S).card := by
    exact_mod_cast hstrict
  refine ⟨?_, by omega, ?_⟩
  · exact ⟨r, by omega⟩
  · rw [hS]
    push_cast
    nlinarith

/-- The final counting step of Andersen's five-vertex case. -/
theorem oddSetCertificate_of_allColors_twice_internal_five
    {F : Finset G.E} {S : Finset G.V} {e : G.E} {k : ℕ}
    (color : G.E → Fin k) (hS : S.card = 5)
    (heF : e ∈ F) (heS : G.fst e ∈ S ∧ G.snd e ∈ S)
    (hall : ∀ c : Fin k,
      2 ≤ ((G.internalEdges (F.erase e) S).filter
        (fun g ↦ color g = c)).card) :
    Odd S.card ∧ 3 ≤ S.card ∧
      (k : ℝ) * ((S.card : ℝ) - 1) <
        (2 : ℝ) * (G.internalEdges F S).card :=
  G.oddSetCertificate_of_saturated_internal_color_fibers
    color (by decide : 0 < (2 : ℕ)) hS heF heS hall

end WeightedEdgeColoring.WeightedMultigraph
