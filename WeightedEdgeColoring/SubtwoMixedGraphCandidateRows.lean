import WeightedEdgeColoring.SubtwoMixedGraphPairing

/-!
# Diffuse candidate envelope for mixed labelled graph atoms

This module bounds the common padded atom alphabet and the ratio between
one atom and its smoothed sampling probability.  It also records the
nonnegative per-edge assignments and their pointwise bound by the shared
unconditioned edge mass.  These are the finite-state and coefficient
hypotheses of the existing candidate-capacity argument.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {Color Label : Type*} [Fintype Color] [DecidableEq Color]
  [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → Color → ℝ)
variable (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
variable (qLaw : ∀ v : G.V, Color → Finset (G.StarEdge v) → ℝ)
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : ∀ v c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel v)
      (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
    s β qstep r hβ hr)

def mixedGraphAtomBound : ℕ :=
  1 + Fintype.card Label * extendedProfileStateBound β qstep r

theorem localExtendedProfileState_card_le
    (v : G.V) (c : Color) (label : Label) :
    Fintype.card (G.LocalExtendedProfileState (R v c label)) ≤
      extendedProfileStateBound β qstep r := by
  have hmenu : Fintype.card {P // P ∈
      G.roundedProfileMenu (R v c label).law hβ hr} ≤
      Fintype.card (G.RoundedProfileIndex (R v c label).law hβ hr) := by
    simp [RoundedProfileIndex]
  have hprofile : Fintype.card {P // P ∈
      G.roundedProfileMenu (R v c label).law hβ hr} ≤
      profileStateBound β qstep r :=
    hmenu.trans
      (G.roundedProfileIndex_card_le_parameters
        (R v c label).law hβ hr)
  simpa [LocalExtendedProfileState, extendedProfileStateBound] using
    Nat.add_le_add_right hprofile 3

theorem mixedGraphAtom_card_le (v : G.V) (c : Color) :
    Fintype.card (G.MixedGraphAtom proposal edgeLabel qLaw R v c) ≤
      mixedGraphAtomBound (Label := Label) (β := β) (qstep := qstep) (r := r) := by
  classical
  exact Subtwo.labelMixtureAtom_card_le
    (fun label ↦ G.LocalExtendedProfileState (R v c label))
    (extendedProfileStateBound β qstep r)
    (fun label ↦ G.localExtendedProfileState_card_le
      proposal edgeLabel qLaw R v c label)

theorem one_le_mixedGraphAtomRatio_mul_smoothedProbability
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel v e = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c) :
    1 ≤ ((mixedGraphAtomBound (Label := Label) (β := β) (qstep := qstep) (r := r) : ℝ) / omega) *
      G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
        omega v c a := by
  have hbase := G.mixedLabelGraphAtomProbability_nonneg
    (edgeLabel v) (fun e : G.StarEdge v ↦ proposal e.1 c)
    (qLaw v c) (R v c) (hq0 v c) (hqsum v c)
    (hqsingle v c) hs hqstep hr0 hleft a
  have hcardPos : 0 < (Fintype.card
      (G.MixedGraphAtom proposal edgeLabel qLaw R v c) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hboundPos : 0 < (mixedGraphAtomBound (Label := Label) (β := β) (qstep := qstep) (r := r) : ℝ) := by
    unfold mixedGraphAtomBound
    positivity
  have hcard : (Fintype.card
      (G.MixedGraphAtom proposal edgeLabel qLaw R v c) : ℝ) ≤
      mixedGraphAtomBound (Label := Label) (β := β) (qstep := qstep) (r := r) := by
    exact_mod_cast G.mixedGraphAtom_card_le
      proposal edgeLabel qLaw R v c
  have hrecip : omega / mixedGraphAtomBound (Label := Label) (β := β) (qstep := qstep) (r := r) ≤
      omega / Fintype.card
        (G.MixedGraphAtom proposal edgeLabel qLaw R v c) := by
    exact div_le_div_of_nonneg_left homega0.le hcardPos hcard
  have hlower : omega / mixedGraphAtomBound (Label := Label) (β := β) (qstep := qstep) (r := r) ≤
      G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
        omega v c a := by
    unfold smoothedMixedGraphProbability
    exact hrecip.trans (le_add_of_nonneg_left
      (mul_nonneg (sub_nonneg.mpr homega1) hbase))
  have hratio : 0 <
      (mixedGraphAtomBound (Label := Label) (β := β) (qstep := qstep) (r := r) : ℝ) / omega :=
    div_pos hboundPos homega0
  calc
    (1 : ℝ) =
        ((mixedGraphAtomBound (Label := Label) (β := β) (qstep := qstep) (r := r) : ℝ) / omega) *
          (omega / mixedGraphAtomBound (Label := Label) (β := β) (qstep := qstep) (r := r)) := by
      field_simp
    _ ≤ ((mixedGraphAtomBound (Label := Label) (β := β) (qstep := qstep) (r := r) : ℝ) / omega) *
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega v c a :=
      mul_le_mul_of_nonneg_left hlower hratio.le

theorem mixedGraphLargeAssign_nonneg
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (i : Fin (explicitLargeSlotBound β qstep r)) :
    0 ≤ G.mixedGraphLargeAssign proposal edgeLabel qLaw R v c e a i := by
  cases a with
  | none => simp [mixedGraphLargeAssign, mixedLabelGraphLargeAssign]
  | some lz =>
      exact mul_nonneg
        (G.subsetLabelMass_nonneg_local (edgeLabel v) (qLaw v c)
          (hq0 v c) lz.1)
        (G.localExtendedProfileLargeAssign_nonneg (R v c lz.1)
          e lz.2 i)

theorem mixedGraphTinyAssign_nonneg
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c) :
    0 ≤ G.mixedGraphTinyAssign proposal edgeLabel qLaw R v c e a := by
  cases a with
  | none => simp [mixedGraphTinyAssign, mixedLabelGraphTinyAssign]
  | some lz =>
      exact mul_nonneg
        (G.subsetLabelMass_nonneg_local (edgeLabel v) (qLaw v c)
          (hq0 v c) lz.1)
        (G.localExtendedProfileTinyAssign_nonneg (R v c lz.1)
          e lz.2)

theorem sum_mixedGraphLargeAssign_le_edgeMass
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (e : G.StarEdge v),
      (∑ S, if e ∈ S then qLaw v c S else 0) = proposal e.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel v e = label)
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c) :
    (∑ i, G.mixedGraphLargeAssign proposal edgeLabel qLaw R v c e a i) ≤
      G.mixedGraphLargeEdgeMass proposal s β e.1 c := by
  have hsingle :
      (∑ i, G.mixedGraphLargeAssign proposal edgeLabel qLaw R v c e a i) ≤
      ∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
        ∑ i, G.mixedGraphLargeAssign proposal edgeLabel qLaw R v c e a i :=
    Finset.single_le_sum
      (fun b _ ↦ Finset.sum_nonneg fun i _ ↦
        G.mixedGraphLargeAssign_nonneg
          proposal edgeLabel qLaw R hq0 v c e b i)
      (Finset.mem_univ a)
  exact hsingle.trans (le_of_eq (by
    simpa [mixedGraphLargeAssign, mixedGraphLargeEdgeMass] using
      G.sum_mixedLabelGraphLargeAssign
        (edgeLabel v) (fun f : G.StarEdge v ↦ proposal f.1 c)
        (qLaw v c) (R v c) (hq0 v c) (hqmarg v c)
        (hqsingle v c) e))

theorem mixedGraphTinyAssign_le_edgeMass
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (e : G.StarEdge v),
      (∑ S, if e ∈ S then qLaw v c S else 0) = proposal e.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel v e = label)
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c) :
    G.mixedGraphTinyAssign proposal edgeLabel qLaw R v c e a ≤
      G.mixedGraphTinyEdgeMass proposal s β e.1 c := by
  have hsingle :
      G.mixedGraphTinyAssign proposal edgeLabel qLaw R v c e a ≤
      ∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
        G.mixedGraphTinyAssign proposal edgeLabel qLaw R v c e a :=
    Finset.single_le_sum
      (fun b _ ↦ G.mixedGraphTinyAssign_nonneg
        proposal edgeLabel qLaw R hq0 v c e b)
      (Finset.mem_univ a)
  exact hsingle.trans (le_of_eq (by
    simpa [mixedGraphTinyAssign, mixedGraphTinyEdgeMass] using
      G.sum_mixedLabelGraphTinyAssign
        (edgeLabel v) (fun f : G.StarEdge v ↦ proposal f.1 c)
        (qLaw v c) (R v c) (hq0 v c) (hqmarg v c)
        (hqsingle v c) e))

end WeightedMultigraph

end

end WeightedEdgeColoring
