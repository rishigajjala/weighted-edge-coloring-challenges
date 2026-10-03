import WeightedEdgeColoring.SubtwoMixedGraphCapacitySelector

/-!
# Actual large and tiny candidate rows for mixed labelled graph atoms

A row fixes a color, center vertex, center mixed atom, and for large edges a
padded ordinary slot.  A source atom contributes only through an edge to the
opposite endpoint.  Both orientations use the same unconditioned paired
mass, while the center and source states keep their own endpoint labels.
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

structure MixedLargeCandidateRow (c : Color) where
  center : G.V
  candidate : G.MixedGraphAtom proposal edgeLabel qLaw R center c
  slot : Fin (explicitLargeSlotBound β qstep r)

structure MixedTinyCandidateRow (c : Color) where
  center : G.V
  candidate : G.MixedGraphAtom proposal edgeLabel qLaw R center c

def mixedLargeCandidateRowEquiv (c : Color) :
    G.MixedLargeCandidateRow proposal edgeLabel qLaw R c ≃
      Σ v : G.V,
        G.MixedGraphAtom proposal edgeLabel qLaw R v c ×
          Fin (explicitLargeSlotBound β qstep r) where
  toFun row := ⟨row.center, row.candidate, row.slot⟩
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv row := by cases row; rfl
  right_inv x := by rcases x with ⟨v, a, i⟩; rfl

noncomputable instance (c : Color) : Fintype
    (G.MixedLargeCandidateRow proposal edgeLabel qLaw R c) :=
  Fintype.ofEquiv _
    (G.mixedLargeCandidateRowEquiv proposal edgeLabel qLaw R c).symm

noncomputable instance (c : Color) : DecidableEq
    (G.MixedLargeCandidateRow proposal edgeLabel qLaw R c) :=
  Classical.decEq _

def mixedTinyCandidateRowEquiv (c : Color) :
    G.MixedTinyCandidateRow proposal edgeLabel qLaw R c ≃
      Σ v : G.V, G.MixedGraphAtom proposal edgeLabel qLaw R v c where
  toFun row := ⟨row.center, row.candidate⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv row := by cases row; rfl
  right_inv x := by rcases x with ⟨v, a⟩; rfl

noncomputable instance (c : Color) : Fintype
    (G.MixedTinyCandidateRow proposal edgeLabel qLaw R c) :=
  Fintype.ofEquiv _
    (G.mixedTinyCandidateRowEquiv proposal edgeLabel qLaw R c).symm

noncomputable instance (c : Color) : DecidableEq
    (G.MixedTinyCandidateRow proposal edgeLabel qLaw R c) :=
  Classical.decEq _

abbrev MixedCandidateRowAt (c : Color) :=
  G.MixedLargeCandidateRow proposal edgeLabel qLaw R c ⊕
    G.MixedTinyCandidateRow proposal edgeLabel qLaw R c

def mixedLargeCandidateEdgeUse
    (rho omega : ℝ) (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c)
    (e : G.E) (row : G.MixedLargeCandidateRow
      proposal edgeLabel qLaw R c) : ℝ :=
  if h : row.center = G.fst e ∧ source = G.snd e then
    ∑ j, G.mixedGraphLargeProductMass proposal edgeLabel qLaw R
      rho omega e c (h.1 ▸ row.candidate)
        (h.2 ▸ sourceAtom) row.slot j
  else if h : row.center = G.snd e ∧ source = G.fst e then
    ∑ i, G.mixedGraphLargeProductMass proposal edgeLabel qLaw R
      rho omega e c (h.2 ▸ sourceAtom)
        (h.1 ▸ row.candidate) i row.slot
  else 0

def mixedTinyCandidateEdgeUse
    (rho omega : ℝ) (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c)
    (e : G.E) (row : G.MixedTinyCandidateRow
      proposal edgeLabel qLaw R c) : ℝ :=
  if h : row.center = G.fst e ∧ source = G.snd e then
    G.weight e * G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
      rho omega e c (h.1 ▸ row.candidate) (h.2 ▸ sourceAtom)
  else if h : row.center = G.snd e ∧ source = G.fst e then
    G.weight e * G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
      rho omega e c (h.2 ▸ sourceAtom) (h.1 ▸ row.candidate)
  else 0

def mixedCandidateAtomUse
    (rho omega : ℝ) (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c)
    (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c) : ℝ :=
  match row with
  | Sum.inl large =>
      ∑ e, G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
        rho omega source c sourceAtom e large
  | Sum.inr tiny =>
      ∑ e, G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
        rho omega source c sourceAtom e tiny

def scaledMixedCandidateAtomUse
    (n : ℕ) (scale rho omega : ℝ)
    (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c)
    (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c) : ℝ :=
  (n : ℝ) *
    G.mixedCandidateAtomUse proposal edgeLabel qLaw R
      rho omega source c sourceAtom row / scale

end WeightedMultigraph

end

end WeightedEdgeColoring
