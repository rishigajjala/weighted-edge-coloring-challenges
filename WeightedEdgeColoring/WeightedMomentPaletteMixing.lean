import WeightedEdgeColoring.BipartitePackets

/-!
# The remaining weighted-moment palette-mixing statement

The deterministic lemmas in `PaletteMixing` assume a pointwise lower bound
on every common missing palette.  The Kempe-switch lemma used by the
coefficient-two proof is weaker: a small exceptional set of residual edge
weight may have poor palette overlap.  It directly constructs fractional
proposals and controls their total uncovered charge.

`WeightedMomentPaletteMixing` records exactly that remaining existence
statement in epsilon--threshold form.  It is a proposition to be proved,
not a theorem established in this file.  The recoloring is only required to
remain proper on `F`; reachability by explicit Kempe path switches is a proof
mechanism and is not consumed by any later coloring argument.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Total residual charge incident with one vertex. -/
def restrictedCharge (R : Finset G.E) (charge : G.E → ℝ)
    (v : G.V) : ℝ :=
  ∑ e ∈ R, if G.Inc v e then charge e else 0

/-- Total residual charge joining one unordered pair of vertices. -/
def pairCharge (R : Finset G.E) (charge : G.E → ℝ)
    (u v : G.V) : ℝ :=
  ∑ e ∈ R,
    if (G.fst e = u ∧ G.snd e = v) ∨
        (G.fst e = v ∧ G.snd e = u) then charge e else 0

/-- Charge in one vertex--color proposal row. -/
def proposalChargeLoad {q : ℕ} (R : Finset G.E)
    (charge : G.E → ℝ) (x : G.E → Fin q → ℝ)
    (v : G.V) (c : Fin q) : ℝ :=
  ∑ e ∈ R, if G.Inc v e then charge e * x e c else 0

/-- Residual charge not covered by the fractional proposal. -/
def uncoveredProposalCharge {q : ℕ} (R : Finset G.E)
    (charge : G.E → ℝ) (x : G.E → Fin q → ℝ)
    (v : G.V) : ℝ :=
  ∑ e ∈ R,
    if G.Inc v e then charge e * (1 - ∑ c, x e c) else 0

/-- Any two proper colorings of the same edge set have the same number of
missing colors at every vertex.  Thus the downstream argument does not need
to remember the individual Kempe switches, only the final proper coloring. -/
theorem card_missingColorsAt_eq_of_isProperOn
    {q : ℕ} (F : Finset G.E) (left right : G.E → Fin q)
    (hleft : G.IsProperOn F left) (hright : G.IsProperOn F right)
    (v : G.V) :
    (G.missingColorsAt F left v).card =
      (G.missingColorsAt F right v).card := by
  rw [G.card_missingColorsAt F left hleft v,
    G.card_missingColorsAt F right hright v]

end WeightedMultigraph

universe u

/-- Uniform weighted-moment mixing by proper recoloring.

`F` is the already properly colored packet set and `R` is the residual
packet set.  `charge` may differ from physical edge weight.  The assumptions
say that every vertex has linearly many missing colors, the palette is
linear in the scale `n`, residual charge at a vertex is at most `n`, and
the charge on one parallel class is bounded by the fixed constant `L`.

For every fixed error `eps`, the conclusion gives a new proper coloring and
fractional residual proposals.  The proposals use only colors missing at
both endpoints, have entries of order `1/n`, have the desired one-row charge
bound, and leave at most `eps * n` charge uncovered at every vertex.

The evenness and `4 ≤ q` assumptions are precisely those used to pair colors
in the Kempe-switch proof. -/
def WeightedMomentPaletteMixing : Prop :=
  ∀ alpha C L eps : ℝ,
    0 < alpha → 0 < C → 0 < L → 0 < eps →
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (n q : ℕ)
      (F R : Finset G.E) (base : G.E → Fin q) (charge : G.E → ℝ),
      N ≤ n →
      0 < n →
      Even q →
      4 ≤ q →
      Disjoint F R →
      G.IsProperOn F base →
      (∀ v,
        alpha * n ≤ (G.missingColorsAt F base v).card) →
      (q : ℝ) ≤ C * n →
      (∀ e ∈ R, 0 ≤ charge e) →
      (∀ v, G.restrictedCharge R charge v ≤ n) →
      (∀ u v, G.pairCharge R charge u v ≤ L) →
      ∃ (mixed : G.E → Fin q) (x : G.E → Fin q → ℝ),
        G.IsProperOn F mixed ∧
        (∀ e ∈ R, ∀ c, 0 < x e c →
          c ∈ G.missingColorsAt F mixed (G.fst e) ∧
            c ∈ G.missingColorsAt F mixed (G.snd e)) ∧
        (∀ e ∈ R, ∀ c,
          0 ≤ x e c ∧ x e c ≤ C / (alpha ^ 2 * n)) ∧
        (∀ e ∈ R, ∑ c, x e c ≤ 1) ∧
        (∀ v c,
          G.proposalChargeLoad R charge x v c ≤
            G.restrictedCharge R charge v /
                (G.missingColorsAt F mixed v).card + eps) ∧
        ∀ v, G.uncoveredProposalCharge R charge x v ≤ eps * n

end WeightedEdgeColoring
