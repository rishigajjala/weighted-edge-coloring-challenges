import WeightedEdgeColoring.SubtwoOrdinaryFiveAllColorsCertificate

/-!
# Uniformly short critical chains in the absence of an odd-set obstruction

The five-path saturation theorem applies to every recoloring of a fixed
critical graph. Thus if that graph has no odd-set violation at palette size
`k`, every critical endpoint chain has length two.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

def NoOddSetCertificateAt (F : Finset G.E) (k : ℕ) : Prop :=
  ¬∃ S : Finset G.V, Odd S.card ∧ 3 ≤ S.card ∧
    (k : ℝ) * ((S.card : ℝ) - 1) <
      (2 : ℝ) * (G.internalEdges F S).card

theorem criticalPath_length_eq_two_of_no_oddSetCertificate
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hno : G.NoOddSetCertificateAt F k) :
    p.1.length = 2 := by
  have hcard := G.criticalPath_support_card_eq_three_or_five
    hcritical heF hproper ha hb p (by omega) hdegree hthreshold
  have hcardLength : p.1.support.toFinset.card = p.1.length + 1 := by
    rw [List.toFinset_card_of_nodup p.property.support_nodup,
      p.1.length_support]
  rcases hcard with hthree | hfive
  · omega
  · have hpLen : p.1.length = 4 := by omega
    exact False.elim (hno (G.oddSetCertificate_of_critical_fivePath
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold))

end WeightedEdgeColoring.WeightedMultigraph
