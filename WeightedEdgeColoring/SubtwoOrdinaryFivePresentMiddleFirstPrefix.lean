import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleFirstChordDichotomy
import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleRotateTransport
import WeightedEdgeColoring.SubtwoOrdinaryFivePresentVZ1Prefix

/-!
# Exterior prefix at a middle first return
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- The part of the right `(b,c)` path preceding its first return to
the five old vertices is genuinely exterior, independent of which
old vertex is met first. -/
theorem FivePathState.first_return_exterior_prefix
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    {z : G.V}
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right z)
    {i : ℕ} (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hit : p.1.getVert i ∈ s.path.1.support.toFinset) :
    ∃ q : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
        s.right (p.1.getVert i),
      q.1.length = i ∧
        (∀ v ∈ q.1.support,
          v ∈ s.path.1.support.toFinset →
            v = s.right ∨ v = p.1.getVert i) := by
  classical
  have hmem : p.1.getVert i ∈ p.1.support :=
    p.1.getVert_mem_support i
  let qWalk := p.1.takeUntil (p.1.getVert i) hmem
  let q : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right (p.1.getVert i) :=
    ⟨qWalk, p.property.takeUntil hmem⟩
  have hqLenLe : q.1.length ≤ p.1.length :=
    p.1.length_takeUntil_le hmem
  have hqEnd : p.1.getVert q.1.length = p.1.getVert i :=
    p.1.getVert_length_takeUntil hmem
  have hqLen : q.1.length = i := by
    apply p.property.getVert_injOn
      (Set.mem_Iic.mpr hqLenLe)
      (Set.mem_Iic.mpr hiLe)
    exact hqEnd
  refine ⟨q, hqLen, ?_⟩
  intro v hv hvS
  obtain ⟨j, hj, hjLe⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
  have hpj : p.1.getVert j = v := by
    exact (p.1.getVert_takeUntil hmem hjLe).symm.trans hj
  have hjI : j ≤ i := by omega
  by_cases hj0 : j = 0
  · left
    have hstart : p.1.getVert 0 = s.right := p.1.getVert_zero
    exact hpj.symm.trans (by simpa [hj0] using hstart)
  by_cases hjIeq : j = i
  · right
    exact hpj.symm.trans (by simpa [hjIeq])
  exact False.elim (hfirst j (by omega) (by omega) (hpj ▸ hvS))

/-- A first return at `Z₂` remains an exterior route to `Z₂` after
switching the old critical `(a,b)` path. -/
theorem FivePathState.exists_switched_z2_prefix
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    {z : G.V}
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right z)
    {i : ℕ} (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ2 : p.1.getVert i = s.path.1.getVert 2) :
    ∃ switched : G.E → Fin k,
      G.IsProperOn (F.erase s.omitted) switched ∧
      (∀ v ∈ s.path.1.support,
        ∀ r ∈ F.erase s.omitted, G.Inc v r →
          s.paint r = a → switched r = b) ∧
      (∀ v ∈ s.path.1.support,
        ∀ r ∈ F.erase s.omitted, G.Inc v r →
          s.paint r = b → switched r = a) ∧
      (∀ r, s.paint r ≠ a → s.paint r ≠ b →
        switched r = s.paint r) ∧
      ∃ q : (G.twoColorGraph (F.erase s.omitted) switched b c).Path
        s.right (s.path.1.getVert 2),
        q.1.length = i ∧
          (∀ v ∈ q.1.support,
            v ∈ s.path.1.support.toFinset →
              v = s.right ∨ v = s.path.1.getVert 2) := by
  obtain ⟨q₀, hqLen, hqSupport⟩ :=
    FivePathState.first_return_exterior_prefix G s p hiLe hfirst
      (hiZ2 ▸ by simpa only [List.mem_toFinset] using
        s.path.1.getVert_mem_support 2)
  obtain ⟨switched, hproper, hswapA, hswapB, hother, hstable⟩ :=
    FivePathState.exists_ab_path_switch_stable_outside G s hcritical
  have hno : ¬(G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj
      s.right (s.path.1.getVert 2) :=
    FivePathState.no_right_bc_adj_old_vertex G s hright
      (by simpa only [List.mem_toFinset] using
        s.path.1.getVert_mem_support 2)
  have hExterior := G.exterior_edges_of_endpoint_only_support
    (G.twoColorGraph (F.erase s.omitted) s.paint b c)
    (fun v ↦ v ∈ s.path.1.support) q₀
    (by intro v hv hvS
        exact hqSupport v hv (by simpa only [List.mem_toFinset] using hvS))
    (by simpa [hiZ2] using hno)
  obtain ⟨q, hsupport, hlength, _⟩ :=
    FivePathState.transfer_exterior_bc_path_after_ab_switch
      G s
      (FivePathState.external_endpoint_color_ne_missing
        G s hleft hright).1
      (FivePathState.external_endpoint_color_ne_missing
        G s hleft hright).2
      hother hstable q₀ hExterior
  let q' := G.pathEndpointsCast rfl hiZ2.symm q
  refine ⟨switched, hproper, hswapA, hswapB, hother, q', ?_, ?_⟩
  · rw [show q'.1.length = q.1.length from
      G.pathEndpointsCast_length rfl hiZ2.symm q]
    exact hlength.trans hqLen
  · intro v hv hvS
    have hvOld : v ∈ q₀.1.support := by
      simpa [q', G.pathEndpointsCast_support, hsupport] using hv
    rcases hqSupport v hvOld hvS with hY | hHit
    · exact Or.inl hY
    · exact Or.inr (hHit.trans hiZ2)

end WeightedEdgeColoring.WeightedMultigraph
