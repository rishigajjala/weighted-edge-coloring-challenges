import WeightedEdgeColoring.SubtwoOrdinaryTriangleShortComponent
import WeightedEdgeColoring.BPOrdinaryCriticalTrianglePresentFavorable

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem false_of_presentColor_and_reachable_first_after_triangleCut_short
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {x y z : G.V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxe : G.Inc x e) (hye : G.Inc y e)
    {a b c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color x)
    (hb : b ∈ G.missingColorsAt (F.erase e) color y)
    (hcX : c ∉ G.missingColorsAt (F.erase e) color x)
    (hcY : c ∉ G.missingColorsAt (F.erase e) color y)
    {gB gA : G.E}
    (hgBF : gB ∈ F.erase e) (hgBx : G.Inc x gB)
    (hgBz : G.Inc z gB) (hgBB : color gB = b)
    (hgAF : gA ∈ F.erase e) (hgAz : G.Inc z gA)
    (hgAy : G.Inc y gA) (hgAA : color gA = a)
    (hnoCXY : ∀ r, r ∈ F.erase e → G.Inc x r →
      G.Inc y r → color r ≠ c)
    (hnoCXZ : ∀ r, r ∈ F.erase e → G.Inc x r →
      G.Inc z r → color r ≠ c)
    (hcut :
      ((G.twoColorGraph (F.erase e) color b c).deleteEdges
        {s(x, z)}).Reachable y x)
    (hdk : d + 1 < k) (hdegree : ∀ v, G.degreeOn F v ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hno : G.NoOddSetCertificateAt F k) : False := by
  classical
  let R := F.erase e
  let H := G.twoColorGraph R color b c
  let D := H.deleteEdges {s(x, z)}
  have hcompXY : H.connectedComponentMk x =
      H.connectedComponentMk y := by
    exact G.presentColor_x_mem_y_twoColorComponent_short
      hcritical heF hproper hxy hxz hyz hxe hye ha hb hcX hcY
        hgAF hgAz hgAy hgAA hnoCXZ hdk hdegree hthreshold hno
  have hHAdjXZ : H.Adj x z := by
    have h := G.twoColorGraph_adj_fst_snd R color b c hgBF (Or.inl hgBB)
    rcases hgBx with hfx | hsx <;> rcases hgBz with hfz | hsz
    · exact False.elim (hxz (hfx.symm.trans hfz))
    · simpa [H, hfx, hsz] using h
    · simpa [H, hsx, hfz] using h.symm
    · exact False.elim (hxz (hsx.symm.trans hsz))
  have hcompZY : H.connectedComponentMk z =
      H.connectedComponentMk y := by
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      hHAdjXZ.symm).trans hcompXY
  let C : H.ConnectedComponent := H.connectedComponentMk y
  have hyC : y ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hxC : x ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact hcompXY
  have hzC : z ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact hcompZY
  have hbc : b ≠ c := by
    intro h
    subst c
    exact hcY hb
  have hyActive : G.IsTwoColorActive R color b c y :=
    Or.inl ⟨hb, hcY⟩
  have htree : C.toSimpleGraph.IsTree :=
    G.twoColorComponent_isTree_of_active hproper C y hyC hyActive
  let X : C := ⟨x, hxC⟩
  let Z : C := ⟨z, hzC⟩
  have hXZ : C.toSimpleGraph.Adj X Z := by
    exact hHAdjXZ
  let pXZWalk : C.toSimpleGraph.Walk X Z :=
    SimpleGraph.Walk.cons hXZ SimpleGraph.Walk.nil
  have hXZne : X ≠ Z := by
    intro h
    exact hxz (congrArg Subtype.val h)
  have hpXZ : pXZWalk.IsPath := by
    simp [pXZWalk, hXZne]
  let pXZ : C.toSimpleGraph.Path X Z := ⟨pXZWalk, hpXZ⟩
  have hpEdge : s(X, Z) ∈ pXZ.1.edges := by simp [pXZ, pXZWalk]
  have hnotXZ : ¬D.Reachable x z := by
    exact WeightedEdgeColoring.SimpleGraph.not_reachable_of_le_deleteEdges_of_mem_componentPath
      H D C htree X Z X Z pXZ hpEdge (by rfl)
  have hnotYZ : ¬D.Reachable y z := by
    intro hyzReach
    have hyxD : D.Reachable y x := by
      simpa [D, H, R] using hcut
    exact hnotXZ (hyxD.symm.trans hyzReach)
  let shifted := G.assignEdgeColor color e b
  have hproperShift : G.IsProperOn (F.erase gB) shifted :=
    G.isProperOn_shiftOmittedEdge_at
      heF hgBF hproper hgBB hxy hxe hye hgBx hb
  let Hshift := G.twoColorGraph (F.erase gB) shifted b c
  have hle : Hshift ≤ D ⊔ SimpleGraph.edge x y := by
    simpa [Hshift, D, H, R, shifted] using
      G.twoColorGraph_shiftOmitted_le_cut_sup_edge_at
        heF hgBF hproper hgBB hxy hxz hxe hye hgBx hgBz hnoCXZ
  have hnotShiftYZ : ¬Hshift.Reachable y z := by
    exact WeightedEdgeColoring.SimpleGraph.not_reachable_of_le_sup_edge_of_reachable
      D Hshift (by simpa [D, H, R] using hcut.symm) hnotYZ hle
  let K : Hshift.ConnectedComponent := Hshift.connectedComponentMk y
  let flip : Hshift.ConnectedComponent → Prop := fun Q ↦ Q = K
  let switched : G.E → Fin k :=
    G.kempeComponentSwitch (F.erase gB) shifted b c flip
  have hyFlip : flip (Hshift.connectedComponentMk y) := by rfl
  have hxFlip : flip (Hshift.connectedComponentMk x) := by
    have heShift : shifted e = b := by simp [shifted, assignEdgeColor]
    have heFg : e ∈ F.erase gB :=
      Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hgBF).1.symm, heF⟩
    have hAdj := G.twoColorGraph_adj_fst_snd
      (F.erase gB) shifted b c heFg (Or.inl heShift)
    have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc hxy hxe hye
    have hAdjXY : Hshift.Adj x y := by
      rcases hends with hdirect | hswap
      · simpa [Hshift, hdirect.1, hdirect.2] using hAdj
      · simpa [Hshift, hswap.1, hswap.2] using hAdj.symm
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      hAdjXY).trans (by rfl)
  have hzNotFlip : ¬flip (Hshift.connectedComponentMk z) := by
    intro hzFlip
    have hcomp : Hshift.connectedComponentMk z =
        Hshift.connectedComponentMk y := by
      simpa [flip, K] using hzFlip
    exact hnotShiftYZ
      (WeightedEdgeColoring.SimpleGraph.reachable_of_connectedComponentMk_eq Hshift hcomp.symm)
  have hproperSwitched : G.IsProperOn (F.erase gB) switched :=
    G.isProperOn_kempeComponentSwitch
      (F.erase gB) shifted hproperShift b c flip
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc hxy hxe hye
  have hab : a ≠ b := by
    intro h
    have hbA : a ∈ G.missingColorsAt (F.erase e) color y := by
      rw [h]
      exact hb
    rcases hends with hdirect | hswap
    · exact G.not_both_mem_missingColorsAt_endpoints_of_colorCritical
        hcritical heF hproper a
          ⟨by simpa [hdirect.1] using ha,
            by simpa [hdirect.2] using hbA⟩
    · exact G.not_both_mem_missingColorsAt_endpoints_of_colorCritical
        hcritical heF hproper a
          ⟨by simpa [hswap.1] using hbA,
            by simpa [hswap.2] using ha⟩
  have hac : a ≠ c := by
    intro h
    subst c
    exact hcX ha
  have haShift : a ∈
      G.missingColorsAt (F.erase gB) shifted x :=
    G.mem_missingColorsAt_shiftOmitted_of_ne hab ha
  have haSwitched : a ∈
      G.missingColorsAt (F.erase gB) switched x :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_fixedColor_iff
      shifted b c flip x a hab hac).mpr haShift
  have hzNotIncE : ¬G.Inc z e := by
    intro hze
    rcases hends with hdirect | hswap
    · rcases hze with hze | hze
      · exact hxz (hdirect.1.symm.trans hze)
      · exact hyz (hdirect.2.symm.trans hze)
    · rcases hze with hze | hze
      · exact hyz (hswap.1.symm.trans hze)
      · exact hxz (hswap.2.symm.trans hze)
  have hbErase : b ∈
      G.missingColorsAt ((F.erase e).erase gB) color z := by
    simpa [hgBB] using
      G.mem_missingColorsAt_erase_of_edgeColor hproper hgBF hgBz
  have hbShift : b ∈
      G.missingColorsAt (F.erase gB) shifted z := by
    apply G.mem_missingColorsAt_assignEdgeColor_of_not_inc
      (R := F.erase gB) (e := e)
    · exact Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp hgBF).1.symm, heF⟩
    · exact hzNotIncE
    · have herase : (F.erase gB).erase e = (F.erase e).erase gB := by
        ext r
        simp [and_left_comm]
      simpa [herase, shifted] using hbErase
  have hbSwitched : b ∈
      G.missingColorsAt (F.erase gB) switched z :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_not_flip_iff
      (F.erase gB) shifted b c flip z hzNotFlip b).mpr hbShift
  have hgBFall : gB ∈ F := (Finset.mem_erase.mp hgBF).2
  rcases G.endpoint_eq_or_endpoint_eq_swap_of_inc hxz hgBx hgBz with
    hdirect | hswap
  · have haFst : a ∈
        G.missingColorsAt (F.erase gB) switched (G.fst gB) := by
      simpa [hdirect.1] using haSwitched
    have hbSnd : b ∈
        G.missingColorsAt (F.erase gB) switched (G.snd gB) := by
      simpa [hdirect.2] using hbSwitched
    obtain ⟨q, _⟩ := G.exists_criticalEndpointPath
      hcritical hgBFall hproperSwitched haFst hbSnd
    have hqLength := G.criticalPath_length_eq_two_of_no_oddSetCertificate
      hcritical hgBFall hproperSwitched haFst hbSnd q
        hdk hdegree hthreshold hno
    let w := q.1.getVert 1
    have hq0 : (G.twoColorGraph (F.erase gB) switched a b).Adj
        x w := by
      simpa [w, hdirect.1] using
        q.1.adj_getVert_succ (i := 0) (by omega)
    have hq1 : (G.twoColorGraph (F.erase gB) switched a b).Adj
        w z := by
      have hend : q.1.getVert 2 = G.snd gB := by
        simpa [hqLength] using q.1.getVert_length
      simpa [w, hend, hdirect.2] using
        q.1.adj_getVert_succ (i := 1) (by omega)
    rcases G.exists_twoColorWitnessEdge
        (F.erase gB) switched a b hq1 with
      ⟨rA, hrAF, hrAw, hrAz, hrAcolor⟩
    have hrAneB : switched rA ≠ b :=
      G.color_ne_of_mem_missingColorsAt
        (F.erase gB) switched z b hbSwitched hrAF hrAz
    have hrAA : switched rA = a := hrAcolor.resolve_right hrAneB
    have hgAneB : gA ≠ gB := by
      intro h
      subst gA
      exact hab (hgAA.symm.trans hgBB)
    have hgAin : gA ∈ F.erase gB :=
      Finset.mem_erase.mpr ⟨hgAneB, (Finset.mem_erase.mp hgAF).2⟩
    have hgAneE : gA ≠ e := (Finset.mem_erase.mp hgAF).1
    have hgAShift : shifted gA = a := by
      simpa [shifted, G.assignEdgeColor_of_ne color hgAneE b] using hgAA
    have hgASwitched : switched gA = a :=
      (G.kempeComponentSwitch_eq_fixedColor_iff
        shifted b c flip a hab hac gA).mpr hgAShift
    have hwY : w = y := by
      by_contra hwY
      have hcolors : switched rA ≠ switched gA :=
        G.color_ne_of_isProperOn_of_incident_otherEndpoints_ne
          hproperSwitched hq1.ne.symm hyz.symm hwY
            hrAF hgAin hrAz hrAw hgAz hgAy
      exact hcolors (hrAA.trans hgASwitched.symm)
    rcases G.exists_twoColorWitnessEdge
        (F.erase gB) switched a b hq0 with
      ⟨rB, hrBF, hrBx, hrBw, hrBcolor⟩
    have hrBneA : switched rB ≠ a :=
      G.color_ne_of_mem_missingColorsAt
        (F.erase gB) switched x a haSwitched hrBF hrBx
    have hrBB : switched rB = b := hrBcolor.resolve_left hrBneA
    have hlocal := G.kempeComponentSwitch_eq_localPerm
      (F.erase gB) shifted b c flip hrBF hrBx
    have hyes : flip
        ((G.twoColorGraph (F.erase gB) shifted b c).connectedComponentMk x) := by
      simpa [Hshift] using hxFlip
    have hswapColor : switched rB = Equiv.swap b c (shifted rB) := by
      simpa [switched, kempeLocalPerm, hyes] using hlocal
    have hrBShiftC : shifted rB = c := by
      apply (Equiv.swap b c).injective
      have h : Equiv.swap b c (shifted rB) = b :=
        hswapColor.symm.trans hrBB
      simpa [hbc] using h
    by_cases hrBe : rB = e
    · subst rB
      have : b = c := by
        simpa [shifted, assignEdgeColor] using hrBShiftC
      exact hbc this
    · have hrBFe : rB ∈ F.erase e :=
        Finset.mem_erase.mpr ⟨hrBe, (Finset.mem_erase.mp hrBF).2⟩
      have hrBOld : color rB = c := by
        simpa [shifted, G.assignEdgeColor_of_ne color hrBe b] using hrBShiftC
      exact (hnoCXY rB hrBFe hrBx (by simpa [w, hwY] using hrBw)) hrBOld
  · have hbFst : b ∈
        G.missingColorsAt (F.erase gB) switched (G.fst gB) := by
      simpa [hswap.1] using hbSwitched
    have haSnd : a ∈
        G.missingColorsAt (F.erase gB) switched (G.snd gB) := by
      simpa [hswap.2] using haSwitched
    obtain ⟨q, _⟩ := G.exists_criticalEndpointPath
      hcritical hgBFall hproperSwitched hbFst haSnd
    have hqLength := G.criticalPath_length_eq_two_of_no_oddSetCertificate
      hcritical hgBFall hproperSwitched hbFst haSnd q
        hdk hdegree hthreshold hno
    let w := q.1.getVert 1
    have hq0 : (G.twoColorGraph (F.erase gB) switched b a).Adj
        z w := by
      simpa [w, hswap.1] using
        q.1.adj_getVert_succ (i := 0) (by omega)
    have hq1 : (G.twoColorGraph (F.erase gB) switched b a).Adj
        w x := by
      have hend : q.1.getVert 2 = G.snd gB := by
        simpa [hqLength] using q.1.getVert_length
      simpa [w, hend, hswap.2] using
        q.1.adj_getVert_succ (i := 1) (by omega)
    rcases G.exists_twoColorWitnessEdge
        (F.erase gB) switched b a hq0 with
      ⟨rA, hrAF, hrAz, hrAw, hrAcolor⟩
    have hrAneB : switched rA ≠ b :=
      G.color_ne_of_mem_missingColorsAt
        (F.erase gB) switched z b hbSwitched hrAF hrAz
    have hrAA : switched rA = a := hrAcolor.resolve_left hrAneB
    have hgAneB : gA ≠ gB := by
      intro h
      subst gA
      exact hab (hgAA.symm.trans hgBB)
    have hgAin : gA ∈ F.erase gB :=
      Finset.mem_erase.mpr ⟨hgAneB, (Finset.mem_erase.mp hgAF).2⟩
    have hgAneE : gA ≠ e := (Finset.mem_erase.mp hgAF).1
    have hgAShift : shifted gA = a := by
      simpa [shifted, G.assignEdgeColor_of_ne color hgAneE b] using hgAA
    have hgASwitched : switched gA = a :=
      (G.kempeComponentSwitch_eq_fixedColor_iff
        shifted b c flip a hab hac gA).mpr hgAShift
    have hwY : w = y := by
      by_contra hwY
      have hcolors : switched rA ≠ switched gA :=
        G.color_ne_of_isProperOn_of_incident_otherEndpoints_ne
          hproperSwitched hq0.ne hyz.symm hwY
            hrAF hgAin hrAz hrAw hgAz hgAy
      exact hcolors (hrAA.trans hgASwitched.symm)
    rcases G.exists_twoColorWitnessEdge
        (F.erase gB) switched b a hq1 with
      ⟨rB, hrBF, hrBw, hrBx, hrBcolor⟩
    have hrBneA : switched rB ≠ a :=
      G.color_ne_of_mem_missingColorsAt
        (F.erase gB) switched x a haSwitched hrBF hrBx
    have hrBB : switched rB = b := hrBcolor.resolve_right hrBneA
    have hlocal := G.kempeComponentSwitch_eq_localPerm
      (F.erase gB) shifted b c flip hrBF hrBx
    have hyes : flip
        ((G.twoColorGraph (F.erase gB) shifted b c).connectedComponentMk x) := by
      simpa [Hshift] using hxFlip
    have hswapColor : switched rB = Equiv.swap b c (shifted rB) := by
      simpa [switched, kempeLocalPerm, hyes] using hlocal
    have hrBShiftC : shifted rB = c := by
      apply (Equiv.swap b c).injective
      have h : Equiv.swap b c (shifted rB) = b :=
        hswapColor.symm.trans hrBB
      simpa [hbc] using h
    by_cases hrBe : rB = e
    · subst rB
      have : b = c := by
        simpa [shifted, assignEdgeColor] using hrBShiftC
      exact hbc this
    · have hrBFe : rB ∈ F.erase e :=
        Finset.mem_erase.mpr ⟨hrBe, (Finset.mem_erase.mp hrBF).2⟩
      have hrBOld : color rB = c := by
        simpa [shifted, G.assignEdgeColor_of_ne color hrBe b] using hrBShiftC
      exact (hnoCXY rB hrBFe hrBx (by simpa [w, hwY] using hrBw)) hrBOld


end WeightedMultigraph
end WeightedEdgeColoring
