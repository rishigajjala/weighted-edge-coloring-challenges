import WeightedEdgeColoring.SubtwoOrdinaryTriangleShortFavorable
import WeightedEdgeColoring.BPOrdinaryCriticalTrianglePresent

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem exists_triangleEdge_of_not_missing_middle_of_threeChain_short
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hdk : d + 1 < k) (hdegree : ∀ v, G.degreeOn F v ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hno : G.NoOddSetCertificateAt F k)
    {c : Fin k}
    (hc : c ∉ G.missingColorsAt (F.erase e) color (p.1.getVert 1)) :
    ∃ g, g ∈ F.erase e ∧ color g = c ∧
      ((G.Inc (G.fst e) g ∧ G.Inc (G.snd e) g) ∨
       (G.Inc (G.fst e) g ∧ G.Inc (p.1.getVert 1) g) ∨
       (G.Inc (G.snd e) g ∧ G.Inc (p.1.getVert 1) g)) := by
  classical
  let x := G.fst e
  let y := G.snd e
  let z := p.1.getVert 1
  have hxe : G.Inc x e := Or.inl rfl
  have hye : G.Inc y e := Or.inr rfl
  have hpLength := G.criticalPath_length_eq_two_of_no_oddSetCertificate
    hcritical heF hproper ha hb p hdk hdegree hthreshold hno
  have hxy : x ≠ y := G.noLoop e
  have hp0 : (G.twoColorGraph (F.erase e) color a b).Adj x z := by
    simpa [x, z] using p.1.adj_getVert_succ (i := 0) (by omega)
  have hp1 : (G.twoColorGraph (F.erase e) color a b).Adj z y := by
    have hend : p.1.getVert 2 = G.snd e := by
      simpa [hpLength] using p.1.getVert_length
    simpa [y, z, hend] using p.1.adj_getVert_succ (i := 1) (by omega)
  have hxz : x ≠ z := hp0.ne
  have hyz : y ≠ z := hp1.ne.symm
  rcases G.exists_twoColorWitnessEdge
      (F.erase e) color a b hp0 with
    ⟨gB, hgBF, hgBx, hgBz, hgBcolor⟩
  rcases G.exists_twoColorWitnessEdge
      (F.erase e) color a b hp1 with
    ⟨gA, hgAF, hgAz, hgAy, hgAcolor⟩
  have hgBneA : color gB ≠ a :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase e) color x a (by simpa [x] using ha) hgBF hgBx
  have hgBB : color gB = b := hgBcolor.resolve_left hgBneA
  have hgAneB : color gA ≠ b :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase e) color y b (by simpa [y] using hb) hgAF hgAy
  have hgAA : color gA = a := hgAcolor.resolve_right hgAneB
  by_contra htriangle
  have hnoCXY : ∀ r, r ∈ F.erase e → G.Inc x r →
      G.Inc y r → color r ≠ c := by
    intro r hr hrx hry hrc
    apply htriangle
    exact ⟨r, hr, hrc, Or.inl ⟨by simpa [x] using hrx,
      by simpa [y] using hry⟩⟩
  have hnoCXZ : ∀ r, r ∈ F.erase e → G.Inc x r →
      G.Inc z r → color r ≠ c := by
    intro r hr hrx hrz hrc
    apply htriangle
    exact ⟨r, hr, hrc, Or.inr (Or.inl
      ⟨by simpa [x] using hrx, by simpa [z] using hrz⟩)⟩
  have hnoCYZ : ∀ r, r ∈ F.erase e → G.Inc y r →
      G.Inc z r → color r ≠ c := by
    intro r hr hry hrz hrc
    apply htriangle
    exact ⟨r, hr, hrc, Or.inr (Or.inr
      ⟨by simpa [y] using hry, by simpa [z] using hrz⟩)⟩
  have hcX : c ∉ G.missingColorsAt (F.erase e) color x := by
    intro hcMissing
    rcases G.exists_oppositeEdge_of_mem_missing_first_of_threeChain_short
        hcritical heF hproper ha hb p hdk hdegree hthreshold hno hcMissing with
      ⟨r, hr, hrz, hry, hrc⟩
    exact (hnoCYZ r hr hry hrz) hrc
  have hcY : c ∉ G.missingColorsAt (F.erase e) color y := by
    intro hcMissing
    rcases G.exists_oppositeEdge_of_mem_missing_second_of_threeChain_short
        hcritical heF hproper ha hb p hdk hdegree hthreshold hno hcMissing with
      ⟨r, hr, hrx, hrz, hrc⟩
    exact (hnoCXZ r hr hrx hrz) hrc
  have hcZ : c ∉ G.missingColorsAt (F.erase e) color z := by
    simpa [z] using hc
  let H := G.twoColorGraph (F.erase e) color b c
  let D := H.deleteEdges {s(x, z)}
  have hcompXY : H.connectedComponentMk x = H.connectedComponentMk y :=
    G.presentColor_x_mem_y_twoColorComponent_short
      hcritical heF hproper hxy hxz hyz hxe hye
        (by simpa [x] using ha) (by simpa [y] using hb) hcX hcY
        hgAF hgAz hgAy hgAA hnoCXZ hdk hdegree hthreshold hno
  have hreachYX : H.Reachable y x :=
    WeightedEdgeColoring.SimpleGraph.reachable_of_connectedComponentMk_eq H hcompXY.symm
  have hAdjXZ : H.Adj x z := by
    have h := G.twoColorGraph_adj_fst_snd
      (F.erase e) color b c hgBF (Or.inl hgBB)
    rcases hgBx with hfx | hsx <;> rcases hgBz with hfz | hsz
    · exact False.elim (hxz (hfx.symm.trans hfz))
    · simpa [H, hfx, hsz] using h
    · simpa [H, hsx, hfz] using h.symm
    · exact False.elim (hxz (hsx.symm.trans hsz))
  have hrecover : D ⊔ SimpleGraph.edge x z = H := by
    simpa [D] using
      WeightedEdgeColoring.SimpleGraph.deleteEdges_sup_edge_eq_of_adj H hAdjXZ
  have hreachSup : (D ⊔ SimpleGraph.edge x z).Reachable y x := by
    simpa [hrecover] using hreachYX
  rcases WeightedEdgeColoring.SimpleGraph.reachable_left_or_right_of_reachable_sup_edge
      D hreachSup with hcutX | hcutZ
  · exact G.false_of_presentColor_and_reachable_first_after_triangleCut_short
      hcritical heF hproper hxy hxz hyz hxe hye
        (by simpa [x] using ha) (by simpa [y] using hb) hcX hcY
        hgBF hgBx hgBz hgBB hgAF hgAz hgAy hgAA
        hnoCXY hnoCXZ (by simpa [D, H] using hcutX)
        hdk hdegree hthreshold hno
  · have hab : a ≠ b :=
      G.critical_endpoint_missingColors_ne hcritical heF hproper ha hb
    have hac : a ≠ c := by
      intro h
      subst c
      exact hcX (by simpa [x] using ha)
    let shiftedA := G.assignEdgeColor color e a
    have hproperA : G.IsProperOn (F.erase gA) shiftedA := by
      exact G.isProperOn_shiftOmittedEdge_at
        heF hgAF hproper hgAA hxy.symm hye hxe
          hgAy (by simpa [x] using ha)
    have hzNotIncE : ¬G.Inc z e := by
      intro hze
      rcases hze with hze | hze
      · exact hxz (by simpa [x] using hze)
      · exact hyz (by simpa [y] using hze)
    have haErase : a ∈
        G.missingColorsAt ((F.erase e).erase gA) color z := by
      simpa [hgAA] using
        G.mem_missingColorsAt_erase_of_edgeColor hproper hgAF hgAz
    have haShift : a ∈ G.missingColorsAt (F.erase gA) shiftedA z := by
      apply G.mem_missingColorsAt_assignEdgeColor_of_not_inc
        (R := F.erase gA) (e := e)
      · exact Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hgAF).1.symm, heF⟩
      · exact hzNotIncE
      · have herase : (F.erase gA).erase e = (F.erase e).erase gA := by
          ext r
          simp [and_left_comm]
        simpa [herase, shiftedA] using haErase
    have hbShift : b ∈ G.missingColorsAt (F.erase gA) shiftedA y :=
      G.mem_missingColorsAt_shiftOmitted_of_ne hab.symm
        (by simpa [y] using hb)
    have hcZShift : c ∉ G.missingColorsAt (F.erase gA) shiftedA z := by
      intro hcNew
      exact hcZ ((G.mem_missingColorsAt_shiftOmitted_iff_of_ne
        heF hgAF hgAA hac.symm).mp hcNew)
    have hcYShift : c ∉ G.missingColorsAt (F.erase gA) shiftedA y := by
      intro hcNew
      exact hcY ((G.mem_missingColorsAt_shiftOmitted_iff_of_ne
        heF hgAF hgAA hac.symm).mp hcNew)
    have hgBneA : gB ≠ gA := by
      intro h
      subst gB
      exact hab (hgAA.symm.trans hgBB)
    have hgBin : gB ∈ F.erase gA :=
      Finset.mem_erase.mpr ⟨hgBneA, (Finset.mem_erase.mp hgBF).2⟩
    have hgBneE : gB ≠ e := (Finset.mem_erase.mp hgBF).1
    have hgBShift : shiftedA gB = b := by
      simpa [shiftedA, G.assignEdgeColor_of_ne color hgBneE a] using hgBB
    have heIn : e ∈ F.erase gA :=
      Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hgAF).1.symm, heF⟩
    have heShift : shiftedA e = a := by simp [shiftedA, assignEdgeColor]
    have hnoShift (u v : G.V)
        (huvOld : ∀ r, r ∈ F.erase e → G.Inc u r →
          G.Inc v r → color r ≠ c) :
        ∀ r, r ∈ F.erase gA → G.Inc u r → G.Inc v r →
          shiftedA r ≠ c := by
      intro r hr hru hrv hrc
      by_cases hre : r = e
      · subst r
        exact hac (by simpa [shiftedA, assignEdgeColor] using hrc)
      · have hrFe : r ∈ F.erase e :=
          Finset.mem_erase.mpr ⟨hre, (Finset.mem_erase.mp hr).2⟩
        have hrOld : color r = c := by
          simpa [shiftedA, G.assignEdgeColor_of_ne color hre a] using hrc
        exact (huvOld r hrFe hru hrv) hrOld
    have hgraphEq :
        G.twoColorGraph (F.erase gA) shiftedA b c = H := by
      simpa [H, shiftedA] using
        G.twoColorGraph_shiftOmitted_eq_of_fixedColors
          heF hgAF hgAA hab hac
    have hcutNew :
        ((G.twoColorGraph (F.erase gA) shiftedA b c).deleteEdges
          {s(z, x)}).Reachable y z := by
      simpa [hgraphEq, Sym2.eq_swap, D] using hcutZ
    have hgAall : gA ∈ F := (Finset.mem_erase.mp hgAF).2
    exact G.false_of_presentColor_and_reachable_first_after_triangleCut_short
      hcritical hgAall hproperA hyz.symm hxz.symm hxy.symm hgAz hgAy
        haShift hbShift hcZShift hcYShift
        hgBin hgBz hgBx hgBShift heIn hxe hye heShift
        (hnoShift z y (fun r hr hrz hry ↦ hnoCYZ r hr hry hrz))
        (hnoShift z x (fun r hr hrz hrx ↦
          hnoCXZ r hr hrx hrz))
        hcutNew hdk hdegree hthreshold hno


end WeightedMultigraph
end WeightedEdgeColoring
