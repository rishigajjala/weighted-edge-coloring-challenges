import WeightedEdgeColoring.BPOrdinaryCriticalTriangle

/-!
# Shifting the omitted edge of a critical colouring

If `e = xy` is omitted, an edge `g = xz` has colour `b`, and `b` is
missing at `y`, we may colour `e` with `b` and omit `g` instead.  This is
the elementary "shift" used in Andersen's three-vertex ring argument.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Once a selected incident edge of colour `c` is removed from a proper
colouring, `c` is missing at that endpoint. -/
theorem mem_missingColorsAt_erase_of_edgeColor
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    (hproper : G.IsProperOn F color)
    {g : G.E} (hgF : g ∈ F) {v : G.V} (hgv : G.Inc v g) :
    color g ∈ G.missingColorsAt (F.erase g) color v := by
  classical
  simp only [missingColorsAt, Finset.mem_sdiff, Finset.mem_univ,
    true_and, Finset.mem_image]
  intro hused
  rcases hused with ⟨r, hr, hrcolor⟩
  have hrData := Finset.mem_filter.mp hr
  have hrF : r ∈ F := (Finset.mem_erase.mp hrData.1).2
  have hrne : r ≠ g := (Finset.mem_erase.mp hrData.1).1
  have hgmem : g ∈ (F.filter (G.Inc v) : Set G.E) :=
    Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgv⟩)
  have hrmem : r ∈ (F.filter (G.Inc v) : Set G.E) :=
    Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hrData.2⟩)
  exact hrne (hproper v hrmem hgmem hrcolor)

/-- A third missing colour remains missing when the omitted edge is shifted:
the removed edge has colour `b`, and the newly inserted edge also receives
`b`. -/
theorem mem_missingColorsAt_shiftOmitted_of_ne
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {e g : G.E} {b c : Fin k} (hcb : c ≠ b)
    {v : G.V}
    (hc : c ∈ G.missingColorsAt (F.erase e) color v) :
    c ∈ G.missingColorsAt (F.erase g) (G.assignEdgeColor color e b) v := by
  classical
  simp only [missingColorsAt, Finset.mem_sdiff, Finset.mem_univ,
    true_and, Finset.mem_image] at hc ⊢
  intro hused
  rcases hused with ⟨r, hr, hrcolor⟩
  have hrData := Finset.mem_filter.mp hr
  by_cases hre : r = e
  · subst r
    exact hcb (by simpa [assignEdgeColor] using hrcolor.symm)
  · apply hc
    refine ⟨r, Finset.mem_filter.mpr ⟨?_, hrData.2⟩, ?_⟩
    · exact Finset.mem_erase.mpr
        ⟨hre, (Finset.mem_erase.mp hrData.1).2⟩
    · simpa [G.assignEdgeColor_of_ne color hre b] using hrcolor

/-- A colour different from the shifted colour has exactly the same
missing indicator before and after a genuine omitted-edge shift. -/
theorem mem_missingColorsAt_shiftOmitted_iff_of_ne
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {e g : G.E} (heF : e ∈ F) (hgFe : g ∈ F.erase e)
    {b c : Fin k} (hgb : color g = b) (hcb : c ≠ b)
    {v : G.V} :
    c ∈ G.missingColorsAt (F.erase g) (G.assignEdgeColor color e b) v ↔
      c ∈ G.missingColorsAt (F.erase e) color v := by
  constructor
  · intro hcNew
    classical
    simp only [missingColorsAt, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_image] at hcNew ⊢
    intro hused
    rcases hused with ⟨r, hr, hrcolor⟩
    have hrData := Finset.mem_filter.mp hr
    have hrg : r ≠ g := by
      intro h
      subst r
      exact hcb (hrcolor.symm.trans hgb)
    have hre : r ≠ e := (Finset.mem_erase.mp hrData.1).1
    apply hcNew
    refine ⟨r, Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr
        ⟨hrg, (Finset.mem_erase.mp hrData.1).2⟩, hrData.2⟩, ?_⟩
    simpa [G.assignEdgeColor_of_ne color hre b] using hrcolor
  · exact G.mem_missingColorsAt_shiftOmitted_of_ne hcb

/-- Inserting a coloured edge does not affect the missing palette of a
vertex not incident with that edge. -/
theorem mem_missingColorsAt_assignEdgeColor_of_not_inc
    {R : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {e : G.E} (heR : e ∈ R) {b : Fin k} {v : G.V}
    (hve : ¬G.Inc v e)
    (hb : b ∈ G.missingColorsAt (R.erase e) color v) :
    b ∈ G.missingColorsAt R (G.assignEdgeColor color e b) v := by
  classical
  simp only [missingColorsAt, Finset.mem_sdiff, Finset.mem_univ,
    true_and, Finset.mem_image] at hb ⊢
  intro hused
  rcases hused with ⟨r, hr, hrcolor⟩
  have hrData := Finset.mem_filter.mp hr
  have hre : r ≠ e := by
    intro hre
    subst r
    exact hve hrData.2
  apply hb
  refine ⟨r, Finset.mem_filter.mpr
    ⟨Finset.mem_erase.mpr ⟨hre, hrData.1⟩, hrData.2⟩, ?_⟩
  simpa [G.assignEdgeColor_of_ne color hre b] using hrcolor

/-- Colour `e` with the old colour of `g` and omit `g`. -/
theorem isProperOn_shiftOmittedEdge
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {e g : G.E} (heF : e ∈ F) (hgFe : g ∈ F.erase e)
    (hproper : G.IsProperOn (F.erase e) color)
    {b : Fin k} (hgb : color g = b)
    (hgx : G.Inc (G.fst e) g)
    (hby : b ∈ G.missingColorsAt (F.erase e) color (G.snd e)) :
    G.IsProperOn (F.erase g) (G.assignEdgeColor color e b) := by
  have hge : g ≠ e := (Finset.mem_erase.mp hgFe).1
  have hgF : g ∈ F := (Finset.mem_erase.mp hgFe).2
  have heFg : e ∈ F.erase g := Finset.mem_erase.mpr ⟨hge.symm, heF⟩
  have hproperDouble :
      G.IsProperOn ((F.erase g).erase e) color := by
    apply IsProperOn.mono G hproper
    intro r hr
    have hrData := Finset.mem_erase.mp hr
    exact Finset.mem_erase.mpr
      ⟨hrData.1, (Finset.mem_erase.mp hrData.2).2⟩
  have hbx0 : color g ∈
      G.missingColorsAt ((F.erase e).erase g) color (G.fst e) :=
    G.mem_missingColorsAt_erase_of_edgeColor hproper hgFe hgx
  have hbx : b ∈
      G.missingColorsAt ((F.erase g).erase e) color (G.fst e) := by
    have herase : (F.erase g).erase e = (F.erase e).erase g := by
      ext r
      simp [and_left_comm, and_comm]
    rw [herase]
    simpa [hgb] using hbx0
  have hby0 : b ∈
      G.missingColorsAt ((F.erase e).erase g) color (G.snd e) :=
    G.mem_missingColorsAt_of_subset (Finset.erase_subset g (F.erase e)) hby
  have hby' : b ∈
      G.missingColorsAt ((F.erase g).erase e) color (G.snd e) := by
    have herase : (F.erase g).erase e = (F.erase e).erase g := by
      ext r
      simp [and_left_comm, and_comm]
    simpa [herase] using hby0
  exact G.isProperOn_assignEdgeColor_of_missing_endpoints
    heFg hproperDouble hbx hby'

/-- Symmetric form of `isProperOn_shiftOmittedEdge`: the shifted-out edge
is incident with the second endpoint, and its colour is missing at the
first endpoint. -/
theorem isProperOn_shiftOmittedEdge_second
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {e g : G.E} (heF : e ∈ F) (hgFe : g ∈ F.erase e)
    (hproper : G.IsProperOn (F.erase e) color)
    {a : Fin k} (hga : color g = a)
    (hgy : G.Inc (G.snd e) g)
    (hax : a ∈ G.missingColorsAt (F.erase e) color (G.fst e)) :
    G.IsProperOn (F.erase g) (G.assignEdgeColor color e a) := by
  have hge : g ≠ e := (Finset.mem_erase.mp hgFe).1
  have hgF : g ∈ F := (Finset.mem_erase.mp hgFe).2
  have heFg : e ∈ F.erase g := Finset.mem_erase.mpr ⟨hge.symm, heF⟩
  have hproperDouble :
      G.IsProperOn ((F.erase g).erase e) color := by
    apply IsProperOn.mono G hproper
    intro r hr
    have hrData := Finset.mem_erase.mp hr
    exact Finset.mem_erase.mpr
      ⟨hrData.1, (Finset.mem_erase.mp hrData.2).2⟩
  have hay0 : color g ∈
      G.missingColorsAt ((F.erase e).erase g) color (G.snd e) :=
    G.mem_missingColorsAt_erase_of_edgeColor hproper hgFe hgy
  have hay : a ∈
      G.missingColorsAt ((F.erase g).erase e) color (G.snd e) := by
    have herase : (F.erase g).erase e = (F.erase e).erase g := by
      ext r
      simp [and_left_comm, and_comm]
    rw [herase]
    simpa [hga] using hay0
  have hax0 : a ∈
      G.missingColorsAt ((F.erase e).erase g) color (G.fst e) :=
    G.mem_missingColorsAt_of_subset (Finset.erase_subset g (F.erase e)) hax
  have hax' : a ∈
      G.missingColorsAt ((F.erase g).erase e) color (G.fst e) := by
    have herase : (F.erase g).erase e = (F.erase e).erase g := by
      ext r
      simp [and_left_comm, and_comm]
    simpa [herase] using hax0
  exact G.isProperOn_assignEdgeColor_of_missing_endpoints
    heFg hproperDouble hax' hay

/-- Endpoint-free shift.  The chosen vertices `x,y` are the distinct ends
of the omitted indexed edge; the edge shifted out is incident with `x`,
and its colour is missing at `y`. -/
theorem isProperOn_shiftOmittedEdge_at
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {e g : G.E} (heF : e ∈ F) (hgFe : g ∈ F.erase e)
    (hproper : G.IsProperOn (F.erase e) color)
    {b : Fin k} (hgb : color g = b)
    {x y : G.V} (hxy : x ≠ y)
    (hxe : G.Inc x e) (hye : G.Inc y e)
    (hgx : G.Inc x g)
    (hby : b ∈ G.missingColorsAt (F.erase e) color y) :
    G.IsProperOn (F.erase g) (G.assignEdgeColor color e b) := by
  have hge : g ≠ e := (Finset.mem_erase.mp hgFe).1
  have heFg : e ∈ F.erase g :=
    Finset.mem_erase.mpr ⟨hge.symm, heF⟩
  have hproperDouble :
      G.IsProperOn ((F.erase g).erase e) color := by
    apply IsProperOn.mono G hproper
    intro r hr
    have hrData := Finset.mem_erase.mp hr
    exact Finset.mem_erase.mpr
      ⟨hrData.1, (Finset.mem_erase.mp hrData.2).2⟩
  have hbx0 : color g ∈
      G.missingColorsAt ((F.erase e).erase g) color x :=
    G.mem_missingColorsAt_erase_of_edgeColor hproper hgFe hgx
  have hbx : b ∈
      G.missingColorsAt ((F.erase g).erase e) color x := by
    have herase : (F.erase g).erase e = (F.erase e).erase g := by
      ext r
      simp [and_left_comm, and_comm]
    rw [herase]
    simpa [hgb] using hbx0
  have hby0 : b ∈
      G.missingColorsAt ((F.erase e).erase g) color y :=
    G.mem_missingColorsAt_of_subset (Finset.erase_subset g (F.erase e)) hby
  have hby' : b ∈
      G.missingColorsAt ((F.erase g).erase e) color y := by
    have herase : (F.erase g).erase e = (F.erase e).erase g := by
      ext r
      simp [and_left_comm, and_comm]
    simpa [herase] using hby0
  have hfstSnd :
      (G.fst e = x ∧ G.snd e = y) ∨
        (G.fst e = y ∧ G.snd e = x) := by
    rcases hxe with hfx | hsx <;> rcases hye with hfy | hsy
    · exact False.elim (hxy (hfx.symm.trans hfy))
    · exact Or.inl ⟨hfx, hsy⟩
    · exact Or.inr ⟨hfy, hsx⟩
    · exact False.elim (hxy (hsx.symm.trans hsy))
  rcases hfstSnd with hdirect | hswap
  · exact G.isProperOn_assignEdgeColor_of_missing_endpoints
      heFg hproperDouble (by simpa [hdirect.1] using hbx)
        (by simpa [hdirect.2] using hby')
  · exact G.isProperOn_assignEdgeColor_of_missing_endpoints
      heFg hproperDouble (by simpa [hswap.1] using hby')
        (by simpa [hswap.2] using hbx)

/-- Shifting an edge of a third colour leaves a fixed two-colour graph
unchanged. -/
theorem twoColorGraph_shiftOmitted_eq_of_fixedColors
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {e g : G.E} (heF : e ∈ F) (hgFe : g ∈ F.erase e)
    {a b c : Fin k} (hga : color g = a)
    (hab : a ≠ b) (hac : a ≠ c) :
    G.twoColorGraph (F.erase g) (G.assignEdgeColor color e a) b c =
      G.twoColorGraph (F.erase e) color b c := by
  classical
  ext u v
  constructor
  · intro huv
    rcases G.exists_twoColorWitnessEdge (F.erase g)
        (G.assignEdgeColor color e a) b c huv with
      ⟨r, hrFg, hru, hrv, hrNew⟩
    have hre : r ≠ e := by
      intro h
      subst r
      rcases hrNew with h | h
      · exact hab (by simpa [assignEdgeColor] using h)
      · exact hac (by simpa [assignEdgeColor] using h)
    have hrFe : r ∈ F.erase e := Finset.mem_erase.mpr
      ⟨hre, (Finset.mem_erase.mp hrFg).2⟩
    have hrOld : color r = b ∨ color r = c := by
      simpa [G.assignEdgeColor_of_ne color hre a] using hrNew
    have h := G.twoColorGraph_adj_fst_snd
      (F.erase e) color b c hrFe hrOld
    rcases hru with hfu | hsu <;> rcases hrv with hfv | hsv
    · exact False.elim (huv.ne (hfu.symm.trans hfv))
    · simpa [hfu, hsv] using h
    · simpa [hsu, hfv] using h.symm
    · exact False.elim (huv.ne (hsu.symm.trans hsv))
  · intro huv
    rcases G.exists_twoColorWitnessEdge (F.erase e) color b c huv with
      ⟨r, hrFe, hru, hrv, hrOld⟩
    have hrg : r ≠ g := by
      intro h
      subst r
      rcases hrOld with h | h
      · exact hab (hga.symm.trans h)
      · exact hac (hga.symm.trans h)
    have hre : r ≠ e := (Finset.mem_erase.mp hrFe).1
    have hrFg : r ∈ F.erase g := Finset.mem_erase.mpr
      ⟨hrg, (Finset.mem_erase.mp hrFe).2⟩
    have hrNew : G.assignEdgeColor color e a r = b ∨
        G.assignEdgeColor color e a r = c := by
      simpa [G.assignEdgeColor_of_ne color hre a] using hrOld
    have h := G.twoColorGraph_adj_fst_snd
      (F.erase g) (G.assignEdgeColor color e a) b c hrFg hrNew
    rcases hru with hfu | hsu <;> rcases hrv with hfv | hsv
    · exact False.elim (huv.ne (hfu.symm.trans hfv))
    · simpa [hfu, hsv] using h
    · simpa [hsu, hfv] using h.symm
    · exact False.elim (huv.ne (hsu.symm.trans hsv))

end WeightedMultigraph
end WeightedEdgeColoring
