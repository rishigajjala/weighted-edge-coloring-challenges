import WeightedEdgeColoring.FiniteColorPairingRoots
import WeightedEdgeColoring.FiniteColorPairingOperators

/-!
# Averaging one block of a perfect color pairing

The component coins of one color pair are selected at a time.  On ideal
statistics this applies the average of the identity and the transposition of
that pair.  Operators belonging to disjoint pairs commute.  Processing every
canonical root therefore gives the full `singleAverage` and `pairAverage`
operators used by the universal schedule.
-/

namespace WeightedEdgeColoring.FiniteColorPairBlockOperators

open WeightedEdgeColoring.FiniteColorPairing
open WeightedEdgeColoring.FiniteColorPairingOperators

noncomputable section

variable {Color : Type*} [Fintype Color] [DecidableEq Color]

/-- Average a one-color list over one transposition. -/
def singleBlockAverage (a b : Color) (h : Color → ℝ) (c : Color) : ℝ :=
  (h c + h (Equiv.swap a b c)) / 2

/-- Average an ordered pair array under the same transposition in both
coordinates. -/
def pairBlockAverage (a b : Color) (h : Color → Color → ℝ)
    (c d : Color) : ℝ :=
  (h c d + h (Equiv.swap a b c) (Equiv.swap a b d)) / 2

theorem singleBlockAverage_apply_left (a b : Color) (h : Color → ℝ) :
    singleBlockAverage a b h a = (h a + h b) / 2 := by
  simp [singleBlockAverage]

theorem singleBlockAverage_apply_right (a b : Color) (h : Color → ℝ) :
    singleBlockAverage a b h b = (h b + h a) / 2 := by
  simp [singleBlockAverage]

theorem singleBlockAverage_apply_of_ne {a b c : Color}
    (hca : c ≠ a) (hcb : c ≠ b) (h : Color → ℝ) :
    singleBlockAverage a b h c = h c := by
  simp [singleBlockAverage, Equiv.swap_apply_of_ne_of_ne hca hcb]

theorem pairBlockAverage_apply_of_ne {a b c d : Color}
    (hca : c ≠ a) (hcb : c ≠ b)
    (hda : d ≠ a) (hdb : d ≠ b)
    (h : Color → Color → ℝ) :
    pairBlockAverage a b h c d = h c d := by
  simp [pairBlockAverage,
    Equiv.swap_apply_of_ne_of_ne hca hcb,
    Equiv.swap_apply_of_ne_of_ne hda hdb]

theorem pairBlockAverage_apply_paired (a b : Color)
    (h : Color → Color → ℝ) (hsym : ∀ c d, h c d = h d c) :
    pairBlockAverage a b h a b = h a b := by
  unfold pairBlockAverage
  simp [hsym b a]

theorem singleBlockAverage_commute
    {a b c d : Color}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (h : Color → ℝ) :
    singleBlockAverage a b (singleBlockAverage c d h) =
      singleBlockAverage c d (singleBlockAverage a b h) := by
  funext x
  have hca : c ≠ a := Ne.symm hac
  have hda : d ≠ a := Ne.symm had
  have hcb : c ≠ b := Ne.symm hbc
  have hdb : d ≠ b := Ne.symm hbd
  have hswap :
      Equiv.swap c d (Equiv.swap a b x) =
        Equiv.swap a b (Equiv.swap c d x) := by
    by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      by_cases hxc : x = c <;> by_cases hxd : x = d <;>
      subst_vars <;> simp_all [Equiv.swap_apply_of_ne_of_ne]
  unfold singleBlockAverage
  rw [hswap]
  ring

theorem pairBlockAverage_commute
    {a b c d : Color}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (h : Color → Color → ℝ) :
    pairBlockAverage a b (pairBlockAverage c d h) =
      pairBlockAverage c d (pairBlockAverage a b h) := by
  funext x y
  have hca : c ≠ a := Ne.symm hac
  have hda : d ≠ a := Ne.symm had
  have hcb : c ≠ b := Ne.symm hbc
  have hdb : d ≠ b := Ne.symm hbd
  have hswapX :
      Equiv.swap c d (Equiv.swap a b x) =
        Equiv.swap a b (Equiv.swap c d x) := by
    by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      by_cases hxc : x = c <;> by_cases hxd : x = d <;>
      subst_vars <;> simp_all [Equiv.swap_apply_of_ne_of_ne]
  have hswapY :
      Equiv.swap c d (Equiv.swap a b y) =
        Equiv.swap a b (Equiv.swap c d y) := by
    by_cases hya : y = a <;> by_cases hyb : y = b <;>
      by_cases hyc : y = c <;> by_cases hyd : y = d <;>
      subst_vars <;> simp_all [Equiv.swap_apply_of_ne_of_ne]
  unfold pairBlockAverage
  rw [hswapX, hswapY]
  ring

/-- Sequential application of the one-color block operators. -/
def applySingleBlockList (p : Pairing Color) :
    List Color → (Color → ℝ) → Color → ℝ
  | [], h => h
  | a :: roots, h =>
      applySingleBlockList p roots
        (singleBlockAverage a (partner Color p a) h)

/-- Sequential application of the pair-array block operators. -/
def applyPairBlockList (p : Pairing Color) :
    List Color → (Color → Color → ℝ) → Color → Color → ℝ
  | [], h => h
  | a :: roots, h =>
      applyPairBlockList p roots
        (pairBlockAverage a (partner Color p a) h)

@[simp] theorem applySingleBlockList_nil
    (p : Pairing Color) (h : Color → ℝ) :
    applySingleBlockList p [] h = h := rfl

@[simp] theorem applySingleBlockList_cons
    (p : Pairing Color) (a : Color) (roots : List Color)
    (h : Color → ℝ) :
    applySingleBlockList p (a :: roots) h =
      applySingleBlockList p roots
        (singleBlockAverage a (partner Color p a) h) := rfl

@[simp] theorem applyPairBlockList_nil
    (p : Pairing Color) (h : Color → Color → ℝ) :
    applyPairBlockList p [] h = h := rfl

@[simp] theorem applyPairBlockList_cons
    (p : Pairing Color) (a : Color) (roots : List Color)
    (h : Color → Color → ℝ) :
    applyPairBlockList p (a :: roots) h =
      applyPairBlockList p roots
        (pairBlockAverage a (partner Color p a) h) := rfl

/-! The final composition statements are for `Fin q`, where canonical roots
are available. -/

theorem root_block_ne_of_roots_ne {q : ℕ}
    (p : Pairing (Fin q)) {a r x : Fin q}
    (ha : a ∈ pairRoots p) (hr : r ∈ pairRoots p) (har : a ≠ r)
    (hx : x = r ∨ x = partner (Fin q) p r) :
    x ≠ a ∧ x ≠ partner (Fin q) p a := by
  have hdis := pair_blocks_disjoint_of_roots_ne p ha hr har
  rcases hx with rfl | rfl
  · exact ⟨har.symm, hdis.2.1.symm⟩
  · exact ⟨hdis.1.symm, hdis.2.2.symm⟩

theorem applySingleBlockList_apply_of_fixed {q : ℕ}
    (p : Pairing (Fin q)) (roots : List (Fin q))
    (h : Fin q → ℝ) (c : Fin q)
    (hfix : ∀ a ∈ roots,
      c ≠ a ∧ c ≠ partner (Fin q) p a) :
    applySingleBlockList p roots h c = h c := by
  induction roots generalizing h with
  | nil => rfl
  | cons a roots ih =>
      rw [applySingleBlockList_cons, ih]
      · exact singleBlockAverage_apply_of_ne
          (hfix a (by simp)).1 (hfix a (by simp)).2 h
      · intro x hx
        exact hfix x (by simp [hx])

theorem applySingleBlockList_eq_singleAverage_of_roots {q : ℕ}
    (p : Pairing (Fin q)) (roots : List (Fin q))
    (h : Fin q → ℝ) (c : Fin q)
    (hsub : ∀ a ∈ roots, a ∈ pairRoots p)
    (hnodup : roots.Nodup)
    (hroot : pairRoot p c ∈ roots) :
    applySingleBlockList p roots h c = singleAverage p h c := by
  let r := pairRoot p c
  have hr : r ∈ pairRoots p := pairRoot_mem_pairRoots p c
  have hcblock : c = r ∨ c = partner (Fin q) p r := by
    simpa [r] using self_eq_pairRoot_or_partner_pairRoot p c
  have hpcblock : partner (Fin q) p c = r ∨
      partner (Fin q) p c = partner (Fin q) p r := by
    rcases hcblock with hc | hc
    · exact Or.inr (by simpa [hc])
    · exact Or.inl (by simpa [hc, partner_partner])
  induction roots generalizing h with
  | nil => simp at hroot
  | cons a roots ih =>
      have ha : a ∈ pairRoots p := hsub a (by simp)
      have hsubTail : ∀ x ∈ roots, x ∈ pairRoots p := by
        intro x hx
        exact hsub x (by simp [hx])
      have hnodupTail : roots.Nodup := (List.nodup_cons.mp hnodup).2
      by_cases har : a = r
      · subst a
        have hrnot : r ∉ roots := (List.nodup_cons.mp hnodup).1
        have hfixC : ∀ x ∈ roots,
            c ≠ x ∧ c ≠ partner (Fin q) p x := by
          intro x hx
          have hxr : x ≠ r := fun h ↦ hrnot (h ▸ hx)
          exact root_block_ne_of_roots_ne p (hsubTail x hx) hr hxr hcblock
        rw [applySingleBlockList_cons,
          applySingleBlockList_apply_of_fixed p roots
            (singleBlockAverage r (partner (Fin q) p r) h) c hfixC]
        unfold singleAverage
        rcases hcblock with hc | hc
        · rw [hc]
          simp [singleBlockAverage]
        · rw [hc]
          simp [singleBlockAverage, partner_partner, add_comm]
      · have hrTail : r ∈ roots := by
          have hrInCons : r ∈ a :: roots := by
            simpa [r] using hroot
          exact (List.mem_cons.mp hrInCons).resolve_left (Ne.symm har)
        rw [applySingleBlockList_cons,
          ih (singleBlockAverage a (partner (Fin q) p a) h)
            hsubTail hnodupTail hrTail]
        unfold singleAverage
        have hfixC := root_block_ne_of_roots_ne p ha hr har hcblock
        have hfixPC := root_block_ne_of_roots_ne p ha hr har hpcblock
        rw [singleBlockAverage_apply_of_ne hfixC.1 hfixC.2,
          singleBlockAverage_apply_of_ne hfixPC.1 hfixPC.2]

theorem applySingleBlockList_pairRoots {q : ℕ}
    (p : Pairing (Fin q)) (h : Fin q → ℝ) :
    applySingleBlockList p (pairRoots p).toList h = singleAverage p h := by
  funext c
  apply applySingleBlockList_eq_singleAverage_of_roots p
  · intro a ha
    simpa using ha
  · exact (pairRoots p).nodup_toList
  · simpa using pairRoot_mem_pairRoots p c

theorem applyPairBlockList_apply_of_fixed {q : ℕ}
    (p : Pairing (Fin q)) (roots : List (Fin q))
    (h : Fin q → Fin q → ℝ) (c d : Fin q)
    (hfixC : ∀ a ∈ roots,
      c ≠ a ∧ c ≠ partner (Fin q) p a)
    (hfixD : ∀ a ∈ roots,
      d ≠ a ∧ d ≠ partner (Fin q) p a) :
    applyPairBlockList p roots h c d = h c d := by
  induction roots generalizing h with
  | nil => rfl
  | cons a roots ih =>
      rw [applyPairBlockList_cons, ih]
      · exact pairBlockAverage_apply_of_ne
          (hfixC a (by simp)).1 (hfixC a (by simp)).2
          (hfixD a (by simp)).1 (hfixD a (by simp)).2 h
      · intro x hx
        exact hfixC x (by simp [hx])
      · intro x hx
        exact hfixD x (by simp [hx])

/-- Lists of distinct canonical roots may be reordered freely: their block
operators commute because the represented two-color blocks are disjoint. -/
theorem applyPairBlockList_eq_of_perm {q : ℕ}
    (p : Pairing (Fin q)) {roots₁ roots₂ : List (Fin q)}
    (hperm : roots₁.Perm roots₂) (hnodup : roots₁.Nodup)
    (hroots : ∀ a ∈ roots₁, a ∈ pairRoots p)
    (h : Fin q → Fin q → ℝ) :
    applyPairBlockList p roots₁ h = applyPairBlockList p roots₂ h := by
  induction hperm generalizing h with
  | nil => rfl
  | cons a hperm ih =>
      rw [applyPairBlockList_cons, applyPairBlockList_cons]
      apply ih
      · exact (List.nodup_cons.mp hnodup).2
      · intro x hx
        exact hroots x (by simp [hx])
  | swap a b roots =>
      have hab : a ≠ b := by
        intro hab
        subst b
        simpa using hnodup
      have ha : a ∈ pairRoots p := hroots a (by simp)
      have hb : b ∈ pairRoots p := hroots b (by simp)
      have hdis := pair_blocks_disjoint_of_roots_ne p ha hb hab
      simp only [applyPairBlockList_cons]
      rw [pairBlockAverage_commute hab hdis.1 hdis.2.1 hdis.2.2]
  | trans h₁ h₂ ih₁ ih₂ =>
      rw [ih₁ hnodup hroots,
        ih₂ (hnodup.perm h₁)
          (fun a ha ↦ hroots a (h₁.mem_iff.mpr ha))]

/-- Processing all blocks of a perfect pairing gives the conditional
two-coordinate averaging operator. -/
theorem applyPairBlockList_pairRoots {q : ℕ}
    (p : Pairing (Fin q)) (h : Fin q → Fin q → ℝ)
    (hsym : ∀ c d, h c d = h d c) (hdiag : ∀ c, h c c = 0) :
    applyPairBlockList p (pairRoots p).toList h = pairAverage p h := by
  funext c d
  by_cases hcd : c = d
  · subst d
    have hdiagBlock : ∀ (roots : List (Fin q))
        (g : Fin q → Fin q → ℝ), (∀ x, g x x = 0) →
        applyPairBlockList p roots g c c = 0 := by
      intro roots
      induction roots with
      | nil => exact fun g hg ↦ hg c
      | cons a roots ih =>
          intro g hg
          rw [applyPairBlockList_cons]
          apply ih
          intro x
          unfold pairBlockAverage
          simp [hg]
    rw [hdiagBlock (pairRoots p).toList h hdiag]
    simp [pairAverage]
  · let r := pairRoot p c
    let s := pairRoot p d
    have hr : r ∈ pairRoots p := pairRoot_mem_pairRoots p c
    have hs : s ∈ pairRoots p := pairRoot_mem_pairRoots p d
    have hcblock : c = r ∨ c = partner (Fin q) p r := by
      simpa [r] using self_eq_pairRoot_or_partner_pairRoot p c
    have hdblock : d = s ∨ d = partner (Fin q) p s := by
      simpa [s] using self_eq_pairRoot_or_partner_pairRoot p d
    let roots := (pairRoots p).toList
    have hnodup : roots.Nodup := (pairRoots p).nodup_toList
    have hroots : ∀ a ∈ roots, a ∈ pairRoots p := by
      intro a ha
      simpa [roots] using ha
    by_cases hrs : r = s
    · have hpaired : partner (Fin q) p c = d := by
        rcases hcblock with hc | hc <;> rcases hdblock with hd | hd
        · exfalso
          exact hcd (hc.trans (hrs.trans hd.symm))
        · rw [hc, hrs]
          exact hd.symm
        · calc
            partner (Fin q) p c =
                partner (Fin q) p (partner (Fin q) p r) := by rw [hc]
            _ = r := partner_partner (Fin q) p r
            _ = s := hrs
            _ = d := hd.symm
        · exfalso
          apply hcd
          rw [hc, hrs]
          exact hd.symm
      have hrmem : r ∈ roots := by simpa [roots] using hr
      have hperm : roots.Perm (r :: roots.erase r) :=
        List.perm_cons_erase hrmem
      rw [applyPairBlockList_eq_of_perm p hperm hnodup hroots h]
      rw [applyPairBlockList_cons]
      have hfixC : ∀ a ∈ roots.erase r,
          c ≠ a ∧ c ≠ partner (Fin q) p a := by
        intro a ha
        have haRoots : a ∈ pairRoots p := hroots a (List.mem_of_mem_erase ha)
        have har : a ≠ r := ((hnodup.mem_erase_iff).mp ha).1
        exact root_block_ne_of_roots_ne p haRoots hr har hcblock
      have hfixD : ∀ a ∈ roots.erase r,
          d ≠ a ∧ d ≠ partner (Fin q) p a := by
        intro a ha
        have haRoots : a ∈ pairRoots p := hroots a (List.mem_of_mem_erase ha)
        have har : a ≠ r := ((hnodup.mem_erase_iff).mp ha).1
        apply root_block_ne_of_roots_ne p haRoots hr har
        simpa [hrs] using hdblock
      rw [applyPairBlockList_apply_of_fixed p (roots.erase r)
        (pairBlockAverage r (partner (Fin q) p r) h) c d hfixC hfixD]
      unfold pairAverage
      rw [if_neg hcd, if_pos hpaired]
      unfold pairBlockAverage
      rcases hcblock with hc | hc <;> rcases hdblock with hd | hd <;>
        simp [hc, hd, hrs, partner_partner, hsym, hdiag]
    · have hrmem : r ∈ roots := by simpa [roots] using hr
      have hsmem : s ∈ roots.erase r := by
        simp [hs, Ne.symm hrs, roots]
      have hperm₁ : roots.Perm (r :: roots.erase r) :=
        List.perm_cons_erase hrmem
      have hperm₂ : (roots.erase r).Perm
          (s :: (roots.erase r).erase s) := List.perm_cons_erase hsmem
      have hperm : roots.Perm
          (r :: s :: (roots.erase r).erase s) :=
        hperm₁.trans (List.Perm.cons r hperm₂)
      rw [applyPairBlockList_eq_of_perm p hperm hnodup hroots h]
      simp only [applyPairBlockList_cons]
      let rest := (roots.erase r).erase s
      have hfixC : ∀ a ∈ rest,
          c ≠ a ∧ c ≠ partner (Fin q) p a := by
        intro a ha
        have ha' : a ∈ (roots.erase r).erase s := by
          simpa [rest] using ha
        have haRoots : a ∈ pairRoots p :=
          hroots a (List.mem_of_mem_erase (List.mem_of_mem_erase ha'))
        have har : a ≠ r :=
          ((hnodup.mem_erase_iff).mp (List.mem_of_mem_erase ha')).1
        exact root_block_ne_of_roots_ne p haRoots hr har hcblock
      have hfixD : ∀ a ∈ rest,
          d ≠ a ∧ d ≠ partner (Fin q) p a := by
        intro a ha
        have ha' : a ∈ (roots.erase r).erase s := by
          simpa [rest] using ha
        have haRoots : a ∈ pairRoots p :=
          hroots a (List.mem_of_mem_erase (List.mem_of_mem_erase ha'))
        have has : a ≠ s := (((hnodup.erase r).mem_erase_iff).mp ha').1
        exact root_block_ne_of_roots_ne p haRoots hs has hdblock
      rw [applyPairBlockList_apply_of_fixed p rest
        (pairBlockAverage s (partner (Fin q) p s)
          (pairBlockAverage r (partner (Fin q) p r) h))
        c d hfixC hfixD]
      have hpcblock : partner (Fin q) p c = r ∨
          partner (Fin q) p c = partner (Fin q) p r := by
        rcases hcblock with hc | hc
        · exact Or.inr (by simpa [hc])
        · exact Or.inl (by simpa [hc, partner_partner])
      have hpdblock : partner (Fin q) p d = s ∨
          partner (Fin q) p d = partner (Fin q) p s := by
        rcases hdblock with hd | hd
        · exact Or.inr (by simpa [hd])
        · exact Or.inl (by simpa [hd, partner_partner])
      have hnotpaired : partner (Fin q) p c ≠ d := by
        intro hpair
        have : r = s := by
          simpa [r, s] using congrArg (pairRoot p) hpair
        exact hrs this
      have hdis := pair_blocks_disjoint_of_roots_ne p hr hs hrs
      unfold pairAverage pairBlockAverage
      rw [if_neg hcd, if_neg hnotpaired]
      rcases hcblock with hc | hc <;> rcases hdblock with hd | hd <;>
        simp [hc, hd, hrs, Ne.symm hrs,
          hdis.1, Ne.symm hdis.1,
          hdis.2.1, Ne.symm hdis.2.1,
          hdis.2.2, Ne.symm hdis.2.2,
          partner_partner, Equiv.swap_apply_of_ne_of_ne] <;> ring

end

end WeightedEdgeColoring.FiniteColorPairBlockOperators
