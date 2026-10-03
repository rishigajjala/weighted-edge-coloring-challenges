import WeightedEdgeColoring.KempeGraphMomentBlockAllCoordinates

/-!
# Sequential realization of a list of pairing blocks

Each ideal block operator is a contraction in the sup norm.  Consequently
the concrete component-selection errors add linearly while a list of disjoint
pairing blocks is processed.
-/

namespace WeightedEdgeColoring

open WeightedEdgeColoring.FiniteColorPairing
open WeightedEdgeColoring.FiniteColorPairingOperators
open WeightedEdgeColoring.FiniteColorPairBlockOperators
open WeightedEdgeColoring.WeightedMultigraph

noncomputable section

theorem singleBlockAverage_sup_nonexpansive
    {Color : Type*} [Fintype Color] [DecidableEq Color]
    (a b : Color) {x y : Color → ℝ} {eta : ℝ} (heta : 0 ≤ eta)
    (hxy : ∀ c, |x c - y c| ≤ eta) (c : Color) :
    |singleBlockAverage a b x c - singleBlockAverage a b y c| ≤ eta := by
  unfold singleBlockAverage
  rw [show
      (x c + x (Equiv.swap a b c)) / 2 -
        (y c + y (Equiv.swap a b c)) / 2 =
      ((x c - y c) +
        (x (Equiv.swap a b c) - y (Equiv.swap a b c))) / 2 by ring]
  calc
    |_ / 2| ≤ (|x c - y c| +
        |x (Equiv.swap a b c) - y (Equiv.swap a b c)|) / 2 := by
      rw [abs_div]
      norm_num
      exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    _ ≤ eta := by linarith [hxy c, hxy (Equiv.swap a b c)]

theorem pairBlockAverage_sup_nonexpansive
    {Color : Type*} [Fintype Color] [DecidableEq Color]
    (a b : Color) {x y : Color → Color → ℝ} {eta : ℝ} (heta : 0 ≤ eta)
    (hxy : ∀ c d, |x c d - y c d| ≤ eta) (c d : Color) :
    |pairBlockAverage a b x c d - pairBlockAverage a b y c d| ≤ eta := by
  unfold pairBlockAverage
  rw [show
      (x c d + x (Equiv.swap a b c) (Equiv.swap a b d)) / 2 -
        (y c d + y (Equiv.swap a b c) (Equiv.swap a b d)) / 2 =
      ((x c d - y c d) +
        (x (Equiv.swap a b c) (Equiv.swap a b d) -
          y (Equiv.swap a b c) (Equiv.swap a b d))) / 2 by ring]
  calc
    |_ / 2| ≤ (|x c d - y c d| +
        |x (Equiv.swap a b c) (Equiv.swap a b d) -
          y (Equiv.swap a b c) (Equiv.swap a b d)|) / 2 := by
      rw [abs_div]
      norm_num
      exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    _ ≤ eta := by
      linarith [hxy c d,
        hxy (Equiv.swap a b c) (Equiv.swap a b d)]

theorem applySingleBlockList_sup_nonexpansive
    {Color : Type*} [Fintype Color] [DecidableEq Color]
    (p : Pairing Color) (roots : List Color)
    {x y : Color → ℝ} {eta : ℝ} (heta : 0 ≤ eta)
    (hxy : ∀ c, |x c - y c| ≤ eta) (c : Color) :
    |applySingleBlockList p roots x c -
      applySingleBlockList p roots y c| ≤ eta := by
  induction roots generalizing x y with
  | nil => exact hxy c
  | cons a roots ih =>
      exact ih
        (singleBlockAverage_sup_nonexpansive
          a (partner Color p a) heta hxy)

theorem applyPairBlockList_sup_nonexpansive
    {Color : Type*} [Fintype Color] [DecidableEq Color]
    (p : Pairing Color) (roots : List Color)
    {x y : Color → Color → ℝ} {eta : ℝ} (heta : 0 ≤ eta)
    (hxy : ∀ c d, |x c d - y c d| ≤ eta) (c d : Color) :
    |applyPairBlockList p roots x c d -
      applyPairBlockList p roots y c d| ≤ eta := by
  induction roots generalizing x y with
  | nil => exact hxy c d
  | cons a roots ih =>
      exact ih
        (pairBlockAverage_sup_nonexpansive
          a (partner Color p a) heta hxy)

@[simp] theorem pairRoot_swap_partner {q : ℕ}
    (p : Pairing (Fin q)) (a c : Fin q) :
    pairRoot p (Equiv.swap a (partner (Fin q) p a) c) = pairRoot p c := by
  by_cases hca : c = a
  · subst c
    simp [pairRoot_partner]
  · by_cases hcb : c = partner (Fin q) p a
    · subst c
      simp [pairRoot_partner]
    · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]

theorem singleBlockTouches_iff_pairRoot_eq {q : ℕ}
    (p : Pairing (Fin q)) (a c : Fin q) :
    singleBlockTouches a (partner (Fin q) p a) c ↔
      pairRoot p c = pairRoot p a := by
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact pairRoot_partner p a
  · intro h
    rcases eq_or_partner_eq_of_pairRoot_eq p h with hca | hpa
    · exact Or.inl hca
    · right
      have := congrArg (partner (Fin q) p) hpa
      simpa [partner_partner] using this

theorem pairBlockTouches_iff_pairRoot_eq {q : ℕ}
    (p : Pairing (Fin q)) (a c d : Fin q) :
    pairBlockTouches a (partner (Fin q) p a) c d ↔
      pairRoot p c = pairRoot p a ∨ pairRoot p d = pairRoot p a := by
  simp only [pairBlockTouches, singleBlockTouches_iff_pairRoot_eq]

theorem applySingleBlockList_pointwise_nonexpansive
    {q : ℕ} (p : Pairing (Fin q)) (roots : List (Fin q))
    {x y : Fin q → ℝ} {rho : Fin q → ℝ}
    (hrho0 : ∀ c, 0 ≤ rho c)
    (hrho : ∀ a c,
      rho (Equiv.swap a (partner (Fin q) p a) c) = rho c)
    (hxy : ∀ c, |x c - y c| ≤ rho c) (c : Fin q) :
    |applySingleBlockList p roots x c -
      applySingleBlockList p roots y c| ≤ rho c := by
  induction roots generalizing x y with
  | nil => exact hxy c
  | cons a roots ih =>
      apply ih
      intro d
      unfold singleBlockAverage
      rw [show
          (x d + x (Equiv.swap a (partner (Fin q) p a) d)) / 2 -
              (y d + y (Equiv.swap a (partner (Fin q) p a) d)) / 2 =
            ((x d - y d) +
              (x (Equiv.swap a (partner (Fin q) p a) d) -
                y (Equiv.swap a (partner (Fin q) p a) d))) / 2 by ring]
      calc
        |_ / 2| ≤ (|x d - y d| +
            |x (Equiv.swap a (partner (Fin q) p a) d) -
              y (Equiv.swap a (partner (Fin q) p a) d)|) / 2 := by
          rw [abs_div]
          norm_num
          exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
        _ ≤ (rho d +
            rho (Equiv.swap a (partner (Fin q) p a) d)) / 2 := by
          gcongr
          · exact hxy d
          · exact hxy _
        _ = rho d := by rw [hrho]; ring

theorem applyPairBlockList_pointwise_nonexpansive
    {q : ℕ} (p : Pairing (Fin q)) (roots : List (Fin q))
    {x y : Fin q → Fin q → ℝ} {rho : Fin q → Fin q → ℝ}
    (hrho0 : ∀ c d, 0 ≤ rho c d)
    (hrho : ∀ a c d,
      rho (Equiv.swap a (partner (Fin q) p a) c)
          (Equiv.swap a (partner (Fin q) p a) d) = rho c d)
    (hxy : ∀ c d, |x c d - y c d| ≤ rho c d) (c d : Fin q) :
    |applyPairBlockList p roots x c d -
      applyPairBlockList p roots y c d| ≤ rho c d := by
  induction roots generalizing x y with
  | nil => exact hxy c d
  | cons a roots ih =>
      apply ih
      intro i j
      unfold pairBlockAverage
      rw [show
          (x i j + x (Equiv.swap a (partner (Fin q) p a) i)
              (Equiv.swap a (partner (Fin q) p a) j)) / 2 -
              (y i j + y (Equiv.swap a (partner (Fin q) p a) i)
                (Equiv.swap a (partner (Fin q) p a) j)) / 2 =
            ((x i j - y i j) +
              (x (Equiv.swap a (partner (Fin q) p a) i)
                  (Equiv.swap a (partner (Fin q) p a) j) -
                y (Equiv.swap a (partner (Fin q) p a) i)
                  (Equiv.swap a (partner (Fin q) p a) j))) / 2 by ring]
      calc
        |_ / 2| ≤ (|x i j - y i j| +
            |x (Equiv.swap a (partner (Fin q) p a) i)
                (Equiv.swap a (partner (Fin q) p a) j) -
              y (Equiv.swap a (partner (Fin q) p a) i)
                (Equiv.swap a (partner (Fin q) p a) j)|) / 2 := by
          rw [abs_div]
          norm_num
          exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
        _ ≤ (rho i j +
            rho (Equiv.swap a (partner (Fin q) p a) i)
              (Equiv.swap a (partner (Fin q) p a) j)) / 2 := by
          gcongr
          · exact hxy i j
          · exact hxy _ _
        _ = rho i j := by rw [hrho]; ring

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Sum of the errors of exactly those blocks containing `c`. -/
def singleRootError {q : ℕ} (p : Pairing (Fin q))
    (roots : List (Fin q)) (E : ℝ) (c : Fin q) : ℝ :=
  (roots.map fun a ↦ if pairRoot p c = pairRoot p a then E else 0).sum

/-- Sum of the errors of blocks containing either pair coordinate. -/
def pairRootError {q : ℕ} (p : Pairing (Fin q))
    (roots : List (Fin q)) (E : ℝ) (c d : Fin q) : ℝ :=
  (roots.map fun a ↦
    if pairRoot p c = pairRoot p a ∨ pairRoot p d = pairRoot p a
      then E else 0).sum

theorem singleRootError_eq_count {q : ℕ} (p : Pairing (Fin q))
    (roots : List (Fin q)) (E : ℝ) (c : Fin q)
    (hroots : ∀ a ∈ roots, a ∈ pairRoots p) :
    singleRootError p roots E c =
      (roots.count (pairRoot p c) : ℕ) * E := by
  induction roots with
  | nil => simp [singleRootError]
  | cons a roots ih =>
      have ha : a ∈ pairRoots p := hroots a (by simp)
      have htail : ∀ d ∈ roots, d ∈ pairRoots p := by
        intro d hd
        exact hroots d (by simp [hd])
      have hra : pairRoot p a = a :=
        pairRoot_unique p a a ha (Or.inl rfl)
      change (if pairRoot p c = pairRoot p a then E else 0) +
          singleRootError p roots E c =
        ((a :: roots).count (pairRoot p c) : ℕ) * E
      rw [ih htail, hra]
      by_cases hca : pairRoot p c = a
      · simp [hca]
        ring
      · have hac : a ≠ pairRoot p c := Ne.symm hca
        simp [hca, hac]

theorem singleRootError_pairRoots {q : ℕ} (p : Pairing (Fin q))
    (E : ℝ) (c : Fin q) :
    singleRootError p (pairRoots p).toList E c = E := by
  rw [singleRootError_eq_count]
  · have hmem : pairRoot p c ∈ (pairRoots p).toList := by
      simpa using pairRoot_mem_pairRoots p c
    have hcount := List.count_eq_one_of_mem
      (pairRoots p).nodup_toList hmem
    rw [hcount]
    norm_num
  · intro a ha
    simpa using ha

theorem pairRootError_le_add_singleRootError {q : ℕ}
    (p : Pairing (Fin q)) (roots : List (Fin q))
    {E : ℝ} (hE : 0 ≤ E) (c d : Fin q) :
    pairRootError p roots E c d ≤
      singleRootError p roots E c + singleRootError p roots E d := by
  induction roots with
  | nil => simp [pairRootError, singleRootError]
  | cons a roots ih =>
      simp only [pairRootError, singleRootError, List.map_cons, List.sum_cons]
        at ih ⊢
      by_cases hc : pairRoot p c = pairRoot p a <;>
        by_cases hd : pairRoot p d = pairRoot p a <;>
        simp [hc, hd] at ih ⊢ <;> linarith

theorem pairRootError_pairRoots_le_two {q : ℕ}
    (p : Pairing (Fin q)) {E : ℝ} (hE : 0 ≤ E) (c d : Fin q) :
    pairRootError p (pairRoots p).toList E c d ≤ 2 * E := by
  calc
    pairRootError p (pairRoots p).toList E c d ≤
        singleRootError p (pairRoots p).toList E c +
          singleRootError p (pairRoots p).toList E d :=
      pairRootError_le_add_singleRootError p _ hE c d
    _ = 2 * E := by rw [singleRootError_pairRoots,
      singleRootError_pairRoots]; ring

/-- Process a finite block list with one proper Kempe switch per block. -/
theorem exists_realizing_momentBlockList
    {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color)
    (p : Pairing (Fin q)) (roots : List (Fin q))
    (alpha L : ℝ) (halpha : 0 < alpha) (hL : 0 < L) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hrestricted : ∀ w, G.restrictedCharge R charge w ≤ n)
    (hpair : ∀ v w, G.pairCharge R charge v w ≤ L) :
    ∃ final : G.E → Fin q,
      G.IsProperOn F final ∧
      (∀ v c,
        |G.graphFirstMoment R charge F final v c -
          applySingleBlockList p roots
            (G.graphFirstMoment R charge F color v) c| ≤
          singleRootError p roots (G.momentBlockError alpha L n q) c) ∧
      (∀ v c,
        |G.graphDiagonalMoment R charge F final v c -
          applySingleBlockList p roots
            (G.graphDiagonalMoment R charge F color v) c| ≤
          singleRootError p roots
            (G.momentBlockError alpha L n q / n) c) ∧
      ∀ v c d,
        |G.graphPairMoment R charge F final v c d -
          applyPairBlockList p roots
            (G.graphPairMoment R charge F color v) c d| ≤
          pairRootError p roots
            (G.momentBlockError alpha L n q / n) c d := by
  induction roots generalizing color with
  | nil =>
      refine ⟨color, hproper, ?_, ?_, ?_⟩
      · intro v c
        simp [singleRootError]
      · intro v c
        simp [singleRootError]
      · intro v c d
        simp [pairRootError]
  | cons a roots ih =>
      let b := partner (Fin q) p a
      have hab : a ≠ b := Ne.symm (partner_ne (Fin q) p a)
      have herror0 : 0 ≤ G.momentBlockError alpha L n q :=
        G.momentBlockError_nonneg halpha hL hn
      have herrorSecond0 : 0 ≤ G.momentBlockError alpha L n q / n :=
        div_nonneg herror0 (Nat.cast_nonneg n)
      rcases G.exists_kempeBoolSwitch_realizing_momentBlock_allCoordinates
          R charge F color hproper a b hab alpha L halpha hL hn hcharge
          hmissing hrestricted hpair with
        ⟨next, hproperNext, hfirstStep, hdiagStep, hpairStep⟩
      have hmissingNext : ∀ w,
          alpha * n ≤ G.momentMissingSize F next w := by
        intro w
        have hcard := G.card_missingColorsAt_eq_of_isProperOn
          F color next hproper hproperNext w
        unfold momentMissingSize
        rw [← hcard]
        exact hmissing w
      rcases ih next hproperNext hmissingNext with
        ⟨final, hproperFinal, hfirstTail, hdiagTail, hpairTail⟩
      refine ⟨final, hproperFinal, ?_, ?_, ?_⟩
      · intro v c
        have hstep : ∀ d,
            |G.graphFirstMoment R charge F next v d -
              singleBlockAverage a b
                (G.graphFirstMoment R charge F color v) d| ≤
              if pairRoot p d = pairRoot p a then
                G.momentBlockError alpha L n q else 0 := by
          intro d
          simpa [b, singleBlockTouches_iff_pairRoot_eq] using
            hfirstStep v d
        have hprop := applySingleBlockList_pointwise_nonexpansive p roots
          (rho := fun d ↦ if pairRoot p d = pairRoot p a then
            G.momentBlockError alpha L n q else 0)
          (by
            intro d
            dsimp
            split
            · exact herror0
            · exact le_rfl)
          (by
            intro r d
            dsimp
            rw [pairRoot_swap_partner]) hstep c
        calc
          |G.graphFirstMoment R charge F final v c -
              applySingleBlockList p (a :: roots)
                (G.graphFirstMoment R charge F color v) c| ≤
            |G.graphFirstMoment R charge F final v c -
              applySingleBlockList p roots
                (G.graphFirstMoment R charge F next v) c| +
            |applySingleBlockList p roots
                (G.graphFirstMoment R charge F next v) c -
              applySingleBlockList p roots
                (singleBlockAverage a b
                  (G.graphFirstMoment R charge F color v)) c| := by
            rw [show
                G.graphFirstMoment R charge F final v c -
                    applySingleBlockList p (a :: roots)
                      (G.graphFirstMoment R charge F color v) c =
                  (G.graphFirstMoment R charge F final v c -
                    applySingleBlockList p roots
                      (G.graphFirstMoment R charge F next v) c) +
                  (applySingleBlockList p roots
                      (G.graphFirstMoment R charge F next v) c -
                    applySingleBlockList p roots
                      (singleBlockAverage a b
                        (G.graphFirstMoment R charge F color v)) c) by
              simp [applySingleBlockList, b]]
            exact abs_add_le _ _
          _ ≤ singleRootError p roots
                (G.momentBlockError alpha L n q) c +
              (if pairRoot p c = pairRoot p a then
                G.momentBlockError alpha L n q else 0) :=
            add_le_add (hfirstTail v c) hprop
          _ = singleRootError p (a :: roots)
              (G.momentBlockError alpha L n q) c := by
            simp [singleRootError, add_comm]
      · intro v c
        have hstep : ∀ d,
            |G.graphDiagonalMoment R charge F next v d -
              singleBlockAverage a b
                (G.graphDiagonalMoment R charge F color v) d| ≤
              if pairRoot p d = pairRoot p a then
                G.momentBlockError alpha L n q / n else 0 := by
          intro d
          simpa [b, singleBlockTouches_iff_pairRoot_eq] using
            hdiagStep v d
        have hprop := applySingleBlockList_pointwise_nonexpansive p roots
          (rho := fun d ↦ if pairRoot p d = pairRoot p a then
            G.momentBlockError alpha L n q / n else 0)
          (by
            intro d
            dsimp
            split
            · exact herrorSecond0
            · exact le_rfl)
          (by
            intro r d
            dsimp
            rw [pairRoot_swap_partner]) hstep c
        calc
          |G.graphDiagonalMoment R charge F final v c -
              applySingleBlockList p (a :: roots)
                (G.graphDiagonalMoment R charge F color v) c| ≤
            |G.graphDiagonalMoment R charge F final v c -
              applySingleBlockList p roots
                (G.graphDiagonalMoment R charge F next v) c| +
            |applySingleBlockList p roots
                (G.graphDiagonalMoment R charge F next v) c -
              applySingleBlockList p roots
                (singleBlockAverage a b
                  (G.graphDiagonalMoment R charge F color v)) c| := by
            rw [show
                G.graphDiagonalMoment R charge F final v c -
                    applySingleBlockList p (a :: roots)
                      (G.graphDiagonalMoment R charge F color v) c =
                  (G.graphDiagonalMoment R charge F final v c -
                    applySingleBlockList p roots
                      (G.graphDiagonalMoment R charge F next v) c) +
                  (applySingleBlockList p roots
                      (G.graphDiagonalMoment R charge F next v) c -
                    applySingleBlockList p roots
                      (singleBlockAverage a b
                        (G.graphDiagonalMoment R charge F color v)) c) by
              simp [applySingleBlockList, b]]
            exact abs_add_le _ _
          _ ≤ singleRootError p roots
                (G.momentBlockError alpha L n q / n) c +
              (if pairRoot p c = pairRoot p a then
                G.momentBlockError alpha L n q / n else 0) :=
            add_le_add (hdiagTail v c) hprop
          _ = singleRootError p (a :: roots)
              (G.momentBlockError alpha L n q / n) c := by
            simp [singleRootError, add_comm]
      · intro v c d
        have hstep : ∀ i j,
            |G.graphPairMoment R charge F next v i j -
              pairBlockAverage a b
                (G.graphPairMoment R charge F color v) i j| ≤
              if pairRoot p i = pairRoot p a ∨
                  pairRoot p j = pairRoot p a then
                G.momentBlockError alpha L n q / n else 0 := by
          intro i j
          simpa [b, pairBlockTouches_iff_pairRoot_eq] using
            hpairStep v i j
        have hprop := applyPairBlockList_pointwise_nonexpansive p roots
          (rho := fun i j ↦
            if pairRoot p i = pairRoot p a ∨
                pairRoot p j = pairRoot p a then
              G.momentBlockError alpha L n q / n else 0)
          (by
            intro i j
            dsimp
            split
            · exact herrorSecond0
            · exact le_rfl)
          (by
            intro r i j
            dsimp
            simp only [pairRoot_swap_partner]) hstep c d
        calc
          |G.graphPairMoment R charge F final v c d -
              applyPairBlockList p (a :: roots)
                (G.graphPairMoment R charge F color v) c d| ≤
            |G.graphPairMoment R charge F final v c d -
              applyPairBlockList p roots
                (G.graphPairMoment R charge F next v) c d| +
            |applyPairBlockList p roots
                (G.graphPairMoment R charge F next v) c d -
              applyPairBlockList p roots
                (pairBlockAverage a b
                  (G.graphPairMoment R charge F color v)) c d| := by
            rw [show
                G.graphPairMoment R charge F final v c d -
                    applyPairBlockList p (a :: roots)
                      (G.graphPairMoment R charge F color v) c d =
                  (G.graphPairMoment R charge F final v c d -
                    applyPairBlockList p roots
                      (G.graphPairMoment R charge F next v) c d) +
                  (applyPairBlockList p roots
                      (G.graphPairMoment R charge F next v) c d -
                    applyPairBlockList p roots
                      (pairBlockAverage a b
                        (G.graphPairMoment R charge F color v)) c d) by
              simp [applyPairBlockList, b]]
            exact abs_add_le _ _
          _ ≤ pairRootError p roots
                (G.momentBlockError alpha L n q / n) c d +
              (if pairRoot p c = pairRoot p a ∨
                  pairRoot p d = pairRoot p a then
                G.momentBlockError alpha L n q / n else 0) :=
            add_le_add (hpairTail v c d) hprop
          _ = pairRootError p (a :: roots)
              (G.momentBlockError alpha L n q / n) c d := by
            simp [pairRootError, add_comm]

/-- Sequentially realizing every block of one perfect pairing costs one
selector error on a single coordinate and at most two on a pair coordinate. -/
theorem exists_realizing_pairingStage
    {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (p : Pairing (Fin q))
    (alpha L : ℝ) (halpha : 0 < alpha) (hL : 0 < L) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hrestricted : ∀ w, G.restrictedCharge R charge w ≤ n)
    (hpair : ∀ v w, G.pairCharge R charge v w ≤ L) :
    ∃ next : G.E → Fin q,
      G.IsProperOn F next ∧
      (∀ v c,
        |G.graphFirstMoment R charge F next v c -
          singleAverage p
            (G.graphFirstMoment R charge F color v) c| ≤
          G.momentBlockError alpha L n q) ∧
      (∀ v c,
        |G.graphDiagonalMoment R charge F next v c -
          singleAverage p
            (G.graphDiagonalMoment R charge F color v) c| ≤
          G.momentBlockError alpha L n q / n) ∧
      ∀ v c d,
        |G.graphPairMoment R charge F next v c d -
          pairAverage p
            (G.graphPairMoment R charge F color v) c d| ≤
          2 * (G.momentBlockError alpha L n q / n) := by
  rcases G.exists_realizing_momentBlockList R charge F color hproper p
      (pairRoots p).toList alpha L halpha hL hn hcharge hmissing
      hrestricted hpair with
    ⟨next, hproperNext, hfirst, hdiag, hpairMoment⟩
  refine ⟨next, hproperNext, ?_, ?_, ?_⟩
  · intro v c
    simpa [applySingleBlockList_pairRoots,
      singleRootError_pairRoots] using hfirst v c
  · intro v c
    simpa [applySingleBlockList_pairRoots,
      singleRootError_pairRoots] using hdiag v c
  · intro v c d
    rw [← applyPairBlockList_pairRoots p
      (G.graphPairMoment R charge F color v)
      (G.graphPairMoment_symmetric R charge F color v)
      (by intro i; simp [graphPairMoment,
        WeightedMomentStatistics.pairMoment])]
    exact (hpairMoment v c d).trans
      (pairRootError_pairRoots_le_two p
        (div_nonneg (G.momentBlockError_nonneg halpha hL hn)
          (Nat.cast_nonneg n)) c d)

end WeightedMultigraph
end
end WeightedEdgeColoring
