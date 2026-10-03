import WeightedEdgeColoring.FiniteColorPairing

/-!
# One canonical representative of each color pair

For `Fin q` we represent a pair by its smaller color.  These representatives
let the component coins for one perfect pairing be selected sequentially
without choosing an arbitrary quotient of the color type.
-/

namespace WeightedEdgeColoring.FiniteColorPairing

noncomputable section

/-- Smaller member of the pair containing `c`. -/
def pairRoot {q : ℕ} (p : Pairing (Fin q)) (c : Fin q) : Fin q :=
  min c (partner (Fin q) p c)

/-- Finset containing exactly the smaller member of every pair. -/
def pairRoots {q : ℕ} (p : Pairing (Fin q)) : Finset (Fin q) :=
  Finset.univ.filter fun a ↦ a < partner (Fin q) p a

theorem mem_pairRoots_iff {q : ℕ} (p : Pairing (Fin q)) (a : Fin q) :
    a ∈ pairRoots p ↔ a < partner (Fin q) p a := by
  simp [pairRoots]

@[simp] theorem pairRoot_partner {q : ℕ}
    (p : Pairing (Fin q)) (c : Fin q) :
    pairRoot p (partner (Fin q) p c) = pairRoot p c := by
  simp [pairRoot, partner_partner, min_comm]

theorem pairRoot_mem_pairRoots {q : ℕ}
    (p : Pairing (Fin q)) (c : Fin q) : pairRoot p c ∈ pairRoots p := by
  rw [mem_pairRoots_iff]
  by_cases hle : c < partner (Fin q) p c
  · simp [pairRoot, min_eq_left hle.le, hle]
  · have hrev : partner (Fin q) p c < c := by
      exact lt_of_le_of_ne (le_of_not_gt hle)
        (partner_ne (Fin q) p c)
    simp [pairRoot, min_eq_right hrev.le, partner_partner, hrev]

theorem self_eq_pairRoot_or_partner_pairRoot {q : ℕ}
    (p : Pairing (Fin q)) (c : Fin q) :
    c = pairRoot p c ∨ c = partner (Fin q) p (pairRoot p c) := by
  by_cases hle : c ≤ partner (Fin q) p c
  · exact Or.inl (by simp [pairRoot, min_eq_left hle])
  · have hrev : partner (Fin q) p c ≤ c := le_of_not_ge hle
    exact Or.inr (by
      simp [pairRoot, min_eq_right hrev, partner_partner])

theorem eq_or_partner_eq_of_pairRoot_eq {q : ℕ}
    (p : Pairing (Fin q)) {c d : Fin q}
    (hroot : pairRoot p c = pairRoot p d) :
    c = d ∨ partner (Fin q) p c = d := by
  rcases self_eq_pairRoot_or_partner_pairRoot p c with hc | hc <;>
    rcases self_eq_pairRoot_or_partner_pairRoot p d with hd | hd
  · exact Or.inl (hc.trans (hroot.trans hd.symm))
  · right
    rw [hc, hroot]
    exact hd.symm
  · right
    rw [hc, hroot, partner_partner]
    exact hd.symm
  · have hp := congrArg (partner (Fin q) p) hroot
    exact Or.inl (hc.trans (hp.trans hd.symm))

/-- Two different roots represent disjoint two-element color blocks. -/
theorem pair_blocks_disjoint_of_roots_ne {q : ℕ}
    (p : Pairing (Fin q)) {a b : Fin q}
    (ha : a ∈ pairRoots p) (hb : b ∈ pairRoots p) (hab : a ≠ b) :
    a ≠ partner (Fin q) p b ∧
      partner (Fin q) p a ≠ b ∧
      partner (Fin q) p a ≠ partner (Fin q) p b := by
  have halt := (mem_pairRoots_iff p a).1 ha
  have hblt := (mem_pairRoots_iff p b).1 hb
  constructor
  · intro h
    subst a
    have := partner_partner (Fin q) p b
    omega
  constructor
  · intro h
    subst b
    have := partner_partner (Fin q) p a
    omega
  · intro h
    exact hab (partner_injective (Fin q) p h)

/-- Every color belongs to the block of its canonical root. -/
theorem color_mem_pairRoot_block {q : ℕ}
    (p : Pairing (Fin q)) (c : Fin q) :
    pairRoot p c ∈ pairRoots p ∧
      (c = pairRoot p c ∨ c = partner (Fin q) p (pairRoot p c)) :=
  ⟨pairRoot_mem_pairRoots p c, self_eq_pairRoot_or_partner_pairRoot p c⟩

/-- The root representing a color is unique. -/
theorem pairRoot_unique {q : ℕ}
    (p : Pairing (Fin q)) (c a : Fin q)
    (ha : a ∈ pairRoots p)
    (hc : c = a ∨ c = partner (Fin q) p a) :
    pairRoot p c = a := by
  have halt := (mem_pairRoots_iff p a).1 ha
  rcases hc with rfl | rfl
  · simp [pairRoot, min_eq_left halt.le]
  · rw [pairRoot, partner_partner, min_eq_right halt.le]

end

end WeightedEdgeColoring.FiniteColorPairing
