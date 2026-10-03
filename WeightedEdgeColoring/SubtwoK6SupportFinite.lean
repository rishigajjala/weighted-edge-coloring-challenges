import Mathlib.Tactic

set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace WeightedEdgeColoring.Subtwo.K6SupportFinite

def degreePairMasks : Array (Array Nat) := #[#[3, 5, 9, 17, 6, 10, 18, 12, 20, 24], #[33, 65, 129, 257, 96, 160, 288, 192, 320, 384], #[34, 514, 1026, 2050, 544, 1056, 2080, 1536, 2560, 3072], #[68, 516, 4100, 8196, 576, 4160, 8256, 4608, 8704, 12288], #[136, 1032, 4104, 16392, 1152, 4224, 16512, 5120, 17408, 20480], #[272, 2064, 8208, 16400, 2304, 8448, 16640, 10240, 18432, 24576]]
def evenCycleMasks : Array Nat := #[102, 170, 204, 306, 340, 408, 549, 579, 1065, 1155, 1548, 1728, 1880, 1940, 2097, 2307, 2580, 2776, 2880, 2956, 3096, 3284, 3404, 3456, 4169, 4229, 4618, 4768, 4920, 5010, 5126, 5216, 5428, 5458, 6264, 6324, 6474, 6534, 6801, 6921, 7249, 7429, 8273, 8453, 8722, 8888, 8992, 9098, 9336, 9426, 9516, 9606, 9873, 9993, 10246, 10336, 10412, 10442, 11337, 11397, 12312, 12466, 12586, 12672, 13361, 13571, 14377, 14467, 15360, 16529, 16649, 17076, 17106, 17196, 17226, 17426, 17524, 17696, 17734, 18001, 18181, 18442, 18540, 18592, 18630, 19017, 19077, 20500, 20594, 20774, 20800, 21041, 21251, 22565, 22595, 23040, 24588, 24682, 24742, 24768, 25129, 25219, 25637, 25667, 26112]
def triangleCuts : Array (Nat × Array Nat) := #[(35, #[12, 20, 68, 132, 260, 516, 1028, 2052, 24, 72, 136, 264, 520, 1032, 2056, 80, 144, 272, 528, 1040, 2064, 192, 320, 576, 1088, 2112, 384, 640, 1152, 2176, 768, 1280, 2304, 1536, 2560, 3072]), (69, #[10, 18, 34, 130, 258, 514, 4098, 8194, 24, 40, 136, 264, 520, 4104, 8200, 48, 144, 272, 528, 4112, 8208, 160, 288, 544, 4128, 8224, 384, 640, 4224, 8320, 768, 4352, 8448, 4608, 8704, 12288]), (137, #[6, 18, 34, 66, 258, 1026, 4098, 16386, 20, 36, 68, 260, 1028, 4100, 16388, 48, 80, 272, 1040, 4112, 16400, 96, 288, 1056, 4128, 16416, 320, 1088, 4160, 16448, 1280, 4352, 16640, 5120, 17408, 20480]), (273, #[6, 10, 34, 66, 130, 2050, 8194, 16386, 12, 36, 68, 132, 2052, 8196, 16388, 40, 72, 136, 2056, 8200, 16392, 96, 160, 2080, 8224, 16416, 192, 2112, 8256, 16448, 2176, 8320, 16512, 10240, 18432, 24576]), (518, #[9, 17, 33, 65, 1025, 2049, 4097, 8193, 24, 40, 72, 1032, 2056, 4104, 8200, 48, 80, 1040, 2064, 4112, 8208, 96, 1056, 2080, 4128, 8224, 1088, 2112, 4160, 8256, 3072, 5120, 9216, 6144, 10240, 12288]), (1034, #[5, 17, 33, 129, 513, 2049, 4097, 16385, 20, 36, 132, 516, 2052, 4100, 16388, 48, 144, 528, 2064, 4112, 16400, 160, 544, 2080, 4128, 16416, 640, 2176, 4224, 16512, 2560, 4608, 16896, 6144, 18432, 20480]), (2066, #[5, 9, 33, 257, 513, 1025, 8193, 16385, 12, 36, 260, 516, 1028, 8196, 16388, 40, 264, 520, 1032, 8200, 16392, 288, 544, 1056, 8224, 16416, 768, 1280, 8448, 16640, 1536, 8704, 16896, 9216, 17408, 24576]), (4108, #[3, 17, 65, 129, 513, 1025, 8193, 16385, 18, 66, 130, 514, 1026, 8194, 16386, 80, 144, 528, 1040, 8208, 16400, 192, 576, 1088, 8256, 16448, 640, 1152, 8320, 16512, 1536, 8704, 16896, 9216, 17408, 24576]), (8212, #[3, 9, 65, 257, 513, 2049, 4097, 16385, 10, 66, 258, 514, 2050, 4098, 16386, 72, 264, 520, 2056, 4104, 16392, 320, 576, 2112, 4160, 16448, 768, 2304, 4352, 16640, 2560, 4608, 16896, 6144, 18432, 20480]), (16408, #[3, 5, 129, 257, 1025, 2049, 4097, 8193, 6, 130, 258, 1026, 2050, 4098, 8194, 132, 260, 1028, 2052, 4100, 8196, 384, 1152, 2176, 4224, 8320, 1280, 2304, 4352, 8448, 3072, 5120, 9216, 6144, 10240, 12288]), (608, #[3, 5, 129, 257, 1025, 2049, 4097, 8193, 6, 130, 258, 1026, 2050, 4098, 8194, 132, 260, 1028, 2052, 4100, 8196, 384, 1152, 2176, 4224, 8320, 1280, 2304, 4352, 8448, 3072, 5120, 9216, 6144, 10240, 12288]), (1184, #[3, 9, 65, 257, 513, 2049, 4097, 16385, 10, 66, 258, 514, 2050, 4098, 16386, 72, 264, 520, 2056, 4104, 16392, 320, 576, 2112, 4160, 16448, 768, 2304, 4352, 16640, 2560, 4608, 16896, 6144, 18432, 20480]), (2336, #[3, 17, 65, 129, 513, 1025, 8193, 16385, 18, 66, 130, 514, 1026, 8194, 16386, 80, 144, 528, 1040, 8208, 16400, 192, 576, 1088, 8256, 16448, 640, 1152, 8320, 16512, 1536, 8704, 16896, 9216, 17408, 24576]), (4288, #[5, 9, 33, 257, 513, 1025, 8193, 16385, 12, 36, 260, 516, 1028, 8196, 16388, 40, 264, 520, 1032, 8200, 16392, 288, 544, 1056, 8224, 16416, 768, 1280, 8448, 16640, 1536, 8704, 16896, 9216, 17408, 24576]), (8512, #[5, 17, 33, 129, 513, 2049, 4097, 16385, 20, 36, 132, 516, 2052, 4100, 16388, 48, 144, 528, 2064, 4112, 16400, 160, 544, 2080, 4128, 16416, 640, 2176, 4224, 16512, 2560, 4608, 16896, 6144, 18432, 20480]), (16768, #[9, 17, 33, 65, 1025, 2049, 4097, 8193, 24, 40, 72, 1032, 2056, 4104, 8200, 48, 80, 1040, 2064, 4112, 8208, 96, 1056, 2080, 4128, 8224, 1088, 2112, 4160, 8256, 3072, 5120, 9216, 6144, 10240, 12288]), (5632, #[6, 10, 34, 66, 130, 2050, 8194, 16386, 12, 36, 68, 132, 2052, 8196, 16388, 40, 72, 136, 2056, 8200, 16392, 96, 160, 2080, 8224, 16416, 192, 2112, 8256, 16448, 2176, 8320, 16512, 10240, 18432, 24576]), (10752, #[6, 18, 34, 66, 258, 1026, 4098, 16386, 20, 36, 68, 260, 1028, 4100, 16388, 48, 80, 272, 1040, 4112, 16400, 96, 288, 1056, 4128, 16416, 320, 1088, 4160, 16448, 1280, 4352, 16640, 5120, 17408, 20480]), (19456, #[10, 18, 34, 130, 258, 514, 4098, 8194, 24, 40, 136, 264, 520, 4104, 8200, 48, 144, 272, 528, 4112, 8208, 160, 288, 544, 4128, 8224, 384, 640, 4224, 8320, 768, 4352, 8448, 4608, 8704, 12288]), (28672, #[12, 20, 68, 132, 260, 516, 1028, 2052, 24, 72, 136, 264, 520, 1032, 2056, 80, 144, 272, 528, 1040, 2064, 192, 320, 576, 1088, 2112, 384, 640, 1152, 2176, 768, 1280, 2304, 1536, 2560, 3072])]
def contains (s m : Nat) : Bool := Nat.land s m == m
def minDegreeTwo (s : Nat) : Bool := degreePairMasks.all (fun pm => pm.any (contains s))
def hasEvenCycle (s : Nat) : Bool := evenCycleMasks.any (contains s)
def hasNarrowTriangle (s : Nat) : Bool :=
  triangleCuts.any (fun tc => contains s tc.1 && tc.2.all (fun pair => !contains s pair))

private theorem block0 :
    ∀ i : Fin 2048, minDegreeTwo (0 + i.val) = true →
      hasEvenCycle (0 + i.val) = true ∨ hasNarrowTriangle (0 + i.val) = true := by
  decide +kernel

private theorem block1 :
    ∀ i : Fin 2048, minDegreeTwo (2048 + i.val) = true →
      hasEvenCycle (2048 + i.val) = true ∨ hasNarrowTriangle (2048 + i.val) = true := by
  decide +kernel

private theorem block2 :
    ∀ i : Fin 2048, minDegreeTwo (4096 + i.val) = true →
      hasEvenCycle (4096 + i.val) = true ∨ hasNarrowTriangle (4096 + i.val) = true := by
  decide +kernel

private theorem block3 :
    ∀ i : Fin 2048, minDegreeTwo (6144 + i.val) = true →
      hasEvenCycle (6144 + i.val) = true ∨ hasNarrowTriangle (6144 + i.val) = true := by
  decide +kernel

private theorem block4 :
    ∀ i : Fin 2048, minDegreeTwo (8192 + i.val) = true →
      hasEvenCycle (8192 + i.val) = true ∨ hasNarrowTriangle (8192 + i.val) = true := by
  decide +kernel

private theorem block5 :
    ∀ i : Fin 2048, minDegreeTwo (10240 + i.val) = true →
      hasEvenCycle (10240 + i.val) = true ∨ hasNarrowTriangle (10240 + i.val) = true := by
  decide +kernel

private theorem block6 :
    ∀ i : Fin 2048, minDegreeTwo (12288 + i.val) = true →
      hasEvenCycle (12288 + i.val) = true ∨ hasNarrowTriangle (12288 + i.val) = true := by
  decide +kernel

private theorem block7 :
    ∀ i : Fin 2048, minDegreeTwo (14336 + i.val) = true →
      hasEvenCycle (14336 + i.val) = true ∨ hasNarrowTriangle (14336 + i.val) = true := by
  decide +kernel

private theorem block8 :
    ∀ i : Fin 2048, minDegreeTwo (16384 + i.val) = true →
      hasEvenCycle (16384 + i.val) = true ∨ hasNarrowTriangle (16384 + i.val) = true := by
  decide +kernel

private theorem block9 :
    ∀ i : Fin 2048, minDegreeTwo (18432 + i.val) = true →
      hasEvenCycle (18432 + i.val) = true ∨ hasNarrowTriangle (18432 + i.val) = true := by
  decide +kernel

private theorem block10 :
    ∀ i : Fin 2048, minDegreeTwo (20480 + i.val) = true →
      hasEvenCycle (20480 + i.val) = true ∨ hasNarrowTriangle (20480 + i.val) = true := by
  decide +kernel

private theorem block11 :
    ∀ i : Fin 2048, minDegreeTwo (22528 + i.val) = true →
      hasEvenCycle (22528 + i.val) = true ∨ hasNarrowTriangle (22528 + i.val) = true := by
  decide +kernel

private theorem block12 :
    ∀ i : Fin 2048, minDegreeTwo (24576 + i.val) = true →
      hasEvenCycle (24576 + i.val) = true ∨ hasNarrowTriangle (24576 + i.val) = true := by
  decide +kernel

private theorem block13 :
    ∀ i : Fin 2048, minDegreeTwo (26624 + i.val) = true →
      hasEvenCycle (26624 + i.val) = true ∨ hasNarrowTriangle (26624 + i.val) = true := by
  decide +kernel

private theorem block14 :
    ∀ i : Fin 2048, minDegreeTwo (28672 + i.val) = true →
      hasEvenCycle (28672 + i.val) = true ∨ hasNarrowTriangle (28672 + i.val) = true := by
  decide +kernel

private theorem block15 :
    ∀ i : Fin 2048, minDegreeTwo (30720 + i.val) = true →
      hasEvenCycle (30720 + i.val) = true ∨ hasNarrowTriangle (30720 + i.val) = true := by
  decide +kernel

private theorem allBlocks (j : Fin 16) (i : Fin 2048)
    (h : minDegreeTwo (2048*j.val + i.val) = true) :
      hasEvenCycle (2048*j.val+i.val) = true ∨
      hasNarrowTriangle (2048*j.val+i.val) = true := by
  fin_cases j

  · simpa using block0 i (by simpa using h)

  · simpa using block1 i (by simpa using h)

  · simpa using block2 i (by simpa using h)

  · simpa using block3 i (by simpa using h)

  · simpa using block4 i (by simpa using h)

  · simpa using block5 i (by simpa using h)

  · simpa using block6 i (by simpa using h)

  · simpa using block7 i (by simpa using h)

  · simpa using block8 i (by simpa using h)

  · simpa using block9 i (by simpa using h)

  · simpa using block10 i (by simpa using h)

  · simpa using block11 i (by simpa using h)

  · simpa using block12 i (by simpa using h)

  · simpa using block13 i (by simpa using h)

  · simpa using block14 i (by simpa using h)

  · simpa using block15 i (by simpa using h)


theorem support_dichotomy (s : Fin 32768)
    (h : minDegreeTwo s.val = true) :
      hasEvenCycle s.val = true ∨ hasNarrowTriangle s.val = true := by
  let j : Fin 16 := ⟨s.val / 2048, by omega⟩
  let i : Fin 2048 := ⟨s.val % 2048, by omega⟩
  have hs : s.val = 2048*j.val + i.val := by
    dsimp [j, i]
    omega
  rw [hs] at h ⊢
  exact allBlocks j i h

end WeightedEdgeColoring.Subtwo.K6SupportFinite
