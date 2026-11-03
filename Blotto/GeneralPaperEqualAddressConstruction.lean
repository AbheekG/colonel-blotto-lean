import Blotto.GeneralPaperStoredRationalWordLength

/-! Build the draw reference width from retained sizes and measured budget
length. Each integer sum/product and each word-length extraction executes
once; all scalar work and returned controls are retained in the price. -/
namespace Blotto.GeneralPaperEqualAddressConstruction
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 2048

def price (model : RationalCostModel) (A a b out : ℕ) : ℕ :=
  GeneralPaperNaturalScalarStep.word a + GeneralPaperNaturalScalarStep.word b +
    GeneralPaperNaturalScalarStep.word out +
    2 * model.rat (max (GeneralPaperNaturalScalarStep.word a) (GeneralPaperNaturalScalarStep.word b)) + 16 * A + 16

theorem price_work (model : RationalCostModel) (A a b out L : ℕ)
    (ha : GeneralPaperNaturalScalarStep.word a ≤ L) (hb : GeneralPaperNaturalScalarStep.word b ≤ L)
    (ho : GeneralPaperNaturalScalarStep.word out ≤ L) : price model A a b out ≤ 5 * model.rat L + 16 * A + 16 := by
  have h1 := ha.trans (model.word_le L)
  have h2 := hb.trans (model.word_le L)
  have h3 := ho.trans (model.word_le L)
  have h4 := model.monotone (max_le ha hb)
  unfold price
  omega

def run (model : RationalCostModel) (A n m k b : ℕ) : ℕ × ℕ :=
  let nWord := GeneralPaperStoredWordLength.run A n
  let s0 := b + nWord.1
  let s1 := s0 + k
  let size := s1 + 10
  let drawWord := 67108864 * size
  let c0 := n + m
  let c1 := c0 + k
  let count := c1 + 69
  let stride := drawWord + 1
  let pool := count * stride
  let target := pool + 1
  let address := GeneralPaperStoredWordLength.run A target
  (address.1, nWord.2 + price model A b nWord.1 s0 + price model A s0 k s1 + price model A s1 10 size +
    price model A 67108864 size drawWord + price model A n m c0 + price model A c0 k c1 +
    price model A c1 69 count + price model A drawWord 1 stride + price model A count stride pool +
    price model A pool 1 target + address.2 + 128 * A + 128)

theorem data (model : RationalCostModel) (A n m k b : ℕ) :
    (run model A n m k b).1 = GeneralPaperEqualBitDrawRates.address n m k b := by
  rfl

def operandWidth (n m k b : ℕ) : ℕ :=
  8 * (binaryWordWidth n + binaryWordWidth m + binaryWordWidth k + binaryWordWidth b + 64)

theorem join_work (A R sc0 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 sc1 : ℕ)
    (h0 : p0 ≤ 5 * R + 16 * A + 16) (h1 : p1 ≤ 5 * R + 16 * A + 16)
    (h2 : p2 ≤ 5 * R + 16 * A + 16) (h3 : p3 ≤ 5 * R + 16 * A + 16)
    (h4 : p4 ≤ 5 * R + 16 * A + 16) (h5 : p5 ≤ 5 * R + 16 * A + 16)
    (h6 : p6 ≤ 5 * R + 16 * A + 16) (h7 : p7 ≤ 5 * R + 16 * A + 16)
    (h8 : p8 ≤ 5 * R + 16 * A + 16) (h9 : p9 ≤ 5 * R + 16 * A + 16)
    (hSc0 : sc0 ≤ 64 * (R + A + 1)) (hSc1 : sc1 ≤ 64 * (R + A + 1)) :
    sc0 + p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8 + p9 + sc1 + 128 * A + 128 ≤
      1024 * (R + A + 1) := by omega

theorem width_bounds (wn wm wk wb wnw s0w s1w sw dw c0w c1w cw stw pw tw : ℕ)
    (hn : wnw ≤ wn + 1)
    (h0 : s0w ≤ wb + wnw + 1)
    (h1 : s1w ≤ s0w + wk + 1)
    (hs : sw ≤ s1w + 4 + 1)
    (hd : dw ≤ 27 + sw)
    (hc0 : c0w ≤ wn + wm + 1)
    (hc1 : c1w ≤ c0w + wk + 1)
    (hc : cw ≤ c1w + 7 + 1)
    (hst : stw ≤ dw + 1 + 1)
    (hp : pw ≤ cw + stw)
    (ht : tw ≤ pw + 1 + 1)
    : 1 + wn ≤ 8 * (wn + wm + wk + wb + 64) ∧
      1 + wm ≤ 8 * (wn + wm + wk + wb + 64) ∧
      1 + wk ≤ 8 * (wn + wm + wk + wb + 64) ∧
      1 + wb ≤ 8 * (wn + wm + wk + wb + 64) ∧
      1 + wnw ≤ 8 * (wn + wm + wk + wb + 64) ∧
      1 + s0w ≤ 8 * (wn + wm + wk + wb + 64) ∧
      1 + s1w ≤ 8 * (wn + wm + wk + wb + 64) ∧
      1 + sw ≤ 8 * (wn + wm + wk + wb + 64) ∧
      1 + dw ≤ 8 * (wn + wm + wk + wb + 64) ∧
      1 + c0w ≤ 8 * (wn + wm + wk + wb + 64) ∧
      1 + c1w ≤ 8 * (wn + wm + wk + wb + 64) ∧
      1 + cw ≤ 8 * (wn + wm + wk + wb + 64) ∧
      1 + stw ≤ 8 * (wn + wm + wk + wb + 64) ∧
      1 + pw ≤ 8 * (wn + wm + wk + wb + 64) ∧
      1 + tw ≤ 8 * (wn + wm + wk + wb + 64) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals omega

theorem work (model : RationalCostModel) (A n m k b : ℕ) :
    (run model A n m k b).2 ≤ 1024 * (model.rat (operandWidth n m k b) + A + 1) := by
  let s0 := b + binaryWordWidth n
  let s1 := s0 + k
  let size := s1 + 10
  let drawWord := 67108864 * size
  let c0 := n + m
  let c1 := c0 + k
  let count := c1 + 69
  let stride := drawWord + 1
  let pool := count * stride
  let target := pool + 1
  let L := operandWidth n m k b
  have hLow : 512 ≤ L := by dsimp only [L, operandWidth]; omega
  have hn : binaryWordWidth (binaryWordWidth n) ≤ binaryWordWidth n + 1 :=
    Nat.add_le_add_right (Nat.log2_le_self (binaryWordWidth n)) 1
  have hs0 := GeneralPaperRayOperandWidthEnvelope.word_add b (binaryWordWidth n)
  have hs1 := GeneralPaperRayOperandWidthEnvelope.word_add s0 k
  have hs := GeneralPaperRayOperandWidthEnvelope.word_add s1 10
  have hd := binaryWordWidth_mul 67108864 size
  have hc0 := GeneralPaperRayOperandWidthEnvelope.word_add n m
  have hc1 := GeneralPaperRayOperandWidthEnvelope.word_add c0 k
  have hc := GeneralPaperRayOperandWidthEnvelope.word_add c1 69
  have hStride := GeneralPaperRayOperandWidthEnvelope.word_add drawWord 1
  have hPool := binaryWordWidth_mul count stride
  have hTarget := GeneralPaperRayOperandWidthEnvelope.word_add pool 1
  have hBig : binaryWordWidth 67108864 = 27 := by decide
  have h10 : binaryWordWidth 10 = 4 := by decide
  have h69 : binaryWordWidth 69 = 7 := by decide
  have h1 : binaryWordWidth 1 = 1 := by decide
  change binaryWordWidth s0 ≤ _ at hs0
  change binaryWordWidth s1 ≤ _ at hs1
  change binaryWordWidth size ≤ _ at hs
  change binaryWordWidth drawWord ≤ _ at hd
  change binaryWordWidth c0 ≤ _ at hc0
  change binaryWordWidth c1 ≤ _ at hc1
  change binaryWordWidth count ≤ _ at hc
  change binaryWordWidth stride ≤ _ at hStride
  change binaryWordWidth pool ≤ _ at hPool
  change binaryWordWidth target ≤ _ at hTarget
  have bounds := width_bounds (binaryWordWidth n) (binaryWordWidth m) (binaryWordWidth k) (binaryWordWidth b) (binaryWordWidth (binaryWordWidth n)) (binaryWordWidth s0) (binaryWordWidth s1) (binaryWordWidth size) (binaryWordWidth drawWord) (binaryWordWidth c0) (binaryWordWidth c1) (binaryWordWidth count) (binaryWordWidth stride) (binaryWordWidth pool) (binaryWordWidth target)
    hn hs0 hs1 (by simpa only [h10] using hs) (by simpa only [hBig] using hd)
    hc0 hc1 (by simpa only [h69] using hc) (by simpa only [h1] using hStride)
    hPool (by simpa only [h1] using hTarget)
  have b0 : 1 + (binaryWordWidth n) ≤ L := bounds.1
  have b1 : 1 + (binaryWordWidth m) ≤ L := bounds.2.1
  have b2 : 1 + (binaryWordWidth k) ≤ L := bounds.2.2.1
  have b3 : 1 + (binaryWordWidth b) ≤ L := bounds.2.2.2.1
  have b4 : 1 + (binaryWordWidth (binaryWordWidth n)) ≤ L := bounds.2.2.2.2.1
  have b5 : 1 + (binaryWordWidth s0) ≤ L := bounds.2.2.2.2.2.1
  have b6 : 1 + (binaryWordWidth s1) ≤ L := bounds.2.2.2.2.2.2.1
  have b7 : 1 + (binaryWordWidth size) ≤ L := bounds.2.2.2.2.2.2.2.1
  have b8 : 1 + (binaryWordWidth drawWord) ≤ L := bounds.2.2.2.2.2.2.2.2.1
  have b9 : 1 + (binaryWordWidth c0) ≤ L := bounds.2.2.2.2.2.2.2.2.2.1
  have b10 : 1 + (binaryWordWidth c1) ≤ L := bounds.2.2.2.2.2.2.2.2.2.2.1
  have b11 : 1 + (binaryWordWidth count) ≤ L := bounds.2.2.2.2.2.2.2.2.2.2.2.1
  have b12 : 1 + (binaryWordWidth stride) ≤ L := bounds.2.2.2.2.2.2.2.2.2.2.2.2.1
  have b13 : 1 + (binaryWordWidth pool) ≤ L := bounds.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have b14 : 1 + (binaryWordWidth target) ≤ L := bounds.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hPrice := model.word_le L
  have hN := (GeneralPaperStoredWordLength.work A n).trans
    (Nat.mul_le_mul_left 64 (Nat.add_le_add_right (Nat.add_le_add_right
      ((Nat.le_add_left (binaryWordWidth n) 1).trans b0 |>.trans hPrice) A) 1))
  have hTW := (GeneralPaperStoredWordLength.work A target).trans
    (Nat.mul_le_mul_left 64 (Nat.add_le_add_right (Nat.add_le_add_right
      ((Nat.le_add_left (binaryWordWidth target) 1).trans b14 |>.trans hPrice) A) 1))
  have hStep0 := price_work model A b (binaryWordWidth n) s0 L b3 b4 b5
  have hStep1 := price_work model A s0 k s1 L b5 b2 b6
  have hStep2 := price_work model A s1 10 size L b6 (by change 1 + binaryWordWidth 10 ≤ L; rw [h10]; exact (by decide : 5 ≤ 512).trans hLow) b7
  have hStep3 := price_work model A 67108864 size drawWord L (by change 1 + binaryWordWidth 67108864 ≤ L; rw [hBig]; exact (by decide : 28 ≤ 512).trans hLow) b7 b8
  have hStep4 := price_work model A n m c0 L b0 b1 b9
  have hStep5 := price_work model A c0 k c1 L b9 b2 b10
  have hStep6 := price_work model A c1 69 count L b10 (by change 1 + binaryWordWidth 69 ≤ L; rw [h69]; exact (by decide : 8 ≤ 512).trans hLow) b11
  have hStep7 := price_work model A drawWord 1 stride L b8 (by change 1 + binaryWordWidth 1 ≤ L; rw [h1]; exact (by decide : 2 ≤ 512).trans hLow) b12
  have hStep8 := price_work model A count stride pool L b11 b12 b13
  have hStep9 := price_work model A pool 1 target L b13 (by change 1 + binaryWordWidth 1 ≤ L; rw [h1]; exact (by decide : 2 ≤ 512).trans hLow) b14
  change (GeneralPaperStoredWordLength.run A n).2 + price model A b (binaryWordWidth n) s0 +
    price model A s0 k s1 + price model A s1 10 size + price model A 67108864 size drawWord +
    price model A n m c0 + price model A c0 k c1 + price model A c1 69 count +
    price model A drawWord 1 stride + price model A count stride pool + price model A pool 1 target +
    (GeneralPaperStoredWordLength.run A target).2 + 128 * A + 128 ≤ 1024 * (model.rat L + A + 1)
  exact join_work A (model.rat L) _ _ _ _ _ _ _ _ _ _ _ _
    hStep0 hStep1 hStep2 hStep3 hStep4 hStep5 hStep6 hStep7 hStep8 hStep9 hN hTW

end Blotto.GeneralPaperEqualAddressConstruction
