import Blotto.RationalPRGLinearFramingWork
import Blotto.PRGAccuracyLogarithm

/-! Separates rational arithmetic from linear-word digit control in the
primary logical-store ledger. Parsing, native-word assembly/reference framing,
remaining metadata and complete space are separate components. -/

namespace Blotto.RationalPRGSharpArithmeticLedger
open RationalPRGLinearFramingWork
set_option autoImplicit false

theorem numeric_preparation_word_bound {n : ℕ} (i : RationalPRGOriginalInput n) (c K : ℕ) :
    RationalNestedInput.preparationNumericBitWork c K ≤ (7+4*c)*(n+K+1)*uniformWidth i K := by
  let W := uniformWidth i K
  let N := n+K+1
  have hW : 1 ≤ W := by dsimp [W,uniformWidth]; omega
  have hK : K ≤ N := by dsimp [N]; omega
  have hKN : K+1 ≤ N := by dsimp [N]; omega
  have hWord : binaryWordWidth K ≤ W := by
    have hl := Nat.log2_le_self K
    dsimp [W,uniformWidth]
    unfold binaryWordWidth
    omega
  have hNW : N ≤ N*W := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left N hW
  have hOne : K ≤ N*W := hK.trans hNW
  have hTwo := Nat.mul_le_mul hK hWord
  have hThree : K+2 ≤ 2*(N*W) := by omega
  have hFour := Nat.mul_le_mul_left (4+2*c) hTwo
  have hFive := Nat.mul_le_mul_left c hThree
  unfold RationalNestedInput.preparationNumericBitWork
  change _ ≤ (7+4*c)*N*W
  nlinarith only [hOne,hFour,hFive]

def sharpBound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c K h : ℕ) : ℕ :=
  3*h+1000000000*(c+1)*((n+1)*model.rat (uniformWidth i K)+(n+K+1)*uniformWidth i K)

theorem bound_sharp {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c K h : ℕ) :
    bound i model c K h ≤ sharpBound i model c K h := by
  let W := uniformWidth i K
  let P := model.rat W
  let N := n+K+1
  let A := (n+1)*P
  let B := N*W
  have widths := width_bounds i K
  have hW : 1 ≤ W := by dsimp [W,uniformWidth]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hn : n ≤ N := by dsimp [N]; omega
  have hPA : P ≤ A := by dsimp [A]; nlinarith
  have hWB : W ≤ B := by dsimp [B]; nlinarith only [hN]
  have hB : 1 ≤ B := hW.trans hWB
  have hNorm : 5*model.rat (1+2*i.originalInputWordWidth) ≤ 5*A := by
    have hm := (model.monotone widths.1).trans hPA
    nlinarith only [hm]
  have hSource : (192*n+15)*model.rat i.processingSourceWidth ≤ 207*A := by
    have hm := Nat.mul_le_mul (show 192*n+15 ≤ 207*(n+1) by omega) (model.monotone widths.2.1)
    simpa only [A,P,W,Nat.mul_assoc] using hm
  have hControl : (24*i.processingInputWidth+52)*(9*n+6*K+6002) ≤ 6002*B := by
    have hInput : 24*i.processingInputWidth+52 ≤ W := widths.2.2.2.2.2.2.1
    calc
      _ ≤ W*(6002*N) := Nat.mul_le_mul hInput (by dsimp [N]; omega)
      _ = 6002*B := by dsimp [B]; ring
  have hArithmetic : (70000020+8*n)*model.rat (i.processingCouplingWidth K) ≤ 70000028*A := by
    have hm : (70000020+8*n)*model.rat (i.processingCouplingWidth K) ≤ 70000028*(n+1)*P :=
      Nat.mul_le_mul (by omega) (model.monotone widths.2.2.1)
    simpa only [A,Nat.mul_assoc] using hm
  have hHeight : 320*i.processingControlHeight K ≤ 320*B := by
    have hh : i.processingControlHeight K ≤ W := by
      have hw := widths.2.2.2.2.2.1
      change 24*i.processingControlHeight K+28 ≤ W at hw
      omega
    exact Nat.mul_le_mul_left 320 (hh.trans hWB)
  have hCoins : (24*i.processingControlHeight K+28)*
      (162+2*RationalLottoResourceSystem.coinBitBudget n K) ≤ 6162*B := by
    have hHeight : 24*i.processingControlHeight K+28 ≤ W := widths.2.2.2.2.2.1
    calc
      _ ≤ W*(6162*N) := Nat.mul_le_mul hHeight (by
        unfold RationalLottoResourceSystem.coinBitBudget
        dsimp [N]
        omega)
      _ = 6162*B := by dsimp [B]; ring
  have hPrep : 9072*RationalNestedInput.preparationNumericBitWork c K ≤ 9072*(7+4*c)*B := by
    have hp := Nat.mul_le_mul_left 9072 (numeric_preparation_word_bound i c K)
    simpa only [B,N,W,Nat.mul_assoc] using hp
  have hFallback : 2*n*model.rat (1+2*(3+i.processingInputWidth)) ≤ 2*A := by
    have hm : 2*n*model.rat (1+2*(3+i.processingInputWidth)) ≤ 2*(n+1)*P :=
      Nat.mul_le_mul (by omega) (model.monotone widths.2.2.2.1)
    simpa only [A,Nat.mul_assoc] using hm
  have hScaling : 4*n*model.rat (i.scalingWidth K) ≤ 4*A := by
    have hm : 4*n*model.rat (i.scalingWidth K) ≤ 4*(n+1)*P :=
      Nat.mul_le_mul (by omega) (model.monotone widths.2.2.2.2.1)
    simpa only [A,Nat.mul_assoc] using hm
  have hFrame : 17*n*(2^77*(i.originalInputWordWidth+K+6)+1) ≤ B := by
    have hWord : 17*(2^77*(i.originalInputWordWidth+K+6)+1) ≤ W := widths.2.2.2.2.2.2.2
    calc
      _ = n*(17*(2^77*(i.originalInputWordWidth+K+6)+1)) := by ring
      _ ≤ n*W := Nat.mul_le_mul_left n hWord
      _ ≤ N*W := Nat.mul_le_mul_right W hn
  have hRatCoeff : 5+207+70000028+2+4 ≤ 1000000000*(c+1) := by omega
  have hWordCoeff : 6002+320+6162+9072*(7+4*c)+1+4 ≤ 1000000000*(c+1) := by omega
  have hRat := Nat.mul_le_mul_right A hRatCoeff
  have hWord := Nat.mul_le_mul_right B hWordCoeff
  unfold bound sharpBound RationalPRGOriginalInput.processingCouplingBound
  change _ ≤ 3*h+1000000000*(c+1)*(A+B)
  nlinarith only [hNorm,hSource,hControl,hArithmetic,hHeight,hCoins,hPrep,hFallback,hScaling,hFrame,hRat,hWord,hB]

theorem source_work_bounds {n : ℕ} (header : List Bool) (prepared : BinaryPRGPreparation.Prepared n)
    (h : prepared.Valid) (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    richWork header prepared h model primitive K bits ≤ sharpBound (prepared.original.source h.2.2) model c K header.length ∧
      poorWork header prepared h model primitive K bits ≤ sharpBound (prepared.original.source h.2.2) model c K header.length := by
  have hw := work_bounds header prepared h model primitive c hPrimitive K bits
  have hs := bound_sharp (prepared.original.source h.2.2) model c K header.length
  exact ⟨hw.1.trans hs,hw.2.trans hs⟩

/-! Keep the additive five bits inside the argument of Rat: monotonicity
does not permit pulling a constant out of an arbitrary rational cost model. -/

def accuracyWidth {n : ℕ} (i : RationalPRGOriginalInput n) (k : ℕ) : ℕ :=
  2^90*(i.originalInputWordWidth+k+11)

def accuracyBound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (c k h : ℕ) : ℕ :=
  3*h+1000000000*(c+1)*((n+1)*model.rat (accuracyWidth i k)+(n+k+6)*accuracyWidth i k)

theorem sharp_bound_accuracy {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (c K k h : ℕ) (hK : K ≤ k+5) :
    sharpBound i model c K h ≤ accuracyBound i model c k h := by
  have hW : uniformWidth i K ≤ accuracyWidth i k := by
    unfold uniformWidth accuracyWidth
    exact Nat.mul_le_mul_left (2^90) (by omega)
  have hR := Nat.mul_le_mul_left (n+1) (model.monotone hW)
  have hB := Nat.mul_le_mul (show n+K+1 ≤ n+k+6 by omega) hW
  exact Nat.add_le_add_left (Nat.mul_le_mul_left (1000000000*(c+1))
    (Nat.add_le_add hR hB)) (3*h)

theorem raw_accuracy_bound {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (model : RationalCostModel) (c h : ℕ) :
    sharpBound i model c a.precision h ≤
      accuracyBound i model c ⌈Real.logb 2 (1/a.real)⌉₊ h := by
  apply sharp_bound_accuracy
  simpa only [a.logExponent_eq_ceil] using a.precision_log_bounds.2

theorem rational_accuracy_bound {n : ℕ} (i : RationalPRGOriginalInput n) (ε : ℚ) (hε : 0 < ε)
    (model : RationalCostModel) (c h : ℕ) :
    sharpBound i model c (rationalAccuracyPrecision ε) h ≤
      accuracyBound i model c ⌈Real.logb 2 (1/(ε:ℝ))⌉₊ h :=
  sharp_bound_accuracy i model c _ _ h (rationalAccuracyPrecision_log_bounds ε hε).2

theorem rational_source_work_bounds {n : ℕ} (header : List Bool)
    (prepared : BinaryPRGPreparation.Prepared n) (h : prepared.Valid)
    (ε : ℚ) (hε : 0 < ε) (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n (rationalAccuracyPrecision ε)) → Bool) :
    let B := accuracyBound (prepared.original.source h.2.2) model c
      ⌈Real.logb 2 (1/(ε:ℝ))⌉₊ header.length
    richWork header prepared h model primitive (rationalAccuracyPrecision ε) bits ≤ B ∧
      poorWork header prepared h model primitive (rationalAccuracyPrecision ε) bits ≤ B := by
  have hw := source_work_bounds header prepared h model primitive c hPrimitive (rationalAccuracyPrecision ε) bits
  have hb := rational_accuracy_bound (prepared.original.source h.2.2) ε hε model c header.length
  exact ⟨hw.1.trans hb,hw.2.trans hb⟩

end Blotto.RationalPRGSharpArithmeticLedger
