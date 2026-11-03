import Blotto.BinaryLinearPRGRowFrame
import Blotto.RationalPRGNormalizationCost
import Blotto.RationalPRGOriginalScalingCost

/-! Composes the primary logical-resource-store arithmetic ledger with the
linear stored-word serializer. This model-qualified source ledger does not
price the concrete cubic Boolean arithmetic implementation, parsing, header
preparation, array extraction, metadata/address bits or native memory. -/
namespace Blotto.RationalPRGLinearFramingWork
open BinaryRationalNormalization BinaryPRGPreparation BinaryLinearRowFrame
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

def bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c K h : ℕ) : ℕ :=
  5*model.rat (1+2*i.originalInputWordWidth)+
    (192*n+15)*model.rat i.processingSourceWidth+
    (24*i.processingInputWidth+52)*(9*n+6*K+6002)+i.processingCouplingBound model c K+
    2*n*model.rat (1+2*(3+i.processingInputWidth))+4*n*model.rat (i.scalingWidth K)+
    3*h+17*n*(2^77*(i.originalInputWordWidth+K+6)+1)+4

noncomputable def richWork {n : ℕ} (header : List Bool) (prepared : Prepared n) (h : prepared.Valid)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  let i := prepared.original.source h.2.2
  i.normalizationBitWork model+i.richProcessingAndScalingWork model primitive false K bits+
    (frameRun header (BinaryPRGOriginalSampler.richSample prepared h K bits).data.toList).trace.length

noncomputable def poorWork {n : ℕ} (header : List Bool) (prepared : Prepared n) (h : prepared.Valid)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  let i := prepared.original.source h.2.2
  i.normalizationBitWork model+i.poorProcessingAndScalingWork model primitive false K bits+
    (frameRun header (BinaryPRGOriginalSampler.poorSample prepared h K bits).data.toList).trace.length

theorem work_bounds {n : ℕ} (header : List Bool) (prepared : Prepared n) (h : prepared.Valid)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    richWork header prepared h model primitive K bits ≤ bound (prepared.original.source h.2.2) model c K header.length ∧
      poorWork header prepared h model primitive K bits ≤ bound (prepared.original.source h.2.2) model c K header.length := by
  have hn := (prepared.original.source h.2.2).normalizationBitWork_bound model
  have hr := (prepared.original.source h.2.2).richProcessingAndScalingWork_bound model primitive c hPrimitive false K bits
  have hp := (prepared.original.source h.2.2).poorProcessingAndScalingWork_logical_bound model primitive c hPrimitive K bits
  have hf := BinaryLinearPRGRowFrame.serialization_bound header prepared h K bits
  dsimp only at hf
  have hc := Nat.mul_le_mul_right (model.rat (prepared.original.source h.2.2).processingSourceWidth)
    (show 32*n+15 ≤ 192*n+15 by omega)
  unfold richWork poorWork bound
  dsimp only
  constructor <;> omega

theorem count_le_inputWidth {n : ℕ} (i : RationalPRGOriginalInput n) : n ≤ i.originalInputWordWidth := by
  have hs : n ≤ ∑ j, rationalWordWidth (i.values j) := by
    calc
      n = ∑ _j : Fin n, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => by unfold rationalWordWidth; omega)
  unfold RationalPRGOriginalInput.originalInputWordWidth
  omega

def uniformWidth {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : ℕ :=
  2^90*(i.originalInputWordWidth+K+6)

set_option maxRecDepth 2000 in
theorem width_bounds {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) :
    1+2*i.originalInputWordWidth ≤ uniformWidth i K ∧
    i.processingSourceWidth ≤ uniformWidth i K ∧
    i.processingCouplingWidth K ≤ uniformWidth i K ∧
    1+2*(3+i.processingInputWidth) ≤ uniformWidth i K ∧
    i.scalingWidth K ≤ uniformWidth i K ∧
    24*i.processingControlHeight K+28 ≤ uniformWidth i K ∧
    24*i.processingInputWidth+52 ≤ uniformWidth i K ∧
    17*(2^77*(i.originalInputWordWidth+K+6)+1) ≤ uniformWidth i K := by
  have hn := count_le_inputWidth i
  have hl := Nat.log2_le_self (n+4)
  unfold uniformWidth RationalPRGOriginalInput.processingSourceWidth
    RationalPRGOriginalInput.processingCouplingWidth RationalPRGOriginalInput.processingControlHeight
    RationalPRGOriginalInput.processingInputWidth RationalPRGOriginalInput.scalingWidth
    RationalTerminalLotto.terminalCouplingWordHeight expressionHeightBudget binaryWordWidth
  norm_num only [Nat.reducePow,Nat.reduceMul]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

theorem numeric_preparation_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c K : ℕ) :
    RationalNestedInput.preparationNumericBitWork c K ≤
      (7+4*c)*(n+K+1)*model.rat (uniformWidth i K) := by
  have hw : 1 ≤ uniformWidth i K := by unfold uniformWidth; norm_num; omega
  have hk : binaryWordWidth K ≤ uniformWidth i K := by
    have hl := Nat.log2_le_self K
    unfold binaryWordWidth uniformWidth
    norm_num only [Nat.reducePow]
    omega
  have hp := model.word_le (uniformWidth i K)
  have h1 : K ≤ (n+K+1)*model.rat (uniformWidth i K) := by nlinarith
  have h2 : K*binaryWordWidth K ≤ (n+K+1)*model.rat (uniformWidth i K) := by nlinarith
  have h3 : K+2 ≤ 2*((n+K+1)*model.rat (uniformWidth i K)) := by nlinarith
  have h4 := Nat.mul_le_mul_left (4+2*c) h2
  have h5 := Nat.mul_le_mul_left c h3
  unfold RationalNestedInput.preparationNumericBitWork
  nlinarith only [h1,h4,h5]

theorem bound_uniform {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (c K h : ℕ) :
    bound i model c K h ≤ 3*h+1000000000*(c+1)*(n+K+1)*model.rat (uniformWidth i K) := by
  let P := model.rat (uniformWidth i K)
  let N := n+K+1
  have widths := width_bounds i K
  have hDom := model.word_le (uniformWidth i K)
  have hW : 1 ≤ uniformWidth i K := by unfold uniformWidth; norm_num; omega
  have hP : 1 ≤ P := hW.trans hDom
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hn : n ≤ N := by dsimp [N]; omega
  have hPN : P ≤ N*P := by nlinarith only [hN]
  have hNP : 1 ≤ N*P := by nlinarith only [hN,hP]
  have hNorm : 5*model.rat (1+2*i.originalInputWordWidth) ≤ 5*N*P := by
    have hh := (model.monotone widths.1).trans hPN
    nlinarith only [hh]
  have hSource : (192*n+15)*model.rat i.processingSourceWidth ≤ 207*N*P := by
    have hh := Nat.mul_le_mul (show 192*n+15 ≤ 207*N by dsimp [N]; omega)
      (model.monotone widths.2.1)
    exact hh
  have hControl : (24*i.processingInputWidth+52)*(9*n+6*K+6002) ≤ 6002*N*P := by
    have hh := Nat.mul_le_mul (widths.2.2.2.2.2.2.1.trans hDom)
      (show 9*n+6*K+6002 ≤ 6002*N by dsimp [N]; omega)
    nlinarith only [hh]
  have hArithmetic : (70000020+8*n)*model.rat (i.processingCouplingWidth K) ≤ 70000028*N*P :=
    Nat.mul_le_mul (by dsimp [N]; omega) (model.monotone widths.2.2.1)
  have hHeight : 320*i.processingControlHeight K ≤ 320*N*P := by
    have hh := widths.2.2.2.2.2.1.trans hDom
    have hSmall : i.processingControlHeight K ≤ P := by dsimp [P] at *; omega
    nlinarith only [hSmall,hPN]
  have hCoins : (24*i.processingControlHeight K+28)*
      (162+2*RationalLottoResourceSystem.coinBitBudget n K) ≤ 6162*N*P := by
    have hh := Nat.mul_le_mul (widths.2.2.2.2.2.1.trans hDom)
      (show 162+2*RationalLottoResourceSystem.coinBitBudget n K ≤ 6162*N by
        unfold RationalLottoResourceSystem.coinBitBudget
        dsimp [N]
        omega)
    nlinarith only [hh]
  have hPrep := Nat.mul_le_mul_left 9072 (numeric_preparation_bound i model c K)
  have hCoupling : i.processingCouplingBound model c K ≤
      (9072*(7+4*c)+70000028+320+6162)*N*P := by
    unfold RationalPRGOriginalInput.processingCouplingBound
    change 9072*RationalNestedInput.preparationNumericBitWork c K ≤ 9072*((7+4*c)*N*P) at hPrep
    nlinarith only [hPrep,hArithmetic,hHeight,hCoins]
  have hFallback : 2*n*model.rat (1+2*(3+i.processingInputWidth)) ≤ 2*N*P :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) (model.monotone widths.2.2.2.1)
  have hScaling : 4*n*model.rat (i.scalingWidth K) ≤ 4*N*P :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 4 hn) (model.monotone widths.2.2.2.2.1)
  have hFrame : 17*n*(2^77*(i.originalInputWordWidth+K+6)+1) ≤ N*P := by
    have hh := Nat.mul_le_mul_left n (widths.2.2.2.2.2.2.2.trans hDom)
    have hh' := Nat.mul_le_mul_right P hn
    nlinarith only [hh,hh']
  have hCoeff : 5+207+6002+(9072*(7+4*c)+70000028+320+6162)+2+4+1+4 ≤ 1000000000*(c+1) := by omega
  have hTotal := Nat.mul_le_mul_right (N*P) hCoeff
  unfold bound
  change _ ≤ 3*h+1000000000*(c+1)*N*P
  nlinarith only [hNorm,hSource,hControl,hCoupling,hFallback,hScaling,hFrame,hNP,hTotal]

theorem uniform_work_bounds {n : ℕ} (header : List Bool) (prepared : Prepared n) (h : prepared.Valid)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    let B := 3*header.length+1000000000*(c+1)*(n+K+1)*
      model.rat (uniformWidth (prepared.original.source h.2.2) K)
    richWork header prepared h model primitive K bits ≤ B ∧
      poorWork header prepared h model primitive K bits ≤ B := by
  have hw := work_bounds header prepared h model primitive c hPrimitive K bits
  have hb := bound_uniform (prepared.original.source h.2.2) model c K header.length
  exact ⟨hw.1.trans hb,hw.2.trans hb⟩

end Blotto.RationalPRGLinearFramingWork
