import Blotto.GeneralPaperOriginalValueBitOperands

/-! A closed envelope for the complete native two-round value bit price.
Every actual scale, scan, returned-array and parent charge is included.
Original rational lengths appear only in the additive aggregate argument. -/
namespace Blotto.GeneralPaperOriginalValueBitEnvelope
open GeneralPaperOriginalValueBitOperands GeneralPaperOriginalSourceValuePrice
open GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def scaleEnvelope (model : RationalCostModel) (n k W : ℕ) : ℕ :=
  64*logarithm n k W*(operand n k W+model.rat (operand n k W))+
    4*model.rat (operand n k W)+128*operand n k W

theorem scale_work (model : RationalCostModel) (n k W c : ℕ) (hc : c≤512) :
    scalePrice model W c n k≤scaleEnvelope model n k W := by
  have h0 := (basics n k W).2.1
  have h1 := (basics n k W).2.2.1
  have h2 := model.monotone (power_width n k W)
  have h3 := model.monotone (scale_width n k W c hc)
  unfold scalePrice scaleEnvelope
  gcongr

theorem native_scale (model : RationalCostModel) (n k W c m : ℕ) (hc : c≤512) (hm : m≤n) :
    GeneralPaperValueRoundingPaperContract.scaleBitProfile model W c m k≤scaleEnvelope model n k W :=
  (scale_price model W c m n k hm).trans (scale_work model n k W c hc)

def ledger (model : RationalCostModel) (n k W S : ℕ) : ℕ :=
  let H := operand n k W
  let P := model.rat H
  let U := model.rat (aggregate n k W S)
  scaleEnvelope model n k W+13*U+512*(n+1)*H+128*H+
    scaleEnvelope model n k W+scaleEnvelope model n k W+
    n*(5*P+128*H)+192*H+GeneralPaperReducedValuesPrice.post model n H H+128*H+
    scaleEnvelope model n k W+13*U+512*(n+1)*H+128*H+128*H

def envelope (model : RationalCostModel) (n k W S : ℕ) : ℕ :=
  4096*(n+logarithm n k W+1)*(model.rat (operand n k W)+operand n k W)+
    26*model.rat (aggregate n k W S)

theorem ledger_bound (model : RationalCostModel) (n k W S : ℕ) : ledger model n k W S≤envelope model n k W S := by
  unfold ledger envelope scaleEnvelope GeneralPaperReducedValuesPrice.post
  nlinarith only [Nat.zero_le (n*model.rat (operand n k W)),Nat.zero_le (logarithm n k W*model.rat (operand n k W)),
    Nat.zero_le (n*operand n k W),Nat.zero_le (logarithm n k W*operand n k W),
    Nat.zero_le (model.rat (operand n k W)),Nat.zero_le (operand n k W)]

theorem native_ledger {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    bitPrice model W k values≤ledger model n k W (GeneralPaperValueRoundingInputPrice.inputSize values) := by
  have hN : 1≤n := v.fields_positive
  have hW := (basics n k W).2.1
  have hS0 := native_scale model n k W 256 n (by decide) le_rfl
  have hS1 := native_scale model n k W 10 1 (by decide) hN
  have hS2 := native_scale model n k W 8 1 (by decide) hN
  have hS3 := scale_work model n k W 512 le_rfl
  have hA0 := array_word n k W n (by omega)
  have hA1 := array_word n k W (2*n) (by omega)
  have hA2 := array_word n k W (2*n+GeneralPaperLightFieldReduction.representatives k) le_rfl
  have hQ := first_denominator_word model W k values v hv
  have hScan := model.monotone (scan_width n k W _ hQ)
  have hReduced := model.monotone (reduced_width n k W _ hQ)
  have hOriginal := model.monotone (first_aggregate k W 256 (by decide) values)
  have hSecond := model.monotone (second_aggregate n k W (GeneralPaperValueRoundingInputPrice.inputSize values))
  dsimp only [bitPrice,GeneralPaperOriginalValueReductionPrice.profile,ledger,GeneralPaperReducedValuesPrice.post]
  gcongr

theorem price_bound {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    bitPrice model W k values≤envelope model n k W (GeneralPaperValueRoundingInputPrice.inputSize values) :=
  (native_ledger model W k values v hv).trans (ledger_bound model n k W _)

theorem native_work {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).2≤
      envelope model n k W (GeneralPaperValueRoundingInputPrice.inputSize values) :=
  (GeneralPaperOriginalSourceValuePrice.bit_work model W k values v hv).trans (price_bound model W k values v hv)

end Blotto.GeneralPaperOriginalValueBitEnvelope
