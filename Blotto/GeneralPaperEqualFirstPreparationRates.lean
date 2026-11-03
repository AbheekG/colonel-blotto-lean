import Blotto.GeneralPaperEqualFirstPreparationWork

/-! Sharp quasilinear fast-bit growth of every executed corrected boundary
preparation phase. Word families here are analysis parameters; an executable
common-reference calibration and peak working-space join remain separate. -/
namespace Blotto.GeneralPaperEqualFirstPreparationRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth
open GeneralPaperEqualRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def aggregate (n k S : ℕ) : ℕ :=
  8 * S + n * (33 + 9 * binaryWordWidth (GeneralPaperValueRoundingPaperContract.scale 256 n k + n))

def profile (model : RationalCostModel) (W A n k S b : ℕ) : ℕ :=
  let L := 3670016 * (binaryWordWidth n + k + 11) + 1
  (GeneralPaperValueRoundingPaperContract.scaleBitProfile model W 256 n k +
      13 * model.rat (aggregate n k S) +
      512 * (n + 1) * GeneralPaperSummaryArrayExecution.arrayWord W n + 128 * W) +
    ((12 * n + 2) * model.rat (1 + 2 * GeneralPaperEqualLengthArray.height (binaryWordWidth n + k + 12)) +
      64 * (n + 1) * (A + 1) + PaperIndexedArrayConstruction.overhead id A n n) +
    ((12 * n + 12) * model.rat (3 + 2 * (binaryWordWidth n + k + 10)) + (12 * n + 24) * A +
      GeneralPaperEqualPackingExecution.unit A n * (2 * n + 4)) +
    (64 * (n + 1) * model.rat (4 * (binaryWordWidth n + k + 10) + 3) +
      4096 * (n + 1) * (A + binaryWordWidth (n + 1) + 1)) +
    (4294967296 * (model.rat (4194304 * (binaryWordWidth n + k + 11)) + A + 1)) +
    (1048576 * (model.rat (1048576 * (binaryWordWidth n + k + 11) + 1) + A + 1)) +
    (1048576 * (model.rat (3670016 * (binaryWordWidth n + k + 11) + 2) + A + 1)) +
    (64 * (binaryWordWidth (k + 5) + 1) * (A + model.rat (GeneralPaperNatPowerOperands.width 2 (k + 5))) + 128 * A + 128) +
    (128 * (L + 1) * (A + model.rat (L + 6) + 1)) +
    (8192 * (L + 1) * (model.rat (L + 8) + A + 1)) +
    (4096 * (b + A + model.rat (8 * (binaryWordWidth n + binaryWordWidth k + binaryWordWidth b + 66)) + 1)) +
    GeneralPaperEqualBitBranchRates.scanProfile model A n (k+1) +
    GeneralPaperEqualBitVertex.bound A n b + 192*A+192

theorem ledger_eq {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (budget : ℚ) :
    GeneralPaperEqualFirstPreparationWork.bound model W A k values budget =
      profile model W A n k (GeneralPaperValueRoundingInputPrice.inputSize values) (rationalWordWidth budget) := by
  unfold GeneralPaperEqualFirstPreparationWork.bound GeneralPaperEqualFirstPrefixRates.prefixBound
    GeneralPaperEqualFirstPreparationWork.continuationBound GeneralPaperEqualFirstPrefixRates.packingBound
    GeneralPaperEqualFirstPrefixRates.routeBound GeneralPaperEqualFirstPrefixRates.segmentBound
    GeneralPaperEqualFirstClosureRates.bound profile aggregate GeneralPaperValueRoundingInputPrice.size
  dsimp only
  ring

theorem scale_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (W n : Input → ℕ) (hW : Tight W) (hn : Small n) :
    Polylog (fun x => GeneralPaperValueRoundingPaperContract.scaleBitProfile model (W x) 256 (n x) x.k) := by
  have hw := of_tight hW
  have hPower : Small (fun x => 2 ^ x.k) := by fun_prop
  unfold GeneralPaperValueRoundingPaperContract.scaleBitProfile GeneralPaperNatPowerOperands.width
    GeneralPaperNaturalPrimitivePrice.binary GeneralPaperNaturalPrimitivePrice.word
  fun_prop (config := {maxSteps := 20000})

theorem aggregate_rate (n S r : Input → ℕ) (hn : Small n)
    (hnr : Linear n r) (hSr : Linear S r) :
    Linear (fun x => aggregate (n x) x.k (S x)) r := by
  unfold aggregate GeneralPaperValueRoundingPaperContract.scale
  fun_prop (config := {maxSteps := 20000})

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (W A n S b : Input → ℕ) (hW : Tight W) (hA : Tight A)
    (hn : Small n) (hS : Small S) (hb : Small b) :
    Linear (fun x => profile model (W x) (A x) (n x) x.k (S x) (b x))
      (fun x => S x + b x + n x) := by
  let r := fun x => S x + b x + n x
  have hnRate : Linear n r := bounded 1 (fun x => by dsimp [r]; omega)
  have hSRate : Linear S r := bounded 1 (fun x => by dsimp [r]; omega)
  have hbRate : Linear b r := bounded 1 (fun x => by dsimp [r]; omega)
  have hw := of_tight hW
  have ha := of_tight hA
  have hWPoly : Polylog W := poly_tight W hW
  have hAPoly : Polylog A := poly_tight A hA
  have hKPoly : Polylog Input.k := poly_tight Input.k k_tight
  have hScale := scale_rate model hFast W n hW hn
  have hScaleRate : Linear (fun x => GeneralPaperValueRoundingPaperContract.scaleBitProfile model (W x) 256 (n x) x.k) r :=
    linear_poly _ r hScale
  have hAggregate := aggregate_rate n S r hn hnRate hSRate
  have hAggregateSmall : Small (fun x => aggregate (n x) x.k (S x)) :=
    linear_small hAggregate (by dsimp [r]; fun_prop)
  have hRatAggregate : Linear (fun x => model.rat (aggregate (n x) x.k (S x))) r :=
    rational_linear model hFast _ r hAggregate hAggregateSmall
  change Linear _ r
  unfold profile GeneralPaperSummaryArrayExecution.arrayWord GeneralPaperEqualLengthArray.height
    expressionHeightBudget GeneralPaperEqualPackingExecution.unit GeneralPaperNatPowerOperands.width GeneralPaperEqualBitBranchRates.scanProfile
    GeneralPaperEqualBitBoundaryScan.stepBound GeneralPaperEqualRouteConstruction.indicesWork
    GeneralPaperEqualBitVertex.bound
  dsimp only
  fun_prop (config := {maxSteps := 30000})


theorem actual_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (W A n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x))
    (hv : ∀ x j, (values x).read j = (v x).weight j) (budget : Input → ℚ)
    (hW : Tight W) (hA : Tight A) (hn : Small n)
    (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)))
    (hb : Small (fun x => rationalWordWidth (budget x))) :
    Linear (fun x => (GeneralPaperEqualFirstBitDispatch.run model (W x) (A x) x.k
      (values x) (v x) (hv x) (budget x)).2)
      (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)+rationalWordWidth (budget x)+n x) := by
  have h := profile_rate model hFast W A n _ _ hW hA hn hS hb
  apply GeneralPaperSourceSoftBounds.dominated h
  intro x
  rw [← ledger_eq]
  exact GeneralPaperEqualFirstPreparationWork.work model (W x) (A x) x.k (values x) (v x) (hv x) (budget x)

end Blotto.GeneralPaperEqualFirstPreparationRates
