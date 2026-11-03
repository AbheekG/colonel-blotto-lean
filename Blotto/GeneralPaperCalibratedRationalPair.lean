import Blotto.GeneralPaperCompilerReferenceGrowth
import Blotto.GeneralPaperRationalPairBitPrice

/-! Complete local rational-pair bit price at a derived logarithmic word.
All source/compiler array-index premises are discharged. The word is an
erased model calibration; no profile evaluation or memory census is added
to preparation. Final paper time rates and whole-compiler live ownership
are separate obligations. The actual returned physical arrays and their
canonical continuous-game contract are preserved at this calibration. -/
namespace Blotto.GeneralPaperCalibratedRationalPair
open GeneralPaperSourceWordGrowth GeneralPaperCompilerReference
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

noncomputable def profile (model : RationalCostModel) (C d : ℕ) (x : Input) : ℕ :=
  let f := (GeneralPaperProxyClassifier.classify x.m x.k (x.b:ℝ)).choice.proxy
  GeneralPaperRationalPairBitPrice.profile model C d (width C d x) x.m x.k x.Qv x.B f.num f.den

theorem actual_work {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) (hm : 0<x.m) (hQv : 0<x.Qv)
    (hp : ∀ j,0<x.weights.read j) :
    (GeneralPaperRationalBitSourcePair.run model (width C d x)
      (GeneralPaperSourcePrecallPreparation.word x.m x.k x.Qv)
      (GeneralPaperRationalPairBitPrice.gridWord x.m x.k x.Qv) x.k x.Qv hQv x.weights hp x.weight_sum x.b).2≤
        profile model C d x := by
  rcases local_words C d x with ⟨hDim,hK,hM,hIndex,hBatch,hFinal,hColumns,hRows⟩
  exact GeneralPaperRationalPairBitPrice.actual_work hg (width C d x) x.k x.Qv hm hQv x.weights hp x.weight_sum
    x.b x.hb x.B x.hB (positive_width C d x) hDim hK hM hIndex hBatch hFinal hColumns hRows

theorem actual_return (model : RationalCostModel) (C d : ℕ) (x : Input) (hm : 0<x.m) (hQv : 0<x.Qv)
    (hp : ∀ j,0<x.weights.read j) :
    ∃ physical pair,
      (GeneralPaperRationalBitSourcePair.run model (width C d x)
        (GeneralPaperSourcePrecallPreparation.word x.m x.k x.Qv)
        (GeneralPaperRationalPairBitPrice.gridWord x.m x.k x.Qv) x.k x.Qv hQv x.weights hp x.weight_sum x.b).1=some physical ∧
      GeneralPaperSourcePairRun.run x.k x.Qv hQv x.weights hp x.weight_sum (x.b:ℝ)=some pair ∧
      GeneralPaperOriginalDrawEquilibrium.Matches physical pair ∧
      GeneralPaperSourcePairContract.Contract x.k x.Qv hQv x.weights hp x.weight_sum (x.b:ℝ) pair :=
  GeneralPaperRationalBitSourcePair.actual_return model (width C d x)
    (GeneralPaperSourcePrecallPreparation.word x.m x.k x.Qv)
    (GeneralPaperRationalPairBitPrice.gridWord x.m x.k x.Qv) x.k x.Qv hm hQv x.weights hp x.weight_sum x.b x.hb

end Blotto.GeneralPaperCalibratedRationalPair
