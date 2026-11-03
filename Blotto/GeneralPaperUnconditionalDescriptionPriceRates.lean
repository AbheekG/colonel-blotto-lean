import Blotto.GeneralPaperNativeSourceTimeHeadline

/-! Source-based sorted row prices without any native/source family
matching premise. Representative count is the unconditional native dyadic
count; no unexecuted-branch relation to reduced count is assumed. -/
namespace Blotto.GeneralPaperUnconditionalDescriptionPriceRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

def rowPrice (model : RationalCostModel) (x : Input) : ℕ :=
  GeneralPaperCachedRowConstructionStorage.price model 1
    (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows (8*2^x.k)
    (1+2*GeneralPaperSourcePairAnchorHeights.width x.m x.k)

def certificate (C d : ℕ) : Certificate (rowPrice (GeneralPaperFastRationalMajorant.model C d)) := by
  have hRows := GeneralPaperSourceStaticConstructionRates.sharp_rows
  have hAnchor := GeneralPaperSourcePairAnchorHeights.width_rate
  have hAcc : Rated (fun x => 2^x.k) 0 0 1 := by simpa only [Nat.zero_add] using dyadic_accuracy 0
  refine ⟨2,0,5,?_⟩
  unfold rowPrice GeneralPaperCachedRowConstructionStorage.price GeneralPaperCachedRowConstructionStorage.rowPrice
    GeneralPaperSortedReferenceConstructionStorage.price GeneralPaperRepresentativeSortStorage.price
    GeneralPaperNativeRepresentativeSort.profile GeneralPaperPricedSort.profile GeneralPaperNativePayloadFillStorage.workCap
  dsimp only [GeneralPaperFastRationalMajorant.model]
  source_space

theorem degrees (C d : ℕ) : ((certificate C d).fields,(certificate C d).symbols,(certificate C d).accuracy)=(2,0,5) := rfl

theorem model_mono (actual upper : RationalCostModel) (h : ∀ w,actual.rat w≤upper.rat w) (x : Input) :
    rowPrice actual x≤rowPrice upper x := by
  unfold rowPrice GeneralPaperCachedRowConstructionStorage.price GeneralPaperCachedRowConstructionStorage.rowPrice
    GeneralPaperSortedReferenceConstructionStorage.price GeneralPaperRepresentativeSortStorage.price
    GeneralPaperNativeRepresentativeSort.profile GeneralPaperPricedSort.profile GeneralPaperNativePayloadFillStorage.workCap
  gcongr
  exact h _

theorem row_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Rated (rowPrice model) 2 0 5 :=
  GeneralPaperSourceSoftBounds.dominated (certificate C d).bound
    (fun x => model_mono model (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg) x)

end Blotto.GeneralPaperUnconditionalDescriptionPriceRates
