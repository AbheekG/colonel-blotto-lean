import Blotto.GeneralPaperPhysicalResponseSourceCache

/-! Close literal full-source prices, including once-only shift construction
and every physical response check, against the same original source model.
Only erased closed profiles are compared with a fast rational majorant. -/
namespace Blotto.GeneralPaperPhysicalResponseSourcePrice
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem extra_mono {m : ℕ} (actual majorant : RationalCostModel) (h : ∀ w,actual.rat w≤majorant.rat w)
    (W qbar t : ℕ) (a : Alphabet) (shared : Shared m) (count : ℕ) :
    GeneralPaperPhysicalResponseSourceCache.bitExtra actual W qbar t a shared count≤
      GeneralPaperPhysicalResponseSourceCache.bitExtra majorant W qbar t a shared count := by
  unfold GeneralPaperPhysicalResponseSourceCache.bitExtra GeneralPaperPhysicalResponseSourceExecution.bitExtra
    GeneralPaperPhysicalResponseExecution.bitProfile GeneralPaperPhysicalResponseExecution.rowBitProfile
    GeneralPaperSourceRowsExecution.rowBitProfile GeneralPaperClosedBidExecution.bitProfile
    GeneralPaperPhysicalShiftExecution.bitProfile
  gcongr <;> apply h

def bitProfile {m : ℕ} (C d W k Qv qbar t : ℕ) (a : Alphabet) (shared : Shared m) (count : ℕ) : ℕ :=
  GeneralPaperFastSourceMajorant.profile C d W m k Qv a count+
    GeneralPaperPhysicalResponseSourceCache.bitExtra (GeneralPaperFastRationalMajorant.model C d) W qbar t a shared count

def arithmeticProfile {m : ℕ} (k Qv : ℕ) (a : Alphabet) (shared : Shared m) (count : ℕ) : ℕ :=
  GeneralPaperGeometricSourcePrice.arithmeticProfile m k Qv a count+
    GeneralPaperPhysicalResponseSourceCache.arithmeticExtra a shared count

theorem bit_work {m : ℕ} {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W k Qv qbar t : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (hB : RationalHeight Br t)
    (hbc : rationalWordWidth Bc≤GeneralPaperTagHeight.word (a.lambda+1) 0)
    (hbr : rationalWordWidth Br≤GeneralPaperTagHeight.word (a.lambda+1) 0) :
    let shared := prepare a k Qv weights Bc Br
    (GeneralPaperPhysicalResponseSourceCache.run true actual W k Qv qbar a c hc shared count).2≤
      bitProfile C d W k Qv qbar t a shared count := by
  let shared := prepare a k Qv weights Bc Br
  have hs := GeneralPaperFastSourceMajorant.native_work hg W k Qv a c hc weights Bc Br hw count he hbc hbr
  have hext := GeneralPaperPhysicalResponseSourceCache.bit_extra actual W k Qv qbar t a c hc shared count a.scalePositive
    (GeneralPaperProfitParameters.leaf_count_spec m a.lambda k Qv) hB
  have hm := extra_mono actual _ (GeneralPaperFastRationalMajorant.dominates hg) W qbar t a shared count
  exact hext.trans (Nat.add_le_add hs hm)

theorem arithmetic_work {m : ℕ} (model : RationalCostModel) (k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    (GeneralPaperPhysicalResponseSourceCache.run false model 1 k Qv qbar a c hc shared count).2≤
      arithmeticProfile k Qv a shared count := by
  have hs := (GeneralPaperGeometricSourcePrice.work model 1 k Qv a c hc weights Bc Br hw count he).2
  exact (GeneralPaperPhysicalResponseSourceCache.arithmetic_extra model k Qv qbar a c hc _ count).trans
    (Nat.add_le_add_right hs _)

end Blotto.GeneralPaperPhysicalResponseSourcePrice
