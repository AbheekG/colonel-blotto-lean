import Blotto.GeneralPaperEncodedSharedParameters

/-! The complete native Shared record, with literal input weights/budget
encodings explicit. Powers, profit grid, trajectory, spans and comparison
controls are bounded from actual one-time preparation. Other retained
front-end classifier/control objects and construction scratch are separate. -/
namespace Blotto.GeneralPaperEncodedSharedSource
open GeneralPaperCatalogueShared GeneralPaperCodeAlphabet GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def inputFootprint {m : ℕ} (W : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W weights+rationalWordWidth Bc+rationalWordWidth Br+64*W

def footprint {m : ℕ} (W : ℕ) (s : Shared m) : ℕ :=
  GeneralPaperEncodedPreparedPowers.footprint W s.powers+
    GeneralPaperEncodedSharedParameters.preparedProfitFootprint W s.profit+
    GeneralPaperEncodedSharedParameters.trajectoryFootprint W s.trajectory+natBits s.wordWidth+
    rationalWordWidth s.unsignedSpan+rationalWordWidth s.signedSpan+
    inputFootprint W s.weights s.Bc s.Br+128*W

def profile {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m a.lambda k Qv
  GeneralPaperEncodedPreparedPowers.profile W m a.lambda k Qv+
    GeneralPaperEncodedSharedParameters.preparedProfitProfile W m a.lambda k Qv+
    5*(H+W)+H+2*GeneralPaperSharedSpanPrice.width a+inputFootprint W weights Bc Br+160*W

theorem comparison_word (m lambda k Qv : ℕ) :
    natBits (GeneralPaperQuantileComparison.width lambda k)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hc := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).comparison
  have hw := GeneralPaperInitializerControlCounters.word_le_self (GeneralPaperQuantileComparison.width lambda k)
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  unfold natBits GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

theorem native {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    footprint W (prepare a k Qv weights Bc Br)≤profile W k Qv a weights Bc Br := by
  have hp := GeneralPaperEncodedPreparedPowers.native W m a.lambda k Qv
  have hg := GeneralPaperEncodedSharedParameters.prepared_profit W m a.lambda k Qv
  have ht := GeneralPaperEncodedSharedParameters.trajectory W m a.lambda k Qv
  have hc := comparison_word m a.lambda k Qv
  have hs := GeneralPaperSharedSpanPrice.widths a
  have hu := hs.2.2.1
  have hsign := hs.2.2.2.2
  unfold footprint profile
  dsimp only [prepare]
  omega

theorem cached {m : ℕ} (W localW k Qv : ℕ) (primitive : ℕ → ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedGridCache.Cache)
    (hc : c=GeneralPaperMaterializedGridCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    footprint W (GeneralPaperCachedSharedPreparation.fromCache primitive localW k a c weights Bc Br).1≤
      profile W k Qv a weights Bc Br := by
  rw [GeneralPaperCachedSharedPreparation.data primitive localW k Qv a c hc]
  exact native W k Qv a weights Bc Br

theorem prepared {m : ℕ} (W : ℕ) (model : RationalCostModel) (k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    footprint W (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1.1.2≤
      profile W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br := by
  rw [GeneralPaperPreparedSharedSource.data]
  exact native W k Qv _ weights Bc Br

theorem arithmetic {m : ℕ} (W k Qv : ℕ) (b : ℝ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    footprint W (GeneralPaperPreparedSharedSource.arithmetic k Qv b weights Bc Br).1.1.2≤
      profile W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br := by
  rw [GeneralPaperPreparedSharedSource.arithmetic_data]
  exact native W k Qv _ weights Bc Br

end Blotto.GeneralPaperEncodedSharedSource
