import Blotto.GeneralPaperRetainedTrajectoryBits

/-! Literal mantissa and signed-exponent payloads remain logarithmic in
the source controls. No exponent is expanded into a rational denominator. -/
namespace Blotto.GeneralPaperStoredNumberBits
open GeneralPaperDyadicFloat GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def bits (x : Number) : ℕ := 1+binaryWordWidth x.mantissa+binaryWordWidth x.exponent.natAbs

theorem bounded (m lambda k Qv : ℕ) (x : Number)
    (hn : Normal (GeneralPaperPowerPrecision.prepare lambda k).unit x)
    (he : x.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k) :
    bits x≤512*measure m lambda k Qv := by
  let M := measure m lambda k Qv
  let p := (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits
  have hNormal : Normal (2^p) x := by rw [←GeneralPaperPowerPrecision.unit_power lambda k]; exact hn
  have hm := GeneralPaperCFOperandPrice.small_word (p+1) x.mantissa (normal_mantissa_bits p x hNormal)
  have hex := (binaryWordWidth_mono he).trans (GeneralPaperStoredExponentEnvelope.word_bound m lambda k Qv)
  have hp := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  change p≤128*M at hp
  change binaryWordWidth x.exponent.natAbs≤256*M at hex
  have hM : 128≤M := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  unfold bits
  change _≤512*M
  omega

theorem cached {height : ℕ} (m lambda k Qv : ℕ) (node : GeneralPaperIntervalCache.Node height)
    (hh : height≤lambda+1) (hv : GeneralPaperIntervalCache.Valid lambda k node)
    (hp : GeneralPaperGlobalNodeQuery.PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    bits (GeneralPaperIntervalCache.mass (GeneralPaperPreparedPowers.prepare lambda k) node)≤512*measure m lambda k Qv :=
  bounded m lambda k Qv _ (GeneralPaperIntervalCache.valid_cache lambda k node hv).1
    (GeneralPaperTreeMassRange.cached lambda k node hh hv hp)

theorem operand (m lambda k Qv : ℕ) (x : Number)
    (hn : Normal (GeneralPaperPowerPrecision.prepare lambda k).unit x)
    (he : x.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k) :
    bits x≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv :=
  (bounded m lambda k Qv x hn he).trans (by unfold GeneralPaperPowerPreparationEnvelope.operandWidth; omega)

end Blotto.GeneralPaperStoredNumberBits
