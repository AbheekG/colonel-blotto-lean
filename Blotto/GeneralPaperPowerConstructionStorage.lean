import Blotto.GeneralPaperEncodedPreparedPowers

/-! Power materialization keeps literal top/annotation/control records and
the shared table prefix. Prefix payloads are owned once; recursion frames
borrow them. The complete bit-operation allowance conservatively reserves
primitive scratch under the paper convention. No exact geometric rational
or runtime encoding/work census is constructed. -/
namespace Blotto.GeneralPaperPowerConstructionStorage
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable
open GeneralPaperEncodedPreparedPowers GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def recordBits (W : ℕ) (table : Table) : ℕ :=
  entryBits W table.top+natBits table.work+64*W

theorem record_bound (W m lambda k Qv columns : ℕ)
    (hc : columns≤(GeneralPaperPowerPrecision.prepare lambda k).columns) :
    let f := GeneralPaperPowerPrecision.prepare lambda k
    let b := (GeneralPaperPreparedPowers.prepare lambda k).base
    recordBits W (build f.unit f.fractionalBits b columns)≤
      3*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+96*W := by
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let b := (GeneralPaperPreparedPowers.prepare lambda k).base
  have hb := GeneralPaperPreparedPowers.prepared_base lambda k
  have hn := (build_good f.unit f.fractionalBits (GeneralPaperPowerPrecision.unit_positive lambda k)
    (GeneralPaperPowerPrecision.unit_power lambda k) b hb.1 hb.2.1 columns).1.2.1
  have he := (GeneralPaperPowerTableExponent.prefix_exponents lambda k columns hc).1
  have hNumber := GeneralPaperStoredNumberBits.operand m lambda k Qv _ hn
    (he.trans (by unfold GeneralPaperQuantileExponentRange.cap; omega))
  have hd := GeneralPaperPowerTableExponent.prefix_degree_cap lambda k columns hc
  have hdW := (Nat.add_le_add_left (binaryWordWidth_mono hd) 1).trans (GeneralPaperFreshMassPrice.offset_width m lambda k Qv)
  have hw := binaryWordWidth_mono (build_work f.unit f.fractionalBits columns b)
  have hm := GeneralPaperPowerTableBounds.metadata_word f.fractionalBits columns b
  have hMono : GeneralPaperPowerTableBounds.width f.fractionalBits columns b≤GeneralPaperPowerTableBounds.width f.fractionalBits f.columns b := by
    unfold GeneralPaperPowerTableBounds.width
    dsimp only [f] at hc ⊢
    omega
  have hWidth := (GeneralPaperPowerPreparationEnvelope.sizes m lambda k Qv).table
  have hWork := hm.trans (hMono.trans hWidth)
  have hCap : columns*(12*(f.fractionalBits+1)+82)+2≤GeneralPaperPowerTableBounds.metadataCap f.fractionalBits columns := by
    unfold GeneralPaperPowerTableBounds.metadataCap
    nlinarith only [Nat.zero_le (12*(f.fractionalBits+1)+82)]
  have hStoredWork := (Nat.add_le_add_left (hw.trans (binaryWordWidth_mono hCap)) 1).trans hWork
  unfold recordBits entryBits natBits
  dsimp only
  dsimp only [f,b,GeneralPaperPreparedPowers.prepare] at hNumber hdW hw hStoredWork ⊢
  omega

def frames (W : ℕ) (f : GeneralPaperPowerPrecision.Parameters) (columns : ℕ) : ℕ :=
  (columns+1)*(natBits f.unit+natBits f.fractionalBits+natBits columns+128*W)

theorem frames_bound (W m lambda k Qv columns : ℕ)
    (hc : columns≤(GeneralPaperPowerPrecision.prepare lambda k).columns) :
    frames W (GeneralPaperPowerPrecision.prepare lambda k) columns≤
      ((GeneralPaperPowerPrecision.prepare lambda k).columns+1)*
        (3*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+128*W) := by
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  have hm := GeneralPaperSourcePreparationControls.metadata m lambda k Qv
  have hp := hm.fractionalBits
  have hCols := hm.columns
  have hu := GeneralPaperParameterOperandBounds.dyadic_word f.fractionalBits
  rw [(GeneralPaperScoreScaleParameters.power_data _).1,←GeneralPaperPowerPrecision.unit_power lambda k] at hu
  have hP := GeneralPaperInitializerControlCounters.word_le_self f.fractionalBits
  have hC := GeneralPaperInitializerControlCounters.word_le_self f.columns
  have hsmall := binaryWordWidth_mono hc
  change f.fractionalBits≤128*GeneralPaperSourcePreparationSizes.measure m lambda k Qv at hp
  change f.columns≤32*GeneralPaperSourcePreparationSizes.measure m lambda k Qv at hCols
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  dsimp only [f] at hu hP hC hsmall hc hp hCols ⊢
  have huW : natBits f.unit≤H := by dsimp [natBits,f,H,GeneralPaperPowerPreparationEnvelope.operandWidth]; omega
  have hpW : natBits f.fractionalBits≤H := by dsimp [natBits,f,H,GeneralPaperPowerPreparationEnvelope.operandWidth]; omega
  have hcW : natBits columns≤H := by dsimp [natBits,f,H,GeneralPaperPowerPreparationEnvelope.operandWidth]; omega
  unfold frames
  exact Nat.mul_le_mul (Nat.add_le_add_right hc 1) (by dsimp only [f,H] at huW hpW hcW; omega)

def window (model : RationalCostModel) (W k : ℕ) (c : GeneralPaperSourcePreparationCache.Cache) (columns : ℕ) : ℕ :=
  let f := c.precision.parameters
  let b := (GeneralPaperStoredBasePrice.run model.rat W f.unit f.fractionalBits k).1
  let table := (GeneralPaperPowerTablePrice.run model.rat W f.unit f.fractionalBits b.number columns).1
  formatFootprint W f+2*tableFootprint W table.entries+2*recordBits W table+
    frames W f columns+(GeneralPaperCachedPowerPreparation.fromCache model.rat W k c).2+256*W

def profile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  4*(H+W)+32*W+2*(f.columns*(2*H+34*W)+32*W)+2*(3*H+96*W)+
    (f.columns+1)*(3*H+128*W)+131072*GeneralPaperSourcePreparationSizes.measure m lambda k Qv*(W+model.rat H)+256*W

theorem bounded (model : RationalCostModel) (W m lambda k Qv : ℕ) (c : GeneralPaperSourcePreparationCache.Cache)
    (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) (columns : ℕ)
    (hn : columns≤(GeneralPaperPowerPrecision.prepare lambda k).columns) :
    window model W k c columns≤profile model W m lambda k Qv := by
  have hScratch := (GeneralPaperCachedPowerPreparation.work model.rat model.monotone W m lambda k Qv c hc).trans
    (GeneralPaperPowerPreparationEnvelope.profile_bound model.rat model.monotone W m lambda k Qv)
  have hRecord := record_bound W m lambda k Qv columns hn
  have hTable := table_prefix W m lambda k Qv columns hn
  have hT := hTable.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  have hFrames := frames_bound W m lambda k Qv columns hn
  have hFormat := format_bound W m lambda k Qv
  subst c
  let f := GeneralPaperPowerPrecision.prepare lambda k
  have hb := GeneralPaperPreparedPowers.prepared_base lambda k
  unfold window
  dsimp only [GeneralPaperSourcePreparationCache.specification,GeneralPaperPrecisionParameterPrice.specification]
  rw [GeneralPaperStoredBasePrice.data,GeneralPaperPowerTablePrice.data model.rat W _ _
    (GeneralPaperPowerPrecision.unit_positive lambda k) (GeneralPaperPowerPrecision.unit_power lambda k)
    (GeneralPaperStoredGeometricBase.construct (GeneralPaperPowerPrecision.prepare lambda k).unit
      (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits k).number hb.1 hb.2.1]
  unfold profile
  dsimp only
  dsimp only [GeneralPaperPreparedPowers.prepare] at hRecord hT
  dsimp only [GeneralPaperSourcePreparationCache.specification,GeneralPaperPrecisionParameterPrice.specification] at hScratch
  omega

end Blotto.GeneralPaperPowerConstructionStorage
