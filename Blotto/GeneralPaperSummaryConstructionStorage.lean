import Blotto.GeneralPaperActualTraversalStorage
import Blotto.GeneralPaperEncodedReferenceVector

/-! Every summary fill reserves all occurrence slots, including unused
slots. Two mutable-array versions, indexed-loop frames and one actual query
callback are reserved together. Repeated codes occupy distinct slots.
No length/encoding pass is introduced by these erased observers. -/
namespace Blotto.GeneralPaperSummaryConstructionStorage
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
open GeneralPaperEncodedScalarStorage GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem element_word (bits : Bool) (primitive : ℕ → ℕ) (W m lambda k Qv digits height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (node : Node height) (hh : height≤lambda+1) (hv : Valid lambda k node)
    (hp : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) (r : Fin c.controls.source.summarySize) :
    natBits (element bits primitive W c digits height node r).1≤height+2 := by
  rw [element_data bits primitive W m lambda k Qv digits height c hc node hh hv hp r]
  have h := GeneralPaperQuantileDescent.code_bound c.powers digits (r.val+1) c.controls.source.summarySize
    (GeneralPaperGlobalNodeQuery.fresh c.powers 0 node).number height node 0
    (GeneralPaperGlobalNodeQuery.fresh c.powers 0 node).number GeneralPaperDyadicFloat.zero
  exact (Nat.add_le_add_left (GeneralPaperCFOperandPrice.small_word height _ h) 1).trans_eq (by omega)

def buffer (bits : Bool) (index primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (digits height : ℕ) (node : Node height) (count : ℕ) (hc : count≤c.controls.source.summarySize) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W c.controls.source.summarySize natBits
    (PaperIndexedArrayConstruction.fill index (if bits then arrayWord W c.controls.source.summarySize else W)
      (element bits primitive W c digits height node) count hc).1

theorem buffer_bound (bits : Bool) (index primitive : ℕ → ℕ) (W m lambda k Qv digits height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (node : Node height) (hh : height≤lambda+1) (hv : Valid lambda k node)
    (hp : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node)
    (count : ℕ) (hcount : count≤c.controls.source.summarySize) :
    buffer bits index primitive W c digits height node count hcount≤c.controls.source.summarySize*(height+2+W)+64*W :=
  GeneralPaperEncodedReferenceVector.indexed_reserved_prefix index _ W (height+2) natBits
    (element bits primitive W c digits height node)
    (element_word bits primitive W m lambda k Qv digits height c hc node hh hv hp) count hcount

def frames (W count : ℕ) : ℕ := (count+1)*(4*(1+binaryWordWidth (count+1))+128*W)

theorem frames_bound (W m lambda k Qv count : ℕ) (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    frames W count≤((GeneralPaperSourceParameters.prepare k).summarySize+1)*
      (8*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+128*W) := by
  have hs := GeneralPaperSummaryArrayControls.size_word m lambda k Qv
  have hw := GeneralPaperRayOperandWidthEnvelope.word_add (GeneralPaperSourceParameters.prepare k).summarySize 1
  have h1 : binaryWordWidth 1=1 := by decide
  have hm := binaryWordWidth_mono (Nat.add_le_add_right hc 1)
  have hH : 2≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    have h := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
    unfold GeneralPaperPowerPreparationEnvelope.operandWidth; omega
  unfold frames
  apply Nat.mul_le_mul (Nat.add_le_add_right hc 1)
  omega

def window (model : RationalCostModel) (index : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (digits height : ℕ) (node : Node height) (count : ℕ) (hc : count≤c.controls.source.summarySize)
    (r : Fin c.controls.source.summarySize) : ℕ :=
  2*buffer true index model.rat W c digits height node count hc+frames W c.controls.source.summarySize+
    GeneralPaperQuantileQueryStorage.window model W c digits (r.val+1) height node+
    natBits r.val+natBits (r.val+1)+128*W

def profile (model : RationalCostModel) (W m lambda k Qv height : ℕ) : ℕ :=
  let n := (GeneralPaperSourceParameters.prepare k).summarySize
  2*(n*(height+2+W)+64*W)+(n+1)*(8*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+128*W)+
    GeneralPaperQuantileQueryStorage.profile model W m lambda k Qv height+
    4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+128*W

theorem bounded (model : RationalCostModel) (index : ℕ → ℕ) (W m lambda k Qv digits height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hd : digits=GeneralPaperQuantileComparison.width lambda k) (node : Node height)
    (hh : height≤lambda+1) (hv : Valid lambda k node) (hp : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node)
    (count : ℕ) (hcount : count≤c.controls.source.summarySize) (r : Fin c.controls.source.summarySize) :
    window model index W c digits height node count hcount r≤profile model W m lambda k Qv height := by
  have hn : c.controls.source.summarySize=(GeneralPaperSourceParameters.prepare k).summarySize := by rw [hc]; rfl
  have hb := buffer_bound true index model.rat W m lambda k Qv digits height c hc node hh hv hp count hcount
  have hf := frames_bound W m lambda k Qv c.controls.source.summarySize (by rw [hn])
  have hr : r.val+1≤(GeneralPaperSourceParameters.prepare k).summarySize := by rw [←hn]; exact r.isLt
  have hq := GeneralPaperQuantileQueryStorage.bounded model W m lambda k Qv digits (r.val+1) height c hc node hd hr hh hv hp
  have hw := GeneralPaperSummaryArrayControls.size_word m lambda k Qv
  have ha := binaryWordWidth_mono (show r.val≤(GeneralPaperSourceParameters.prepare k).summarySize by omega)
  have ha1 := binaryWordWidth_mono hr
  unfold window profile
  rw [hn] at hb
  unfold natBits
  dsimp only
  omega

end Blotto.GeneralPaperSummaryConstructionStorage
