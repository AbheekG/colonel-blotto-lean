import Blotto.BinaryRegisterArithmeticEntryWork
import Blotto.BinaryWriteLoopBackend

/-! Proof-only entry charges follow resource arithmetic, actual persistent
writes and the subsequent active-set comparisons. Existing retained cells pay
all reached entries; old runtime fields and producers are unchanged. -/
namespace Blotto.BinarySelectionArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryTracePlanMeasured
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapPackedStore (Packed pack)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {capacity : Store} {n : ℕ} {hCount : n=capacity.cap.value}

theorem comparison_trace (a b : SignedWord) :
    BinaryArithmeticEntryWork.comparison a b ≤ 2*listCells (BinaryRationalComparisonMeasured.traced a b).1.2 := by
  simpa only [BinaryRationalComparisonMeasured.traced,listCells,Nat.add_zero] using
    BinaryArithmeticEntryWork.comparison_bound a b

def fractional (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) (depth : ℕ) : ℕ :=
  let bid := (BinaryPackedReadPlan.readWithEmission bids address.word).1
  let limit := (BinaryPackedReadPlan.readWithEmission (pack limits) address.word).1
  BinaryArithmeticEntryWork.comparison bid.1.1 BinaryRationalOpcode.zero+
    BinaryArithmeticEntryWork.comparison limit.1.1 bid.1.1

theorem fractional_bound (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) (depth : ℕ) :
    fractional limits bids address depth ≤ 2*listCells (denote (BinaryPrimitiveScanPlan.fractionalAt limits bids address depth).1.1.2) := by
  have hp := comparison_trace (BinaryPackedReadPlan.readWithEmission bids address.word).1.1.1 BinaryRationalOpcode.zero
  have hb := comparison_trace (BinaryPackedReadPlan.readWithEmission (pack limits) address.word).1.1.1
    (BinaryPackedReadPlan.readWithEmission bids address.word).1.1.1
  simp only [fractional,BinaryPrimitiveScanPlan.fractionalAt,denote,listCells_append,listCells_under,listCells]
  omega

def scan (limits : Stored capacity.tree) (bids : Packed capacity.width) : List (Address capacity.width capacity.cap) → ℕ → ℕ
  | [],_depth => 0
  | address::rest,depth => fractional limits bids address (depth+2)+scan limits bids rest (depth+2)

theorem scan_bound (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) (depth : ℕ) :
    scan limits bids addresses depth ≤ 2*listCells (denote (BinaryPrimitiveScanPlan.scanAt limits bids addresses depth).1.1.2) := by
  induction addresses generalizing depth with
  | nil => simp [scan,BinaryPrimitiveScanPlan.scanAt,denote,listCells]
  | cons address rest ih =>
      have hf := fractional_bound limits bids address (depth+2)
      have ht := ih (depth+2)
      simp only [scan,BinaryPrimitiveScanPlan.scanAt,denote,listCells_append,listCells]
      omega

theorem scan_emitted (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    scan limits bids addresses 0 ≤ 2*listCells (BinaryPrimitiveScanPlan.scanWithEmission limits bids addresses).1.1.1.2 := by
  have h := scan_bound limits bids addresses 0
  simpa only [BinaryPrimitiveScanPlan.scanWithEmission,BinaryNumericalReadbackPlan.finish_record,
    BinaryNumericalReadbackPlan.view] using h

theorem normalized_trace (op : RealArithmeticOp) (a b : SignedWord) :
    BinaryArithmeticEntryWork.raw op a b ≤ 2*listCells (BinaryNormalizationPlan.apply op a b).1.1.1.2 := by
  have h := BinaryArithmeticEntryWork.normalized_plan op a b 0
  simpa only [BinaryNormalizationPlan.apply,BinaryNormalizationPlan.finishMeasured,
    BinaryNumericalReadbackPlan.finish,emitFull_erases,emit_data,List.append_nil] using h

def resource (first second chosen : SignedWord) : ℕ :=
  let total := BinaryNormalizationPlan.apply .add first second
  BinaryArithmeticEntryWork.raw .add first second+
    BinaryArithmeticEntryWork.raw .sub total.1.1.1.1 chosen

theorem resource_bound (first second chosen : SignedWord) :
    resource first second chosen ≤ 2*(listCells (BinaryResourceOpcodePlan.pair first second chosen).1.1.1.1.2+
      listCells (BinaryResourceOpcodePlan.pair first second chosen).1.2.1.1.2) := by
  have ht := normalized_trace .add first second
  have ho := normalized_trace .sub (BinaryNormalizationPlan.apply .add first second).1.1.1.1 chosen
  simp only [resource,BinaryResourceOpcodePlan.pair]
  omega

def update (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap)) (chosen : SignedWord) : ℕ :=
  let a := (BinaryPackedReadPlan.readWithEmission state.packed first.word).1
  let b := (BinaryPackedReadPlan.readWithEmission state.packed second.word).1
  let arithmetic := BinaryResourceOpcodePlan.pair a.1.1 b.1.1 chosen
  let leaves := BinaryWriteLeafPlan.executeAtMeasured state.packed
    [(first.word,chosen),(second.word,arithmetic.1.2.1.1.1)] 0
  resource a.1.1 b.1.1 chosen+scan limits leaves.1.1.1.1 [first,second] 0

theorem update_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap)) (chosen : SignedWord) :
    update limits state first second tail chosen ≤
      2*listCells (BinaryWriteUpdatePlan.updateTraceMeasured limits state first second tail chosen).1.1.1.1.1.2 := by
  let a := (BinaryPackedReadPlan.readWithEmission state.packed first.word).1
  let b := (BinaryPackedReadPlan.readWithEmission state.packed second.word).1
  let arithmetic := BinaryResourceOpcodePlan.pair a.1.1 b.1.1 chosen
  let leaves := BinaryWriteLeafPlan.executeAtMeasured state.packed
    [(first.word,chosen),(second.word,arithmetic.1.2.1.1.1)] 0
  have hr := resource_bound a.1.1 b.1.1 chosen
  have hs := scan_emitted limits leaves.1.1.1.1 [first,second]
  dsimp only [a,b,arithmetic,leaves] at hr hs
  simp only [update,BinaryWriteUpdatePlan.updateTraceMeasured,BinaryPackedPairPlan.six_trace,
    wrapList,wrap,combine,listCells_append,listCells_under,listCells]
  omega

variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

def selected (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (outputs : BinaryPRGWordControllerPairOutputs.Outputs) (branch : Bool) : ℕ :=
  update limits state first second tail (if branch then outputs.upper else outputs.lower)

theorem selected_trace (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active=first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs=(BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs) (branch : Bool) :
    selected limits state first second tail outputs branch ≤
      2*listCells (BinaryWriteUpdatePlan.selectTraceMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).1.1.1.1.1.2 := by
  have h := update_bound limits state first second tail (if branch then outputs.upper else outputs.lower)
  simp only [selected,BinaryWriteUpdatePlan.selectTraceMeasured,BinaryPackedUpdatePlan.finishSelection,
    BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]
  omega

theorem selected_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active=first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs=(BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs) (branch : Bool) :
    selected limits state first second tail outputs branch ≤
      2*listCells (BinaryWriteLoopBackend.select limits hC state first second tail he outputs hOutputs branch).1.1.data.trace := by
  simpa only [BinaryWriteLoopBackend.select] using selected_trace limits state first second tail he outputs hOutputs branch

def prepared (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active=first::second::tail) : ℕ :=
  BinaryRegisterArithmeticEntryWork.outputs (BinaryPackedPairPlan.source (hC := hC) limits state first second tail he).1.1.1 0

theorem prepared_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active=first::second::tail) :
    prepared (hC := hC) limits state first second tail he ≤
      2*listCells (BinaryPackedLoopPlan.prepare limits hC state first second tail he).1.data.trace := by
  simpa only [prepared,BinaryPackedLoopPlan.prepare] using
    BinaryRegisterArithmeticEntryWork.packed_bound (hC := hC) limits state first second tail he

end Blotto.BinarySelectionArithmeticEntryWork
