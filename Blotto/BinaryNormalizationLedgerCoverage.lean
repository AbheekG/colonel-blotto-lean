import Blotto.BinaryReturnedControlExtras
import Blotto.BinaryPromiseOpcodeBounds

/-! Attribution of already returned normalization charges. The three parser
normalization fields are present in the current complete entry, including both
sequential executions. Register and resource division/emission are retained at
the actual selected packed producers. These are proof-only views of existing
records, not extra executions, newly charged work, or native-cost claims. -/
namespace Blotto.BinaryNormalizationLedgerCoverage
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem raw_parser_fields (rich : Bool) (frame bits : List Bool) :
    let produced := BinaryPromiseOpcodeRequest.rawWithControlExtras rich frame bits
    let old := produced.1.1.1.1
    old.2.2.2.1.1.2 = (BinaryCanonicalNormalizationParser.read frame).2.2 ∧
      old.2.2.2.1.2 = (BinaryNumericalOpcodeParser.read frame).2.2 ∧
      old.2.2.2.2 = (BinaryPromiseOpcodeParser.read frame).2.2 := by
  have hPN := BinaryPromiseOpcodeRequest.raw_preceding rich frame bits
  have hNC := BinaryNumericalOpcodeRequest.raw_preceding rich frame bits
  have hCanonical := BinaryCanonicalNormalizationBounds.raw_price rich frame bits
  have hNumerical := BinaryNumericalOpcodeBounds.raw_price rich frame bits
  have hPromise := BinaryPromiseOpcodeBounds.raw_price rich frame bits
  have hC1 := congrArg (fun out => out.2.2.2.1.2) hPN
  have hC2 := congrArg (fun out => out.2.2.2.2) hNC
  have hN := congrArg (fun out => out.2.2.2.2) hPN
  dsimp only [BinaryRawParserProjection.keepComplete] at hC1 hC2 hN
  exact ⟨hC1.trans (hC2.trans hCanonical),hN.trans hNumerical,hPromise⟩

theorem parsedRaw_parser_fields (rich : Bool) (frame bits : List Bool) :
    let produced := BinaryPromiseOpcodeRequest.parsedRawWithControlExtras rich frame bits
    let old := produced.1.1.1.1
    old.2.2.2.1.1.2 = (BinaryCanonicalNormalizationParser.read frame).2.2 ∧
      old.2.2.2.1.2 = (BinaryNumericalOpcodeParser.read frame).2.2 ∧
      old.2.2.2.2 = (BinaryPromiseOpcodeParser.read frame).2.2 := by
  have hPN := BinaryPromiseOpcodeRequest.parsedRaw_preceding rich frame bits
  have hNC := BinaryNumericalOpcodeRequest.parsedRaw_preceding rich frame bits
  have hCanonical := BinaryCanonicalNormalizationBounds.parsedRaw_price rich frame bits
  have hNumerical := BinaryNumericalOpcodeBounds.parsedRaw_price rich frame bits
  have hPromise := BinaryPromiseOpcodeBounds.parsedRaw_price rich frame bits
  have hC1 := congrArg (fun out => out.2.2.2.1.2) hPN
  have hC2 := congrArg (fun out => out.2.2.2.2) hNC
  have hN := congrArg (fun out => out.2.2.2.2) hPN
  dsimp only [BinaryRawParserProjection.keepComplete] at hC1 hC2 hN
  exact ⟨hC1.trans (hC2.trans hCanonical),hN.trans hNumerical,hPromise⟩

theorem generated_parser_fields {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    let produced := BinaryPromiseOpcodeRequest.generatedWithControlExtras next rich frame state
    let old := produced.1.1.1.1
    old.2.2.2.1.1.2 = (BinaryCanonicalNormalizationParser.read frame).2.2 ∧
      old.2.2.2.1.2 = (BinaryNumericalOpcodeParser.read frame).2.2 ∧
      old.2.2.2.2 = (BinaryPromiseOpcodeParser.read frame).2.2 := by
  have hPN := BinaryPromiseOpcodeRequest.generated_preceding next rich frame state
  have hNC := BinaryNumericalOpcodeRequest.generated_preceding next rich frame state
  have hCanonical := BinaryCanonicalNormalizationBounds.generated_price next rich frame state
  have hNumerical := BinaryNumericalOpcodeBounds.generated_price next rich frame state
  have hPromise := BinaryPromiseOpcodeBounds.generated_price next rich frame state
  have hC1 := congrArg (fun out => out.2.2.2.1.2) hPN
  have hC2 := congrArg (fun out => out.2.2.2.2) hNC
  have hN := congrArg (fun out => out.2.2.2.2) hPN
  dsimp only [BinaryRawParserProjection.keepComplete] at hC1 hC2 hN
  exact ⟨hC1.trans (hC2.trans hCanonical),hN.trans hNumerical,hPromise⟩

theorem parsedGenerated_parser_fields {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    let produced := BinaryPromiseOpcodeRequest.parsedGeneratedWithControlExtras next rich frame state
    let old := produced.1.1.1.1
    old.2.2.2.1.1.2 = (BinaryCanonicalNormalizationParser.read frame).2.2 ∧
      old.2.2.2.1.2 = (BinaryNumericalOpcodeParser.read frame).2.2 ∧
      old.2.2.2.2 = (BinaryPromiseOpcodeParser.read frame).2.2 := by
  have hPN := BinaryPromiseOpcodeRequest.parsedGenerated_preceding next rich frame state
  have hNC := BinaryNumericalOpcodeRequest.parsedGenerated_preceding next rich frame state
  have hCanonical := BinaryCanonicalNormalizationBounds.parsedGenerated_price next rich frame state
  have hNumerical := BinaryNumericalOpcodeBounds.parsedGenerated_price next rich frame state
  have hPromise := BinaryPromiseOpcodeBounds.parsedGenerated_price next rich frame state
  have hC1 := congrArg (fun out => out.2.2.2.1.2) hPN
  have hC2 := congrArg (fun out => out.2.2.2.2) hNC
  have hN := congrArg (fun out => out.2.2.2.2) hPN
  dsimp only [BinaryRawParserProjection.keepComplete] at hC1 hC2 hN
  exact ⟨hC1.trans (hC2.trans hCanonical),hN.trans hNumerical,hPromise⟩

theorem pair_parser_fields {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    let produced := BinaryPromiseOpcodeRequest.pairWithControlExtras next frame state
    let old := produced.1.1.1.1
    old.2.2.2.1.1.2 = 2*(BinaryCanonicalNormalizationParser.read frame).2.2 ∧
      old.2.2.2.1.2 = 2*(BinaryNumericalOpcodeParser.read frame).2.2 ∧
      old.2.2.2.2 = 2*(BinaryPromiseOpcodeParser.read frame).2.2 := by
  have hPN := BinaryPromiseOpcodeRequest.pair_preceding next frame state
  have hNC := BinaryNumericalOpcodeRequest.pair_preceding next frame state
  have hCanonical := BinaryCanonicalNormalizationBounds.pair_price next frame state
  have hNumerical := BinaryNumericalOpcodeBounds.pair_price next frame state
  have hPromise := BinaryPromiseOpcodeBounds.pair_price next frame state
  have hC1 := congrArg (fun out => out.2.2.2.1.2) hPN
  have hC2 := congrArg (fun out => out.2.2.2.2) hNC
  have hN := congrArg (fun out => out.2.2.2.2) hPN
  dsimp only [BinaryRawParserProjection.keepComplete] at hC1 hC2 hN
  exact ⟨hC1.trans (hC2.trans hCanonical),hN.trans hNumerical,hPromise⟩

theorem parsedPair_parser_fields {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    let produced := BinaryPromiseOpcodeRequest.parsedPairWithControlExtras next frame state
    let old := produced.1.1.1.1
    old.2.2.2.1.1.2 = 2*(BinaryCanonicalNormalizationParser.read frame).2.2 ∧
      old.2.2.2.1.2 = 2*(BinaryNumericalOpcodeParser.read frame).2.2 ∧
      old.2.2.2.2 = 2*(BinaryPromiseOpcodeParser.read frame).2.2 := by
  have hPN := BinaryPromiseOpcodeRequest.parsedPair_preceding next frame state
  have hNC := BinaryNumericalOpcodeRequest.parsedPair_preceding next frame state
  have hCanonical := BinaryCanonicalNormalizationBounds.parsedPair_price next frame state
  have hNumerical := BinaryNumericalOpcodeBounds.parsedPair_price next frame state
  have hPromise := BinaryPromiseOpcodeBounds.parsedPair_price next frame state
  have hC1 := congrArg (fun out => out.2.2.2.1.2) hPN
  have hC2 := congrArg (fun out => out.2.2.2.2) hNC
  have hN := congrArg (fun out => out.2.2.2.2) hPN
  dsimp only [BinaryRawParserProjection.keepComplete] at hC1 hC2 hN
  exact ⟨hC1.trans (hC2.trans hCanonical),hN.trans hNumerical,hPromise⟩

open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

theorem register_pair_retains (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    let input := (BinaryPackedPairPlan.source (hC := hC) limits state first second tail he).1
    let registers := BinaryRegisterStoragePlan.outputsWithEmission input.1.1
    let produced := BinaryPackedPairPlan.pairMeasured (hC := hC) limits state first second tail he
    produced.1.2 = registers.1.2 ∧ registers.2 ≤ produced.2 := by
  unfold BinaryPackedPairPlan.pairMeasured
  dsimp only
  exact ⟨rfl,by omega⟩

theorem resource_update_retains (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    let a := (BinaryPackedReadPlan.readWithEmission state.packed first.word).1
    let b := (BinaryPackedReadPlan.readWithEmission state.packed second.word).1
    let arithmetic := BinaryResourceOpcodePlan.pair a.1.1 b.1.1 chosen
    let produced := BinaryWriteUpdatePlan.updateTraceMeasured limits state first second tail chosen
    produced.1.1.1.2 = arithmetic.1.1.2+arithmetic.1.2.2 ∧ arithmetic.2 ≤ produced.1.2 := by
  unfold BinaryWriteUpdatePlan.updateTraceMeasured
  dsimp only
  exact ⟨rfl,by omega⟩

end Blotto.BinaryNormalizationLedgerCoverage
