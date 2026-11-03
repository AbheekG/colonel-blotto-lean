import Blotto.BinaryInitialArithmeticEntryWork
import Blotto.BinaryCacheArithmeticEntryWork
import Blotto.BinaryCacheFinishRequest

/-! Concrete request entry charges include initial comparisons, all reached
resource pairs and selected updates, and terminal cache preparation. This class
stops before terminal sampling/scaling; it does not assert whole-draw native cost. -/
namespace Blotto.BinaryResourceArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTracePlanMeasured
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryPRGTerminalWork
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {n : ℕ}

theorem native_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    BinaryInitialArithmeticEntryWork.source seed request rich pc hp 0 ≤ 2*listCells
      (BinaryWriteContinuationRequest.nativeAtWithEmission seed request rich pc hp).1.1.1.1.1.1.1.1.1.1.1.2 := by
  have h := BinaryInitialArithmeticEntryWork.source_emitted seed request rich pc hp
  simp only [BinaryWriteContinuationRequest.nativeAtWithEmission]
  split <;> simp only [emitFull_erases,emit_data,List.append_nil,denote,listCells_append,listCells_under,listCells] <;> omega

def run (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) : ℕ :=
  BinaryInitialArithmeticEntryWork.source seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega) 0

theorem run_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    run seed request rich ≤ 2*listCells
      (BinaryWriteContinuationRequest.runWithCharges seed request rich).1.1.1.1.1.1.1.1.1.2 := by
  have h := native_bound seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  simp only [run,BinaryWriteContinuationRequest.runWithCharges,emitFull_erases,emit_data,List.append_nil,
    denote,listCells_append,listCells_under,listCells]
  omega

theorem backend_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    run seed request rich ≤ 2*listCells
      (BinaryWriteContinuationRequest.backend.run seed request rich).1.1.1.1.2 :=
  run_bound seed request rich

def cache (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) : ℕ :=
  let supplied := BinaryWriteContinuationRequest.backend.run seed parsed.2 rich
  let initialized := supplied.1
  let returned := initialized.1
  let resource := returned.1
  run seed parsed.2 rich+
    match resource.1.1.1.1 with
    | none => 0
    | some state => BinaryCacheArithmeticEntryWork.cache
        (terminalInput parsed.2.logical.request rich state) parsed.2.physical.lengthStore 0

theorem cache_bound (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    cache parsed seed rich ≤ 2*listCells (BinaryCacheFinishRequest.cache parsed seed rich).1.1.1.2 := by
  have hr := backend_bound seed parsed.2 rich
  simp only [cache,BinaryCacheFinishRequest.cache]
  split
  · rename_i hNone
    simp only [hNone,BinaryWrapperEmission.one_trace,wrap,combine,listCells_append,listCells_under,listCells]
    omega
  · rename_i state hSome
    have hc := BinaryCacheArithmeticEntryWork.emitted_bound
      (terminalInput parsed.2.logical.request rich state) parsed.2.physical.lengthStore
    simp only [hSome,BinaryWrapperEmission.two_trace,wrap,combine,listCells_append,listCells_under,listCells]
    omega

theorem cache_with_work (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    let produced := BinaryCacheFinishRequest.cache parsed seed rich
    cache parsed seed rich+produced.1.1.2 ≤ 2*(listCells produced.1.1.1.2+produced.1.1.2) := by
  have h := cache_bound parsed seed rich
  dsimp only
  omega

theorem cache_width (parsed : PhysicalRequest) (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    binaryWordWidth (cache parsed seed rich) ≤
      binaryWordWidth (2*listCells (BinaryCacheFinishRequest.cache parsed seed rich).1.1.1.2) :=
  binaryWordWidth_mono (cache_bound parsed seed rich)

end Blotto.BinaryResourceArithmeticEntryWork
