import Blotto.BinaryLifetimeArrayMeasured
import Blotto.BinaryPRGGlobalFallbackLifetime

/-! The original budget/zero global fallback uses the one-callback builder.
Budget and zero words are borrowed. Work includes source control and copied
reference reservations; native bit/address/ownership/observer/allocator prices
remain separate. This is the original global fallback, without local repair. -/

namespace Blotto.BinaryPRGGlobalFallbackMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false

def prepare {n : ℕ} (input : BinaryLottoResourceInput.Input n) : (FixedArrayTable n SignedWord × Trace) × ℕ :=
  BinaryLifetimeArrayMeasured.build n
    (fun j => ((if j.val = 0 then input.budget else BinaryRationalOpcode.zero,wrap 8 1 []),4))

theorem prepare_data {n : ℕ} (input : BinaryLottoResourceInput.Input n) :
    (prepare input).1.1 = (BinaryPRGGlobalFallbackLifetime.prepareWithTrace input).1 := by
  simp only [prepare,BinaryLifetimeArrayMeasured.build_data,BinaryPRGGlobalFallbackLifetime.prepareWithTrace,
    BinaryNestedResidualLifetime.copyWithTrace]

theorem prepare_state {n : ℕ} (input : BinaryLottoResourceInput.Input n) :
    (prepare input).1.1 = BinaryLottoSampler.fallback input := by
  rw [prepare_data,BinaryPRGGlobalFallbackLifetime.prepareWithTrace_erasure]

theorem prepare_read {n : ℕ} (input : BinaryLottoResourceInput.Input n) (j : Fin n) :
    (prepare input).1.1.read j = if j.val = 0 then input.budget else BinaryRationalOpcode.zero := by
  rw [prepare_state,BinaryLottoSampler.fallback,FixedArrayTable.read_ofFn]

theorem prepare_canonical {n : ℕ} (input : BinaryLottoResourceInput.Input n) (hC : input.Canonical) :
    ∀ j,CanonicalWord ((prepare input).1.1.read j) := by
  rw [prepare_state]
  exact BinaryLottoSampler.fallback_canonical input hC

theorem prepare_refines {n : ℕ} (input : BinaryLottoResourceInput.Input n)
    (source : RationalLottoResourceSystem n) (hRef : input.Refines source) :
    BinaryTerminalPartialRun.sourceRow (prepare input).1.1 = source.fallbackAllocation := by
  rw [prepare_state]
  exact BinaryLottoSampler.fallback_refines input source hRef

theorem prepare_fullBudget {n : ℕ} (input : BinaryLottoResourceInput.Input n)
    (source : RationalLottoResourceSystem n) (hRef : input.Refines source) :
    FullBudget (source.B : ℝ) (fun j => (value ((prepare input).1.1.read j) : ℝ)) := by
  change FullBudget (source.B : ℝ)
    (fun j => (BinaryTerminalPartialRun.sourceRow (prepare input).1.1 j : ℝ))
  rw [prepare_refines input source hRef]
  exact source.fallbackAllocation_fullBudget

theorem prepare_work {n : ℕ} (input : BinaryLottoResourceInput.Input n) :
    (prepare input).2 ≤ n*4+64*(n+1)^2 :=
  BinaryLifetimeArrayMeasured.build_work_bound n _ 4 (fun _ => le_rfl)

def envelope (n : ℕ) : ℕ := n*8+BinaryLifetimeArrayMeasured.storageReserve n+2*n+11

theorem prepare_usage {n : ℕ} (input : BinaryLottoResourceInput.Input n) :
    usage (prepare input).1.2 ≤ envelope n :=
  BinaryLifetimeArrayMeasured.build_bounds n _ 8 1
    (fun _ => by simp [BinaryPRGHeapPrimitiveLifetime.cells,wrap,combine,listCells,arraySlots])
    (fun _ => by simp [wrap,combine,framePeak])

theorem all_prefix {n : ℕ} (input : BinaryLottoResourceInput.Input n) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepare input).1.2 steps ≤ borrowed+envelope n ∧
      framePeak ((prepare input).1.2.take steps) ≤ envelope n :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (prepare_usage input) borrowed steps

theorem prepare_work_quadratic {n : ℕ} (input : BinaryLottoResourceInput.Input n) :
    (prepare input).2 ≤ 68*(n+1)^2 := by
  have h := prepare_work input
  nlinarith

theorem envelope_quadratic (n : ℕ) : envelope n ≤ 128*(n+1)^2 := by
  unfold envelope BinaryLifetimeArrayMeasured.storageReserve
  nlinarith

end Blotto.BinaryPRGGlobalFallbackMeasured
