import Blotto.BinaryTerminalPhysicalParsedRawMeasured
import Blotto.BinaryTerminalPhysicalParsedGeneratedBounds
import Blotto.BinaryTerminalPhysicalParsedGeneratedLaw

/-! Joined contract for the actual parser-priced finite-bit source sampler.
The same producer has uniform joint work/allowance/usage and every-prefix
bounds, exact original bit counts, hard budgets and independent whole-law
continuous-regret guarantees at its actual accepted physical request. This
is the named fair-bit/source-component contract, not a native-machine claim. -/
namespace Blotto.BinaryTerminalPhysicalParsedContract
open MeasureTheory RationalLottoResourceSystem
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalParsedGeneratedMeasured
open BinaryTerminalPhysicalParsedGeneratedLaw (logical law pairLaw)
set_option autoImplicit false

theorem uniform_pair_resources : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S)
    (frame : List Bool) (state : S) (borrowed steps : ℕ),
    let output := pair next frame state
    let B := C*(frame.length+1)^d
    output.2+BinaryBigEndian.littleValue output.1.1.2.1+BinaryBigEndian.littleValue output.1.1.2.2+
        usage output.1.2 ≤ B ∧
      retainedHeap (borrowed+frame.length) output.1.2 steps ≤ borrowed+frame.length+B ∧
      framePeak (output.1.2.take steps) ≤ B := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalParsedGeneratedBounds.pair_uniform_joint
  refine ⟨C,d,?_⟩
  intro S next frame state borrowed steps
  have h := hBound next frame state
  have hu : usage (pair next frame state).1.2 ≤ C*(frame.length+1)^d := by omega
  exact ⟨h,all_prefix _ _ hu (borrowed+frame.length) steps⟩

theorem accepted_drawCount (frame : List Bool) (prepared : Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n)
    (hRead : (BinaryPRGPhysicalRawRequestMeasured.read frame).1.1 = some (prepared,[])) :
    BinaryPRGFreshRawLifetime.drawCount frame =
      sampleBitBudget prepared.1 prepared.2.logical.request.precision := by
  have h := BinaryTerminalPhysicalParsedGeneratedLaw.accepted_logical frame prepared hRead
  simp only [BinaryPRGFreshRawLifetime.drawCount,h,logical,ite_true]

theorem accepted_pair_bit_count {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) (calls : ℕ)
    (prepared : Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n)
    (hRead : (BinaryPRGPhysicalRawRequestMeasured.read frame).1.1 = some (prepared,[])) :
    (pair (FreshBitSeedLifetime.countedFresh next) frame (state,calls)).1.1.1.2.2 =
      calls+2*sampleBitBudget prepared.1 prepared.2.logical.request.precision := by
  have h := congrArg (fun data => data.2.2) (pair_counted next frame state calls)
  simpa only [accepted_drawCount frame prepared hRead] using h

theorem pair_bit_count_bound {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) (calls : ℕ) :
    (pair (FreshBitSeedLifetime.countedFresh next) frame (state,calls)).1.1.1.2.2 ≤ calls+16*frame.length+6050 := by
  have h := congrArg (fun data => data.2.2) (pair_counted next frame state calls)
  dsimp only at h
  have hb := BinaryPRGFreshPairLifetime.drawCount_bound frame
  omega

theorem accepted_pair_guarantees {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S)
    (prepared : Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n)
    (hRead : (BinaryPRGPhysicalRawRequestMeasured.read frame).1.1 = some (prepared,[])) :
    let request := logical prepared
    (pairLaw frame request : Measure (Allocation request.1 × Allocation request.1)) =
        (law frame request true : Measure (Allocation request.1)).prod
          (law frame request false : Measure (Allocation request.1)) ∧
      (regret request.2.request.source.realValues (request.2.request.source.a : ℝ)
          (law frame request true) (law frame request false) < request.2.request.accuracy.numeric.real ∧
        regret request.2.request.source.realValues (request.2.request.source.b : ℝ)
          (law frame request false) (law frame request true) < request.2.request.accuracy.numeric.real) ∧
      (FullBudget (request.2.request.source.a : ℝ)
          (fun j => (BinaryPRGSeedOutputLaw.readback request.1 ((pair next frame state).1.1.1.1.1.getD []) j : ℝ)) ∧
        FullBudget (request.2.request.source.b : ℝ)
          (fun j => (BinaryPRGSeedOutputLaw.readback request.1 ((pair next frame state).1.1.1.1.2.getD []) j : ℝ))) := by
  have hLogical := BinaryTerminalPhysicalParsedGeneratedLaw.accepted_logical frame prepared hRead
  exact ⟨BinaryTerminalPhysicalParsedGeneratedLaw.pairLaw_product frame (logical prepared) hLogical,
    BinaryTerminalPhysicalParsedGeneratedLaw.law_regrets frame (logical prepared) hLogical,
    BinaryTerminalPhysicalParsedGeneratedLaw.pair_every_path_fullBudget next frame (logical prepared) hLogical state⟩

end Blotto.BinaryTerminalPhysicalParsedContract
