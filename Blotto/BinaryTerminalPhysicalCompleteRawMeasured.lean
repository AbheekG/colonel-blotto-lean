import Blotto.BinaryTerminalPhysicalCompleteSeedBounds
import Blotto.BinaryTerminalPhysicalOutputRaw

/-! Complete raw execution consumes the measured validator and full terminal/
fallback/output companion. Previous optional bytes and encoded allowances are
preserved; every reached source continuation and branch-control charge is
included. Parser execution and full native-machine pricing remain separate. -/

namespace Blotto.BinaryTerminalPhysicalCompleteRawMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def runReference (rich : Bool) (frame seed : List Bool) : ((Option (List Bool) × List Bool) × Trace) × ℕ :=
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  match hParsed : decoded.1 with
  | none => (((none,[]),wrap 16 2 [decoded.2]),4)
  | some parsed =>
      if parsed.2 = [] then
        let output := BinaryTerminalPhysicalCompleteSeedMeasured.run frame parsed hParsed rich seed
        ((output.1.1,wrap 32 2 [decoded.2,output.1.2]),output.2+8)
      else (((none,[]),wrap 24 2 [decoded.2]),4)


def runWithCharges (rich : Bool) (frame seed : List Bool) :
    (((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges :=
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  match hParsed : decoded.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 16 2 decoded.2
      ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
  | some parsed =>
      if parsed.2 = [] then
        let returned := BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges frame parsed hParsed rich seed
        let output := returned.1
        let emitted := BinaryWrapperEmission.two 32 2 decoded.2 output.1.2
        (((output.1.1,emitted.1),output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
      else
        let emitted := BinaryWrapperEmission.one 24 2 decoded.2
        ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)

def run (rich : Bool) (frame seed : List Bool) : ((Option (List Bool) × List Bool) × Trace) × ℕ :=
  (runWithCharges rich frame seed).1

theorem run_eq_reference (rich : Bool) (frame seed : List Bool) : run rich frame seed = runReference rich frame seed := by
  unfold run runWithCharges runReference
  dsimp only
  split
  · rename_i hNone
    simp only [hNone,BinaryWrapperEmission.one_trace]
  · rename_i parsed hSome
    split <;> simp only [BinaryTerminalPhysicalCompleteSeedMeasured.run,
      BinaryWrapperEmission.one_trace,BinaryWrapperEmission.two_trace]

theorem runWithCharges_compat (rich : Bool) (frame seed : List Bool) :
    (runWithCharges rich frame seed).1 = run rich frame seed := rfl

theorem run_data (rich : Bool) (frame seed : List Bool) :
    (run rich frame seed).1.1 = (BinaryTerminalPhysicalOutputRaw.run rich frame seed).1.1 := by
  rw [run_eq_reference]
  unfold runReference BinaryTerminalPhysicalOutputRaw.run
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i parsed hSome
      cases hNone.symm.trans hSome
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans hOther)
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail]
        exact (BinaryTerminalPhysicalCompleteSeedMeasured.run_data frame parsed hSome rich seed).symm
      · simp only [ite_eq_right hTail]

theorem uniform_work : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool),
    (run rich frame seed).2+BinaryBigEndian.littleValue (run rich frame seed).1.1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalCompleteSeedBounds.accepted_uniform_work
  refine ⟨C+8,d,?_⟩
  intro rich frame seed
  have hOne : 1 ≤ (frame.length+1)^d := Nat.one_le_pow _ _ (by omega)
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split
  · change 4+0 ≤ _
    nlinarith only [hOne]
  · rename_i parsed hParsed
    split
    · have h := hBound frame parsed hParsed rich seed
      change (BinaryTerminalPhysicalCompleteSeedMeasured.run frame parsed hParsed rich seed).2+8+
        BinaryBigEndian.littleValue (BinaryTerminalPhysicalCompleteSeedMeasured.run frame parsed hParsed rich seed).1.1.2 ≤ _
      nlinarith only [h,hOne]
    · change 4+0 ≤ _
      nlinarith only [hOne]

theorem uniform_usage : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool),
    usage (run rich frame seed).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSeed⟩ := BinaryTerminalPhysicalCompleteSeedBounds.accepted_uniform_usage
  obtain ⟨P,e,hParser⟩ := BinaryTerminalPhysicalRawPolynomial.uniform_envelope
  refine ⟨C+P+64,max d e,?_⟩
  intro rich frame seed
  have hX : 0 < frame.length+1 := by omega
  have hRead := (BinaryPRGPhysicalRawRequestLifetime.readWithTrace_usage frame).trans (hParser frame.length)
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have he := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  have hOne : 1 ≤ (frame.length+1)^(max d e) := Nat.one_le_pow _ _ (by omega)
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split
  · have hw := wrap_usage 16 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) ≤ _
    nlinarith only [hw,hRead,he,hOne]
  · rename_i parsed hParsed
    split
    · let output := BinaryTerminalPhysicalCompleteSeedMeasured.run frame parsed hParsed rich seed
      have h := hSeed frame parsed hParsed rich seed
      change usage output.1.2 ≤ _ at h
      have hw := wrap_usage 32 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,output.1.2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 32 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,output.1.2]) ≤ _
      nlinarith only [hw,hRead,h,hd,he,hOne]
    · have hw := wrap_usage 24 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) ≤ _
      nlinarith only [hw,hRead,he,hOne]

theorem all_prefixes : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool) (borrowed steps : ℕ),
    let B := C*(frame.length+1)^d
    retainedHeap (borrowed+frame.length+seed.length) (run rich frame seed).1.2 steps ≤
      borrowed+frame.length+seed.length+B ∧ framePeak ((run rich frame seed).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hBound⟩ := uniform_usage
  exact ⟨C,d,fun rich frame seed borrowed steps =>
    all_prefix _ _ (hBound rich frame seed) (borrowed+frame.length+seed.length) steps⟩

end Blotto.BinaryTerminalPhysicalCompleteRawMeasured
