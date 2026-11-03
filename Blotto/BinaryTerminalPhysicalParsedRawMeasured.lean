import Blotto.BinaryPRGPhysicalRawRequestMeasured
import Blotto.BinaryTerminalPhysicalCompleteRawMeasured

/-! Actual complete measured physical parsing feeds the measured supplied-
seed validator/terminal/fallback/output path once. Full preceding data/trace
are exact; the source charge now includes actual parsing on every branch.
Native addressing/reference/ownership/observer/allocator joins remain open. -/
namespace Blotto.BinaryTerminalPhysicalParsedRawMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3000000

def runReference (rich : Bool) (frame seed : List Bool) : ((Option (List Bool) × List Bool) × Trace) × ℕ :=
  let decoded := BinaryPRGPhysicalRawRequestMeasured.read frame
  match hParsed : decoded.1.1 with
  | none => (((none,[]),wrap 16 2 [decoded.1.2]),decoded.2+4)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hParsed
        let output := BinaryTerminalPhysicalCompleteSeedMeasured.run frame parsed hOriginal rich seed
        ((output.1.1,wrap 32 2 [decoded.1.2,output.1.2]),decoded.2+output.2+8)
      else (((none,[]),wrap 24 2 [decoded.1.2]),decoded.2+4)


def runWithCharges (rich : Bool) (frame seed : List Bool) :
    (((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges :=
  let decoded := BinaryPRGPhysicalRawRequestMeasured.read frame
  match hParsed : decoded.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
      ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hParsed
        let returned := BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges frame parsed hOriginal rich seed
        let output := returned.1
        let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
        (((output.1.1,emitted.1),decoded.2+output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
      else
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)

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

theorem run_erases (rich : Bool) (frame seed : List Bool) :
    (run rich frame seed).1 = (BinaryTerminalPhysicalCompleteRawMeasured.run rich frame seed).1 := by
  rw [run_eq_reference,BinaryTerminalPhysicalCompleteRawMeasured.run_eq_reference]
  unfold runReference BinaryTerminalPhysicalCompleteRawMeasured.runReference
  dsimp only
  split
  · rename_i hNone
    have hOld := (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hNone
    split
    · simp only [BinaryPRGPhysicalRawRequestMeasured.read_erases]
    · rename_i parsed hSome
      cases hOld.symm.trans hSome
  · rename_i parsed hSome
    have hOld := (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hSome
    symm
    split
    · rename_i hNone
      cases hOld.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hOld.symm.trans hOther)
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,BinaryPRGPhysicalRawRequestMeasured.read_erases]
      · simp only [ite_eq_right hTail,BinaryPRGPhysicalRawRequestMeasured.read_erases]

theorem run_charge (rich : Bool) (frame seed : List Bool) :
    (run rich frame seed).2 = (BinaryPRGPhysicalRawRequestMeasured.read frame).2+
      (BinaryTerminalPhysicalCompleteRawMeasured.run rich frame seed).2 := by
  rw [run_eq_reference,BinaryTerminalPhysicalCompleteRawMeasured.run_eq_reference]
  unfold runReference BinaryTerminalPhysicalCompleteRawMeasured.runReference
  dsimp only
  split
  · rename_i hNone
    have hOld := (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hNone
    split
    · rfl
    · rename_i parsed hSome
      cases hOld.symm.trans hSome
  · rename_i parsed hSome
    have hOld := (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hSome
    symm
    split
    · rename_i hNone
      cases hOld.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hOld.symm.trans hOther)
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail]; omega
      · simp only [ite_eq_right hTail]

theorem run_data (rich : Bool) (frame seed : List Bool) :
    (run rich frame seed).1.1 = (BinaryTerminalPhysicalOutputRaw.run rich frame seed).1.1 := by
  rw [run_erases]
  exact BinaryTerminalPhysicalCompleteRawMeasured.run_data rich frame seed

theorem uniform_joint : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool),
    (run rich frame seed).2+BinaryBigEndian.littleValue (run rich frame seed).1.1.2+
      usage (run rich frame seed).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hWork⟩ := BinaryTerminalPhysicalCompleteRawMeasured.uniform_work
  obtain ⟨U,e,hUsage⟩ := BinaryTerminalPhysicalCompleteRawMeasured.uniform_usage
  obtain ⟨P,f,hParser⟩ := BinaryPRGPhysicalRawRequestMeasured.uniform_joint
  let D := max (max d e) f
  refine ⟨C+U+P,D,?_⟩
  intro rich frame seed
  have hW := hWork rich frame seed
  have hU := hUsage rich frame seed
  have hP := hParser frame
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (show d ≤ D by dsimp [D]; omega))
  have he := Nat.mul_le_mul_left U (Nat.pow_le_pow_right hX (show e ≤ D by dsimp [D]; omega))
  have hf := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (show f ≤ D by dsimp [D]; omega))
  rw [run_charge,run_erases]
  nlinarith only [hW,hU,hP,hd,he,hf]

theorem all_prefixes : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool) (borrowed steps : ℕ),
    let B := C*(frame.length+1)^d
    retainedHeap (borrowed+frame.length+seed.length) (run rich frame seed).1.2 steps ≤
      borrowed+frame.length+seed.length+B ∧ framePeak ((run rich frame seed).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hBound⟩ := uniform_joint
  refine ⟨C,d,?_⟩
  intro rich frame seed borrowed steps
  have hu : usage (run rich frame seed).1.2 ≤ C*(frame.length+1)^d := by have h := hBound rich frame seed; omega
  exact all_prefix _ _ hu (borrowed+frame.length+seed.length) steps

end Blotto.BinaryTerminalPhysicalParsedRawMeasured
