import Blotto.BinaryFreshGenerationPlan
import Blotto.BinaryGenerationExecutionCharges
import Blotto.BinaryPRGPhysicalRawRequestMeasured
import Blotto.BinaryTerminalPhysicalCompleteGeneratedBounds

/-! Actual complete measured physical parsing precedes entropy generation
and the complete measured validator/terminal/global-fallback/output path.
The full old bytes/state/allowance/trace survive. Parser work is included on
all branches, and rejection still occurs before entropy. Native joins remain. -/
namespace Blotto.BinaryTerminalPhysicalParsedGeneratedMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def runReference {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (((Option (List Bool) × S) × List Bool) × Trace) × ℕ :=
  let decoded := BinaryPRGPhysicalRawRequestMeasured.read frame
  match hParsed : decoded.1.1 with
  | none => ((((none,state),[]),wrap 24 2 [decoded.1.2]),decoded.2+4)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hParsed
        let generated := BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state
        let output := BinaryTerminalPhysicalCompleteSeedMeasured.run frame parsed hOriginal rich generated.1.1.1
        ((((output.1.1.1,generated.1.1.2),output.1.1.2),
          wrap 48 2 [decoded.1.2,generated.1.2,output.1.2]),decoded.2+output.2+generated.2+8)
      else ((((none,state),[]),wrap 32 2 [decoded.1.2]),decoded.2+4)

def runWithChargesReference {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    ((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges :=
  let decoded := BinaryPRGPhysicalRawRequestMeasured.read frame
  match hParsed : decoded.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
      (((((none,state),[]),emitted.1),decoded.2+4),
        BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hParsed
        let generated := BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state
        let returned := BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges
          frame parsed hOriginal rich generated.1.1.1
        let output := returned.1
        let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
        (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),decoded.2+output.2+generated.2+8),
          BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
      else
        let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
        (((((none,state),[]),emitted.1),decoded.2+4),
          BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)

def runWithGeneration {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    ((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges :=
  let decoded := BinaryPRGPhysicalRawRequestMeasured.read frame
  match hParsed : decoded.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
      (((((none,state),[]),emitted.1),decoded.2+4),
        BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let returned := BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges
          frame parsed hOriginal rich generated.1.1.1
        let output := returned.1
        let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
        (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),decoded.2+output.2+generated.2+8),
          BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
      else
        let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
        (((((none,state),[]),emitted.1),decoded.2+4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)

def runWithCharges {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    ((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges :=
  let returned := runWithGeneration next rich frame state
  (returned.1,returned.2.sampler)

theorem runWithCharges_eq_reference {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    runWithCharges next rich frame state = runWithChargesReference next rich frame state := by
  unfold runWithCharges runWithGeneration runWithChargesReference
  dsimp only
  split
  · rfl
  · split
    · simp only [BinaryFreshGenerationPlan.generateWithEmission_compat]
      rfl
    · rfl


def run {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : (((Option (List Bool) × S) × List Bool) × Trace) × ℕ :=
  (runWithCharges next rich frame state).1

theorem run_eq_reference {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : run next rich frame state = runReference next rich frame state := by
  unfold run
  rw [runWithCharges_eq_reference]
  unfold runWithChargesReference runReference
  dsimp only
  split
  · simp only [BinaryWrapperEmission.one_trace]
  · split <;> simp only [BinaryTerminalPhysicalCompleteSeedMeasured.run,
      BinaryWrapperEmission.one_trace,BinarySeedWrapperEmission.three_trace]

theorem runWithCharges_compat {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (runWithCharges next rich frame state).1 = run next rich frame state := rfl

theorem run_erases {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (run next rich frame state).1 = (BinaryTerminalPhysicalCompleteGeneratedMeasured.run next rich frame state).1 := by
  rw [run_eq_reference,BinaryTerminalPhysicalCompleteGeneratedMeasured.run_eq_reference]
  unfold runReference BinaryTerminalPhysicalCompleteGeneratedMeasured.runReference
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

theorem run_charge {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (run next rich frame state).2 = (BinaryPRGPhysicalRawRequestMeasured.read frame).2+
      (BinaryTerminalPhysicalCompleteGeneratedMeasured.run next rich frame state).2 := by
  rw [run_eq_reference,BinaryTerminalPhysicalCompleteGeneratedMeasured.run_eq_reference]
  unfold runReference BinaryTerminalPhysicalCompleteGeneratedMeasured.runReference
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

theorem reject_none {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S)
    (hRead : (BinaryPRGPhysicalRawRequestMeasured.read frame).1.1 = none) :
    run next rich frame state =
      ((((none,state),[]),wrap 24 2 [(BinaryPRGPhysicalRawRequestMeasured.read frame).1.2]),
        (BinaryPRGPhysicalRawRequestMeasured.read frame).2+4) := by
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split
  · rfl
  · rename_i parsed hSome
    rw [hRead] at hSome
    cases hSome

theorem reject_tail {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S)
    (parsed : Parsed) (hRead : (BinaryPRGPhysicalRawRequestMeasured.read frame).1.1 = some parsed)
    (hTail : parsed.2 ≠ []) :
    run next rich frame state =
      ((((none,state),[]),wrap 32 2 [(BinaryPRGPhysicalRawRequestMeasured.read frame).1.2]),
        (BinaryPRGPhysicalRawRequestMeasured.read frame).2+4) := by
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i other hOther
    have he := Option.some.inj (hOther.symm.trans hRead)
    subst other
    simp only [ite_eq_right hTail]

theorem accepted_charge {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S)
    (parsed : Parsed) (hRead : (BinaryPRGPhysicalRawRequestMeasured.read frame).1.1 = some parsed)
    (hTail : parsed.2 = []) :
    let hOriginal := (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hRead
    let generated := BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state
    let output := BinaryTerminalPhysicalCompleteSeedMeasured.run frame parsed hOriginal rich generated.1.1.1
    (run next rich frame state).2+BinaryBigEndian.littleValue (run next rich frame state).1.1.2 =
      (BinaryPRGPhysicalRawRequestMeasured.read frame).2+output.2+
        BinaryBigEndian.littleValue output.1.1.2+generated.2+8 := by
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i other hOther
    have he := Option.some.inj (hOther.symm.trans hRead)
    subst other
    simp only [ite_eq_left hTail]
    omega

theorem run_counted {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (calls : ℕ) :
    (run (FreshBitSeedLifetime.countedFresh next) rich frame (state,calls)).1.1.1 =
      ((run next rich frame state).1.1.1.1,((run next rich frame state).1.1.1.2,
        calls+BinaryPRGFreshRawLifetime.drawCount frame)) := by
  simp only [run_erases,BinaryTerminalPhysicalCompleteGeneratedMeasured.run_counted]

def pairReference {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ :=
  let rich := run next true frame state
  let poor := run next false frame rich.1.1.1.2
  let data := ((rich.1.1.1.1,poor.1.1.1.1),poor.1.1.1.2)
  (((data,(rich.1.1.2,poor.1.1.2)),wrap 64 2 [rich.1.2,poor.1.2]),rich.2+poor.2+8)

def pairWithChargesReference {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinarySamplerExecutionCharges.Charges :=
  let rich := runWithCharges next true frame state
  let poor := runWithCharges next false frame rich.1.1.1.1.2
  let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
  let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
  ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
    BinarySamplerExecutionCharges.addWrapper (BinarySamplerExecutionCharges.add rich.2 poor.2) emitted.2)

def pairWithGeneration {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges :=
  let rich := runWithGeneration next true frame state
  let poor := runWithGeneration next false frame rich.1.1.1.1.2
  let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
  let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
  ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
    BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)

def pairWithCharges {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinarySamplerExecutionCharges.Charges :=
  let returned := pairWithGeneration next frame state
  (returned.1,returned.2.sampler)

theorem pairWithCharges_eq_reference {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    pairWithCharges next frame state = pairWithChargesReference next frame state := by
  unfold pairWithCharges pairWithGeneration pairWithChargesReference runWithCharges
  rfl


def pair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ :=
  (pairWithCharges next frame state).1

theorem pair_eq_reference {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    pair next frame state = pairReference next frame state := by
  unfold pair
  rw [pairWithCharges_eq_reference]
  simp only [pairWithChargesReference,pairReference,run,BinaryWrapperEmission.two_trace]

theorem pairWithCharges_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pairWithCharges next frame state).1 = pair next frame state := rfl

theorem pair_erases {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair next frame state).1 = (BinaryTerminalPhysicalCompleteGeneratedMeasured.pair next frame state).1 := by
  simp only [pair_eq_reference,pairReference,BinaryTerminalPhysicalCompleteGeneratedMeasured.pair_eq_reference,
    BinaryTerminalPhysicalCompleteGeneratedMeasured.pairReference,run_erases]

theorem pair_charge {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair next frame state).2 = 2*(BinaryPRGPhysicalRawRequestMeasured.read frame).2+
      (BinaryTerminalPhysicalCompleteGeneratedMeasured.pair next frame state).2 := by
  simp only [pair_eq_reference,pairReference,BinaryTerminalPhysicalCompleteGeneratedMeasured.pair_eq_reference,
    BinaryTerminalPhysicalCompleteGeneratedMeasured.pairReference,run_charge,run_erases]
  omega

theorem pair_counted {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) (calls : ℕ) :
    (pair (FreshBitSeedLifetime.countedFresh next) frame (state,calls)).1.1.1 =
      ((pair next frame state).1.1.1.1,((pair next frame state).1.1.1.2,
        calls+2*BinaryPRGFreshRawLifetime.drawCount frame)) := by
  simp only [pair_erases,BinaryTerminalPhysicalCompleteGeneratedMeasured.pair_counted]

end Blotto.BinaryTerminalPhysicalParsedGeneratedMeasured
