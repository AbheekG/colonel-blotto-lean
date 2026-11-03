import Blotto.BinaryWrapperEmission
import Blotto.BinaryTerminalPhysicalCompleteDrawMeasured
import Blotto.BinaryPRGGlobalFallbackMeasured
import Blotto.BinaryTerminalPhysicalAllowanceFramed

/-! The complete measured optional terminal joins the original global B-zero
fallback only on exhaustion. Exact old normalized rows, allowance and cursor
are retained, with reached fallback reference-control work now included. -/
namespace Blotto.BinaryTerminalPhysicalCompleteFixedMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryPRGResourceWork
set_option autoImplicit false
set_option maxHeartbeats 2500000

def runReference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ((((FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) :=
  let drawn := BinaryTerminalPhysicalCompleteDrawMeasured.run frame parsed hParsed seed rich K outer scalar
  match drawn.1.1.1.1 with
  | some row => ((((row,drawn.1.1.1.2),drawn.1.1.2),wrap 24 2 [drawn.1.2]),drawn.2+4)
  | none =>
      let fallback := BinaryPRGGlobalFallbackMeasured.prepare (resourceInput parsed.1.2.logical.request rich)
      ((((fallback.1.1,drawn.1.1.1.2),drawn.1.1.2),wrap 32 2 [drawn.1.2,fallback.1.2]),drawn.2+fallback.2+8)

def runWithCharges (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (((((FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges :=
  let returned := BinaryTerminalPhysicalCompleteDrawMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar
  let drawn := returned.1
  match drawn.1.1.1.1 with
  | some row =>
      let emitted := BinaryWrapperEmission.one 24 2 drawn.1.2
      (((((row,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+4),
        BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  | none =>
      let fallback := BinaryPRGGlobalFallbackMeasured.prepare (resourceInput parsed.1.2.logical.request rich)
      let emitted := BinaryWrapperEmission.two 32 2 drawn.1.2 fallback.1.2
      (((((fallback.1.1,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+fallback.2+8),
        BinaryExecutionCharges.addWrapper returned.2 emitted.2)

def run (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ((((FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) :=
  (runWithCharges frame parsed hParsed seed rich K outer scalar).1

theorem run_eq_reference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    run frame parsed hParsed seed rich K outer scalar = runReference frame parsed hParsed seed rich K outer scalar := by
  unfold run runWithCharges runReference
  simp only [BinaryTerminalPhysicalCompleteDrawMeasured.run]
  split <;> simp only [BinaryWrapperEmission.one_trace,BinaryWrapperEmission.two_trace]

theorem run_data (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (run frame parsed hParsed seed rich K outer scalar).1.1 =
      (BinaryTerminalPhysicalAllowanceFramed.fixed frame parsed hParsed seed rich K outer scalar).1.1 := by
  simp only [run_eq_reference,runReference,BinaryTerminalPhysicalAllowanceFramed.fixed,BinaryTerminalPhysicalCompleteDrawMeasured.run_data]
  cases (BinaryTerminalPhysicalAllowanceDraw.run frame parsed hParsed seed rich K outer scalar).1.1.1.1 with
  | none => exact Prod.ext (Prod.ext (BinaryPRGGlobalFallbackMeasured.prepare_data _) rfl) rfl
  | some row => rfl

theorem run_allowance (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (run frame parsed hParsed seed rich K outer scalar).1.1.2 =
      (BinaryTerminalPhysicalCompleteDrawMeasured.run frame parsed hParsed seed rich K outer scalar).1.1.2 := by
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split <;> rfl

theorem accepted_reference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (run frame parsed hParsed seed rich K outer scalar).1.1.1 =
      (BinaryTerminalPhysicalFixedLifetime.runWithTrace frame parsed hParsed seed rich K outer scalar).1 := by
  rw [run_data]
  exact BinaryTerminalPhysicalAllowanceFramed.fixed_data frame parsed hParsed seed rich K outer scalar

def fallbackPrice (n : ℕ) : ℕ := 68*(n+1)^2

theorem fallback_joined_bound (n : ℕ) : fallbackPrice n+BinaryPRGGlobalFallbackMeasured.envelope n ≤ 512*(n+1)^2 := by
  have h := BinaryPRGGlobalFallbackMeasured.envelope_quadratic n
  unfold fallbackPrice
  nlinarith

theorem run_additive_bounds (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (run frame parsed hParsed seed rich K outer scalar).2 ≤
      (BinaryTerminalPhysicalCompleteDrawMeasured.run frame parsed hParsed seed rich K outer scalar).2+
        fallbackPrice parsed.1.1+8 ∧
    usage (run frame parsed hParsed seed rich K outer scalar).1.2 ≤
      usage (BinaryTerminalPhysicalCompleteDrawMeasured.run frame parsed hParsed seed rich K outer scalar).1.2+
        BinaryPRGGlobalFallbackMeasured.envelope parsed.1.1+128 := by
  let drawn := BinaryTerminalPhysicalCompleteDrawMeasured.run frame parsed hParsed seed rich K outer scalar
  have hF := And.intro (BinaryPRGGlobalFallbackMeasured.prepare_work_quadratic (resourceInput parsed.1.2.logical.request rich))
    (BinaryPRGGlobalFallbackMeasured.prepare_usage (resourceInput parsed.1.2.logical.request rich))
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split
  · have hw := wrap_usage 24 2 [drawn.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change drawn.2+4 ≤ drawn.2+_+8 ∧ usage (wrap 24 2 [drawn.1.2]) ≤ usage drawn.1.2+_+128
    exact ⟨by omega,by omega⟩
  · let fallback := BinaryPRGGlobalFallbackMeasured.prepare (resourceInput parsed.1.2.logical.request rich)
    have hw := wrap_usage 32 2 [drawn.1.2,fallback.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change fallback.2 ≤ fallbackPrice parsed.1.1 ∧
      usage fallback.1.2 ≤ BinaryPRGGlobalFallbackMeasured.envelope parsed.1.1 at hF
    change drawn.2+fallback.2+8 ≤ drawn.2+_+8 ∧ usage (wrap 32 2 [drawn.1.2,fallback.1.2]) ≤ usage drawn.1.2+_+128
    exact ⟨by omega,by omega⟩

theorem accepted_uniform_joint : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K),
    (run frame parsed hParsed seed rich K outer scalar).2+
      BinaryBigEndian.littleValue (run frame parsed hParsed seed rich K outer scalar).1.1.2+
      usage (run frame parsed hParsed seed rich K outer scalar).1.2 ≤ C*(frame.length+K+seed.width+seed.cap.value+3)^d := by
  obtain ⟨W,d,hWork⟩ := BinaryTerminalPhysicalCompleteDrawMeasured.accepted_uniform_work
  obtain ⟨U,e,hUsage⟩ := BinaryTerminalPhysicalCompleteDrawMeasured.accepted_uniform_usage
  refine ⟨W+U+512+136,max (max d e) 2,?_⟩
  intro frame parsed hParsed seed rich K outer scalar
  let X := frame.length+K+seed.width+seed.cap.value+3
  let D := max (max d e) 2
  let drawn := BinaryTerminalPhysicalCompleteDrawMeasured.run frame parsed hParsed seed rich K outer scalar
  have hX : 0 < X := by dsimp only [X]; omega
  have hW := hWork frame parsed hParsed seed rich K outer scalar
  have hU := hUsage frame parsed hParsed seed rich K outer scalar
  change drawn.2+BinaryBigEndian.littleValue drawn.1.1.2 ≤ W*X^d at hW
  change usage drawn.1.2 ≤ U*X^e at hU
  have hAdd := run_additive_bounds frame parsed hParsed seed rich K outer scalar
  change (run frame parsed hParsed seed rich K outer scalar).2 ≤ drawn.2+_+8 ∧
    usage (run frame parsed hParsed seed rich K outer scalar).1.2 ≤ usage drawn.1.2+_+128 at hAdd
  have hFall := fallback_joined_bound parsed.1.1
  have hn := BinaryTerminalPhysicalRouteLifetime.accepted_dimension frame parsed hParsed
  have hF := (Nat.pow_le_pow_left (show parsed.1.1+1 ≤ X by dsimp only [X]; omega) 2).trans
    (Nat.pow_le_pow_right hX (Nat.le_max_right (max d e) 2))
  have hd := Nat.mul_le_mul_left W (Nat.pow_le_pow_right hX ((Nat.le_max_left d e).trans (Nat.le_max_left _ 2)))
  have he := Nat.mul_le_mul_left U (Nat.pow_le_pow_right hX ((Nat.le_max_right d e).trans (Nat.le_max_left _ 2)))
  have hf := Nat.mul_le_mul_left 512 hF
  have hOne : 1 ≤ X^D := Nat.one_le_pow _ _ (by omega)
  rw [run_allowance]
  change (run frame parsed hParsed seed rich K outer scalar).2+BinaryBigEndian.littleValue drawn.1.1.2+
    usage (run frame parsed hParsed seed rich K outer scalar).1.2 ≤ (W+U+512+136)*X^D
  calc
    _ ≤ W*X^D+U*X^D+512*X^D+136*X^D := by
      change _ ≤ W*X^D+U*X^D+512*X^D+136*X^D
      dsimp only [D] at *
      omega
    _ = _ := by ring

theorem accepted_uniform_bounds : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K),
    (run frame parsed hParsed seed rich K outer scalar).2+
      BinaryBigEndian.littleValue (run frame parsed hParsed seed rich K outer scalar).1.1.2 ≤ C*(frame.length+K+seed.width+seed.cap.value+3)^d ∧
    usage (run frame parsed hParsed seed rich K outer scalar).1.2 ≤ C*(frame.length+K+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,h⟩ := accepted_uniform_joint
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich K outer scalar
  have hb := h frame parsed hParsed seed rich K outer scalar
  exact ⟨by omega,by omega⟩

theorem accepted_canonical (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ∀ j,CanonicalWord ((run frame parsed hParsed seed rich K outer scalar).1.1.1.1.read j) := by
  rw [accepted_reference]
  exact BinaryTerminalPhysicalFixedLifetime.accepted_canonical frame parsed hParsed seed rich K outer scalar

theorem accepted_fullBudget (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    FullBudget (value (resourceInput parsed.1.2.logical.request rich).budget : ℝ)
      (fun j => (value ((run frame parsed hParsed seed rich K outer scalar).1.1.1.1.read j) : ℝ)) := by
  rw [accepted_reference]
  exact BinaryTerminalPhysicalFixedLifetime.accepted_fullBudget frame parsed hParsed seed rich K outer scalar

theorem accepted_all_prefix : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) (borrowed steps : ℕ),
    retainedHeap borrowed (run frame parsed hParsed seed rich K outer scalar).1.2 steps ≤ borrowed+C*(frame.length+K+seed.width+seed.cap.value+3)^d ∧
    framePeak ((run frame parsed hParsed seed rich K outer scalar).1.2.take steps) ≤ C*(frame.length+K+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,h⟩ := accepted_uniform_bounds
  exact ⟨C,d,fun frame parsed hParsed seed rich K outer scalar borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _ (h frame parsed hParsed seed rich K outer scalar).2 borrowed steps⟩

theorem runWithCharges_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (runWithCharges frame parsed hParsed seed rich K outer scalar).1 = run frame parsed hParsed seed rich K outer scalar := rfl

theorem runWithCharges_fields (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    let child := (BinaryTerminalPhysicalCompleteDrawMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar).2
    let charges := (runWithCharges frame parsed hParsed seed rich K outer scalar).2
    charges.primitive = child.primitive ∧ charges.coinSource = child.coinSource ∧
      charges.write = child.write ∧ charges.native = child.native := by
  unfold runWithCharges
  dsimp only
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem runWithCharges_step (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    let child := BinaryTerminalPhysicalCompleteDrawMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar
    let produced := runWithCharges frame parsed hParsed seed rich K outer scalar
    BinaryExecutionCharges.total produced.2 ≤ BinaryExecutionCharges.total child.2+
        5*produced.1.1.2.length+8 ∧
      child.1.1.2.length ≤ produced.1.1.2.length ∧ child.1.2 ≤ produced.1.2 := by
  unfold runWithCharges
  dsimp only
  split <;> simp only [BinaryExecutionCharges.total_addWrapper,BinaryWrapperEmission.one_work,
    BinaryWrapperEmission.two_work,BinaryWrapperEmission.one_length,BinaryWrapperEmission.two_length] <;> omega

end Blotto.BinaryTerminalPhysicalCompleteFixedMeasured
