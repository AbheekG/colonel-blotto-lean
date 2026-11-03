import Blotto.BinaryWrapperEmission
import Blotto.BinaryTerminalPhysicalCompleteFixedMeasured
import Blotto.BinaryTerminalPhysicalOutputFramed

/-! The complete measured cached terminal/global fallback now feeds actual
measured physical scaling and framing once. Previous exact bytes, absolute
cursor and encoded allowance are retained. The joined source-component ledger
includes reached terminal, fallback and output work; parser, projection/native
reference transport and complete machine realization remain separate. -/
namespace Blotto.BinaryTerminalPhysicalCompleteFramedMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryPRGHeapFixedProperties
set_option autoImplicit false
set_option maxHeartbeats 2500000

def runReference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    ((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) :=
  let drawn := BinaryTerminalPhysicalCompleteFixedMeasured.run frame parsed hParsed seed rich K outer scalar
  let output := BinaryPhysicalOutputMeasured.output parsed.1.2.logical.request.prepared.original.a
    header.bytes drawn.1.1.1.1.data.toList
  ((((output.1.1,drawn.1.1.1.2),drawn.1.1.2),
    wrapList parsed.1.1 32 (parsed.1.1+2) [drawn.1.2,output.1.2]),drawn.2+output.2+8)

def runWithCharges (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges :=
  let returned := BinaryTerminalPhysicalCompleteFixedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar
  let drawn := returned.1
  let output := BinaryPhysicalOutputMeasured.output parsed.1.2.logical.request.prepared.original.a
    header.bytes drawn.1.1.1.1.data.toList
  let emitted := BinaryWrapperEmission.listTwo parsed.1.1 32 (parsed.1.1+2) drawn.1.2 output.1.2
  (((((output.1.1,drawn.1.1.1.2),drawn.1.1.2),emitted.1),drawn.2+output.2+8),
    BinaryExecutionCharges.addWrapper returned.2 emitted.2)

def run (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    ((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) :=
  (runWithCharges frame parsed hParsed seed rich K outer scalar header).1

theorem run_eq_reference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    run frame parsed hParsed seed rich K outer scalar header = runReference frame parsed hParsed seed rich K outer scalar header := by
  unfold run runWithCharges runReference
  simp only [BinaryTerminalPhysicalCompleteFixedMeasured.run]
  simp only [BinaryWrapperEmission.listTwo_trace]

theorem run_data (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (run frame parsed hParsed seed rich K outer scalar header).1.1 =
      (BinaryTerminalPhysicalOutputFramed.run frame parsed hParsed seed rich K outer scalar header).1.1 := by
  simp only [run_eq_reference,runReference,BinaryTerminalPhysicalOutputFramed.run,BinaryTerminalPhysicalCompleteFixedMeasured.run_data]

theorem accepted_reference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (run frame parsed hParsed seed rich K outer scalar header).1.1.1 =
      (BinaryTerminalPhysicalFramedLifetime.runWithTrace frame parsed hParsed seed rich K outer scalar header).1 := by
  rw [run_data]
  have h := congrArg (fun result => result.1.1)
    (BinaryTerminalPhysicalOutputFramed.run_erases frame parsed hParsed seed rich K outer scalar header)
  exact h.trans (BinaryTerminalPhysicalAllowanceFramed.run_data frame parsed hParsed seed rich K outer scalar header)

theorem accepted_bytes (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (run frame parsed hParsed seed rich K outer scalar header).1.1.1.1 =
      BinaryStoredRowFrame.row (BinaryPRGWordControllerRequest.originalFixedSample seed parsed.1.2.logical.request rich K outer scalar) := by
  rw [accepted_reference]
  exact BinaryTerminalPhysicalFramedLifetime.accepted_bytes frame parsed hParsed seed rich K outer scalar header

theorem accepted_cursor (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (run frame parsed hParsed seed rich K outer scalar header).1.1.1.2 =
      (BinaryPRGWordControllerRequest.run seed parsed.1.2.logical.request rich K outer scalar).2 := by
  rw [accepted_reference]
  exact BinaryTerminalPhysicalFramedLifetime.accepted_cursor frame parsed hParsed seed rich K outer scalar header

theorem output_bounds (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    let drawn := BinaryTerminalPhysicalCompleteFixedMeasured.run frame parsed hParsed seed rich K outer scalar
    let output := BinaryPhysicalOutputMeasured.output parsed.1.2.logical.request.prepared.original.a header.bytes drawn.1.1.1.1.data.toList
    output.2 ≤ BinaryPhysicalOutputLifetime.bound parsed.1.1 (wordWidth parsed.1.2.logical.request K) header.bytes.length ∧
      usage output.1.2 ≤ BinaryPhysicalOutputLifetime.bound parsed.1.1 (wordWidth parsed.1.2.logical.request K) header.bytes.length := by
  let request := parsed.1.2.logical.request
  let drawn := BinaryTerminalPhysicalCompleteFixedMeasured.run frame parsed hParsed seed rich K outer scalar
  have hRow : drawn.1.1.1.1 = (BinaryPRGHeapFixedLifetime.runWithTrace seed request rich K outer scalar).1.1 :=
    (congrArg Prod.fst (BinaryTerminalPhysicalCompleteFixedMeasured.accepted_reference frame parsed hParsed seed rich K outer scalar)).trans
      (congrArg Prod.fst (BinaryTerminalPhysicalFixedLifetime.accepted_logical_output frame parsed hParsed seed rich K outer scalar))
  have hRows : ∀ word ∈ drawn.1.1.1.1.data.toList,BinaryRationalOpcode.Valid word ∧ width word ≤ wordWidth request K := by
    rw [hRow,← BinaryPRGPhysicalFramedLifetime.table_list]
    intro word hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact ⟨(BinaryPRGHeapFixedLifetime.runWithTrace_canonical seed request rich K outer scalar j).1,
      row_width seed request rich K outer scalar j⟩
  have hW := BinaryPhysicalOutputMeasured.output_bound request.prepared.original.a header.bytes drawn.1.1.1.1.data.toList
    request.valid.2.1.1.1 (wordWidth request K) (scale_width request K) hRows
  have hU := BinaryPhysicalOutputLifetime.output_usage request.prepared.original.a header.bytes drawn.1.1.1.1.data.toList
    request.valid.2.1.1.1 (wordWidth request K) (scale_width request K) hRows
  have hLength : drawn.1.1.1.1.data.toList.length = parsed.1.1 := by rw [Array.length_toList,drawn.1.1.1.1.size]
  rw [hLength] at hW hU
  dsimp only
  refine ⟨hW,?_⟩
  rw [BinaryPhysicalOutputMeasured.output_erases]
  exact hU

set_option backward.isDefEq.respectTransparency true in
theorem run_additive_bounds (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    let drawn := BinaryTerminalPhysicalCompleteFixedMeasured.run frame parsed hParsed seed rich K outer scalar
    let B := BinaryPhysicalOutputLifetime.bound parsed.1.1 (wordWidth parsed.1.2.logical.request K) header.bytes.length
    (run frame parsed hParsed seed rich K outer scalar header).2 ≤ drawn.2+B+8 ∧
      usage (run frame parsed hParsed seed rich K outer scalar header).1.2 ≤ usage drawn.1.2+B+2*(parsed.1.1+1)^2+64 := by
  let drawn := BinaryTerminalPhysicalCompleteFixedMeasured.run frame parsed hParsed seed rich K outer scalar
  let output := BinaryPhysicalOutputMeasured.output parsed.1.2.logical.request.prepared.original.a header.bytes drawn.1.1.1.1.data.toList
  have hOutput := output_bounds frame parsed hParsed seed rich K outer scalar header
  with_reducible change output.2 ≤ _ ∧ usage output.1.2 ≤ _ at hOutput
  have hw := wrapList_usage parsed.1.1 32 (parsed.1.1+2) [drawn.1.2,output.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  have hn : 2*parsed.1.1 ≤ 2*(parsed.1.1+1)^2 := by nlinarith
  rw [run_eq_reference]
  unfold runReference
  with_reducible
    change drawn.2+output.2+8 ≤ drawn.2+_+8 ∧
      usage (wrapList parsed.1.1 32 (parsed.1.1+2) [drawn.1.2,output.1.2]) ≤ usage drawn.1.2+_+2*(parsed.1.1+1)^2+64
  with_reducible exact ⟨by omega,by omega⟩

theorem output_envelope_polynomial : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (K headerLength : ℕ),
    BinaryPhysicalOutputLifetime.bound parsed.1.1 (wordWidth parsed.1.2.logical.request K) headerLength ≤
      C*(frame.length+K+headerLength+3)^d := by
  obtain ⟨C,d,hExtra⟩ := BinaryPRGPhysicalOutputPolynomial.extra_polynomial
  refine ⟨C*5^d,d,?_⟩
  intro frame parsed hParsed K headerLength
  let request := parsed.1.2.logical.request
  let s := request.source.originalInputWordWidth
  have hn := BinaryTerminalPhysicalRouteLifetime.accepted_dimension frame parsed hParsed
  have hs := BinaryTerminalPhysicalRouteLifetime.accepted_source_width frame parsed hParsed
  have hExtraBound := hExtra ⟨parsed.1.1,s,K,0,0,headerLength⟩
  change BinaryPRGPhysicalOutputPolynomial.extraEnvelope parsed.1.1 s K headerLength ≤
    C*(parsed.1.1+s+K+0+0+headerLength+1)^d at hExtraBound
  have hBase : BinaryPhysicalOutputLifetime.bound parsed.1.1 (wordWidth request K) headerLength ≤
      BinaryPRGPhysicalOutputPolynomial.extraEnvelope parsed.1.1 s K headerLength := by
    change BinaryPhysicalOutputLifetime.bound parsed.1.1
      (1+2*expressionHeightBudget (max (3+s) (K+2)) 75) headerLength ≤ _
    dsimp only [BinaryPRGPhysicalOutputPolynomial.extraEnvelope,BinaryPRGPhysicalOutputPolynomial.extraEnvelopeAt]
    omega
  have hSize : parsed.1.1+s+K+0+0+headerLength+1 ≤ 5*(frame.length+K+headerLength+3) := by
    dsimp only [s,request] at *
    omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hp
  exact (hBase.trans hExtraBound).trans (hp.trans_eq (by ring))

theorem accepted_uniform_joint : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1),
    (run frame parsed hParsed seed rich K outer scalar header).2+
      BinaryBigEndian.littleValue (run frame parsed hParsed seed rich K outer scalar header).1.1.2+
      usage (run frame parsed hParsed seed rich K outer scalar header).1.2 ≤
      C*(frame.length+K+seed.width+seed.cap.value+header.bytes.length+3)^d := by
  obtain ⟨C,d,hFixed⟩ := BinaryTerminalPhysicalCompleteFixedMeasured.accepted_uniform_joint
  obtain ⟨P,e,hOutput⟩ := output_envelope_polynomial
  refine ⟨C+2*P+2+72,max (max d e) 2,?_⟩
  intro frame parsed hParsed seed rich K outer scalar header
  let drawn := BinaryTerminalPhysicalCompleteFixedMeasured.run frame parsed hParsed seed rich K outer scalar
  let X := frame.length+K+seed.width+seed.cap.value+header.bytes.length+3
  let D := max (max d e) 2
  have hX : 0 < X := by dsimp only [X]; omega
  have hF := hFixed frame parsed hParsed seed rich K outer scalar
  change drawn.2+BinaryBigEndian.littleValue drawn.1.1.2+usage drawn.1.2 ≤ C*(frame.length+K+seed.width+seed.cap.value+3)^d at hF
  have hOut := hOutput frame parsed hParsed K header.bytes.length
  have hAdd := run_additive_bounds frame parsed hParsed seed rich K outer scalar header
  have hn := BinaryTerminalPhysicalRouteLifetime.accepted_dimension frame parsed hParsed
  have hd := (Nat.pow_le_pow_left (show frame.length+K+seed.width+seed.cap.value+3 ≤ X by dsimp only [X]; omega) d).trans
    (Nat.pow_le_pow_right hX ((Nat.le_max_left d e).trans (Nat.le_max_left _ 2)))
  have he := (Nat.pow_le_pow_left (show frame.length+K+header.bytes.length+3 ≤ X by dsimp only [X]; omega) e).trans
    (Nat.pow_le_pow_right hX ((Nat.le_max_right d e).trans (Nat.le_max_left _ 2)))
  have hN := (Nat.pow_le_pow_left (show parsed.1.1+1 ≤ X by dsimp only [X]; omega) 2).trans
    (Nat.pow_le_pow_right hX (Nat.le_max_right (max d e) 2))
  have hOne : 1 ≤ X^D := Nat.one_le_pow _ _ (by omega)
  have hc := Nat.mul_le_mul_left C hd
  have hp := Nat.mul_le_mul_left P he
  change (run frame parsed hParsed seed rich K outer scalar header).2+BinaryBigEndian.littleValue drawn.1.1.2+
    usage (run frame parsed hParsed seed rich K outer scalar header).1.2 ≤ (C+2*P+2+72)*X^D
  calc
    _ ≤ C*X^D+2*(P*X^D)+2*X^D+72*X^D := by
      change (run frame parsed hParsed seed rich K outer scalar header).2 ≤ drawn.2+_+8 ∧
        usage (run frame parsed hParsed seed rich K outer scalar header).1.2 ≤ usage drawn.1.2+_+2*(parsed.1.1+1)^2+64 at hAdd
      dsimp only [D] at *
      omega
    _ = _ := by ring

theorem accepted_uniform_bounds : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1),
    (run frame parsed hParsed seed rich K outer scalar header).2+
      BinaryBigEndian.littleValue (run frame parsed hParsed seed rich K outer scalar header).1.1.2 ≤
      C*(frame.length+K+seed.width+seed.cap.value+header.bytes.length+3)^d ∧
    usage (run frame parsed hParsed seed rich K outer scalar header).1.2 ≤
      C*(frame.length+K+seed.width+seed.cap.value+header.bytes.length+3)^d := by
  obtain ⟨C,d,h⟩ := accepted_uniform_joint
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich K outer scalar header
  have hb := h frame parsed hParsed seed rich K outer scalar header
  exact ⟨by omega,by omega⟩

theorem accepted_all_prefix : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) (borrowed steps : ℕ),
    retainedHeap borrowed (run frame parsed hParsed seed rich K outer scalar header).1.2 steps ≤
      borrowed+C*(frame.length+K+seed.width+seed.cap.value+header.bytes.length+3)^d ∧
    framePeak ((run frame parsed hParsed seed rich K outer scalar header).1.2.take steps) ≤
      C*(frame.length+K+seed.width+seed.cap.value+header.bytes.length+3)^d := by
  obtain ⟨C,d,h⟩ := accepted_uniform_bounds
  exact ⟨C,d,fun frame parsed hParsed seed rich K outer scalar header borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _ (h frame parsed hParsed seed rich K outer scalar header).2 borrowed steps⟩

theorem accepted_read (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) (suffix : List Bool) :
    BinaryRatListFrame.readRow ((run frame parsed hParsed seed rich K outer scalar header).1.1.1.1++suffix) =
      some (parsed.1.1,List.ofFn (fun j => value
        ((BinaryPRGWordControllerRequest.originalFixedSample seed parsed.1.2.logical.request rich K outer scalar).read j)),suffix) := by
  rw [accepted_reference]
  exact BinaryTerminalPhysicalFramedLifetime.accepted_read frame parsed hParsed seed rich K outer scalar header suffix

theorem runWithCharges_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (runWithCharges frame parsed hParsed seed rich K outer scalar header).1 = run frame parsed hParsed seed rich K outer scalar header := rfl

theorem runWithCharges_fields (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    let child := (BinaryTerminalPhysicalCompleteFixedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar).2
    let charges := (runWithCharges frame parsed hParsed seed rich K outer scalar header).2
    charges.primitive = child.primitive ∧ charges.coinSource = child.coinSource ∧
      charges.write = child.write ∧ charges.native = child.native := by
  unfold runWithCharges
  dsimp only
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem runWithCharges_step (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    let child := BinaryTerminalPhysicalCompleteFixedMeasured.runWithCharges frame parsed hParsed seed rich K outer scalar
    let produced := runWithCharges frame parsed hParsed seed rich K outer scalar header
    BinaryExecutionCharges.total produced.2 ≤ BinaryExecutionCharges.total child.2+
        5*produced.1.1.2.length+8 ∧
      child.1.1.2.length ≤ produced.1.1.2.length ∧ child.1.2 ≤ produced.1.2 := by
  unfold runWithCharges
  dsimp only
  simp only [BinaryExecutionCharges.total_addWrapper,BinaryWrapperEmission.listTwo_work,BinaryWrapperEmission.listTwo_length]
  omega

end Blotto.BinaryTerminalPhysicalCompleteFramedMeasured
