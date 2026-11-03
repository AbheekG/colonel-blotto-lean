import Blotto.BinaryWrapperEmission
import Blotto.BinaryWordTerminalCompletePolynomial
import Blotto.BinaryTerminalPhysicalAllowanceDraw

/-! The actual certified Boolean-allowance cache and its returned cursor feed
complete measured terminal dispatch, factories, draws and route emission. The
encoded prefix allowance is preserved and reached terminal source work is
added to the natural charge. Native-machine and global fallback joins remain. -/
namespace Blotto.BinaryTerminalPhysicalCompleteDrawMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedGroupInputHeight
set_option autoImplicit false
set_option maxHeartbeats 2500000

def runReference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (((BinaryPRGWordControllerTerminal.Result seed parsed.1.1 × List Bool) × Trace) × ℕ) :=
  let request := parsed.1.2.logical.request
  let observed := BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich
  match hs : observed.1.1.1.1 with
  | none => ((((none,observed.1.1.1.2),observed.1.1.2),wrap 16 2 [observed.1.2]),observed.2+4)
  | some result =>
      let drawn := BinaryWordTerminalCompleteMeasured.run seed result.2
        (terminal_canonical request rich result.1)
        (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result
          (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result hs))
        K outer scalar observed.1.1.1.2 (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich)
      (((drawn.1.1,observed.1.1.2),wrap 32 2 [observed.1.2,drawn.1.2]),observed.2+drawn.2+8)

def runWithCharges (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ((((BinaryPRGWordControllerTerminal.Result seed parsed.1.1 × List Bool) × Trace) × ℕ)) × BinaryExecutionCharges.Charges :=
  let request := parsed.1.2.logical.request
  let returned := BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich
  let observed := returned.1
  match hs : observed.1.1.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 16 2 observed.1.2
      (((((none,observed.1.1.1.2),observed.1.1.2),emitted.1),observed.2+4),
        BinaryExecutionCharges.addWrapper returned.2 emitted.2)
  | some result =>
      let drawn := BinaryWordTerminalCompleteMeasured.run seed result.2
        (terminal_canonical request rich result.1)
        (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result
          (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result hs))
        K outer scalar observed.1.1.1.2 (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich)
      let emitted := BinaryWrapperEmission.two 32 2 observed.1.2 drawn.1.2
      ((((drawn.1.1,observed.1.1.2),emitted.1),observed.2+drawn.2+8),
        BinaryExecutionCharges.addWrapper returned.2 emitted.2)

def run (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (((BinaryPRGWordControllerTerminal.Result seed parsed.1.1 × List Bool) × Trace) × ℕ) :=
  (runWithCharges frame parsed hParsed seed rich K outer scalar).1

theorem run_eq_reference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    run frame parsed hParsed seed rich K outer scalar = runReference frame parsed hParsed seed rich K outer scalar := by
  unfold run runWithCharges runReference
  simp only [BinaryTerminalPhysicalAllowanceCertified.run]
  split <;> simp only [BinaryWrapperEmission.one_trace,BinaryWrapperEmission.two_trace]

theorem run_data (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (run frame parsed hParsed seed rich K outer scalar).1.1 =
      (BinaryTerminalPhysicalAllowanceDraw.run frame parsed hParsed seed rich K outer scalar).1.1 := by
  rw [run_eq_reference]
  unfold runReference BinaryTerminalPhysicalAllowanceDraw.run
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i result hSome
      cases hNone.symm.trans hSome
  · rename_i result hSome
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans hOther)
      subst other
      exact Prod.ext (BinaryWordTerminalCompleteMeasured.run_data seed result.2 _ _ K outer scalar _ _) rfl

theorem run_allowance (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (run frame parsed hParsed seed rich K outer scalar).1.1.2 =
      (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).1.1.2 := by
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split <;> rfl

theorem accepted_reference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (run frame parsed hParsed seed rich K outer scalar).1.1.1 =
      BinaryPRGWordControllerRequest.run seed parsed.1.2.logical.request rich K outer scalar := by
  rw [run_data]
  exact BinaryTerminalPhysicalAllowanceDraw.accepted_reference frame parsed hParsed seed rich K outer scalar

theorem run_additive_bounds (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (run frame parsed hParsed seed rich K outer scalar).2 ≤
      (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).2+
        BinaryWordTerminalCompletePolynomial.jointEnvelope parsed.1.1 (inputHeight parsed.1.2.logical.request) K seed.width seed.cap.value+8 ∧
    usage (run frame parsed hParsed seed rich K outer scalar).1.2 ≤
      usage (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).1.2+
        BinaryWordTerminalCompletePolynomial.jointEnvelope parsed.1.1 (inputHeight parsed.1.2.logical.request) K seed.width seed.cap.value+64 := by
  let request := parsed.1.2.logical.request
  let observed := BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich
  let J := BinaryWordTerminalCompletePolynomial.jointEnvelope parsed.1.1 (inputHeight request) K seed.width seed.cap.value
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split
  · have hw := wrap_usage 16 2 [observed.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change observed.2+4 ≤ observed.2+J+8 ∧ usage (wrap 16 2 [observed.1.2]) ≤ usage observed.1.2+J+64
    exact ⟨by omega,by omega⟩
  · rename_i result hSome
    have hLogical := BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result hSome
    have hs : 3 ≤ inputHeight request := by unfold inputHeight; omega
    let drawn := BinaryWordTerminalCompleteMeasured.run seed result.2 (terminal_canonical request rich result.1)
      (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result hLogical)
      K outer scalar observed.1.1.1.2 (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich)
    have hDraw := BinaryWordTerminalCompleteMeasured.run_bounds seed result.2
      (terminal_canonical request rich result.1)
      (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result hLogical)
      (inputHeight request) hs
      (BinaryPRGHeapCertifiedPrefixProperties.uniform_height seed request rich result hLogical)
      (BinaryPRGHeapCertifiedPrefixProperties.mixed_height seed request rich result hLogical)
      (BinaryPRGHeapCertifiedPrefixProperties.route_height seed request rich result hLogical)
      K outer scalar observed.1.1.1.2 (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich)
    have hW := hDraw.1.trans (BinaryWordTerminalCompletePolynomial.work_le_joint _ _ _ _ _)
    have hU := hDraw.2.trans (BinaryWordTerminalCompletePolynomial.usage_le_joint _ _ _ _ _)
    change drawn.2 ≤ J at hW
    change usage drawn.1.2 ≤ J at hU
    have hw := wrap_usage 32 2 [observed.1.2,drawn.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change observed.2+drawn.2+8 ≤ observed.2+J+8 ∧
      usage (wrap 32 2 [observed.1.2,drawn.1.2]) ≤ usage observed.1.2+J+64
    exact ⟨by omega,by omega⟩

theorem accepted_continuation_envelope : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (K i cap : ℕ),
    BinaryWordTerminalCompletePolynomial.jointEnvelope parsed.1.1 (inputHeight parsed.1.2.logical.request) K i cap ≤
      C*(frame.length+K+i+cap+3)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryWordTerminalCompletePolynomial.joint_polynomial
  refine ⟨C*40^d,d,?_⟩
  intro frame parsed hParsed K i cap
  have hn := BinaryTerminalPhysicalRouteLifetime.accepted_dimension frame parsed hParsed
  have hs := BinaryTerminalPhysicalRouteLifetime.accepted_source_width frame parsed hParsed
  have hSize : parsed.1.1+inputHeight parsed.1.2.logical.request+K+i+cap+2 ≤ 40*(frame.length+K+i+cap+3) := by
    unfold inputHeight
    omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hp
  exact (hBound parsed.1.1 (inputHeight parsed.1.2.logical.request) K i cap).trans (hp.trans_eq (by ring))

theorem accepted_uniform_work : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K),
    (run frame parsed hParsed seed rich K outer scalar).2+
      BinaryBigEndian.littleValue (run frame parsed hParsed seed rich K outer scalar).1.1.2 ≤
      C*(frame.length+K+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,hPrefix⟩ := BinaryTerminalPhysicalAllowanceCertified.accepted_uniform_carried_work
  obtain ⟨P,e,hTerminal⟩ := accepted_continuation_envelope
  refine ⟨C+P+8,max d e,?_⟩
  intro frame parsed hParsed seed rich K outer scalar
  let X := frame.length+K+seed.width+seed.cap.value+3
  have hX : 0 < X := by dsimp only [X]; omega
  have hPrefixBound := hPrefix frame parsed hParsed seed rich
  have hTermBound := hTerminal frame parsed hParsed K seed.width seed.cap.value
  have hAdd := (run_additive_bounds frame parsed hParsed seed rich K outer scalar).1
  rw [run_allowance]
  have hd := (Nat.pow_le_pow_left (show frame.length+seed.width+seed.cap.value+3 ≤ X by dsimp only [X]; omega) d).trans
    (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have he := Nat.pow_le_pow_right hX (Nat.le_max_right d e)
  have hOne : 1 ≤ X^(max d e) := Nat.one_le_pow _ _ (by omega)
  change _ ≤ (C+P+8)*X^(max d e)
  have hC := Nat.mul_le_mul_left C hd
  have hP := Nat.mul_le_mul_left P he
  dsimp only [X] at hC hP hOne ⊢
  rw [Nat.add_mul,Nat.add_mul]
  omega

theorem accepted_uniform_usage : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K),
    usage (run frame parsed hParsed seed rich K outer scalar).1.2 ≤ C*(frame.length+K+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,hPrefix⟩ := BinaryTerminalPhysicalAllowanceCertified.accepted_uniform_usage
  obtain ⟨P,e,hTerminal⟩ := accepted_continuation_envelope
  refine ⟨C+P+64,max d e,?_⟩
  intro frame parsed hParsed seed rich K outer scalar
  let X := frame.length+K+seed.width+seed.cap.value+3
  have hX : 0 < X := by dsimp only [X]; omega
  have hPrefixBound := hPrefix frame parsed hParsed seed rich
  have hTermBound := hTerminal frame parsed hParsed K seed.width seed.cap.value
  have hAdd := (run_additive_bounds frame parsed hParsed seed rich K outer scalar).2
  have hd := (Nat.pow_le_pow_left (show frame.length+seed.width+seed.cap.value+3 ≤ X by dsimp only [X]; omega) d).trans
    (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have he := Nat.pow_le_pow_right hX (Nat.le_max_right d e)
  have hOne : 1 ≤ X^(max d e) := Nat.one_le_pow _ _ (by omega)
  change _ ≤ (C+P+64)*X^(max d e)
  have hC := Nat.mul_le_mul_left C hd
  have hP := Nat.mul_le_mul_left P he
  dsimp only [X] at hC hP hOne ⊢
  rw [Nat.add_mul,Nat.add_mul]
  omega

theorem accepted_uniform_all_prefix : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) (borrowed steps : ℕ),
    retainedHeap borrowed (run frame parsed hParsed seed rich K outer scalar).1.2 steps ≤
      borrowed+C*(frame.length+K+seed.width+seed.cap.value+3)^d ∧
    framePeak ((run frame parsed hParsed seed rich K outer scalar).1.2.take steps) ≤ C*(frame.length+K+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,hBound⟩ := accepted_uniform_usage
  exact ⟨C,d,fun frame parsed hParsed seed rich K outer scalar borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound frame parsed hParsed seed rich K outer scalar) borrowed steps⟩

theorem runWithCharges_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (runWithCharges frame parsed hParsed seed rich K outer scalar).1 = run frame parsed hParsed seed rich K outer scalar := rfl

theorem runWithCharges_fields (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    let child := (BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich).2
    let charges := (runWithCharges frame parsed hParsed seed rich K outer scalar).2
    charges.primitive = child.primitive ∧ charges.coinSource = child.coinSource ∧
      charges.write = child.write ∧ charges.native = child.native := by
  unfold runWithCharges
  dsimp only
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem runWithCharges_step (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    let child := BinaryTerminalPhysicalAllowanceCertified.runWithCharges frame parsed hParsed seed rich
    let produced := runWithCharges frame parsed hParsed seed rich K outer scalar
    BinaryExecutionCharges.total produced.2 ≤ BinaryExecutionCharges.total child.2+
        5*produced.1.1.2.length+8 ∧
      child.1.1.2.length ≤ produced.1.1.2.length ∧ child.1.2 ≤ produced.1.2 := by
  unfold runWithCharges
  dsimp only
  split <;> simp only [BinaryExecutionCharges.total_addWrapper,BinaryWrapperEmission.one_work,
    BinaryWrapperEmission.two_work,BinaryWrapperEmission.one_length,BinaryWrapperEmission.two_length] <;> omega

end Blotto.BinaryTerminalPhysicalCompleteDrawMeasured
