import Blotto.BinaryFourGluingFixedMeasuredPolynomial
import Blotto.BinaryCachedFourGluingMeasured
import Blotto.BinaryCachedFourBranchWork

/-! Actual successful physical-cache original mixed-three fields instantiate
complete measured fixed gluing, including deterministic lower fallback. Accepted
frame length and seed parameters bound source work and every retained prefix.
The reflected fixed branch and whole-sampler/native joins remain separate. -/
namespace Blotto.BinaryCachedFourGluingFixedMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryCachedFourBranchWork BinaryCachedFourParameterWork BinaryCachedThreeDescriptorWork
open BinaryCachedGroupInputHeight BinaryGroupInputs BinaryGroupSamplers
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryTerminalPhysicalAllowanceCache
open BinaryCachedFourGluingMeasured (fromCached fromCached_height)
set_option autoImplicit false
set_option maxHeartbeats 500000

def run (checked : Checked) (hGuard : BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (store : BinarySeedLookupTree.Store) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ((FixedArrayTable 4 SignedWord × FixedBinaryWord store.width) × Trace) × ℕ :=
  BinaryFourGluingFixedMeasured.run store checked.ordered checked.ordered_canonical
    (BinaryFourGluingDrawLifetime.sampler_admissible checked.ordered checked.ordered_canonical
      checked.ordered_admissible hGuard) K scalar pc hp

theorem run_data (checked : Checked) (hGuard : BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (store : BinarySeedLookupTree.Store) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run checked hGuard store K scalar pc hp).1.1 =
      (BinaryFourGluingFixedLifetime.runWithTrace store checked.ordered checked.ordered_canonical
        (BinaryFourGluingDrawLifetime.sampler_admissible checked.ordered checked.ordered_canonical checked.ordered_admissible hGuard) K scalar pc hp).1 := by
  unfold run
  apply BinaryFourGluingFixedMeasured.run_data

theorem run_bounds (checked : Checked) (hGuard : BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (s : ℕ) (hs : 3 ≤ s) (hH : MixedHeights checked.input s)
    (store : BinarySeedLookupTree.Store) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run checked hGuard store K scalar pc hp).2 ≤ BinaryFourGluingFixedMeasured.workEnvelope s K store.width store.cap.value ∧
      usage (run checked hGuard store K scalar pc hp).1.2 ≤ BinaryFourGluingFixedMeasured.envelope s K store.width store.cap.value := by
  obtain ⟨source,hR⟩ := checked.admissible
  have hRef := BinaryFourSpecSampler.orderedInput_refines (mixedFour checked.input) source.fourInput
    (mixedFour_canonical checked.input checked.canonical) (mixedFour_refines checked.input source hR)
  have hCase := (BinaryFourParentCompiler.gluingCase_iff checked.ordered source.fourInput.input
    checked.ordered_canonical hRef).mp hGuard
  exact BinaryFourGluingFixedMeasured.run_bounds store checked.ordered source.fourInput.input checked.ordered_canonical
    hRef hCase _ s hs (source_four_heights checked.input source hR s hH).input K scalar pc hp

theorem accepted_envelope : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (K i cap : ℕ),
    BinaryFourGluingFixedMeasuredPolynomial.jointEnvelope (inputHeight parsed.1.2.logical.request) K i cap ≤
      C*(frame.length+K+i+cap+2)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryFourGluingFixedMeasuredPolynomial.joint_polynomial
  refine ⟨C*34^d,d,?_⟩
  intro frame parsed hParsed K i cap
  have hs := BinaryTerminalPhysicalRouteLifetime.accepted_source_width frame parsed hParsed
  have hSize : inputHeight parsed.1.2.logical.request+K+i+cap+2 ≤ 34*(frame.length+K+i+cap+2) := by
    unfold inputHeight
    omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hp
  exact (hBound (inputHeight parsed.1.2.logical.request) K i cap).trans (hp.trans_eq (by ring))

theorem accepted_cached_bounds : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (result : BinaryPRGHeapCertifiedPrefixLifetime.CachedResult parsed.1.2.logical.request rich)
    (hFound : (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed store rich).1.1.1.1 = some result)
    (hCount : result.2.count = 3) (selected : Fin _) (hPivot : result.2.pivot = some selected)
    (hGuard : BinaryFourParentCompiler.gluingCase
      (fromCached store parsed.1.2.logical.request rich result
        (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound) hCount selected hPivot).ordered = true)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    let checked := fromCached store parsed.1.2.logical.request rich result
      (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound) hCount selected hPivot
    (run checked hGuard store K scalar pc hp).2 ≤ C*(frame.length+K+store.width+store.cap.value+2)^d ∧
      usage (run checked hGuard store K scalar pc hp).1.2 ≤ C*(frame.length+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := accepted_envelope
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed store rich result hFound hCount selected hPivot hGuard K scalar pc hp
  have hSuccess := BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound
  let checked := fromCached store parsed.1.2.logical.request rich result hSuccess hCount selected hPivot
  have hHeight := fromCached_height store parsed.1.2.logical.request rich result hSuccess hCount selected hPivot
  have hs : 3 ≤ inputHeight parsed.1.2.logical.request := by unfold inputHeight; omega
  have h := run_bounds checked hGuard _ hs hHeight store K scalar pc hp
  have hb := hBound frame parsed hParsed K store.width store.cap.value
  have hResult : (run checked hGuard store K scalar pc hp).2 ≤ C*(frame.length+K+store.width+store.cap.value+2)^d ∧
      usage (run checked hGuard store K scalar pc hp).1.2 ≤ C*(frame.length+K+store.width+store.cap.value+2)^d :=
    ⟨h.1.trans ((BinaryFourGluingFixedMeasuredPolynomial.work_le_joint _ _ _ _).trans hb),
      h.2.trans ((BinaryFourGluingFixedMeasuredPolynomial.usage_le_joint _ _ _ _).trans hb)⟩
  -- Match the shared record without expanding its measured arithmetic.
  with_reducible exact hResult

end Blotto.BinaryCachedFourGluingFixedMeasured
