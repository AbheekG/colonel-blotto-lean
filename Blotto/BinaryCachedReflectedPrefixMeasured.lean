import Blotto.BinaryReflectedPrefixMeasuredPolynomial
import Blotto.BinaryCachedFourGluingMeasured

/-! Actual successful physical-cache mixed-three fields instantiate the
measured reflected preparation/resource/terminal-input prefix. Accepted frame
and incoming seed parameters bound the joined source work and every prefix.
Nested profile factories, the reflected draw and native realization remain. -/
namespace Blotto.BinaryCachedReflectedPrefixMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryCachedFourBranchWork BinaryCachedFourParameterWork BinaryCachedThreeDescriptorWork
open BinaryCachedGroupInputHeight BinaryGroupInputs BinaryGroupSamplers
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryTerminalPhysicalAllowanceCache
open BinaryCachedFourGluingMeasured (fromCached fromCached_height)
set_option autoImplicit false
set_option maxHeartbeats 700000

def run (checked : Checked) (store : BinarySeedLookupTree.Store) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryReflectedTerminalPrefixMeasured.Result store checked.ordered :=
  BinaryReflectedTerminalPrefixMeasured.run store checked.ordered checked.ordered_canonical pc hp

theorem run_data (checked : Checked) (store : BinarySeedLookupTree.Store)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run checked store pc hp).1.1 =
      (BinaryReflectedTerminalPrefixLifetime.runWithTrace store checked.ordered checked.ordered_canonical pc hp).1 :=
  BinaryReflectedTerminalPrefixMeasured.run_data store checked.ordered checked.ordered_canonical pc hp

theorem run_bounds (checked : Checked) (hGuard : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights checked.input s)
    (store : BinarySeedLookupTree.Store) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run checked store pc hp).2 ≤ BinaryReflectedPrefixMeasuredPolynomial.jointEnvelope s store.width store.cap.value ∧
      usage (run checked store pc hp).1.2 ≤ BinaryReflectedPrefixMeasuredPolynomial.jointEnvelope s store.width store.cap.value := by
  obtain ⟨source,hR⟩ := checked.admissible
  have hRef := BinaryFourSpecSampler.orderedInput_refines (mixedFour checked.input) source.fourInput
    (mixedFour_canonical checked.input checked.canonical) (mixedFour_refines checked.input source hR)
  have hCase : source.fourInput.input.w < (1-source.fourInput.input.p)*source.fourInput.input.ell :=
    lt_of_not_ge (fun h => hGuard ((BinaryFourParentCompiler.gluingCase_iff checked.ordered source.fourInput.input
      checked.ordered_canonical hRef).mpr h))
  have h := BinaryReflectedTerminalPrefixMeasured.run_bounds store checked.ordered source.fourInput.input
    checked.ordered_canonical hRef hCase s hs (source_four_heights checked.input source hR s hH).input pc hp
  exact ⟨h.1.trans (BinaryReflectedPrefixMeasuredPolynomial.work_le_joint _ _ _),
    h.2.trans (BinaryReflectedPrefixMeasuredPolynomial.usage_le_joint _ _ _)⟩

theorem accepted_envelope : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (i cap : ℕ),
    BinaryReflectedPrefixMeasuredPolynomial.jointEnvelope (inputHeight parsed.1.2.logical.request) i cap ≤
      C*(frame.length+i+cap+2)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryReflectedPrefixMeasuredPolynomial.joint_polynomial
  refine ⟨C*34^d,d,?_⟩
  intro frame parsed hParsed i cap
  have hs := BinaryTerminalPhysicalRouteLifetime.accepted_source_width frame parsed hParsed
  have hSize : inputHeight parsed.1.2.logical.request+i+cap+2 ≤ 34*(frame.length+i+cap+2) := by
    unfold inputHeight; omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hp
  exact (hBound (inputHeight parsed.1.2.logical.request) i cap).trans (hp.trans_eq (by ring))

theorem accepted_cached_bounds : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (result : BinaryPRGHeapCertifiedPrefixLifetime.CachedResult parsed.1.2.logical.request rich)
    (hFound : (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed store rich).1.1.1.1 = some result)
    (hCount : result.2.count = 3) (selected : Fin _) (hPivot : result.2.pivot = some selected)
    (hGuard : ¬BinaryFourParentCompiler.gluingCase
      (fromCached store parsed.1.2.logical.request rich result
        (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound) hCount selected hPivot).ordered = true)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    let checked := fromCached store parsed.1.2.logical.request rich result
      (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound) hCount selected hPivot
    (run checked store pc hp).2 ≤ C*(frame.length+store.width+store.cap.value+2)^d ∧
      usage (run checked store pc hp).1.2 ≤ C*(frame.length+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := accepted_envelope
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed store rich result hFound hCount selected hPivot hGuard pc hp
  have hSuccess := BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound
  let checked := fromCached store parsed.1.2.logical.request rich result hSuccess hCount selected hPivot
  have hHeight := fromCached_height store parsed.1.2.logical.request rich result hSuccess hCount selected hPivot
  have hs : 2 ≤ inputHeight parsed.1.2.logical.request := by unfold inputHeight; omega
  have h := run_bounds checked hGuard _ hs hHeight store pc hp
  have hb := hBound frame parsed hParsed store.width store.cap.value
  have hResult : (run checked store pc hp).2 ≤ C*(frame.length+store.width+store.cap.value+2)^d ∧
      usage (run checked store pc hp).1.2 ≤ C*(frame.length+store.width+store.cap.value+2)^d := ⟨h.1.trans hb,h.2.trans hb⟩
  with_reducible exact hResult

end Blotto.BinaryCachedReflectedPrefixMeasured
