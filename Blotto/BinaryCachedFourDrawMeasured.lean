import Blotto.BinaryFourMeasuredPolynomial
import Blotto.BinaryCachedFourGluingMeasured

/-! Original mixed-three fields of the actual successful physical cache feed
complete measured sorting, guard/root dispatch and inverse row restoration.
Accepted frame length and seed parameters derive source work and usage without
a branch assumption. Fixed fallback and whole-sampler/native joins remain. -/
namespace Blotto.BinaryCachedFourDrawMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryCachedFourBranchWork BinaryCachedFourParameterWork BinaryCachedThreeDescriptorWork
open BinaryCachedGroupInputHeight BinaryGroupInputs BinaryGroupSamplers
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryTerminalPhysicalAllowanceCache
open BinaryCachedFourGluingMeasured (fromCached fromCached_height)
set_option autoImplicit false
set_option maxHeartbeats 700000

def run (checked : Checked) (store : BinarySeedLookupTree.Store) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :=
  BinaryFourRestoredMeasured.run store (mixedFour checked.input) (mixedFour_canonical checked.input checked.canonical)
    (mixedFour_admissible checked.input checked.canonical checked.admissible) K outer scalar pc hp

theorem run_data (checked : Checked) (store : BinarySeedLookupTree.Store) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run checked store K outer scalar pc hp).1.1 = BinaryPRGWordControllerFour.restoredRun store
      (mixedFour checked.input) (mixedFour_canonical checked.input checked.canonical)
      (mixedFour_admissible checked.input checked.canonical checked.admissible) K outer scalar pc hp := by
  unfold run
  apply BinaryFourRestoredMeasured.run_erasure

theorem run_bounds (checked : Checked) (s : ℕ) (hs : 3 ≤ s) (hH : MixedHeights checked.input s)
    (store : BinarySeedLookupTree.Store) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run checked store K outer scalar pc hp).2 ≤ BinaryFourMeasuredPolynomial.jointEnvelope s K store.width store.cap.value ∧
      usage (run checked store K outer scalar pc hp).1.2 ≤ BinaryFourMeasuredPolynomial.jointEnvelope s K store.width store.cap.value := by
  obtain ⟨source,hR⟩ := checked.admissible
  have h := BinaryFourRestoredMeasured.run_bounds store (mixedFour checked.input) source.fourInput
    (mixedFour_canonical checked.input checked.canonical) (mixedFour_refines checked.input source hR)
    (mixedFour_admissible checked.input checked.canonical checked.admissible) s hs
    (source_four_heights checked.input source hR s hH) K outer scalar pc hp
  exact ⟨h.1.trans (BinaryFourMeasuredPolynomial.restored_work_le_joint _ _ _ _),
    h.2.trans (BinaryFourMeasuredPolynomial.restored_usage_le_joint _ _ _ _)⟩

theorem accepted_envelope : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (K i cap : ℕ),
    BinaryFourMeasuredPolynomial.jointEnvelope (inputHeight parsed.1.2.logical.request) K i cap ≤ C*(frame.length+K+i+cap+2)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryFourMeasuredPolynomial.joint_polynomial
  refine ⟨C*34^d,d,?_⟩
  intro frame parsed hParsed K i cap
  have hs := BinaryTerminalPhysicalRouteLifetime.accepted_source_width frame parsed hParsed
  have hSize : inputHeight parsed.1.2.logical.request+K+i+cap+2 ≤ 34*(frame.length+K+i+cap+2) := by unfold inputHeight; omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hp
  exact (hBound (inputHeight parsed.1.2.logical.request) K i cap).trans (hp.trans_eq (by ring))

theorem accepted_cached_bounds : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (result : BinaryPRGHeapCertifiedPrefixLifetime.CachedResult parsed.1.2.logical.request rich)
    (hFound : (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed store rich).1.1.1.1 = some result)
    (hCount : result.2.count = 3) (selected : Fin _) (hPivot : result.2.pivot = some selected)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value),
    let checked := fromCached store parsed.1.2.logical.request rich result
      (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound) hCount selected hPivot
    (run checked store K outer scalar pc hp).2 ≤ C*(frame.length+K+store.width+store.cap.value+2)^d ∧
      usage (run checked store K outer scalar pc hp).1.2 ≤ C*(frame.length+K+store.width+store.cap.value+2)^d := by
  obtain ⟨C,d,hBound⟩ := accepted_envelope
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed store rich result hFound hCount selected hPivot K outer scalar pc hp
  have hSuccess := BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed store rich result hFound
  let checked := fromCached store parsed.1.2.logical.request rich result hSuccess hCount selected hPivot
  have hHeight := fromCached_height store parsed.1.2.logical.request rich result hSuccess hCount selected hPivot
  have hs : 3 ≤ inputHeight parsed.1.2.logical.request := by unfold inputHeight; omega
  have h := run_bounds checked _ hs hHeight store K outer scalar pc hp
  have hb := hBound frame parsed hParsed K store.width store.cap.value
  have hResult : (run checked store K outer scalar pc hp).2 ≤ C*(frame.length+K+store.width+store.cap.value+2)^d ∧
      usage (run checked store K outer scalar pc hp).1.2 ≤ C*(frame.length+K+store.width+store.cap.value+2)^d := ⟨h.1.trans hb,h.2.trans hb⟩
  with_reducible exact hResult

end Blotto.BinaryCachedFourDrawMeasured
