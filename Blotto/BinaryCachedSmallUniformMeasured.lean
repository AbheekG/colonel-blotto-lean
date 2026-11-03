import Blotto.BinarySmallUniformMeasuredPolynomial
import Blotto.BinaryCachedFourGluingMeasured

/-! Actual successful physical-cache mixed-three fields instantiate the
measured small-uniform root handoff companion. Original accepted-frame/seed
parameters derive work and retained-source bounds. The reflected branch,
complete small-root dispatch and native model realization remain separate. -/
namespace Blotto.BinaryCachedSmallUniformMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryCachedFourBranchWork BinaryCachedFourParameterWork BinaryCachedThreeDescriptorWork
open BinaryCachedGroupInputHeight BinaryGroupInputs BinaryGroupSamplers
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryTerminalPhysicalAllowanceCache
open BinaryCachedFourGluingMeasured (fromCached fromCached_height)
set_option autoImplicit false
set_option maxHeartbeats 500000

def run (checked : Checked) (hGuard : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (store : BinarySeedLookupTree.Store) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerFour.Result store × Trace) × ℕ :=
  BinaryFourSmallUniformCoinHandoffMeasured.run store checked.ordered checked.ordered_canonical
    (BinaryFourAdmissibility.small_guard checked.ordered checked.ordered_canonical checked.ordered_admissible hGuard)
    K scalar pc hp

theorem run_data (checked : Checked) (hGuard : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (store : BinarySeedLookupTree.Store) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run checked hGuard store K scalar pc hp).1.1 =
      (BinaryFourSmallUniformCoinHandoffLifetime.runWithTrace store checked.ordered checked.ordered_canonical
        (BinaryFourAdmissibility.small_guard checked.ordered checked.ordered_canonical checked.ordered_admissible hGuard)
        K scalar pc hp).1 :=
  BinaryFourSmallUniformCoinHandoffMeasured.run_data store checked.ordered checked.ordered_canonical _ K scalar pc hp

theorem old_true_branch (checked : Checked) (hGuard : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (store : BinarySeedLookupTree.Store) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (hTrue : (BinaryFourSmallCoinMeasured.sample store checked.ordered pc hp).1.1.1 = some true) :
    (run checked hGuard store K scalar pc hp).1.1 = BinaryPRGWordControllerFour.run store checked.ordered
      checked.ordered_canonical checked.ordered_admissible K outer scalar pc hp := by
  have h := BinaryFourSmallUniformCoinHandoffMeasured.old_true_branch store checked.ordered checked.ordered_canonical
    (BinaryFourAdmissibility.small_guard checked.ordered checked.ordered_canonical checked.ordered_admissible hGuard)
    K outer scalar pc hp hTrue
  unfold BinaryPRGWordControllerFour.run
  simp only [hGuard,dite_false]
  exact h

theorem run_bounds (checked : Checked) (hGuard : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (s : ℕ) (hs : 3 ≤ s) (hH : MixedHeights checked.input s)
    (store : BinarySeedLookupTree.Store) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run checked hGuard store K scalar pc hp).2 ≤ BinarySmallUniformMeasuredPolynomial.jointEnvelope s K store.width store.cap.value ∧
      usage (run checked hGuard store K scalar pc hp).1.2 ≤ BinarySmallUniformMeasuredPolynomial.jointEnvelope s K store.width store.cap.value := by
  obtain ⟨source,hR⟩ := checked.admissible
  have hRef := BinaryFourSpecSampler.orderedInput_refines (mixedFour checked.input) source.fourInput
    (mixedFour_canonical checked.input checked.canonical) (mixedFour_refines checked.input source hR)
  have hCase : source.fourInput.input.w < (1-source.fourInput.input.p)*source.fourInput.input.ell :=
    lt_of_not_ge (fun h => hGuard ((BinaryFourParentCompiler.gluingCase_iff checked.ordered source.fourInput.input
      checked.ordered_canonical hRef).mpr h))
  have h := BinaryFourSmallUniformCoinHandoffMeasured.run_bounds store checked.ordered source.fourInput.input
    checked.ordered_canonical hRef hCase
    (BinaryFourAdmissibility.small_guard checked.ordered checked.ordered_canonical checked.ordered_admissible hGuard) s hs (source_four_heights checked.input source hR s hH).input K scalar pc hp
  exact ⟨h.1.trans (BinarySmallUniformMeasuredPolynomial.handoff_work_le_joint _ _ _ _ _ (Nat.sub_le _ _)),
    h.2.trans (BinarySmallUniformMeasuredPolynomial.handoff_usage_le_joint _ _ _ _ _ (Nat.sub_le _ _))⟩

theorem accepted_envelope : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (K i cap : ℕ),
    BinarySmallUniformMeasuredPolynomial.jointEnvelope (inputHeight parsed.1.2.logical.request) K i cap ≤
      C*(frame.length+K+i+cap+2)^d := by
  obtain ⟨C,d,hBound⟩ := BinarySmallUniformMeasuredPolynomial.joint_polynomial
  refine ⟨C*34^d,d,?_⟩
  intro frame parsed hParsed K i cap
  have hs := BinaryTerminalPhysicalRouteLifetime.accepted_source_width frame parsed hParsed
  have hSize : inputHeight parsed.1.2.logical.request+K+i+cap+2 ≤ 34*(frame.length+K+i+cap+2) := by
    unfold inputHeight
    omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hp
  exact (hBound (inputHeight parsed.1.2.logical.request) K i cap).trans (hp.trans_eq (by ring))

theorem accepted_cached_bounds : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (result : BinaryPRGHeapCertifiedPrefixLifetime.CachedResult parsed.1.2.logical.request rich)
    (hFound : (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed store rich).1.1.1.1 = some result)
    (hCount : result.2.count = 3) (selected : Fin _) (hPivot : result.2.pivot = some selected)
    (hGuard : ¬BinaryFourParentCompiler.gluingCase
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
    ⟨h.1.trans hb,h.2.trans hb⟩
  with_reducible exact hResult

end Blotto.BinaryCachedSmallUniformMeasured
