import Blotto.BinaryGroupFactoryMeasured
import Blotto.BinaryPRGHeapResourcePolynomial
import Blotto.BinaryTerminalPhysicalAllowanceDraw

/-! Original canonical cached fields, not intermediate descriptors or prices,
derive uniform polynomial factory source work and retained-source bounds.
Accepted raw-frame length controls the height parameter. This prices only the
factory stages; categorical/point and native model obligations remain separate. -/

namespace Blotto.BinaryGroupFactoryMeasuredPolynomial
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork BinaryCachedGroupInputHeight
open BinaryPRGHeapResourcePolynomial BinaryTerminalPhysicalAllowanceCache
open BinaryPRGResourceWork BinaryPRGTerminalWork
set_option autoImplicit false
set_option maxHeartbeats 3500000

def jointEnvelope (s : ℕ) : ℕ :=
  BinaryGroupFactoryMeasured.workEnvelope s+4+BinaryGroupFactoryMeasured.envelope s+20

macro "unfold_measured_group_factory" : tactic => `(tactic|
  simp only [jointEnvelope,BinaryGroupFactoryMeasured.workEnvelope,BinaryGroupFactoryMeasured.envelope,
    BinaryThreeFactoryMeasured.workEnvelope,BinaryThreeFactoryMeasured.orderedWork,
    BinaryThreeFactoryMeasured.envelope,BinaryThreeFactoryMeasured.orderedEnvelope,
    BinaryThreeGeometryMeasured.regimeWork,BinaryThreeGeometryMeasured.geometryWork,
    BinaryThreeGeometryMeasured.geometryEnvelope,BinaryQuadraticThreeFactoryMeasured.workEnvelope,
    BinaryQuadraticThreeFactoryMeasured.expressionWork,BinaryQuadraticThreeFactoryMeasured.envelope,
    BinaryQuadraticThreeFactoryMeasured.expressionCells,BinaryQuadraticThreeFactoryMeasured.expressionFrames,
    BinaryThreeGeometryLifetime.regimeEnvelope,BinaryThreeGeometryLifetime.comparisonEnvelope,
    BinaryQuadraticThreeFactoryLifetime.expressionBound,BinaryQuadraticThreeFactoryLifetime.expressionFrames,
    BinaryQuadraticSyntaxMeasured.workEnvelope,BinaryQuadraticSyntaxLifetime.bound,BinaryQuadraticSyntaxLifetime.frames,
    BinaryQuadraticExpression.uniformPrice,BinaryQuadraticExpressionLifetime.stepBound,
    BinaryQuadraticExpressionLifetime.frameBound,BinaryQuadraticLifetime.opcodeBound,
    BinaryQuadraticLifetime.opcodeFrames,BinaryLifetimeArrayMeasured.storageReserve])

theorem diagonal_polynomial : NaturalPolynomialEnvelope inputSize (fun p => jointEnvelope p.wordWidth) := by
  unfold_measured_group_factory
  resource_polynomial

theorem joint_mono {s t : ℕ} (h : s ≤ t) : jointEnvelope s ≤ jointEnvelope t := by
  unfold_measured_group_factory
  unfold expressionHeightBudget
  gcongr

theorem joint_polynomial : ∃ C d : ℕ, ∀ s,jointEnvelope s ≤ C*(s+2)^d := by
  obtain ⟨C,d,hBound⟩ := diagonal_polynomial
  refine ⟨C,d,?_⟩
  intro s
  have h := hBound ⟨0,s,0,0,0⟩
  have hSize : inputSize ⟨0,s,0,0,0⟩+1 = s+2 := by simp [inputSize,binaryWordWidth]
  rw [hSize] at h
  exact h

theorem uniform_source_bounds : ∃ C d : ℕ, ∀ {m : ℕ} (input : UniformInput m)
    (hC : input.Canonical) (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3)
    (s : ℕ),3 ≤ s → UniformHeights input s →
    (BinaryGroupFactoryMeasured.uniformPrepared input hC hAd hm).2 ≤ C*(s+2)^d ∧
      usage (BinaryGroupFactoryMeasured.uniformPrepared input hC hAd hm).1.2 ≤ C*(s+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro m input hC hAd hm s hs hH
  have h := BinaryGroupFactoryMeasured.uniformPrepared_bounds input hC hAd hm s hs hH
  have hb := hBound s
  unfold jointEnvelope at hb
  exact ⟨h.1.trans (by omega),h.2.trans (by omega)⟩

theorem mixed_source_bounds : ∃ C d : ℕ, ∀ (input : MixedInput 2)
    (hC : input.Canonical) (hAd : MixedAdmissible input) (s : ℕ),3 ≤ s → MixedHeights input s →
    (BinaryGroupFactoryMeasured.mixedTwoPrepared input hC hAd).2 ≤ C*(s+2)^d ∧
      usage (BinaryGroupFactoryMeasured.mixedTwoPrepared input hC hAd).1.2 ≤ C*(s+2)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C,d,?_⟩
  intro input hC hAd s hs hH
  have h := BinaryGroupFactoryMeasured.mixedTwoPrepared_bounds input hC hAd s hs hH
  have hb := hBound s
  unfold jointEnvelope at hb
  exact ⟨h.1.trans (by omega),h.2.trans (by omega)⟩

theorem accepted_envelope : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed),
    jointEnvelope (inputHeight parsed.1.2.logical.request) ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := joint_polynomial
  refine ⟨C*34^d,d,?_⟩
  intro frame parsed hParsed
  have hs := BinaryTerminalPhysicalRouteLifetime.accepted_source_width frame parsed hParsed
  have hSize : inputHeight parsed.1.2.logical.request+2 ≤ 34*(frame.length+1) := by
    unfold inputHeight
    omega
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hp
  exact (hBound (inputHeight parsed.1.2.logical.request)).trans (hp.trans_eq (by ring))

theorem accepted_cached_uniform : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (result : BinaryPRGHeapCertifiedPrefixLifetime.CachedResult parsed.1.2.logical.request rich)
    (hFound : (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).1.1.1.1 = some result)
    (hm : result.2.count = 2 ∨ result.2.count = 3),
    (BinaryGroupFactoryMeasured.uniformFactory result.2.uniform hm).2 ≤ C*(frame.length+1)^d ∧
      usage (BinaryGroupFactoryMeasured.uniformFactory result.2.uniform hm).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := accepted_envelope
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich result hFound hm
  have hSuccess := BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result hFound
  have hHeight := BinaryPRGHeapCertifiedPrefixProperties.uniform_height seed parsed.1.2.logical.request rich result hSuccess
  have hs : 3 ≤ inputHeight parsed.1.2.logical.request := by unfold inputHeight; omega
  have h := BinaryGroupFactoryMeasured.uniformFactory_bounds result.2.uniform
    (result.2.uniform_canonical (terminal_canonical parsed.1.2.logical.request rich result.1)) hm
    (inputHeight parsed.1.2.logical.request) hs hHeight
  have hb := hBound frame parsed hParsed
  unfold jointEnvelope at hb
  exact ⟨h.1.trans (by omega),h.2.trans (by omega)⟩

end Blotto.BinaryGroupFactoryMeasuredPolynomial
