import Blotto.BinaryPRGHeapThreeNativeLifetimeBound

/-! Uniform source-cell/activation polynomials for a complete native physical
resource call: original-array preparation, the actual loop and materialization.
Every retained prefix is bounded; original arrays and seed remain borrowed. -/

namespace Blotto.BinaryPRGHeapNativeLifetimePolynomial
open BinaryPRGHeapResourcePolynomial BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGHeapTraceUsage BinaryPRGHeapNativeLifetime
set_option maxHeartbeats 2000000

macro "unfold_native_lifetime_envelope" : tactic => `(tactic|
  simp only [BinaryPRGHeapNativeLifetimeBound.envelope,
    BinaryPRGHeapThreeNativeLifetimeBound.envelope,
    BinaryPRGHeapInitialLifetimeBound.envelope,BinaryPRGHeapInitialLifetimeBound.buildEnvelope,
    BinaryPRGHeapEnumerationLifetime.envelope,BinaryPRGHeapEnumerationLifetime.localEnvelope,
    BinaryPRGHeapMaterializationLifetime.envelope,BinaryPRGHeapMaterializationLifetime.rowEnvelope,
    BinaryPRGHeapMaterializationLifetime.collectEnvelope,BinaryPRGWordStoreHeapMachine.countBound,
    BinaryPRGHeapResourceInputCost.heapBound,
    BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope,BinaryPRGHeapLifetimePolynomial.threeLoopEnvelope,
    BinaryPRGHeapResourceThreeSource.inputWidth,BinaryPRGHeapResourceThreeSource.initialCells,
    BinaryPRGHeapResourceThreeSource.heapCap,BinaryPRGHeapResourceInputBounds.initialHeapBound,
    BinaryPRGWordControllerBooleanResourceLoopWork.widthBound,
    BinaryPRGWordControllerBooleanResourceThreeWork.widthBound,
    BinaryThreeResourceHeight.resourceHeight,BinaryThreeResourceHeight.coinWidth])

theorem array_envelope_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => BinaryPRGHeapNativeLifetimeBound.envelope p.count p.wordWidth p.denominator p.seedWidth p.seedCap) := by
  unfold_native_lifetime_envelope
  unfold_heap_lifetime_envelope
  resource_polynomial

theorem three_envelope_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => BinaryPRGHeapThreeNativeLifetimeBound.envelope p.wordWidth p.seedWidth p.seedCap) := by
  unfold_native_lifetime_envelope
  unfold_heap_lifetime_envelope
  resource_polynomial

theorem uniform_original_array_native_usage : ∃ C d : ℕ,
    ∀ {n : ℕ} (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
      (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) (W D : ℕ),
    1 ≤ W → 0 < D → (∀ j,width (capacity.read j) ≤ W) → (∀ j,width (resource.read j) ≤ W) →
    (∀ j,OnRationalLattice D (value (capacity.read j))) →
    (∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1) →
    (∀ j,OnRationalLattice D (value (resource.read j))) →
    (∀ j,0 ≤ value (resource.read j) ∧ value (resource.read j) ≤ value (capacity.read j)) →
    ∀ (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
    usage (nativeWithTrace seed capacity resource hC hR pc hp).2 ≤
      C * (n + W + binaryWordWidth D + seed.width + seed.cap.value + 1)^d := by
  rcases array_envelope_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n seed capacity resource hC hR W D hW hD hCapacity hResource hLattice hBox hRL hRB pc hp
  exact (BinaryPRGHeapNativeLifetimeBound.nativeWithTrace_input_usage seed capacity resource hC hR W D hW hD
    hCapacity hResource hLattice hBox hRL hRB pc hp).trans (hBound ⟨n,W,D,seed.width,seed.cap.value⟩)

theorem uniform_original_three_native_usage : ∃ C d : ℕ,∀ (s : ℕ),2 ≤ s →
    ∀ (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable 3 SignedWord)
      (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)),
    (∀ j,RationalHeight (value (capacity.read j)) s) → (∀ j,RationalHeight (value (resource.read j)) s) →
    ∀ (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
    usage (nativeWithTrace seed capacity resource hC hR pc hp).2 ≤
      C * (s + seed.width + seed.cap.value + 2)^d := by
  rcases three_envelope_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro s hs seed capacity resource hC hR hCapacity hResource pc hp
  have h := (BinaryPRGHeapThreeNativeLifetimeBound.nativeWithTrace_input_usage s hs seed capacity resource
    hC hR hCapacity hResource pc hp).trans (hBound ⟨0,s,0,seed.width,seed.cap.value⟩)
  have hSize : inputSize ⟨0,s,0,seed.width,seed.cap.value⟩ + 1 = s + seed.width + seed.cap.value + 2 := by
    simp [inputSize,binaryWordWidth]
    omega
  simpa only [hSize] using h

end Blotto.BinaryPRGHeapNativeLifetimePolynomial
