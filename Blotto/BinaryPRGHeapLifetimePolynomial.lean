import Blotto.BinaryPRGHeapLoopSourceLifetime
import Blotto.BinaryPRGHeapResourcePolynomial

/-! Polynomial growth of the retained physical loop source reservation, with
the allocation/activation measure tied to the actual loop observer. These are
source cells and activations, not a host compiler/allocator-space theorem. -/

namespace Blotto.BinaryPRGHeapLifetimePolynomial
open BinaryPRGHeapLoopSourceLifetime
set_option maxHeartbeats 1500000

macro "unfold_heap_lifetime_envelope" : tactic => `(tactic|
  simp only [sourceEnvelope,BinaryPRGHeapLifetimeReservation.stepEnvelope,
    BinaryPRGHeapLifetimeReservation.coinEnvelope,BinaryPRGHeapPairLifetime.pairEnvelope,
    BinaryPRGHeapUpdateLifetime.updateEnvelope,BinaryPRGHeapUpdateLifetime.writesEnvelope,
    BinaryPRGHeapPackedLifetime.writeReservation,BinaryPRGHeapScanLifetime.scanEnvelope,
    BinaryPRGHeapScanLifetime.fractionalEnvelope,BinaryPRGHeapTraceUsage.readEnvelope,
    BinaryPRGHeapResourceReservation.sourceHeapCap,BinaryPRGHeapResourceReservation.sourceSize,
    BinaryPRGWordStoreHeap.heapBound,BinaryPRGHeapStoredTree.readBound,
    BinaryPRGWordStoreHeapMachine.lookupBound,BinaryPRGWordStoreHeapMachine.lookupAllocation,
    BinaryPRGWordStoreHeapMachine.patchBound,BinaryPRGWordStoreHeapMachine.readBound,
    BinaryPRGWordStoreHeapMachine.skipBound,BinaryPRGWordStoreHeapMachine.allocationBound,
    BinaryQuadraticResourcePairLifetime.outputsBound,BinaryQuadraticResourcePairLifetime.outputsFrames,
    BinaryQuadraticResourcePairLifetime.pairBound,BinaryQuadraticResourcePairLifetime.pairFrames,
    BinaryQuadraticResourcePairLifetime.instructionBound,BinaryQuadraticResourcePairLifetime.instructionFrames,
    BinaryQuadraticLifetime.opcodeBound,BinaryQuadraticLifetime.opcodeFrames,
    BinaryQuadraticResourceStateLifetime.compareBound,BinaryQuadraticResourceStateLifetime.compareFrames,
    BinaryWordCoinLifetime.sampleBound,BinaryWordCoinLifetime.localBound])

open BinaryPRGHeapResourcePolynomial in
theorem diagonal_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => sourceEnvelope p.wordWidth p.wordWidth p.wordWidth p.wordWidth
      p.wordWidth p.wordWidth p.wordWidth p.wordWidth) := by
  unfold_heap_lifetime_envelope
  resource_polynomial

theorem sourceEnvelope_mono {n h k w p q i s N H K W P Q I S : ℕ}
    (hn : n ≤ N) (hh : h ≤ H) (hk : k ≤ K) (hw : w ≤ W)
    (hp : p ≤ P) (hq : q ≤ Q) (hi : i ≤ I) (hs : s ≤ S) :
    sourceEnvelope n h k w p q i s ≤ sourceEnvelope N H K W P Q I S := by
  unfold_heap_lifetime_envelope
  gcongr <;> apply binaryWordWidth_mono <;> gcongr

theorem uniform_sourceEnvelope : ∃ C d : ℕ,∀ (n h k w p q i s : ℕ),
    sourceEnvelope n h k w p q i s ≤ C * (n + h + k + w + p + q + i + s + 2)^d := by
  rcases diagonal_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n h k w p q i s
  let T := n + h + k + w + p + q + i + s
  have hMono : sourceEnvelope n h k w p q i s ≤ sourceEnvelope T T T T T T T T :=
    sourceEnvelope_mono (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega)
      (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega) (by dsimp [T]; omega)
  have h := hBound ⟨0,T,0,0,0⟩
  have hSize : BinaryPRGHeapResourcePolynomial.inputSize ⟨0,T,0,0,0⟩ + 1 = T + 2 := by
    simp [BinaryPRGHeapResourcePolynomial.inputSize,binaryWordWidth]
  rw [hSize] at h
  exact hMono.trans h

def arrayLoopEnvelope (n W D indexWidth seedCap : ℕ) : ℕ :=
  sourceEnvelope n (BinaryPRGHeapResourceInputBounds.initialHeapBound n W)
    (BinaryPRGHeapResourceInputBounds.initialHeapBound n W) (binaryWordWidth n)
    (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) (1 + 2 * binaryWordWidth D) indexWidth seedCap

open BinaryPRGHeapResourcePolynomial in
theorem arrayLoopEnvelope_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => arrayLoopEnvelope p.count p.wordWidth p.denominator p.seedWidth p.seedCap) := by
  simp only [arrayLoopEnvelope,BinaryPRGHeapResourceInputBounds.initialHeapBound,
    BinaryPRGWordControllerBooleanResourceLoopWork.widthBound]
  unfold_heap_lifetime_envelope
  resource_polynomial

open BinaryRationalNormalization BinaryRationalEncoding in
theorem original_array_loop_usage {n : ℕ} (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (W D : ℕ) (hW : 1 ≤ W) (hD : 0 < D)
    (hCapacity : ∀ j,width (capacity.read j) ≤ W) (hResource : ∀ j,width (resource.read j) ≤ W)
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hResourceLattice : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hResourceBox : ∀ j,0 ≤ value (resource.read j) ∧ value (resource.read j) ≤ value (capacity.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let prepared := BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR
    BinaryPRGHeapTraceUsage.usage (BinaryPRGHeapLoopLifetime.runWithTrace seed prepared.1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2 pc hp).2 ≤
        arrayLoopEnvelope n W D seed.width seed.cap.value := by
  let prepared := BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR
  have hInv := BinaryPRGHeapResourceInvariant.initial_lattice capacity resource hC hR D hResourceLattice hResourceBox
  have hLat : ∀ j,OnRationalLattice D (value ((BinaryPRGWordControllerBooleanResourceUpdate.table
      (BinaryPRGHeapResourceSource.capStore capacity).cap (BinaryPRGHeapResourceSource.capStore capacity).tree
      n (BinaryPRGHeapResourceSource.count capacity)).read j)) := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hLattice
  have hBounds : ∀ j,0 ≤ value ((BinaryPRGWordControllerBooleanResourceUpdate.table
      (BinaryPRGHeapResourceSource.capStore capacity).cap (BinaryPRGHeapResourceSource.capStore capacity).tree
      n (BinaryPRGHeapResourceSource.count capacity)).read j) ∧
      value ((BinaryPRGWordControllerBooleanResourceUpdate.table
        (BinaryPRGHeapResourceSource.capStore capacity).cap (BinaryPRGHeapResourceSource.capStore capacity).tree
        n (BinaryPRGHeapResourceSource.count capacity)).read j) ≤ 1 := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hBox
  have hLoop := BinaryPRGHeapLoopSourceLifetime.lattice_usage
    (hC := BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    D hD hLat hBounds seed prepared.1.1 prepared.1.2 hInv pc hp
  have hHeaps := BinaryPRGHeapResourceInputBounds.initial_heaps_bound capacity resource hC hR W hW hCapacity hResource
  have hDepth := BinaryPRGHeapResourceInputBounds.source_depth capacity
  exact hLoop.trans (sourceEnvelope_mono le_rfl hHeaps.2 hHeaps.1 hDepth le_rfl le_rfl le_rfl le_rfl)

open BinaryRationalNormalization BinaryRationalEncoding in
theorem uniform_original_array_loop_usage : ∃ C d : ℕ,
    ∀ {n : ℕ} (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
      (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) (W D : ℕ),
    1 ≤ W → 0 < D → (∀ j,width (capacity.read j) ≤ W) → (∀ j,width (resource.read j) ≤ W) →
    (∀ j,OnRationalLattice D (value (capacity.read j))) →
    (∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1) →
    (∀ j,OnRationalLattice D (value (resource.read j))) →
    (∀ j,0 ≤ value (resource.read j) ∧ value (resource.read j) ≤ value (capacity.read j)) →
    ∀ (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
    let prepared := BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR
    BinaryPRGHeapTraceUsage.usage (BinaryPRGHeapLoopLifetime.runWithTrace seed prepared.1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2 pc hp).2 ≤
        C * (n + W + binaryWordWidth D + seed.width + seed.cap.value + 1)^d := by
  rcases arrayLoopEnvelope_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n seed capacity resource hC hR W D hW hD hCapacity hResource hLattice hBox hRL hRB pc hp
  exact (original_array_loop_usage seed capacity resource hC hR W D hW hD hCapacity hResource
    hLattice hBox hRL hRB pc hp).trans (hBound ⟨n,W,D,seed.width,seed.cap.value⟩)

def threeLoopEnvelope (s indexWidth seedCap : ℕ) : ℕ :=
  let W := BinaryPRGWordControllerBooleanResourceThreeWork.widthBound 2 s
  let K := BinaryPRGHeapResourceInputBounds.initialHeapBound 3 W
  sourceEnvelope 3 K K (binaryWordWidth 3) W (BinaryThreeResourceHeight.coinWidth 2 s) indexWidth seedCap

open BinaryPRGHeapResourcePolynomial in
theorem threeLoopEnvelope_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => threeLoopEnvelope p.wordWidth p.seedWidth p.seedCap) := by
  simp only [threeLoopEnvelope,BinaryPRGHeapResourceInputBounds.initialHeapBound,
    BinaryPRGWordControllerBooleanResourceThreeWork.widthBound,
    BinaryThreeResourceHeight.resourceHeight,BinaryThreeResourceHeight.coinWidth]
  unfold_heap_lifetime_envelope
  resource_polynomial

open BinaryRationalNormalization BinaryRationalEncoding in
theorem original_three_loop_usage (s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let prepared := BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR
    BinaryPRGHeapTraceUsage.usage (BinaryPRGHeapLoopLifetime.runWithTrace seed prepared.1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2 pc hp).2 ≤
        threeLoopEnvelope s seed.width seed.cap.value := by
  let prepared := BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR
  let W := BinaryPRGWordControllerBooleanResourceThreeWork.widthBound 2 s
  have hW : 1 ≤ W := by unfold W BinaryPRGWordControllerBooleanResourceThreeWork.widthBound; omega
  have hcWidth : ∀ j,width (capacity.read j) ≤ W := by
    intro j
    have hw := (hC j).2.trans (rationalWordWidth_of_height (hCapacity j))
    have hHeight := expressionHeightBudget_ge_input s (3 * 2)
    unfold W BinaryPRGWordControllerBooleanResourceThreeWork.widthBound BinaryThreeResourceHeight.resourceHeight
    omega
  have hrWidth : ∀ j,width (resource.read j) ≤ W := by
    intro j
    have hw := (hR j).2.trans (rationalWordWidth_of_height (hResource j))
    have hHeight := expressionHeightBudget_ge_input s (3 * 2)
    unfold W BinaryPRGWordControllerBooleanResourceThreeWork.widthBound BinaryThreeResourceHeight.resourceHeight
    omega
  have hHeaps := BinaryPRGHeapResourceInputBounds.initial_heaps_bound capacity resource hC hR W hW hcWidth hrWidth
  have hDepth := BinaryPRGHeapResourceInputBounds.source_depth capacity
  have hCap : ∀ j,RationalHeight (value ((BinaryPRGWordControllerBooleanResourceUpdate.table
      (BinaryPRGHeapResourceSource.capStore capacity).cap (BinaryPRGHeapResourceSource.capStore capacity).tree
      3 (BinaryPRGHeapResourceSource.count capacity)).read j)) s := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hCapacity
  have hState : BinaryPRGHeapResourceThreeStep.HeightInv 2 s prepared.1.2 := by
    unfold BinaryPRGHeapResourceThreeStep.HeightInv
    rw [BinaryPRGHeapResourceSource.initialWithWork_reference]
    exact BinaryPRGWordControllerBooleanResourceThreeWork.source_initial_height capacity resource hC hR s hResource
  have hLoop := BinaryPRGHeapLoopSourceLifetime.height_usage
    (hC := BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    2 s hs hCap seed prepared.1.1 prepared.1.2 hState pc hp
  exact hLoop.trans (sourceEnvelope_mono le_rfl hHeaps.2 hHeaps.1 hDepth le_rfl le_rfl le_rfl le_rfl)

open BinaryRationalNormalization BinaryRationalEncoding in
theorem uniform_original_three_loop_usage : ∃ C d : ℕ,∀ (s : ℕ),2 ≤ s →
    ∀ (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable 3 SignedWord)
      (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)),
    (∀ j,RationalHeight (value (capacity.read j)) s) → (∀ j,RationalHeight (value (resource.read j)) s) →
    ∀ (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
    let prepared := BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR
    BinaryPRGHeapTraceUsage.usage (BinaryPRGHeapLoopLifetime.runWithTrace seed prepared.1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2 pc hp).2 ≤
        C * (s + seed.width + seed.cap.value + 2)^d := by
  rcases threeLoopEnvelope_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro s hs seed capacity resource hC hR hCapacity hResource pc hp
  have h := (original_three_loop_usage s hs seed capacity resource hC hR hCapacity hResource pc hp).trans
    (hBound ⟨0,s,0,seed.width,seed.cap.value⟩)
  have hSize : BinaryPRGHeapResourcePolynomial.inputSize ⟨0,s,0,seed.width,seed.cap.value⟩ + 1 =
      s + seed.width + seed.cap.value + 2 := by
    simp [BinaryPRGHeapResourcePolynomial.inputSize,binaryWordWidth]
    omega
  simpa only [hSize] using h

end Blotto.BinaryPRGHeapLifetimePolynomial
