import Blotto.BinaryPRGHeapResourceThreeSource
import Blotto.BinaryPRGHeapResourcePolynomial

/-! The physical three-coordinate source price is polynomial in the original
height promise and seed parameters, uniformly over the incoming cursor. -/

namespace Blotto.BinaryPRGHeapResourceThreePolynomial
open BinaryPRGHeapResourcePolynomial

theorem bound_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => BinaryPRGHeapResourceThreeSource.bound p.wordWidth p.seedWidth p.seedCap) := by
  simp only [BinaryPRGHeapResourceThreeSource.bound,BinaryPRGHeapResourceThreeSource.loopBound,
    BinaryPRGHeapResourceThreeSource.heapCap,BinaryPRGHeapResourceThreeSource.initialCells,
    BinaryPRGHeapResourceThreeSource.inputWidth,
    BinaryPRGHeapResourceInputBounds.preparationBound,BinaryPRGHeapResourceInputBounds.initialHeapBound,
    BinaryPRGHeapResourceReservation.sourceHeapCap,BinaryPRGHeapResourceReservation.sourceSize,
    BinaryPRGHeapResourceThreeReservation.stepBound,BinaryPRGHeapResourceThreeStep.pairBound,
    BinaryPRGWordControllerBooleanResourceThreeWork.widthBound,
    BinaryThreeResourceHeight.coinWidth,BinaryThreeResourceHeight.resourceHeight,
    BinaryPRGHeapResourceUpdateBudget.updateBound,BinaryPRGHeapResourceUpdateBudget.scanBound,
    BinaryPRGHeapResourceUpdateBudget.testBound,BinaryPRGHeapResourceSourceReservation.terminalBound,
    BinaryPRGWordControllerBooleanResourcePair.bound,BinaryPRGWordControllerPairOutputWork.traceBound,
    BinaryPRGWordControllerPairRegisters.instructionBound,
    BinaryPRGHeapStoredTree.readBound,BinaryPRGWordStoreHeapMachine.lookupBound,
    BinaryPRGWordStoreHeapMachine.patchBound,BinaryPRGWordStoreHeapMachine.readBound,
    BinaryPRGWordStoreHeapMachine.skipBound,BinaryPRGWordStoreHeapMachine.allocationBound,
    BinaryPRGWordStoreHeap.heapBound,BinaryWordIndexCoinController.sampleBound,
    BinaryWordIndexCoinController.allowance]
  resource_polynomial

open BinaryRationalNormalization BinaryRationalEncoding in
theorem uniform_sourceRun_bound : ∃ C d : ℕ,
    ∀ (s : ℕ),2 ≤ s → ∀ (seed : BinarySeedLookupTree.Store)
      (capacity resource : FixedArrayTable 3 SignedWord)
      (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)),
      (∀ j,RationalHeight (value (capacity.read j)) s) →
      (∀ j,RationalHeight (value (resource.read j)) s) →
      ∀ (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
      (BinaryPRGHeapResourceThreeSource.sourceRun seed capacity resource hC hR pc hp).2 ≤
        C * (s + seed.width + seed.cap.value + 2)^d := by
  rcases bound_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro s hs seed capacity resource hC hR hcHeight hrHeight pc hp
  have h := (BinaryPRGHeapResourceThreeSource.sourceRun_bound
    s hs seed capacity resource hC hR hcHeight hrHeight pc hp).trans
      (hBound ⟨0,s,0,seed.width,seed.cap.value⟩)
  have he : s + 1 + seed.width + seed.cap.value + 1 = s + seed.width + seed.cap.value + 2 := by omega
  simpa only [inputSize,binaryWordWidth,Nat.log2_zero,Nat.zero_add,he] using h

end Blotto.BinaryPRGHeapResourceThreePolynomial
