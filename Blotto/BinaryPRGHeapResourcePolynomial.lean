import Blotto.BinaryPRGHeapResourceInputCost
import Blotto.NaturalPolynomialEnvelope

/-! The input-only envelope already bounds actual physical resource work.
Its growth is polynomial in dimension, original word width, lattice denominator
bit width and seed storage parameters. This does not price all PRG phases or
the host runtime's ownership, metadata and allocator behavior. -/

namespace Blotto.BinaryPRGHeapResourcePolynomial

structure Parameters where
  count : ℕ
  wordWidth : ℕ
  denominator : ℕ
  seedWidth : ℕ
  seedCap : ℕ

def inputSize (p : Parameters) : ℕ :=
  p.count + p.wordWidth + binaryWordWidth p.denominator + p.seedWidth + p.seedCap

theorem count_polynomial : NaturalPolynomialEnvelope inputSize (fun p => p.count) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (fun _ => by unfold inputSize; omega)

theorem width_polynomial : NaturalPolynomialEnvelope inputSize (fun p => p.wordWidth) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (fun _ => by unfold inputSize; omega)

theorem latticeWidth_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => binaryWordWidth p.denominator) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (fun _ => by unfold inputSize; omega)

theorem seedWidth_polynomial : NaturalPolynomialEnvelope inputSize (fun p => p.seedWidth) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (fun _ => by unfold inputSize; omega)

theorem seedCap_polynomial : NaturalPolynomialEnvelope inputSize (fun p => p.seedCap) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (fun _ => by unfold inputSize; omega)

open Lean Meta Elab Tactic in
elab "resource_polynomial" : tactic => do
  for _ in [:10000] do
    if (← getGoals).isEmpty then return
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let fn := target.getAppArgs.back!
    let body := match fn with
      | .lam _ _ body _ => body.headBeta
      | _ => fn
    let rule ← match body.getAppFn.constName? with
      | some ``Parameters.count => `(tactic| exact count_polynomial)
      | some ``Parameters.wordWidth => `(tactic| exact width_polynomial)
      | some ``Parameters.seedWidth => `(tactic| exact seedWidth_polynomial)
      | some ``Parameters.seedCap => `(tactic| exact seedCap_polynomial)
      | some ``HAdd.hAdd => `(tactic| apply NaturalPolynomialEnvelope.add)
      | some ``HMul.hMul => `(tactic| apply NaturalPolynomialEnvelope.mul)
      | some ``HPow.hPow => `(tactic| apply NaturalPolynomialEnvelope.pow)
      | some ``HSub.hSub => `(tactic| apply NaturalPolynomialEnvelope.sub)
      | some ``Max.max => `(tactic| apply NaturalPolynomialEnvelope.max)
      | some ``expressionHeightBudget => `(tactic| apply NaturalPolynomialEnvelope.height)
      | some ``binaryWordWidth =>
          if body.getAppArgs.back!.getAppFn.constName? == some ``Parameters.denominator then
            `(tactic| exact latticeWidth_polynomial)
          else `(tactic| apply NaturalPolynomialEnvelope.wordWidth)
      | _ =>
          if body.hasLooseBVars then throwError "unhandled resource envelope expression: {body}"
          else `(tactic| exact NaturalPolynomialEnvelope.constant _ _)
    evalTactic rule
  throwError "resource envelope exceeds structural step budget"

theorem nativeBound_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => BinaryPRGHeapResourceInputCost.nativeBound
      p.count p.wordWidth p.denominator p.seedWidth p.seedCap) := by
  simp only [BinaryPRGHeapResourceInputCost.nativeBound,
    BinaryPRGHeapResourceInputCost.loopBound,BinaryPRGHeapResourceInputCost.heapBound,
    BinaryPRGHeapResourceInputBounds.preparationBound,
    BinaryPRGHeapResourceInputBounds.initialHeapBound,
    BinaryPRGHeapResourceReservation.stepBound,BinaryPRGHeapResourceReservation.pairBound,
    BinaryPRGHeapResourceReservation.sourceHeapCap,BinaryPRGHeapResourceReservation.sourceSize,
    BinaryPRGWordControllerBooleanResourceLoopWork.widthBound,
    BinaryPRGWordControllerBooleanResourcePair.bound,
    BinaryPRGWordControllerPairOutputWork.traceBound,
    BinaryPRGWordControllerPairRegisters.instructionBound,
    BinaryPRGHeapResourceUpdateBudget.updateBound,
    BinaryPRGHeapResourceUpdateBudget.scanBound,BinaryPRGHeapResourceUpdateBudget.testBound,
    BinaryPRGHeapResourceSourceReservation.terminalBound,
    BinaryPRGHeapStoredTree.readBound,BinaryPRGWordStoreHeapMachine.lookupBound,
    BinaryPRGWordStoreHeapMachine.patchBound,BinaryPRGWordStoreHeapMachine.readBound,
    BinaryPRGWordStoreHeapMachine.skipBound,BinaryPRGWordStoreHeapMachine.allocationBound,
    BinaryPRGWordStoreHeap.heapBound,BinaryWordIndexCoinController.sampleBound,
    BinaryWordIndexCoinController.allowance]
  resource_polynomial

theorem heapBound_polynomial : NaturalPolynomialEnvelope inputSize
    (fun p => BinaryPRGHeapResourceInputCost.heapBound p.count p.wordWidth p.denominator) := by
  simp only [BinaryPRGHeapResourceInputCost.heapBound,
    BinaryPRGHeapResourceInputBounds.initialHeapBound,
    BinaryPRGHeapResourceReservation.sourceHeapCap,BinaryPRGHeapResourceReservation.sourceSize,
    BinaryPRGWordControllerBooleanResourceLoopWork.widthBound,BinaryPRGWordStoreHeap.heapBound]
  resource_polynomial

open BinaryRationalNormalization BinaryRationalEncoding in
theorem uniform_native_work_bound : ∃ C d : ℕ,
    ∀ {n : ℕ} (seed : BinarySeedLookupTree.Store)
      (capacity resource : FixedArrayTable n SignedWord)
      (hC : ∀ j,CanonicalWord (capacity.read j))
      (hR : ∀ j,CanonicalWord (resource.read j)) (W D : ℕ),
      1 ≤ W → 0 < D →
      (∀ j,width (capacity.read j) ≤ W) →
      (∀ j,width (resource.read j) ≤ W) →
      (∀ j,OnRationalLattice D (value (capacity.read j))) →
      (∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1) →
      (∀ j,OnRationalLattice D (value (resource.read j))) →
      (∀ j,0 ≤ value (resource.read j) ∧ value (resource.read j) ≤ value (capacity.read j)) →
      (BinaryPRGHeapResourceMaterialization.runNativeWithWork
        seed capacity resource hC hR).2 ≤
        C * (n + W + binaryWordWidth D + seed.width + seed.cap.value + 1)^d := by
  rcases nativeBound_polynomial with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n seed capacity resource hC hR W D hW hD hCapacity hResource
    hLattice hBox hResourceLattice hResourceBox
  exact (BinaryPRGHeapResourceInputCost.runNativeWithWork_input_bound
    seed capacity resource hC hR W D hW hD hCapacity hResource
    hLattice hBox hResourceLattice hResourceBox).trans
      (hBound ⟨n,W,D,seed.width,seed.cap.value⟩)

end Blotto.BinaryPRGHeapResourcePolynomial
