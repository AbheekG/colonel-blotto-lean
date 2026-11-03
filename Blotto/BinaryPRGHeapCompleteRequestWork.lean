import Blotto.BinaryPRGHeapRequestWork
import Blotto.BinaryPRGHeapTerminalWork

/-! The prepared request uses physical resource tapes both in the general
phase and in the reached reflected continuation. Earlier measured backends
serve only as erased comparisons in the semantic and price proofs. -/

namespace Blotto.BinaryPRGHeapCompleteRequestWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedTerminalPreparation
open BinaryCachedGroupInputHeight BinaryCachedThreeDescriptorWork

def run {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) : BinaryPRGWordControllerRequest.Result store n × ℕ :=
  let observed := BinaryPRGHeapResourceRequest.run store request rich
  match hs : observed.1.1 with
  | none => ((none,observed.1.2),observed.2 + 2)
  | some state =>
      have hState : (BinaryPRGWordControllerResource.requestRun store request rich).1 = some state :=
        (congrArg Prod.fst (BinaryPRGHeapResourceRequest.run_erasure store request rich)).symm.trans hs
      let prepared := prepare (terminalInput request rich state)
      have hPosition : observed.1.2.value ≤ store.cap.value := by
        rw [BinaryPRGHeapResourceRequest.run_erasure]
        exact BinaryPRGWordControllerRequest.resource_position store request rich
      let later := BinaryPRGHeapTerminalWork.runPrepared store prepared
        (terminal_canonical request rich state)
        (BinaryPRGWordControllerRequest.resource_terminal_admissible store request rich state hState)
        K outer scalar observed.1.2 hPosition
      (later.1,observed.2 + BinaryPRGWordControllerRequestWork.prefixWork prepared + later.2 + 2)

theorem run_compare {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (run store request rich K outer scalar).1 =
        (BinaryPRGHeapRequestWork.run store request rich K outer scalar).1 ∧
      (run store request rich K outer scalar).2 ≤
        (BinaryPRGHeapRequestWork.run store request rich K outer scalar).2 +
          BinaryPRGHeapReflectedSetup.bound (BinaryCachedTerminalPrimitiveRun.requestHeight request)
            store.width store.cap.value := by
  unfold run BinaryPRGHeapRequestWork.run
  dsimp only
  split
  · rename_i hNone
    split
    · exact ⟨rfl,by omega⟩
    · rename_i state hSome
      cases hNone.symm.trans hSome
  · rename_i state hSome
    have hState : (BinaryPRGWordControllerResource.requestRun store request rich).1 = some state :=
      (congrArg Prod.fst (BinaryPRGHeapResourceRequest.run_erasure store request rich)).symm.trans hSome
    have hReached : (resourceWork request rich store.cap.value (BinaryWordIndexCoinController.reader store)).1.1 = some state := by
      have he := congrArg Prod.fst (BinaryPRGWordControllerResource.requestRun_state store request rich)
      exact he.symm.trans hState
    let prepared := prepare (terminalInput request rich state)
    have hPosition : (BinaryPRGHeapResourceRequest.run store request rich).1.2.value ≤ store.cap.value := by
      rw [BinaryPRGHeapResourceRequest.run_erasure]
      exact BinaryPRGWordControllerRequest.resource_position store request rich
    have hMixed := fun selected hPivot => BinaryCachedTerminalPrimitiveRun.mixedHeights_mono
      (cached_mixed_heights request rich store.cap.value (BinaryWordIndexCoinController.reader store)
        state hReached selected hPivot) (le_max_left (inputHeight request) 3)
    have hCost := BinaryPRGHeapTerminalWork.runPrepared_cost_le store prepared
      (terminal_canonical request rich state)
      (BinaryPRGWordControllerRequest.resource_terminal_admissible store request rich state hState)
      (BinaryCachedTerminalPrimitiveRun.requestHeight request) (le_max_right _ _) hMixed K outer scalar
      (BinaryPRGHeapResourceRequest.run store request rich).1.2 hPosition
    have hData := (BinaryPRGHeapTerminalWork.runPrepared_erasure store prepared
      (terminal_canonical request rich state)
      (BinaryPRGWordControllerRequest.resource_terminal_admissible store request rich state hState)
      K outer scalar (BinaryPRGHeapResourceRequest.run store request rich).1.2 hPosition).trans
        (BinaryPRGWordControllerTerminalWork.runPrepared_erasure store prepared
          (terminal_canonical request rich state)
          (BinaryPRGWordControllerRequest.resource_terminal_admissible store request rich state hState)
          K outer scalar (BinaryPRGHeapResourceRequest.run store request rich).1.2 hPosition).symm
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he : state = other := Option.some.inj (hSome.symm.trans hOther)
      subst other
      exact ⟨hData,by dsimp only [prepared] at hCost; omega⟩

theorem run_erasure {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (run store request rich K outer scalar).1 =
      BinaryPRGWordControllerRequest.run store request rich K outer scalar :=
  (run_compare store request rich K outer scalar).1.trans
    (BinaryPRGHeapRequestWork.run_erasure store request rich K outer scalar)

noncomputable def bound {n : ℕ} (request : BinaryPRGRequest.Request n) (K indexWidth N : ℕ) : ℕ :=
  BinaryPRGHeapRequestWork.bound request K indexWidth N +
    BinaryPRGHeapReflectedSetup.bound (BinaryCachedTerminalPrimitiveRun.requestHeight request) indexWidth N

theorem run_bound {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (run store request rich K outer scalar).2 ≤ bound request K store.width store.cap.value := by
  have hCompare := (run_compare store request rich K outer scalar).2
  have hOld := BinaryPRGHeapRequestWork.run_bound store request rich K outer scalar
  unfold bound
  omega

def fixedSample {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) : FixedArrayTable n SignedWord × ℕ :=
  let drawn := run store request rich K outer scalar
  let fallback := BinaryPRGFallbackInventory.prepare (resourceInput request rich)
  (drawn.1.1.getD fallback.1,drawn.2 + fallback.2.writes + fallback.2.wordCells +
    n * (n + 1) + 2 * n + 2)

theorem fixedSample_erasure {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (fixedSample store request rich K outer scalar).1 =
      BinaryPRGWordControllerRequest.fixedSample store request rich K outer scalar := by
  unfold fixedSample BinaryPRGWordControllerRequest.fixedSample
  dsimp only
  rw [run_erasure,BinaryPRGFallbackInventory.prepare_state]

theorem fixedSample_cost_le {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n)
    (rich : Bool) (K : ℕ) (outer scalar : Fin K → Bool) :
    (fixedSample store request rich K outer scalar).2 ≤
      (BinaryPRGHeapRequestWork.fixedSample store request rich K outer scalar).2 +
        BinaryPRGHeapReflectedSetup.bound (BinaryCachedTerminalPrimitiveRun.requestHeight request)
          store.width store.cap.value := by
  have h := (run_compare store request rich K outer scalar).2
  unfold fixedSample BinaryPRGHeapRequestWork.fixedSample
  dsimp only
  omega

noncomputable def fixedBound {n : ℕ} (request : BinaryPRGRequest.Request n) (K indexWidth N : ℕ) : ℕ :=
  BinaryPRGHeapRequestWork.fixedBound request K indexWidth N +
    BinaryPRGHeapReflectedSetup.bound (BinaryCachedTerminalPrimitiveRun.requestHeight request) indexWidth N

theorem fixedSample_bound {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (fixedSample store request rich K outer scalar).2 ≤ fixedBound request K store.width store.cap.value := by
  have hCompare := fixedSample_cost_le store request rich K outer scalar
  have hOld := BinaryPRGHeapRequestWork.fixedSample_bound store request rich K outer scalar
  unfold fixedBound
  omega

end Blotto.BinaryPRGHeapCompleteRequestWork
