import Blotto.BinaryPRGHeapResourceRequest
import Blotto.BinaryPRGWordControllerRequestWork

/-! A complete prepared PRG draw uses the physical general-resource backend,
then the retained measured terminal and fallback code. The exact old result
and cursor are preserved; a separate bound adds the physical resource price.
Reflected inner resource callers retain their existing backend here. -/

namespace Blotto.BinaryPRGHeapRequestWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedTerminalPreparation

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
      let later := BinaryPRGWordControllerTerminalWork.runPrepared store prepared
        (terminal_canonical request rich state)
        (BinaryPRGWordControllerRequest.resource_terminal_admissible store request rich state hState)
        K outer scalar observed.1.2 hPosition
      (later.1,observed.2 + BinaryPRGWordControllerRequestWork.prefixWork prepared + later.2 + 2)

theorem run_compare {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (run store request rich K outer scalar).1 =
        (BinaryPRGWordControllerRequestWork.run store request rich K outer scalar).1 ∧
      (run store request rich K outer scalar).2 +
        (BinaryPRGWordControllerResourceWork.requestRun store request rich).2 =
      (BinaryPRGWordControllerRequestWork.run store request rich K outer scalar).2 +
        (BinaryPRGHeapResourceRequest.run store request rich).2 := by
  have hData := (BinaryPRGHeapResourceRequest.run_erasure store request rich).trans
    (BinaryPRGWordControllerResourceWork.requestRun_erasure store request rich).symm
  have hOption := congrArg Prod.fst hData
  have hPC := congrArg Prod.snd hData
  unfold run BinaryPRGWordControllerRequestWork.run
  dsimp only
  split
  · rename_i hNone
    have hOld := hOption.symm.trans hNone
    split
    · exact ⟨congrArg (fun p => (none,p)) hPC,by omega⟩
    · rename_i state hOther
      cases hOld.symm.trans hOther
  · rename_i state hSome
    have hOld := hOption.symm.trans hSome
    split
    · rename_i hNone
      cases hOld.symm.trans hNone
    · rename_i other hOther
      have he : state = other := Option.some.inj (hOld.symm.trans hOther)
      subst other
      simp only [hPC]
      exact ⟨trivial,by omega⟩

theorem run_erasure {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (run store request rich K outer scalar).1 =
      BinaryPRGWordControllerRequest.run store request rich K outer scalar :=
  (run_compare store request rich K outer scalar).1.trans
    (BinaryPRGWordControllerRequestWork.run_erasure store request rich K outer scalar)

noncomputable def bound {n : ℕ} (request : BinaryPRGRequest.Request n) (K indexWidth N : ℕ) : ℕ :=
  BinaryPRGWordControllerRequestWork.bound request K indexWidth N +
    BinaryPRGHeapResourceRequest.bound request indexWidth N

theorem run_bound {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (run store request rich K outer scalar).2 ≤ bound request K store.width store.cap.value := by
  have hCompare := (run_compare store request rich K outer scalar).2
  have hOld := BinaryPRGWordControllerRequestWork.run_bound store request rich K outer scalar
  have hResource := BinaryPRGHeapResourceRequest.run_bound store request rich
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

theorem fixedSample_work_compare {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n)
    (rich : Bool) (K : ℕ) (outer scalar : Fin K → Bool) :
    (fixedSample store request rich K outer scalar).2 +
        (BinaryPRGWordControllerResourceWork.requestRun store request rich).2 =
      (BinaryPRGWordControllerRequestWork.fixedSample store request rich K outer scalar).2 +
        (BinaryPRGHeapResourceRequest.run store request rich).2 := by
  have h := (run_compare store request rich K outer scalar).2
  unfold fixedSample BinaryPRGWordControllerRequestWork.fixedSample
  dsimp only
  omega

noncomputable def fixedBound {n : ℕ} (request : BinaryPRGRequest.Request n) (K indexWidth N : ℕ) : ℕ :=
  BinaryPRGWordControllerRequestWork.fixedBound request K indexWidth N +
    BinaryPRGHeapResourceRequest.bound request indexWidth N

theorem fixedSample_bound {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (fixedSample store request rich K outer scalar).2 ≤ fixedBound request K store.width store.cap.value := by
  have hCompare := fixedSample_work_compare store request rich K outer scalar
  have hOld := BinaryPRGWordControllerRequestWork.fixedSample_bound store request rich K outer scalar
  have hResource := BinaryPRGHeapResourceRequest.run_bound store request rich
  unfold fixedBound
  omega

end Blotto.BinaryPRGHeapRequestWork
