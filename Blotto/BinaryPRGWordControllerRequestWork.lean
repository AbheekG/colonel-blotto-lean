import Blotto.BinaryPRGWordControllerTerminalWork
import Blotto.BinaryPRGWordControllerResourceWork
import Blotto.BinaryPRGWordControllerRouteCopyWork
import Blotto.BinaryPRGFallbackInventory

/-! Reached source work through resource, terminal preparation, routes, every
group continuation and global fallback.  This joins each actual arithmetic
backend and its concrete Store counter.  Route writes permit complete old/new
region copies.  Global fallback is conservatively charged on every getD call;
no compiler/lazy-default sharing is assumed.  Logical address and small-scalar
interpretation remain explicit further obligations of the full machine model. -/

namespace Blotto.BinaryPRGWordControllerRequestWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedTerminalPreparation
open BinaryCachedGroupInputHeight BinaryCachedThreeDescriptorWork

def prefixWork {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input) : ℕ :=
  BinaryCachedTerminalWork.arithmeticWork prepared +
    (BinaryPRGWordControllerRouteCopyWork.prepareWithWork input.length prepared.packing).2 +
      BinaryGreedyPackingExecution.structuralWork input.length.read input.budget (BinaryTerminalGrouping.uniformItems input) +
        12 * n + 60

def prefixBound (n sourceWidth sourceHeight : ℕ) : ℕ :=
  (454000 * n + 96000) * (sourceWidth + 2)^3 +
    BinaryPRGWordControllerRouteCopyWork.bound n 3 sourceHeight + 20 * n + 61

theorem reached_prefixWork_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state) :
    prefixWork (prepare (terminalInput request rich state)) ≤
      prefixBound n request.source.originalInputWordWidth (inputHeight request) := by
  let prepared := prepare (terminalInput request rich state)
  have hC := terminal_canonical request rich state
  have hAd := terminal_admissible request rich N bits state h
  have hArithmetic := BinaryCachedTerminalWork.reached_arithmeticWork_bound request rich N bits state h
  change BinaryCachedTerminalWork.arithmeticWork prepared ≤ _ at hArithmetic
  have hLengths : ∀ j, RationalHeight (value ((terminalInput request rich state).length.read j)) (inputHeight request) := by
    intro j
    exact (length_height request rich j).mono (by have hd := lattice_height_original request; omega)
  have hTotals : ∀ g, RationalHeight (value (prepared.packing.read g).2) (inputHeight request) := by
    intro g
    have ht := cached_total_height request rich N bits state h g
    change RationalHeight (value (prepared.totals.read g)) (inputHeight request) at ht
    rw [prepared.totals_eq, FixedArrayTable.read_ofFn] at ht
    exact ht
  have hCopies := BinaryPRGWordControllerRouteCopyWork.prepareWithWork_bound (terminalInput request rich state).length
    prepared.packing hC.2.1 (BinaryCachedTerminalWork.Prepared.total_canonical prepared hC) _ hLengths hTotals
    (BinaryCachedTerminalWork.Prepared.members_length prepared hC hAd)
  have hCount := prepared.count_bound hC hAd
  have hThree : prepared.count ≤ 3 := by rcases hCount with hCount | hCount <;> omega
  have hCopyBound : BinaryPRGWordControllerRouteCopyWork.bound n prepared.count (inputHeight request) ≤
      BinaryPRGWordControllerRouteCopyWork.bound n 3 (inputHeight request) := by
    unfold BinaryPRGWordControllerRouteCopyWork.bound
    gcongr
  have hPacking := BinaryGreedyPackingExecution.terminal_structuralWork_bound (terminalInput request rich state)
  unfold prefixWork prefixBound
  change BinaryCachedTerminalWork.arithmeticWork prepared +
    (BinaryPRGWordControllerRouteCopyWork.prepareWithWork (terminalInput request rich state).length prepared.packing).2 +
      BinaryGreedyPackingExecution.structuralWork (terminalInput request rich state).length.read
        (terminalInput request rich state).budget (BinaryTerminalGrouping.uniformItems (terminalInput request rich state)) +
          12 * n + 60 ≤ _
  omega

def run {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) : BinaryPRGWordControllerRequest.Result store n × ℕ :=
  let observed := BinaryPRGWordControllerResourceWork.requestRun store request rich
  match hs : observed.1.1 with
  | none => ((none, observed.1.2), observed.2 + 2)
  | some state =>
      have hState : (BinaryPRGWordControllerResource.requestRun store request rich).1 = some state :=
        (congrArg Prod.fst (BinaryPRGWordControllerResourceWork.requestRun_erasure store request rich)).symm.trans hs
      let prepared := prepare (terminalInput request rich state)
      have hPosition : observed.1.2.value ≤ store.cap.value := by
        rw [BinaryPRGWordControllerResourceWork.requestRun_erasure]
        exact BinaryPRGWordControllerRequest.resource_position store request rich
      let later := BinaryPRGWordControllerTerminalWork.runPrepared store prepared (terminal_canonical request rich state)
        (BinaryPRGWordControllerRequest.resource_terminal_admissible store request rich state hState)
        K outer scalar observed.1.2 hPosition
      (later.1, observed.2 + prefixWork prepared + later.2 + 2)

theorem run_erasure {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (run store request rich K outer scalar).1 = BinaryPRGWordControllerRequest.run store request rich K outer scalar := by
  have hErasure := BinaryPRGWordControllerResourceWork.requestRun_erasure store request rich
  have hOption := congrArg Prod.fst hErasure
  have hPC := congrArg Prod.snd hErasure
  unfold run BinaryPRGWordControllerRequest.run
  dsimp only
  split
  · rename_i hNone
    have hOld := hOption.symm.trans hNone
    split
    · exact congrArg (fun p => (none, p)) hPC
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
      rw [BinaryPRGWordControllerTerminalWork.runPrepared_erasure]
      simp only [hPC]

noncomputable def bound {n : ℕ} (request : BinaryPRGRequest.Request n) (K indexWidth N : ℕ) : ℕ :=
  BinaryPRGWordControllerResourceWork.initialBound n request.source.normalizedInput.latticeDenominator indexWidth N +
    prefixBound n request.source.originalInputWordWidth (inputHeight request) +
      BinaryPRGWordControllerTerminalWork.bound n (BinaryCachedTerminalPrimitiveRun.requestHeight request) K indexWidth N + 2

theorem terminalBound_span_mono (n s K indexWidth : ℕ) {first second : ℕ} (h : first ≤ second) :
    BinaryPRGWordControllerTerminalWork.bound n s K indexWidth first ≤
      BinaryPRGWordControllerTerminalWork.bound n s K indexWidth second := by
  simp only [BinaryPRGWordControllerTerminalWork.bound, BinaryPRGWordControllerGroupWork.uniformBound, BinaryPRGWordControllerGroupWork.mixedBound, BinaryPRGWordControllerFourWork.restoredBound, BinaryPRGWordControllerFourWork.runBound, BinaryPRGWordControllerFourWork.gluingBound, BinaryPRGWordControllerFourWork.smallBound, BinaryPRGWordControllerFourWork.rootBound, BinaryPRGWordControllerFourWork.uniformBound, BinaryPRGWordControllerReflectedWork.bound, BinaryPRGWordControllerReflectedWork.selectionBound, BinaryPRGWordControllerReflectedSetupWork.bound,
    BinaryPRGWordControllerBooleanResourceThreeWork.sourceBound,
    BinaryPRGWordControllerBooleanResourceThreeWork.sourceEnvelope,
    BinaryPRGWordControllerBooleanResourceThreeWork.bound,
    BinaryPRGWordControllerBooleanResourceThreeWork.pairBound, BinaryPRGWordControllerThreeResourceWork.bound, BinaryPRGWordControllerWork.segmentBound, BinaryPRGWordControllerWork.selectionBound]
  gcongr

theorem run_bound {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (run store request rich K outer scalar).2 ≤ bound request K store.width store.cap.value := by
  have hResource := BinaryPRGWordControllerResourceWork.requestRun_bound store request rich
  unfold run
  dsimp only
  split
  · unfold bound; omega
  · rename_i state hState
    have hReached : (resourceWork request rich store.cap.value (BinaryWordIndexCoinController.reader store)).1.1 = some state := by
      have he := congrArg Prod.fst (BinaryPRGWordControllerResource.requestRun_state store request rich)
      have hn := congrArg Prod.fst (BinaryPRGWordControllerResourceWork.requestRun_erasure store request rich)
      exact he.symm.trans (hn.symm.trans hState)
    have hPrefix := reached_prefixWork_bound request rich store.cap.value (BinaryWordIndexCoinController.reader store) state hReached
    let prepared := prepare (terminalInput request rich state)
    have hPosition : (BinaryPRGWordControllerResourceWork.requestRun store request rich).1.2.value ≤ store.cap.value := by
      rw [BinaryPRGWordControllerResourceWork.requestRun_erasure]
      exact BinaryPRGWordControllerRequest.resource_position store request rich
    have hUniform := BinaryCachedTerminalPrimitiveRun.uniformHeights_mono
      (cached_uniform_heights request rich store.cap.value (BinaryWordIndexCoinController.reader store) state hReached)
      (le_max_left (inputHeight request) 3)
    have hMixed := fun selected hPivot => BinaryCachedTerminalPrimitiveRun.mixedHeights_mono
      (cached_mixed_heights request rich store.cap.value (BinaryWordIndexCoinController.reader store) state hReached selected hPivot)
      (le_max_left (inputHeight request) 3)
    have hRoutes : ∀ j, RationalHeight (value (prepared.routes.read j).2)
        (expressionHeightBudget (BinaryCachedTerminalPrimitiveRun.requestHeight request) 1) := by
      intro j
      have hr := BinaryCachedRouteHeight.reached_route_height request rich store.cap.value
        (BinaryWordIndexCoinController.reader store) state hReached j
      exact hr.mono (by unfold BinaryCachedTerminalPrimitiveRun.requestHeight expressionHeightBudget; gcongr; exact le_max_left _ _)
    have hTerminal := BinaryPRGWordControllerTerminalWork.runPrepared_bound store prepared (terminal_canonical request rich state)
      (terminal_admissible request rich store.cap.value (BinaryWordIndexCoinController.reader store) state hReached)
      (BinaryCachedTerminalPrimitiveRun.requestHeight request) (le_max_right _ _) hUniform hMixed hRoutes
      K outer scalar (BinaryPRGWordControllerResourceWork.requestRun store request rich).1.2 hPosition
    have hTerminal' := hTerminal.trans (terminalBound_span_mono n (BinaryCachedTerminalPrimitiveRun.requestHeight request)
      K store.width (Nat.sub_le _ _))
    unfold bound
    dsimp only [prepared] at hTerminal'
    omega

def fixedSample {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) : FixedArrayTable n SignedWord × ℕ :=
  let drawn := run store request rich K outer scalar
  let fallback := BinaryPRGFallbackInventory.prepare (resourceInput request rich)
  (drawn.1.1.getD fallback.1, drawn.2 + fallback.2.writes + fallback.2.wordCells + n * (n + 1) + 2 * n + 2)

theorem fixedSample_erasure {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (fixedSample store request rich K outer scalar).1 = BinaryPRGWordControllerRequest.fixedSample store request rich K outer scalar := by
  unfold fixedSample BinaryPRGWordControllerRequest.fixedSample
  dsimp only
  rw [run_erasure, BinaryPRGFallbackInventory.prepare_state]

noncomputable def fixedBound {n : ℕ} (request : BinaryPRGRequest.Request n) (K indexWidth N : ℕ) : ℕ :=
  bound request K indexWidth N + BinaryPRGOutputRun.fallbackBound n (inputHeight request) + n * (n + 1) + 2 * n + 2

theorem fixedSample_bound {n : ℕ} (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (fixedSample store request rich K outer scalar).2 ≤ fixedBound request K store.width store.cap.value := by
  have hRun := run_bound store request rich K outer scalar
  obtain ⟨hWrites, hWords⟩ := BinaryPRGFallbackInventory.request_prepare_bound request rich
  unfold fixedSample fixedBound BinaryPRGOutputRun.fallbackBound
  dsimp only
  omega

end Blotto.BinaryPRGWordControllerRequestWork
