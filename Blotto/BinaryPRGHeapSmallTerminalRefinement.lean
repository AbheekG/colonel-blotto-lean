import Blotto.BinaryPRGHeapSmallTerminalLifetime
import Blotto.BinaryPRGWordControllerRequest

/-! Complete data/cursor refinement of the physical source/cache/small-terminal
trace to the retained native request. The explicit SmallBranch promise is the
only branch restriction; none and source/terminal exhaustion are preserved. -/
namespace Blotto.BinaryPRGHeapSmallTerminalRefinement
open BinaryPRGHeapSmallTerminalLifetime BinaryPRGResourceWork BinaryPRGTerminalWork
set_option maxHeartbeats 2000000

theorem runWithTrace_erasure {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (hSmall : SmallBranch store request rich) (K : ℕ) (outer scalar : Fin K → Bool) :
    (runWithTrace store request rich hSmall K scalar).1 = BinaryPRGWordControllerRequest.run store request rich K outer scalar := by
  have hPrefix := BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace_reference store request rich
  have hPosition := congrArg Prod.snd hPrefix
  change (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.2 =
    (BinaryPRGWordControllerResource.requestRun store request rich).2 at hPosition
  have hReturned := congrArg Prod.fst hPrefix
  change (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.1 =
    (BinaryPRGWordControllerResource.requestRun store request rich).1.map (fun state =>
      (⟨state,BinaryTerminalCacheCertificate.zeroWork (BinaryCachedTerminalPreparation.prepare (terminalInput request rich state))⟩ :
        BinaryPRGHeapCertifiedPrefixLifetime.CachedResult request rich)) at hReturned
  unfold BinaryPRGWordControllerRequest.run
  dsimp only
  split
  · rename_i hNone
    have hEmpty : (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.1 = none := by
      rw [hReturned,hNone,Option.map_none]
      rfl
    rw [runWithTrace_none store request rich hSmall K scalar hEmpty,hPosition]
  · rename_i state hSome
    let result : BinaryPRGHeapCertifiedPrefixLifetime.CachedResult request rich :=
      ⟨state,BinaryTerminalCacheCertificate.zeroWork (BinaryCachedTerminalPreparation.prepare (terminalInput request rich state))⟩
    have hResult : (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.1 = some result := by
      rw [hReturned,hSome]
      rfl
    rw [runWithTrace_some store request rich hSmall K outer scalar result hResult]
    dsimp only [result]
    congr 1 <;> exact BinaryScalarTape.ofFn_read _

theorem runWithTrace_state {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (hSmall : SmallBranch store request rich) (K : ℕ) (outer scalar : Fin K → Bool) :
    BinaryPRGWordControllerRequest.decoded store (runWithTrace store request rich hSmall K scalar).1 =
      (BinaryPRGCachedPrimitiveRun.run request rich K store.cap.value outer scalar (BinaryWordIndexCoinController.reader store)).1 := by
  rw [runWithTrace_erasure]
  exact BinaryPRGWordControllerRequest.run_state store request rich K outer scalar

end Blotto.BinaryPRGHeapSmallTerminalRefinement
