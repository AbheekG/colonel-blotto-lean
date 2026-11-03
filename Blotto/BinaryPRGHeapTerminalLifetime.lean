import Blotto.BinaryScalarTape
import Blotto.BinaryPRGHeapCertifiedPrefixProperties
import Blotto.BinaryWordTerminalLifetime
import Blotto.BinaryPRGWordControllerRequest

/-! The actual physical resource/cache prefix feeds every terminal regime,
including mixed-three, using its retained fields and returned absolute cursor.
Original request promises derive all continuation heights internally. -/
namespace Blotto.BinaryPRGHeapTerminalLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedGroupInputHeight
open BinaryPRGHeapCertifiedPrefixLifetime
set_option maxHeartbeats 2000000

def runWithTrace {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) : BinaryPRGWordControllerTerminal.Result store n × Trace :=
  let observed := BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich
  match hSome : observed.1.1 with
  | none => ((none,observed.1.2),wrap 16 2 [observed.2])
  | some result =>
      let drawn := BinaryWordTerminalLifetime.runWithTrace store result.2
        (terminal_canonical request rich result.1)
        (BinaryPRGHeapCertifiedPrefixProperties.admissible store request rich result hSome)
        K outer scalar observed.1.2 (BinaryPRGHeapCertifiedPrefixProperties.cursor_bound store request rich)
      (drawn.1,wrap 32 2 [observed.2,drawn.2])

theorem runWithTrace_none {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (h : (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.1 = none) :
    (runWithTrace store request rich K outer scalar).1 =
      (none,(BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.2) := by
  unfold runWithTrace
  dsimp only
  split
  · rfl
  · rename_i result hOther
    cases h.symm.trans hOther

theorem runWithTrace_some {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (result : CachedResult request rich)
    (h : (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.1 = some result) :
    (runWithTrace store request rich K outer scalar).1 =
      BinaryPRGWordControllerTerminal.runPrepared store
        (BinaryCachedTerminalPreparation.prepare (terminalInput request rich result.1))
        (terminal_canonical request rich result.1) (BinaryPRGHeapCertifiedPrefixProperties.admissible store request rich result h)
        K outer scalar (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.2
        (BinaryPRGHeapCertifiedPrefixProperties.cursor_bound store request rich) := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hOther
    cases hOther.symm.trans h
  · rename_i other hOther
    have he : other = result := Option.some.inj (hOther.symm.trans h)
    subst other
    rw [BinaryWordTerminalLifetime.runWithTrace_erasure]
    rw [(BinaryPRGHeapCertifiedPrefixProperties.reached store request rich result h).2]
    exact BinaryTerminalCacheCertificate.zeroWork_runPrepared _ _ _ _ _ _ _ _ _

theorem runWithTrace_erasure {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (runWithTrace store request rich K outer scalar).1 =
      BinaryPRGWordControllerRequest.run store request rich K outer scalar := by
  have hPrefix := BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace_reference store request rich
  have hPosition := congrArg Prod.snd hPrefix
  change (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.2 =
    (BinaryPRGWordControllerResource.requestRun store request rich).2 at hPosition
  have hReturned := congrArg Prod.fst hPrefix
  change (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.1 =
    (BinaryPRGWordControllerResource.requestRun store request rich).1.map (fun state =>
      (⟨state,BinaryTerminalCacheCertificate.zeroWork (BinaryCachedTerminalPreparation.prepare (terminalInput request rich state))⟩ :
        CachedResult request rich)) at hReturned
  unfold BinaryPRGWordControllerRequest.run
  dsimp only
  split
  · rename_i hNone
    have hEmpty : (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.1 = none := by
      rw [hReturned,hNone,Option.map_none]
      rfl
    rw [runWithTrace_none store request rich K outer scalar hEmpty,hPosition]
  · rename_i state hSome
    let result : CachedResult request rich :=
      ⟨state,BinaryTerminalCacheCertificate.zeroWork (BinaryCachedTerminalPreparation.prepare (terminalInput request rich state))⟩
    have hResult : (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.1 = some result := by
      rw [hReturned,hSome]
      rfl
    rw [runWithTrace_some store request rich K outer scalar result hResult]
    dsimp only [result]
    congr 1

theorem runWithTrace_state {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    BinaryPRGWordControllerRequest.decoded store (runWithTrace store request rich K outer scalar).1 =
      (BinaryPRGCachedPrimitiveRun.run request rich K store.cap.value outer scalar (BinaryWordIndexCoinController.reader store)).1 := by
  rw [runWithTrace_erasure]
  exact BinaryPRGWordControllerRequest.run_state store request rich K outer scalar

noncomputable def envelope {n : ℕ} (request : BinaryPRGRequest.Request n) (K indexWidth seedCap : ℕ) : ℕ :=
  BinaryPRGHeapCertifiedPrefixLifetime.envelope request indexWidth seedCap +
    BinaryWordTerminalLifetime.envelope n (inputHeight request) K indexWidth seedCap seedCap + 128

theorem runWithTrace_usage {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    usage (runWithTrace store request rich K outer scalar).2 ≤ envelope request K store.width store.cap.value := by
  let observed := BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich
  have hPrefix := BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace_usage store request rich
  change usage observed.2 ≤ _ at hPrefix
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 16 2 [observed.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [observed.2]) ≤ _
    unfold envelope
    omega
  · rename_i result hSome
    have hs : 3 ≤ inputHeight request := by unfold inputHeight; omega
    let drawn := BinaryWordTerminalLifetime.runWithTrace store result.2
      (terminal_canonical request rich result.1) (BinaryPRGHeapCertifiedPrefixProperties.admissible store request rich result hSome)
      K outer scalar observed.1.2 (BinaryPRGHeapCertifiedPrefixProperties.cursor_bound store request rich)
    have hDraw := BinaryWordTerminalLifetime.runWithTrace_usage store result.2
      (terminal_canonical request rich result.1) (BinaryPRGHeapCertifiedPrefixProperties.admissible store request rich result hSome)
      (inputHeight request) hs (BinaryPRGHeapCertifiedPrefixProperties.uniform_height store request rich result hSome)
      (BinaryPRGHeapCertifiedPrefixProperties.mixed_height store request rich result hSome)
      (BinaryPRGHeapCertifiedPrefixProperties.route_height store request rich result hSome)
      K outer scalar observed.1.2 (BinaryPRGHeapCertifiedPrefixProperties.cursor_bound store request rich)
    change usage drawn.2 ≤ _ at hDraw
    have hMono := BinaryWordTerminalLifetime.envelope_remaining_mono n (inputHeight request) K store.width
      store.cap.value (store.cap.value-observed.1.2.value) store.cap.value (Nat.sub_le _ _)
    have hw := wrap_usage 32 2 [observed.2,drawn.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [observed.2,drawn.2]) ≤ _
    unfold envelope
    omega

theorem all_prefix {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store request rich K outer scalar).2 steps ≤
      borrowed + envelope request K store.width store.cap.value ∧
    framePeak ((runWithTrace store request rich K outer scalar).2.take steps) ≤ envelope request K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (runWithTrace_usage store request rich K outer scalar) borrowed steps

end Blotto.BinaryPRGHeapTerminalLifetime
