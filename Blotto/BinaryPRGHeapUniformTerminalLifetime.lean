import Blotto.BinaryScalarTape
import Blotto.BinaryPRGHeapCertifiedPrefixProperties
import Blotto.BinaryWordUniformTerminalLifetime

/-! The physical general-resource/cache prefix feeds its own returned cache
and Boolean cursor directly into the complete uniform terminal continuation.
This entry point has an explicit uniform-branch scope. Mixed continuations,
global fallback and original-budget output remain separate obligations. -/
namespace Blotto.BinaryPRGHeapUniformTerminalLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedGroupInputHeight
open BinaryPRGHeapCertifiedPrefixLifetime
set_option maxHeartbeats 2000000

def UniformBranch {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) : Prop :=
  ∀ result : CachedResult request rich,(BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.1 = some result →
    result.2.pivot = none

def runWithTrace {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (hUniform : UniformBranch store request rich) (K : ℕ) (scalar : BinaryScalarTape K) :
    BinaryPRGWordControllerTerminal.Result store n × Trace :=
  let observed := BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich
  match hs : observed.1.1 with
  | none => ((none,observed.1.2),wrap 16 2 [observed.2])
  | some result =>
      let drawn := BinaryWordUniformTerminalLifetime.runWithTrace store result.2
        (terminal_canonical request rich result.1) (BinaryPRGHeapCertifiedPrefixProperties.admissible store request rich result hs)
        (hUniform result hs) K scalar observed.1.2 (BinaryPRGHeapCertifiedPrefixProperties.cursor_bound store request rich)
      (drawn.1,wrap 32 2 [observed.2,drawn.2])

theorem runWithTrace_none {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (hUniform : UniformBranch store request rich) (K : ℕ) (scalar : BinaryScalarTape K)
    (h : (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.1 = none) :
    (runWithTrace store request rich hUniform K scalar).1 =
      (none,(BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.2) := by
  unfold runWithTrace
  dsimp only
  split
  · rfl
  · rename_i result hOther
    cases h.symm.trans hOther

theorem runWithTrace_some {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (hUniform : UniformBranch store request rich) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (result : CachedResult request rich)
    (h : (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store request rich).1.1 = some result) :
    (runWithTrace store request rich hUniform K scalar).1 =
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
    rw [BinaryWordUniformTerminalLifetime.runWithTrace_erasure _ _ _ _ _ K outer]
    rw [(BinaryPRGHeapCertifiedPrefixProperties.reached store request rich result h).2]
    exact BinaryTerminalCacheCertificate.zeroWork_runPrepared _ _ _ _ _ _ _ _ _

noncomputable def envelope {n : ℕ} (request : BinaryPRGRequest.Request n) (K indexWidth seedCap : ℕ) : ℕ :=
  BinaryPRGHeapCertifiedPrefixLifetime.envelope request indexWidth seedCap +
    BinaryWordUniformTerminalLifetime.envelope n (inputHeight request) K indexWidth seedCap + 64

theorem runWithTrace_usage {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (hUniform : UniformBranch store request rich) (K : ℕ) (scalar : BinaryScalarTape K) :
    usage (runWithTrace store request rich hUniform K scalar).2 ≤ envelope request K store.width store.cap.value := by
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
    let drawn := BinaryWordUniformTerminalLifetime.runWithTrace store result.2
      (terminal_canonical request rich result.1) (BinaryPRGHeapCertifiedPrefixProperties.admissible store request rich result hSome)
      (hUniform result hSome) K scalar observed.1.2 (BinaryPRGHeapCertifiedPrefixProperties.cursor_bound store request rich)
    have hDraw := BinaryWordUniformTerminalLifetime.runWithTrace_usage store result.2
      (terminal_canonical request rich result.1) (BinaryPRGHeapCertifiedPrefixProperties.admissible store request rich result hSome)
      (hUniform result hSome) (inputHeight request) hs (BinaryPRGHeapCertifiedPrefixProperties.uniform_height store request rich result hSome)
      (BinaryPRGHeapCertifiedPrefixProperties.route_height store request rich result hSome)
      K scalar observed.1.2 (BinaryPRGHeapCertifiedPrefixProperties.cursor_bound store request rich)
    change usage drawn.2 ≤ _ at hDraw
    have hw := wrap_usage 32 2 [observed.2,drawn.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [observed.2,drawn.2]) ≤ _
    unfold envelope
    omega

theorem all_prefix {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (hUniform : UniformBranch store request rich) (K : ℕ) (scalar : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store request rich hUniform K scalar).2 steps ≤ borrowed + envelope request K store.width store.cap.value ∧
      framePeak ((runWithTrace store request rich hUniform K scalar).2.take steps) ≤ envelope request K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (runWithTrace_usage store request rich hUniform K scalar) borrowed steps

end Blotto.BinaryPRGHeapUniformTerminalLifetime
