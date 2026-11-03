import Blotto.BinaryScalarTape
import Blotto.BinaryWordGroupLifetimePolynomial
import Blotto.BinaryCachedRouteHeight

/-! The uniform terminal branch consumes the retained cache directly. Its
count, totals and routes feed the complete actual factory/draw/emission path.
The mixed-three/four-variable branch is a separate continuation obligation. -/
namespace Blotto.BinaryWordUniformTerminalLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryCachedTerminalPreparation BinaryCachedTerminalPromises BinaryCachedThreeDescriptorWork
set_option maxHeartbeats 2000000

def runWithTrace {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hPivot : prepared.pivot = none) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store n × Trace :=
  let drawn := BinaryWordGroupEmissionLifetime.uniformRun store prepared.uniform (prepared.uniform_canonical hC)
    (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot) (prepared.count_bound hC hAd) prepared.routes K scalar pc hp
  (drawn.1,wrap 32 2 [drawn.2])

theorem runWithTrace_erasure {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hPivot : prepared.pivot = none) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store prepared hC hAd hPivot K scalar pc hp).1 =
      BinaryPRGWordControllerTerminal.runPrepared store prepared hC hAd K outer scalar pc hp := by
  unfold runWithTrace BinaryPRGWordControllerTerminal.runPrepared
  dsimp only
  rw [BinaryWordGroupEmissionLifetime.uniformRun_erasure _ _ _ _ _ _
    (BinaryCachedTerminalPromises.Prepared.routes_canonical prepared hC)]
  split
  · rfl
  · rename_i selected hOther
    cases hPivot.symm.trans hOther

def envelope (n s K indexWidth seedCap : ℕ) : ℕ :=
  BinaryWordGroupEmissionLifetime.uniformEnvelope n 3 s K indexWidth seedCap + 40

theorem runWithTrace_usage {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hPivot : prepared.pivot = none) (s : ℕ) (hs : 3 ≤ s) (hHeight : UniformHeights prepared.uniform s)
    (hRoutes : ∀ j,RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store prepared hC hAd hPivot K scalar pc hp).2 ≤ envelope n s K store.width store.cap.value := by
  have hm := prepared.count_bound hC hAd
  let drawn := BinaryWordGroupEmissionLifetime.uniformRun store prepared.uniform (prepared.uniform_canonical hC)
    (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot) hm prepared.routes K scalar pc hp
  have hDraw := BinaryWordGroupEmissionLifetime.uniformRun_usage store prepared.uniform (prepared.uniform_canonical hC)
    (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot) hm prepared.routes
    (BinaryCachedTerminalPromises.Prepared.routes_canonical prepared hC) s hs hHeight hRoutes K scalar pc hp
  have hMono := BinaryWordGroupLifetimePolynomial.uniform_mono (le_refl n) (show prepared.count ≤ 3 by omega)
    (le_refl s) (le_refl K) (le_refl store.width) (le_refl store.cap.value)
  have hw := wrap_usage 32 2 [drawn.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage drawn.2 ≤ _ at hDraw
  change usage (wrap 32 2 [drawn.2]) ≤ _
  unfold envelope
  omega

theorem envelope_polynomial : ∃ C d : ℕ,∀ n s K i b,
    envelope n s K i b ≤ C * (n + s + K + i + b + 5)^d := by
  rcases BinaryWordGroupLifetimePolynomial.uniform_envelope_polynomial with ⟨C,d,hBound⟩
  refine ⟨C + 40,d,?_⟩
  intro n s K i b
  have h := hBound n 3 s K i b
  have hSize : n + 3 + s + K + i + b + 2 = n + s + K + i + b + 5 := by omega
  rw [hSize] at h
  have hOne := Nat.one_le_pow d (n + s + K + i + b + 5) (by omega)
  unfold envelope
  nlinarith

theorem all_prefix {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hPivot : prepared.pivot = none) (s : ℕ) (hs : 3 ≤ s) (hHeight : UniformHeights prepared.uniform s)
    (hRoutes : ∀ j,RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store prepared hC hAd hPivot K scalar pc hp).2 steps ≤
        borrowed + envelope n s K store.width store.cap.value ∧
      framePeak ((runWithTrace store prepared hC hAd hPivot K scalar pc hp).2.take steps) ≤ envelope n s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (runWithTrace_usage store prepared hC hAd hPivot s hs hHeight hRoutes K scalar pc hp) borrowed steps

end Blotto.BinaryWordUniformTerminalLifetime
