import Blotto.BinaryScalarTape
import Blotto.BinaryWordGroupLifetimePolynomial
import Blotto.BinaryCachedTerminalPromises

/-! The mixed-two terminal continuation consumes retained fields and routes.
Dimension transport is erased; actual production/drawing/emission uses the
complete unordered/exceptional three-variable path. -/
namespace Blotto.BinaryWordMixedTwoTerminalLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork BinaryCachedTerminalPreparation
set_option maxHeartbeats 2000000

def drawWithTrace {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store n × Trace := by
  subst m
  exact BinaryWordGroupEmissionLifetime.mixedTwoRun store input hC hAd routes pivot K scalar pc hp

theorem drawWithTrace_erasure {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (hm : m = 2 ∨ m = 3)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (hRoutes : ∀ j,CanonicalWord (routes.read j).2)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawWithTrace store input hC hAd hTwo routes pivot K scalar pc hp).1 =
      let drawn := BinaryPRGWordControllerTerminal.mixedRun store input hC hAd hm K outer scalar pc hp
      (drawn.1.map (BinaryGroupRoutes.emitMixed routes pivot),drawn.2) := by
  subst m
  exact BinaryWordGroupEmissionLifetime.mixedTwoRun_erasure store input hC hAd routes pivot hRoutes K scalar pc hp

theorem drawWithTrace_usage {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (drawWithTrace store input hC hAd hTwo routes pivot K scalar pc hp).2 ≤
      BinaryWordGroupEmissionLifetime.mixedEnvelope n s K store.width store.cap.value := by
  subst m
  exact BinaryWordGroupEmissionLifetime.mixedTwoRun_usage store input hC hAd routes pivot hRoutesC s hs hHeight hRoutes K scalar pc hp

def runWithTrace {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hTwo : prepared.count = 2) (selected : Fin n) (hPivot : prepared.pivot = some selected)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store n × Trace :=
  let drawn := drawWithTrace store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
    (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot) hTwo prepared.routes selected K scalar pc hp
  (drawn.1,wrap 32 2 [drawn.2])

theorem runWithTrace_erasure {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hTwo : prepared.count = 2) (selected : Fin n) (hPivot : prepared.pivot = some selected)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store prepared hC hAd hTwo selected hPivot K scalar pc hp).1 =
      BinaryPRGWordControllerTerminal.runPrepared store prepared hC hAd K outer scalar pc hp := by
  unfold runWithTrace BinaryPRGWordControllerTerminal.runPrepared
  dsimp only
  rw [drawWithTrace_erasure _ _ _ _ _ (prepared.count_bound hC hAd) _ _
    (BinaryCachedTerminalPromises.Prepared.routes_canonical prepared hC) K outer]
  split
  · rename_i hOther
    cases hOther.symm.trans hPivot
  · rename_i other hOther
    have he : other = selected := Option.some.inj (hOther.symm.trans hPivot)
    subst other
    rfl

def envelope (n s K indexWidth seedCap : ℕ) : ℕ :=
  BinaryWordGroupEmissionLifetime.mixedEnvelope n s K indexWidth seedCap + 40

theorem runWithTrace_usage {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hTwo : prepared.count = 2) (selected : Fin n) (hPivot : prepared.pivot = some selected)
    (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights prepared.mixed s)
    (hRoutes : ∀ j,RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store prepared hC hAd hTwo selected hPivot K scalar pc hp).2 ≤ envelope n s K store.width store.cap.value := by
  let drawn := drawWithTrace store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
    (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot) hTwo prepared.routes selected K scalar pc hp
  have hDraw := drawWithTrace_usage store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
    (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot) hTwo prepared.routes selected
    (BinaryCachedTerminalPromises.Prepared.routes_canonical prepared hC) s hs hHeight hRoutes K scalar pc hp
  have hw := wrap_usage 32 2 [drawn.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage drawn.2 ≤ _ at hDraw
  change usage (wrap 32 2 [drawn.2]) ≤ _
  unfold envelope
  omega

theorem envelope_polynomial : ∃ C d : ℕ,∀ n s K i b,
    envelope n s K i b ≤ C * (n + s + K + i + b + 2)^d := by
  rcases BinaryWordGroupLifetimePolynomial.mixed_envelope_polynomial with ⟨C,d,hBound⟩
  refine ⟨C + 40,d,?_⟩
  intro n s K i b
  have h := hBound n s K i b
  have hOne := Nat.one_le_pow d (n + s + K + i + b + 2) (by omega)
  unfold envelope
  nlinarith

end Blotto.BinaryWordMixedTwoTerminalLifetime
