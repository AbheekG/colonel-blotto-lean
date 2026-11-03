import Blotto.BinaryScalarTape
import Blotto.BinaryWordMixedThreeLifetime

/-! The cached mixed-three branch consumes retained totals, routes and pivot.
Dimension equality is erased; the actual four-variable draw and route emission
operate on the returned cached fields and cursor. -/
namespace Blotto.BinaryWordMixedThreeTerminalLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork BinaryCachedTerminalPreparation
set_option maxHeartbeats 2000000

def drawWithTrace {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m)
    (hC : input.Canonical) (hAd : MixedAdmissible input) (hThree : m = 3)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store n × Trace := by
  subst m
  exact BinaryWordMixedThreeLifetime.runWithTrace store input hC hAd routes pivot K outer scalar pc hp

theorem drawWithTrace_erasure {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m)
    (hC : input.Canonical) (hAd : MixedAdmissible input) (hThree : m = 3) (hm : m = 2 ∨ m = 3)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (hRoutes : ∀ j,CanonicalWord (routes.read j).2)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawWithTrace store input hC hAd hThree routes pivot K outer scalar pc hp).1 =
      let drawn := BinaryPRGWordControllerTerminal.mixedRun store input hC hAd hm K outer scalar pc hp
      (drawn.1.map (BinaryGroupRoutes.emitMixed routes pivot),drawn.2) := by
  subst m
  exact BinaryWordMixedThreeLifetime.runWithTrace_erasure store input hC hAd routes pivot hRoutes K outer scalar pc hp

theorem drawWithTrace_usage {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m)
    (hC : input.Canonical) (hAd : MixedAdmissible input) (hThree : m = 3)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hH : MixedHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (drawWithTrace store input hC hAd hThree routes pivot K outer scalar pc hp).2 ≤
      BinaryWordMixedThreeLifetime.envelope n s K store.width store.cap.value (store.cap.value-pc.value) := by
  subst m
  exact BinaryWordMixedThreeLifetime.runWithTrace_usage store input hC hAd routes pivot hRoutesC
    s hs hH hRoutes K outer scalar pc hp

def runWithTrace {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hThree : prepared.count = 3) (selected : Fin n) (hPivot : prepared.pivot = some selected)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store n × Trace :=
  let drawn := drawWithTrace store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
    (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
    hThree prepared.routes selected K outer scalar pc hp
  (drawn.1,wrap 32 2 [drawn.2])

theorem runWithTrace_erasure {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hThree : prepared.count = 3) (selected : Fin n) (hPivot : prepared.pivot = some selected)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store prepared hC hAd hThree selected hPivot K outer scalar pc hp).1 =
      BinaryPRGWordControllerTerminal.runPrepared store prepared hC hAd K outer scalar pc hp := by
  unfold runWithTrace BinaryPRGWordControllerTerminal.runPrepared
  dsimp only
  rw [drawWithTrace_erasure _ _ _ _ _ (prepared.count_bound hC hAd) _ _
    (BinaryCachedTerminalPromises.Prepared.routes_canonical prepared hC) K outer scalar]
  split
  · rename_i hOther
    cases hOther.symm.trans hPivot
  · rename_i other hOther
    have he : other = selected := Option.some.inj (hOther.symm.trans hPivot)
    subst other
    rfl

def envelope (n s K indexWidth seedCap remaining : ℕ) : ℕ :=
  BinaryWordMixedThreeLifetime.envelope n s K indexWidth seedCap remaining + 64

theorem runWithTrace_usage {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (hThree : prepared.count = 3) (selected : Fin n) (hPivot : prepared.pivot = some selected)
    (s : ℕ) (hs : 3 ≤ s) (hH : MixedHeights prepared.mixed s)
    (hRoutes : ∀ j,RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store prepared hC hAd hThree selected hPivot K outer scalar pc hp).2 ≤
      envelope n s K store.width store.cap.value (store.cap.value-pc.value) := by
  let drawn := drawWithTrace store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
    (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
    hThree prepared.routes selected K outer scalar pc hp
  have hDraw := drawWithTrace_usage store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
    (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
    hThree prepared.routes selected (BinaryCachedTerminalPromises.Prepared.routes_canonical prepared hC)
    s hs hH hRoutes K outer scalar pc hp
  change usage drawn.2 ≤ _ at hDraw
  have hw := wrap_usage 32 2 [drawn.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [drawn.2]) ≤ _
  unfold envelope
  omega

end Blotto.BinaryWordMixedThreeTerminalLifetime
