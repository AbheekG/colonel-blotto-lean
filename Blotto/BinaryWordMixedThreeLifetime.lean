import Blotto.BinaryScalarTape
import Blotto.BinaryFourRestoredLifetime
import Blotto.BinaryWordGroupEmissionLifetime

/-! A retained mixed-three group consumes the complete sorted/restored
four-variable draw, then actual cached-route multiplication and pivot addition.
Successful row heights are derived from its exact partial-run refinement. -/
namespace Blotto.BinaryWordMixedThreeLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork
set_option maxHeartbeats 2000000

def drawWithTrace (store : BinarySeedLookupTree.Store) (input : MixedInput 3)
    (hC : input.Canonical) (hAd : MixedAdmissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store 4 × Trace :=
  let drawn := BinaryFourRestoredLifetime.runWithTrace store (mixedFour input) (mixedFour_canonical input hC)
    (mixedFour_admissible input hC hAd) K outer scalar pc hp
  (drawn.1,wrap 32 2 [drawn.2])

theorem drawWithTrace_erasure (store : BinarySeedLookupTree.Store) (input : MixedInput 3)
    (hC : input.Canonical) (hAd : MixedAdmissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawWithTrace store input hC hAd K outer scalar pc hp).1 =
      BinaryPRGWordControllerTerminal.mixedRun store input hC hAd (Or.inr rfl) K outer scalar pc hp :=
  BinaryFourRestoredLifetime.runWithTrace_erasure store _ _ _ K outer scalar pc hp

theorem drawWithTrace_success (store : BinarySeedLookupTree.Store) (input : MixedInput 3)
    (hC : input.Canonical) (hAd : MixedAdmissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (row : FixedArrayTable 4 SignedWord)
    (h : (drawWithTrace store input hC hAd K outer scalar pc hp).1.1 = some row) :
    (BinaryGroupPartialRun.mixedRun input hC hAd (Or.inr rfl) K store.cap.value outer scalar
      (BinaryWordIndexCoinController.reader store) pc.value hp).1 = some row := by
  have hNative : (BinaryPRGWordControllerTerminal.mixedRun store input hC hAd (Or.inr rfl)
      K outer scalar pc hp).1 = some row := by
    rw [← drawWithTrace_erasure]
    exact h
  have hState := congrArg Prod.fst
    (BinaryPRGWordControllerTerminal.mixedRun_state store input hC hAd (Or.inr rfl) K outer scalar pc hp)
  exact hState.symm.trans hNative

theorem drawWithTrace_canonical (store : BinarySeedLookupTree.Store) (input : MixedInput 3)
    (hC : input.Canonical) (hAd : MixedAdmissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (row : FixedArrayTable 4 SignedWord)
    (h : (drawWithTrace store input hC hAd K outer scalar pc hp).1.1 = some row) :
    ∀ j,CanonicalWord (row.read j) :=
  BinaryGroupPartialRun.mixedRun_canonical input hC hAd (Or.inr rfl) K store.cap.value outer scalar
    (BinaryWordIndexCoinController.reader store) pc.value hp row
    (drawWithTrace_success store input hC hAd K outer scalar pc hp row h)

theorem drawWithTrace_height (store : BinarySeedLookupTree.Store) (input : MixedInput 3)
    (hC : input.Canonical) (hAd : MixedAdmissible input) (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights input s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (row : FixedArrayTable 4 SignedWord)
    (h : (drawWithTrace store input hC hAd K outer scalar pc hp).1.1 = some row) :
    ∀ j,RationalHeight (value (row.read j)) (expressionHeightBudget (max s (K+2)) 72) :=
  BinaryGroupReachedHeight.mixed_success_height input hC hAd (Or.inr rfl) s hs hH K store.cap.value
    outer scalar (BinaryWordIndexCoinController.reader store) pc.value hp row
    (drawWithTrace_success store input hC hAd K outer scalar pc hp row h)

def drawEnvelope (s K indexWidth seedCap remaining : ℕ) : ℕ :=
  BinaryFourRestoredLifetime.envelope s K indexWidth seedCap remaining + 64

theorem drawWithTrace_usage (store : BinarySeedLookupTree.Store) (input : MixedInput 3)
    (hC : input.Canonical) (hAd : MixedAdmissible input) (s : ℕ) (hs : 3 ≤ s) (hH : MixedHeights input s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (drawWithTrace store input hC hAd K outer scalar pc hp).2 ≤
      drawEnvelope s K store.width store.cap.value (store.cap.value-pc.value) := by
  obtain ⟨source,hr⟩ := hAd
  have hSource : source.fourInput.FieldsHeight s := by
    refine ⟨?_,?_,?_,?_⟩
    · change RationalHeight source.B s
      rw [← hr.1]
      exact hH.1
    · intro j
      change RationalHeight (source.length j) s
      rw [← hr.2.1 j]
      exact hH.2.1 j
    · change RationalHeight source.ell s
      rw [← hr.2.2.1]
      exact hH.2.2.1
    · change RationalHeight source.p s
      rw [← hr.2.2.2]
      exact hH.2.2.2
  let drawn := BinaryFourRestoredLifetime.runWithTrace store (mixedFour input) (mixedFour_canonical input hC)
    (mixedFour_admissible input hC ⟨source,hr⟩) K outer scalar pc hp
  have hDraw := BinaryFourRestoredLifetime.runWithTrace_usage store (mixedFour input) source.fourInput
    (mixedFour_canonical input hC) (mixedFour_refines input source hr)
    (mixedFour_admissible input hC ⟨source,hr⟩) s hs hSource K outer scalar pc hp
  change usage drawn.2 ≤ _ at hDraw
  have hw := wrap_usage 32 2 [drawn.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [drawn.2]) ≤ _
  unfold drawEnvelope
  omega

def runWithTrace {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3)
    (hC : input.Canonical) (hAd : MixedAdmissible input)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store n × Trace :=
  let drawn := drawWithTrace store input hC hAd K outer scalar pc hp
  let emitted := BinaryGroupEmissionLifetime.emitMixedOptionWithTrace routes pivot drawn.1.1
  ((emitted.1,drawn.1.2),wrap 32 2 [drawn.2,emitted.2])

theorem runWithTrace_erasure {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3)
    (hC : input.Canonical) (hAd : MixedAdmissible input)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (hRoutes : ∀ j,CanonicalWord (routes.read j).2)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC hAd routes pivot K outer scalar pc hp).1 =
      let drawn := BinaryPRGWordControllerTerminal.mixedRun store input hC hAd (Or.inr rfl) K outer scalar pc hp
      (drawn.1.map (BinaryGroupRoutes.emitMixed routes pivot),drawn.2) := by
  have hRows := drawWithTrace_canonical store input hC hAd K outer scalar pc hp
  unfold runWithTrace
  dsimp only
  rw [BinaryGroupEmissionLifetime.emitMixedOptionWithTrace_erasure _ _ _ hRoutes hRows,drawWithTrace_erasure]

def envelope (n s K indexWidth seedCap remaining : ℕ) : ℕ :=
  drawEnvelope s K indexWidth seedCap remaining +
    BinaryGroupEmissionLifetimeBound.mixedEnvelope n 3 (expressionHeightBudget (max s (K+2)) 72) + 128

theorem runWithTrace_usage {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3)
    (hC : input.Canonical) (hAd : MixedAdmissible input)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hH : MixedHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store input hC hAd routes pivot K outer scalar pc hp).2 ≤
      envelope n s K store.width store.cap.value (store.cap.value-pc.value) := by
  let drawn := drawWithTrace store input hC hAd K outer scalar pc hp
  have hDraw := drawWithTrace_usage store input hC hAd s hs hH K outer scalar pc hp
  change usage drawn.2 ≤ _ at hDraw
  have hRowsC := drawWithTrace_canonical store input hC hAd K outer scalar pc hp
  have hRowsH := drawWithTrace_height store input hC hAd s (by omega) hH K outer scalar pc hp
  have hRouteH : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget (max s (K+2)) 72) := by
    intro j
    exact (hRoutes j).mono (BinaryWordGroupEmissionLifetime.route_height_le s K)
  have hs72 : 3 ≤ expressionHeightBudget (max s (K+2)) 72 :=
    (hs.trans (le_max_left _ _)).trans (expressionHeightBudget_ge_input _ 72)
  have hEmit := BinaryGroupEmissionLifetimeBound.emitMixedOptionWithTrace_usage routes pivot drawn.1.1
    hRoutesC hRowsC _ hs72 hRouteH hRowsH
  have hw := wrap_usage 32 2 [drawn.2,
    (BinaryGroupEmissionLifetime.emitMixedOptionWithTrace routes pivot drawn.1.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [drawn.2,
    (BinaryGroupEmissionLifetime.emitMixedOptionWithTrace routes pivot drawn.1.1).2]) ≤ _
  unfold envelope
  omega

theorem all_prefix {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3)
    (hC : input.Canonical) (hAd : MixedAdmissible input)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hH : MixedHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store input hC hAd routes pivot K outer scalar pc hp).2 steps ≤
      borrowed + envelope n s K store.width store.cap.value (store.cap.value-pc.value) ∧
    framePeak ((runWithTrace store input hC hAd routes pivot K outer scalar pc hp).2.take steps) ≤
      envelope n s K store.width store.cap.value (store.cap.value-pc.value) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage store input hC hAd routes pivot hRoutesC s hs hH hRoutes K outer scalar pc hp) borrowed steps

end Blotto.BinaryWordMixedThreeLifetime
