import Blotto.BinaryScalarTape
import Blotto.BinaryWordGroupResult
import Blotto.BinaryGroupEmissionLifetimeBound

/-! Complete cached uniform-two/uniform-three and mixed-two factory, draw and
route emission. Original group/coefficient heights derive selected row prices;
no descriptor, row or arithmetic price is supplied by the caller. -/
namespace Blotto.BinaryWordGroupEmissionLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork
set_option maxHeartbeats 2000000

def uniformRun {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store n × Trace :=
  let drawn := BinaryWordGroupLifetime.uniformRun store input hC hAd hm K scalar pc hp
  let emitted := BinaryGroupEmissionLifetime.emitOptionWithTrace routes drawn.1.1
  ((emitted.1,drawn.1.2),wrap 32 2 [drawn.2,emitted.2])

theorem uniformRun_erasure {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (hRoutes : ∀ j,CanonicalWord (routes.read j).2) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store input hC hAd hm routes K scalar pc hp).1 =
      let drawn := BinaryPRGWordControllerTerminal.uniformRun store input hC hAd hm K scalar pc hp
      (drawn.1.map (BinaryGroupRoutes.emit routes),drawn.2) := by
  have hRows := BinaryWordGroupResult.uniform_canonical store input hC hAd hm K scalar pc hp
  unfold uniformRun
  dsimp only
  rw [BinaryGroupEmissionLifetime.emitOptionWithTrace_erasure _ _ hRoutes hRows,BinaryWordGroupLifetime.uniformRun_erasure]

def mixedTwoRun {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store n × Trace :=
  let drawn := BinaryWordGroupLifetime.mixedTwoRun store input hC hAd K scalar pc hp
  let emitted := BinaryGroupEmissionLifetime.emitMixedOptionWithTrace routes pivot drawn.1.1
  ((emitted.1,drawn.1.2),wrap 32 2 [drawn.2,emitted.2])

theorem mixedTwoRun_erasure {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (hRoutes : ∀ j,CanonicalWord (routes.read j).2) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRun store input hC hAd routes pivot K scalar pc hp).1 =
      let drawn := BinaryPRGWordControllerSegment.run store (mixedTwoPrepared input hC hAd) 0 K scalar pc hp
      (drawn.1.map (BinaryGroupRoutes.emitMixed routes pivot),drawn.2) := by
  have hRows := BinaryWordGroupResult.mixedTwo_canonical store input hC hAd K scalar pc hp
  unfold mixedTwoRun
  dsimp only
  rw [BinaryGroupEmissionLifetime.emitMixedOptionWithTrace_erasure _ _ _ hRoutes hRows,BinaryWordGroupLifetime.mixedTwoRun_erasure]

def groupHeight (s K : ℕ) : ℕ := expressionHeightBudget (max s (K + 2)) 72

theorem route_height_le (s K : ℕ) : expressionHeightBudget s 1 ≤ groupHeight s K :=
  (expressionHeightBudget_input_mono (le_max_left s (K + 2)) 1).trans (expressionHeightBudget_mono _ (by decide : 1 ≤ 72))

def uniformEnvelope (n m s K indexWidth seedCap : ℕ) : ℕ := BinaryWordGroupLifetime.uniformEnvelope m s K indexWidth seedCap +
  BinaryGroupEmissionLifetimeBound.envelope n (2 * groupHeight s K + 1) + 64

def mixedEnvelope (n s K indexWidth seedCap : ℕ) : ℕ := BinaryWordGroupLifetime.mixedEnvelope s K indexWidth seedCap +
  BinaryGroupEmissionLifetimeBound.mixedEnvelope n 2 (groupHeight s K) + 64

theorem uniformRun_usage {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : UniformHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (uniformRun store input hC hAd hm routes K scalar pc hp).2 ≤ uniformEnvelope n m s K store.width store.cap.value := by
  let drawn := BinaryWordGroupLifetime.uniformRun store input hC hAd hm K scalar pc hp
  have hDraw := BinaryWordGroupLifetime.uniformRun_usage store input hC hAd hm s hs hHeight K scalar pc hp
  have hRowH : ∀ row,drawn.1.1 = some row → ∀ j,RationalHeight (value (row.read j)) (groupHeight s K) := by
    intro row hRow j
    exact (BinaryWordGroupResult.uniform_height store input hC hAd hm s (by omega) hHeight K scalar pc hp row hRow j).mono
      (expressionHeightBudget_mono _ (by decide : 21 ≤ 72))
  have hRouteW : ∀ j,width (routes.read j).2 ≤ 2 * groupHeight s K + 1 := by
    intro j
    have h := (hRoutesC j).2.trans (rationalWordWidth_of_height ((hRoutes j).mono (route_height_le s K)))
    omega
  have hRowW : ∀ row,drawn.1.1 = some row → ∀ j,width (row.read j) ≤ 2 * groupHeight s K + 1 := by
    intro row hRow j
    have hc := BinaryWordGroupResult.uniform_canonical store input hC hAd hm K scalar pc hp row hRow j
    have h := hc.2.trans (rationalWordWidth_of_height (hRowH row hRow j))
    omega
  have hEmit := BinaryGroupEmissionLifetimeBound.emitOptionWithTrace_usage routes drawn.1.1 _ hRouteW hRowW
  have hw := wrap_usage 32 2 [drawn.2,(BinaryGroupEmissionLifetime.emitOptionWithTrace routes drawn.1.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [drawn.2,(BinaryGroupEmissionLifetime.emitOptionWithTrace routes drawn.1.1).2]) ≤ _
  change usage drawn.2 ≤ _ at hDraw
  unfold uniformEnvelope
  omega

theorem mixedTwoRun_usage {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (mixedTwoRun store input hC hAd routes pivot K scalar pc hp).2 ≤ mixedEnvelope n s K store.width store.cap.value := by
  let drawn := BinaryWordGroupLifetime.mixedTwoRun store input hC hAd K scalar pc hp
  have hDraw := BinaryWordGroupLifetime.mixedTwoRun_usage store input hC hAd s hs hHeight K scalar pc hp
  have hRowC := BinaryWordGroupResult.mixedTwo_canonical store input hC hAd K scalar pc hp
  have hRowH := BinaryWordGroupResult.mixedTwo_height store input hC hAd s (by omega) hHeight K scalar pc hp
  have hTop : 3 ≤ groupHeight s K := hs.trans ((le_max_left _ _).trans (expressionHeightBudget_ge_input _ _))
  have hEmit := BinaryGroupEmissionLifetimeBound.emitMixedOptionWithTrace_usage routes pivot drawn.1.1 hRoutesC hRowC
    (groupHeight s K) hTop (fun j => (hRoutes j).mono (route_height_le s K)) hRowH
  have hw := wrap_usage 32 2 [drawn.2,(BinaryGroupEmissionLifetime.emitMixedOptionWithTrace routes pivot drawn.1.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [drawn.2,(BinaryGroupEmissionLifetime.emitMixedOptionWithTrace routes pivot drawn.1.1).2]) ≤ _
  change usage drawn.2 ≤ _ at hDraw
  unfold mixedEnvelope
  omega

end Blotto.BinaryWordGroupEmissionLifetime
