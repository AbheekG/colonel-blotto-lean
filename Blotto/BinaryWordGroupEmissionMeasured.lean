import Blotto.BinaryMeasuredEmissionGrowth
import Blotto.BinaryWordGroupLifetimePolynomial
import Blotto.BinaryWordMixedThreeLifetime

/-! Every selected group branch consumes its actual returned draw in measured
route emission. Factories/draws are unchanged source calls, not rerun to obtain
the charge. The charge covers emission and wrapper control only; factory/draw
work and native model realization remain separate. All three branches, EOF
and optional failure outputs are retained. -/

namespace Blotto.BinaryWordGroupEmissionMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork BinaryMeasuredEmissionGrowth
set_option autoImplicit false
set_option maxHeartbeats 3500000

def uniformRun {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ :=
  let drawn := BinaryWordGroupLifetime.uniformRun store input hC hAd hm K scalar pc hp
  let emitted := BinaryGroupEmissionMeasured.emitOption routes drawn.1.1
  (((emitted.1.1,drawn.1.2),wrap 32 2 [drawn.2,emitted.1.2]),emitted.2+8)

theorem uniformRun_data {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store input hC hAd hm routes K scalar pc hp).1.1 =
      (BinaryWordGroupEmissionLifetime.uniformRun store input hC hAd hm routes K scalar pc hp).1 := by
  simp only [uniformRun,BinaryWordGroupEmissionLifetime.uniformRun,BinaryGroupEmissionMeasured.emitOption_data]

theorem uniformRun_growth {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Growth (BinaryWordGroupEmissionLifetime.uniformRun store input hC hAd hm routes K scalar pc hp).2
      (uniformRun store input hC hAd hm routes K scalar pc hp).1.2 (arrayDelta n+4) := by
  exact wrap_pair 32 2 _ _ _ _ (option_growth routes _)

theorem uniform_widths {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : UniformHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (∀ j,width (routes.read j).2 ≤ 2*BinaryWordGroupEmissionLifetime.groupHeight s K+1) ∧
      (∀ row,(BinaryWordGroupLifetime.uniformRun store input hC hAd hm K scalar pc hp).1.1 = some row →
        ∀ j,width (row.read j) ≤ 2*BinaryWordGroupEmissionLifetime.groupHeight s K+1) := by
  constructor
  · intro j
    have h := (hRoutesC j).2.trans (rationalWordWidth_of_height
      ((hRoutes j).mono (BinaryWordGroupEmissionLifetime.route_height_le s K)))
    omega
  · intro row hRow j
    have hc := BinaryWordGroupResult.uniform_canonical store input hC hAd hm K scalar pc hp row hRow j
    have hh := (BinaryWordGroupResult.uniform_height store input hC hAd hm s (by omega)
      hHeight K scalar pc hp row hRow j).mono (expressionHeightBudget_mono _ (by decide : 21 ≤ 72))
    have h := hc.2.trans (rationalWordWidth_of_height hh)
    dsimp only [BinaryWordGroupEmissionLifetime.groupHeight]
    omega

def uniformWork (n s K : ℕ) : ℕ :=
  BinaryGroupEmissionMeasured.workEnvelope n (2*BinaryWordGroupEmissionLifetime.groupHeight s K+1)+12

theorem uniformRun_work {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : UniformHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store input hC hAd hm routes K scalar pc hp).2 ≤ uniformWork n s K := by
  obtain ⟨hRW,hRows⟩ := uniform_widths store input hC hAd hm routes hRoutesC s hs hHeight hRoutes K scalar pc hp
  have h := BinaryGroupEmissionMeasured.emitOption_work routes
    (BinaryWordGroupLifetime.uniformRun store input hC hAd hm K scalar pc hp).1.1 _ hRW hRows
  change _+8 ≤ _
  unfold uniformWork
  omega

theorem uniformRun_usage {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : UniformHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (uniformRun store input hC hAd hm routes K scalar pc hp).1.2 ≤
      BinaryWordGroupEmissionLifetime.uniformEnvelope n m s K store.width store.cap.value+2*(arrayDelta n+4) := by
  have hOld := BinaryWordGroupEmissionLifetime.uniformRun_usage store input hC hAd hm routes hRoutesC s hs hHeight hRoutes K scalar pc hp
  have h := usage_growth _ _ _ (uniformRun_growth store input hC hAd hm routes K scalar pc hp)
  omega

def mixedTwoRun {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ :=
  let drawn := BinaryWordGroupLifetime.mixedTwoRun store input hC hAd K scalar pc hp
  let emitted := BinaryGroupEmissionMeasured.emitMixedOption routes pivot drawn.1.1
  (((emitted.1.1,drawn.1.2),wrap 32 2 [drawn.2,emitted.1.2]),emitted.2+8)

theorem mixedTwoRun_data {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRun store input hC hAd routes pivot K scalar pc hp).1.1 =
      (BinaryWordGroupEmissionLifetime.mixedTwoRun store input hC hAd routes pivot K scalar pc hp).1 := by
  simp only [mixedTwoRun,BinaryWordGroupEmissionLifetime.mixedTwoRun,BinaryGroupEmissionMeasured.emitMixedOption_data]

theorem mixedTwoRun_growth {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Growth (BinaryWordGroupEmissionLifetime.mixedTwoRun store input hC hAd routes pivot K scalar pc hp).2
      (mixedTwoRun store input hC hAd routes pivot K scalar pc hp).1.2 (mixedDelta n 2+4) := by
  exact wrap_pair 32 2 _ _ _ _ (mixed_option_growth routes pivot _)

def mixedWork (n m s K : ℕ) : ℕ :=
  BinaryGroupEmissionMeasured.mixedWorkEnvelope n m (BinaryWordGroupEmissionLifetime.groupHeight s K)+12

theorem mixedTwoRun_work {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRun store input hC hAd routes pivot K scalar pc hp).2 ≤ mixedWork n 2 s K := by
  have hRowsC := BinaryWordGroupResult.mixedTwo_canonical store input hC hAd K scalar pc hp
  have hRowsH := BinaryWordGroupResult.mixedTwo_height store input hC hAd s (by omega) hHeight K scalar pc hp
  have hTop : 3 ≤ BinaryWordGroupEmissionLifetime.groupHeight s K :=
    hs.trans ((le_max_left _ _).trans (expressionHeightBudget_ge_input _ _))
  have h := BinaryGroupEmissionMeasured.emitMixedOption_work routes pivot
    (BinaryWordGroupLifetime.mixedTwoRun store input hC hAd K scalar pc hp).1.1 hRoutesC hRowsC
    _ hTop (fun j => (hRoutes j).mono (BinaryWordGroupEmissionLifetime.route_height_le s K)) hRowsH
  change _+8 ≤ _
  unfold mixedWork
  omega

theorem mixedTwoRun_usage {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (mixedTwoRun store input hC hAd routes pivot K scalar pc hp).1.2 ≤
      BinaryWordGroupEmissionLifetime.mixedEnvelope n s K store.width store.cap.value+2*(mixedDelta n 2+4) := by
  have hOld := BinaryWordGroupEmissionLifetime.mixedTwoRun_usage store input hC hAd routes pivot hRoutesC s hs hHeight hRoutes K scalar pc hp
  have h := usage_growth _ _ _ (mixedTwoRun_growth store input hC hAd routes pivot K scalar pc hp)
  omega

def mixedThreeRun {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ :=
  let drawn := BinaryWordMixedThreeLifetime.drawWithTrace store input hC hAd K outer scalar pc hp
  let emitted := BinaryGroupEmissionMeasured.emitMixedOption routes pivot drawn.1.1
  (((emitted.1.1,drawn.1.2),wrap 32 2 [drawn.2,emitted.1.2]),emitted.2+8)

theorem mixedThreeRun_data {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedThreeRun store input hC hAd routes pivot K outer scalar pc hp).1.1 =
      (BinaryWordMixedThreeLifetime.runWithTrace store input hC hAd routes pivot K outer scalar pc hp).1 := by
  simp only [mixedThreeRun,BinaryWordMixedThreeLifetime.runWithTrace,BinaryGroupEmissionMeasured.emitMixedOption_data]

theorem mixedThreeRun_growth {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Growth (BinaryWordMixedThreeLifetime.runWithTrace store input hC hAd routes pivot K outer scalar pc hp).2
      (mixedThreeRun store input hC hAd routes pivot K outer scalar pc hp).1.2 (mixedDelta n 3+4) := by
  exact wrap_pair 32 2 _ _ _ _ (mixed_option_growth routes pivot _)

theorem mixedThreeRun_work {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedThreeRun store input hC hAd routes pivot K outer scalar pc hp).2 ≤ mixedWork n 3 s K := by
  have hRowsC := BinaryWordMixedThreeLifetime.drawWithTrace_canonical store input hC hAd K outer scalar pc hp
  have hRowsH := BinaryWordMixedThreeLifetime.drawWithTrace_height store input hC hAd s (by omega) hHeight K outer scalar pc hp
  have hTop : 3 ≤ BinaryWordGroupEmissionLifetime.groupHeight s K :=
    hs.trans ((le_max_left _ _).trans (expressionHeightBudget_ge_input _ _))
  have h := BinaryGroupEmissionMeasured.emitMixedOption_work routes pivot
    (BinaryWordMixedThreeLifetime.drawWithTrace store input hC hAd K outer scalar pc hp).1.1 hRoutesC hRowsC
    _ hTop (fun j => (hRoutes j).mono (BinaryWordGroupEmissionLifetime.route_height_le s K)) hRowsH
  change _+8 ≤ _
  unfold mixedWork
  omega

theorem mixedThreeRun_usage {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (mixedThreeRun store input hC hAd routes pivot K outer scalar pc hp).1.2 ≤
      BinaryWordMixedThreeLifetime.envelope n s K store.width store.cap.value (store.cap.value-pc.value)+
        2*(mixedDelta n 3+4) := by
  have hOld := BinaryWordMixedThreeLifetime.runWithTrace_usage store input hC hAd routes pivot hRoutesC s hs hHeight hRoutes K outer scalar pc hp
  have h := usage_growth _ _ _ (mixedThreeRun_growth store input hC hAd routes pivot K outer scalar pc hp)
  omega

end Blotto.BinaryWordGroupEmissionMeasured
