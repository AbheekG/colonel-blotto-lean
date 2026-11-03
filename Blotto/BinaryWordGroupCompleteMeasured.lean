import Blotto.BinaryWordGroupDrawMeasured
import Blotto.BinaryFourRestoredMeasured
import Blotto.BinaryWordGroupEmissionMeasured
import Blotto.BinaryCachedFourParameterWork

/-! Actual measured group factories/draws feed measured route emission once.
Uniform, mixed-two and optional mixed-three execution retain exact old rows,
failure and absolute cursors. The complete PRG's global exhaustion fallback is
not replaced by a local fixed four-variable fallback. Work and storage retain
the existing measured source-component scope, not full native-machine cost. -/
namespace Blotto.BinaryWordGroupCompleteMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork
set_option autoImplicit false
set_option maxHeartbeats 2000000

def collect {n m : ℕ} (store : BinarySeedLookupTree.Store)
    (drawn : (BinaryPRGWordControllerTerminal.Result store m × Trace) × ℕ)
    (emitted : (Option (FixedArrayTable n SignedWord) × Trace) × ℕ) :
    (BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ :=
  (((emitted.1.1,drawn.1.1.2),wrap 32 2 [drawn.1.2,emitted.1.2]),drawn.2+emitted.2+8)

theorem collect_bounds {n m : ℕ} (store : BinarySeedLookupTree.Store)
    (drawn : (BinaryPRGWordControllerTerminal.Result store m × Trace) × ℕ)
    (emitted : (Option (FixedArrayTable n SignedWord) × Trace) × ℕ) (P E U V : ℕ)
    (hD : drawn.2 ≤ P ∧ usage drawn.1.2 ≤ U) (hE : emitted.2 ≤ E+4 ∧ usage emitted.1.2 ≤ V+32) :
    (collect store drawn emitted).2 ≤ P+E+12 ∧ usage (collect store drawn emitted).1.2 ≤ U+V+128 := by
  have hw := wrap_usage 32 2 [drawn.1.2,emitted.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change drawn.2+emitted.2+8 ≤ _ ∧ usage (wrap 32 2 [drawn.1.2,emitted.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

set_option cleanup.letToHave false in
def uniformRunWithFactoryExtras {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ) × ℕ) × ℕ :=
  let all := BinaryWordGroupDrawMeasured.uniformRunWithFactoryExtras store input hC hAd hm K scalar pc hp
  let produced := all.1
  let drawn := produced.1
  let emitted := BinaryGroupEmissionMeasured.emitOptionWithExtras routes drawn.1.1.1
  (((collect store drawn emitted.1,produced.2),emitted.2),all.2)

def uniformRunWithRouteExtras {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ) × ℕ :=
  (uniformRunWithFactoryExtras store input hC hAd hm routes K scalar pc hp).1

theorem uniformRunWithFactoryExtras_compat {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRunWithFactoryExtras store input hC hAd hm routes K scalar pc hp).1 = uniformRunWithRouteExtras store input hC hAd hm routes K scalar pc hp := rfl

theorem uniformRunWithRouteExtras_record {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    uniformRunWithRouteExtras store input hC hAd hm routes K scalar pc hp =
  let produced := BinaryWordGroupDrawMeasured.uniformRunWithDrawExtras store input hC hAd hm K scalar pc hp
  let drawn := produced.1
  let emitted := BinaryGroupEmissionMeasured.emitOptionWithExtras routes drawn.1.1.1
  ((collect store drawn emitted.1,produced.2),emitted.2) := by
  simp only [uniformRunWithRouteExtras,uniformRunWithFactoryExtras,BinaryFourRestoredMeasured.afterOrderWithFactoryExtras_compat,BinaryFourRestoredMeasured.runWithFactoryExtras_compat,BinaryWordGroupDrawMeasured.uniformRunWithFactoryExtras_compat,BinaryWordGroupDrawMeasured.mixedTwoRunWithFactoryExtras_compat]

def uniformRunWithDrawExtras {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ :=
  (uniformRunWithRouteExtras store input hC hAd hm routes K scalar pc hp).1

theorem uniformRunWithRouteExtras_compat {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRunWithRouteExtras store input hC hAd hm routes K scalar pc hp).1 = uniformRunWithDrawExtras store input hC hAd hm routes K scalar pc hp := rfl

theorem uniformRunWithDrawExtras_record {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    uniformRunWithDrawExtras store input hC hAd hm routes K scalar pc hp =
  let produced := BinaryWordGroupDrawMeasured.uniformRunWithDrawExtras store input hC hAd hm K scalar pc hp
  let drawn := produced.1
  (collect store drawn (BinaryGroupEmissionMeasured.emitOption routes drawn.1.1.1),produced.2) := by
  simp only [uniformRunWithDrawExtras,uniformRunWithRouteExtras_record]
  rfl

def uniformRun {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ :=
  (uniformRunWithDrawExtras store input hC hAd hm routes K scalar pc hp).1

theorem uniformRunWithDrawExtras_compat {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRunWithDrawExtras store input hC hAd hm routes K scalar pc hp).1 = uniformRun store input hC hAd hm routes K scalar pc hp := rfl

theorem uniformRun_record {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    uniformRun store input hC hAd hm routes K scalar pc hp =
  let drawn := BinaryWordGroupDrawMeasured.uniformRun store input hC hAd hm K scalar pc hp
  collect store drawn (BinaryGroupEmissionMeasured.emitOption routes drawn.1.1.1) := by
  simp only [uniformRun,uniformRunWithDrawExtras_record]
  rfl

theorem uniformRun_data {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store input hC hAd hm routes K scalar pc hp).1.1 =
      (BinaryWordGroupEmissionLifetime.uniformRun store input hC hAd hm routes K scalar pc hp).1 := by
  simp only [uniformRun_record,collect,BinaryWordGroupEmissionLifetime.uniformRun,
    BinaryGroupEmissionMeasured.emitOption_data,BinaryWordGroupDrawMeasured.uniformRun_data]

def uniformPrice (n m s K i cap : ℕ) : ℕ := BinaryWordGroupDrawMeasured.uniformPrice m s K i cap+
  BinaryGroupEmissionMeasured.workEnvelope n (2*BinaryWordGroupEmissionLifetime.groupHeight s K+1)+12

def uniformEnvelope (n m s K i cap : ℕ) : ℕ := BinaryWordGroupDrawMeasured.uniformEnvelope m s K i cap+
  BinaryGroupEmissionMeasured.envelope n (2*BinaryWordGroupEmissionLifetime.groupHeight s K+1)+128

theorem uniformRun_bounds {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : UniformHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store input hC hAd hm routes K scalar pc hp).2 ≤ uniformPrice n m s K store.width store.cap.value ∧
      usage (uniformRun store input hC hAd hm routes K scalar pc hp).1.2 ≤ uniformEnvelope n m s K store.width store.cap.value := by
  let drawn := BinaryWordGroupDrawMeasured.uniformRun store input hC hAd hm K scalar pc hp
  have hDraw := And.intro (BinaryWordGroupDrawMeasured.uniformRun_work store input hC hAd hm s hs hHeight K scalar pc hp)
    (BinaryWordGroupDrawMeasured.uniformRun_usage store input hC hAd hm s hs hHeight K scalar pc hp)
  have hWidths := BinaryWordGroupEmissionMeasured.uniform_widths store input hC hAd hm routes hRoutesC s hs hHeight hRoutes K scalar pc hp
  have hRows : ∀ row,drawn.1.1.1 = some row → ∀ j,width (row.read j) ≤ 2*BinaryWordGroupEmissionLifetime.groupHeight s K+1 := by
    simpa only [drawn,BinaryWordGroupDrawMeasured.uniformRun_data] using hWidths.2
  have hE := And.intro (BinaryGroupEmissionMeasured.emitOption_work routes drawn.1.1.1 _ hWidths.1 hRows)
    (BinaryGroupEmissionMeasured.emitOption_usage routes drawn.1.1.1 _ hWidths.1 hRows)
  have hResult := collect_bounds store drawn (BinaryGroupEmissionMeasured.emitOption routes drawn.1.1.1) _ _ _ _ hDraw hE
  simp only [uniformRun_record,uniformPrice,uniformEnvelope]
  with_reducible exact hResult

def afterMixedWithRouteExtras {n m : ℕ} (store : BinarySeedLookupTree.Store) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (drawn : (BinaryPRGWordControllerTerminal.Result store (m+1) × Trace) × ℕ) : ((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ :=
  let produced := BinaryGroupEmissionMeasured.emitMixedOptionWithExtras routes pivot drawn.1.1.1
  (collect store drawn produced.1,produced.2)

def afterMixed {n m : ℕ} (store : BinarySeedLookupTree.Store) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (drawn : (BinaryPRGWordControllerTerminal.Result store (m+1) × Trace) × ℕ) :
    (BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ :=
  (afterMixedWithRouteExtras store routes pivot drawn).1

theorem afterMixedWithRouteExtras_compat {n m : ℕ} (store : BinarySeedLookupTree.Store) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (drawn : (BinaryPRGWordControllerTerminal.Result store (m+1) × Trace) × ℕ) :
    (afterMixedWithRouteExtras store routes pivot drawn).1 = afterMixed store routes pivot drawn := rfl

theorem afterMixed_record {n m : ℕ} (store : BinarySeedLookupTree.Store) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (drawn : (BinaryPRGWordControllerTerminal.Result store (m+1) × Trace) × ℕ) :
    afterMixed store routes pivot drawn =
  collect store drawn (BinaryGroupEmissionMeasured.emitMixedOption routes pivot drawn.1.1.1) := by
  dsimp only [afterMixed,afterMixedWithRouteExtras]
  rfl

theorem afterMixed_bounds {n m : ℕ} (store : BinarySeedLookupTree.Store) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (drawn : (BinaryPRGWordControllerTerminal.Result store (m+1) × Trace) × ℕ)
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2)
    (hRowsC : ∀ row,drawn.1.1.1 = some row → ∀ j,CanonicalWord (row.read j))
    (H : ℕ) (hs : 3 ≤ H) (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) H)
    (hRows : ∀ row,drawn.1.1.1 = some row → ∀ j,RationalHeight (value (row.read j)) H)
    (P U : ℕ) (hDraw : drawn.2 ≤ P ∧ usage drawn.1.2 ≤ U) :
    (afterMixed store routes pivot drawn).2 ≤ P+BinaryGroupEmissionMeasured.mixedWorkEnvelope n m H+12 ∧
      usage (afterMixed store routes pivot drawn).1.2 ≤ U+BinaryGroupEmissionMeasured.mixedEnvelope n m H+128 := by
  have hE := And.intro (BinaryGroupEmissionMeasured.emitMixedOption_work routes pivot drawn.1.1.1 hRoutesC hRowsC H hs hRoutes hRows)
    (BinaryGroupEmissionMeasured.emitMixedOption_usage routes pivot drawn.1.1.1 hRoutesC hRowsC H hs hRoutes hRows)
  exact collect_bounds store drawn _ _ _ _ _ hDraw hE

set_option cleanup.letToHave false in
def mixedTwoRunWithFactoryExtras {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ) × ℕ) × ℕ :=
  let all := BinaryWordGroupDrawMeasured.mixedTwoRunWithFactoryExtras store input hC hAd K scalar pc hp
  let produced := all.1
  let emitted := afterMixedWithRouteExtras store routes pivot produced.1
  (((emitted.1,produced.2),emitted.2),all.2)

def mixedTwoRunWithRouteExtras {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ) × ℕ :=
  (mixedTwoRunWithFactoryExtras store input hC hAd routes pivot K scalar pc hp).1

theorem mixedTwoRunWithFactoryExtras_compat {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRunWithFactoryExtras store input hC hAd routes pivot K scalar pc hp).1 = mixedTwoRunWithRouteExtras store input hC hAd routes pivot K scalar pc hp := rfl

theorem mixedTwoRunWithRouteExtras_record {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    mixedTwoRunWithRouteExtras store input hC hAd routes pivot K scalar pc hp =
  let produced := BinaryWordGroupDrawMeasured.mixedTwoRunWithDrawExtras store input hC hAd K scalar pc hp
  let emitted := afterMixedWithRouteExtras store routes pivot produced.1
  ((emitted.1,produced.2),emitted.2) := by
  simp only [mixedTwoRunWithRouteExtras,mixedTwoRunWithFactoryExtras,BinaryFourRestoredMeasured.afterOrderWithFactoryExtras_compat,BinaryFourRestoredMeasured.runWithFactoryExtras_compat,BinaryWordGroupDrawMeasured.uniformRunWithFactoryExtras_compat,BinaryWordGroupDrawMeasured.mixedTwoRunWithFactoryExtras_compat,uniformRunWithFactoryExtras_compat]

def mixedTwoRunWithDrawExtras {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ :=
  (mixedTwoRunWithRouteExtras store input hC hAd routes pivot K scalar pc hp).1

theorem mixedTwoRunWithRouteExtras_compat {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRunWithRouteExtras store input hC hAd routes pivot K scalar pc hp).1 = mixedTwoRunWithDrawExtras store input hC hAd routes pivot K scalar pc hp := rfl

theorem mixedTwoRunWithDrawExtras_record {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    mixedTwoRunWithDrawExtras store input hC hAd routes pivot K scalar pc hp =
  let produced := BinaryWordGroupDrawMeasured.mixedTwoRunWithDrawExtras store input hC hAd K scalar pc hp
  (afterMixed store routes pivot produced.1,produced.2) := by
  simp only [mixedTwoRunWithDrawExtras,mixedTwoRunWithRouteExtras_record]
  rfl

def mixedTwoRun {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ :=
  (mixedTwoRunWithDrawExtras store input hC hAd routes pivot K scalar pc hp).1

theorem mixedTwoRunWithDrawExtras_compat {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRunWithDrawExtras store input hC hAd routes pivot K scalar pc hp).1 = mixedTwoRun store input hC hAd routes pivot K scalar pc hp := rfl

theorem mixedTwoRun_record {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    mixedTwoRun store input hC hAd routes pivot K scalar pc hp =
  afterMixed store routes pivot (BinaryWordGroupDrawMeasured.mixedTwoRun store input hC hAd K scalar pc hp) := by
  simp only [mixedTwoRun,mixedTwoRunWithDrawExtras_record]
  rfl

theorem mixedTwoRun_data {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRun store input hC hAd routes pivot K scalar pc hp).1.1 =
      (BinaryWordGroupEmissionLifetime.mixedTwoRun store input hC hAd routes pivot K scalar pc hp).1 := by
  simp only [mixedTwoRun_record,afterMixed_record,collect,BinaryWordGroupEmissionLifetime.mixedTwoRun,
    BinaryGroupEmissionMeasured.emitMixedOption_data,BinaryWordGroupDrawMeasured.mixedTwoRun_data]

def mixedTwoPrice (n s K i cap : ℕ) : ℕ := BinaryWordGroupDrawMeasured.mixedPrice s K i cap+
  BinaryGroupEmissionMeasured.mixedWorkEnvelope n 2 (BinaryWordGroupEmissionLifetime.groupHeight s K)+12

def mixedTwoEnvelope (n s K i cap : ℕ) : ℕ := BinaryWordGroupDrawMeasured.mixedEnvelope s K i cap+
  BinaryGroupEmissionMeasured.mixedEnvelope n 2 (BinaryWordGroupEmissionLifetime.groupHeight s K)+128

theorem mixedTwoRun_bounds {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRun store input hC hAd routes pivot K scalar pc hp).2 ≤ mixedTwoPrice n s K store.width store.cap.value ∧
      usage (mixedTwoRun store input hC hAd routes pivot K scalar pc hp).1.2 ≤ mixedTwoEnvelope n s K store.width store.cap.value := by
  let drawn := BinaryWordGroupDrawMeasured.mixedTwoRun store input hC hAd K scalar pc hp
  have hRowsC : ∀ row,drawn.1.1.1 = some row → ∀ j,CanonicalWord (row.read j) := by
    simpa only [drawn,BinaryWordGroupDrawMeasured.mixedTwoRun_data] using
      BinaryWordGroupResult.mixedTwo_canonical store input hC hAd K scalar pc hp
  have hRows : ∀ row,drawn.1.1.1 = some row → ∀ j,RationalHeight (value (row.read j)) (BinaryWordGroupEmissionLifetime.groupHeight s K) := by
    simpa only [drawn,BinaryWordGroupDrawMeasured.mixedTwoRun_data,BinaryWordGroupEmissionLifetime.groupHeight] using
      BinaryWordGroupResult.mixedTwo_height store input hC hAd s (by omega) hHeight K scalar pc hp
  have hDraw := And.intro (BinaryWordGroupDrawMeasured.mixedTwoRun_work store input hC hAd s hs hHeight K scalar pc hp)
    (BinaryWordGroupDrawMeasured.mixedTwoRun_usage store input hC hAd s hs hHeight K scalar pc hp)
  have hResult := afterMixed_bounds store routes pivot drawn hRoutesC hRowsC _
    (hs.trans ((le_max_left _ _).trans (expressionHeightBudget_ge_input _ _)))
    (fun j => (hRoutes j).mono (BinaryWordGroupEmissionLifetime.route_height_le s K)) hRows _ _ hDraw
  simp only [mixedTwoRun_record,mixedTwoPrice,mixedTwoEnvelope]
  dsimp only [BinaryWordGroupEmissionLifetime.groupHeight]
  with_reducible exact hResult

theorem four_data (store : BinarySeedLookupTree.Store) (input : BinaryFourSpecSampler.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourRestoredMeasured.run store input hC hAd K outer scalar pc hp).1.1 =
      (BinaryFourRestoredLifetime.runWithTrace store input hC hAd K outer scalar pc hp).1 :=
  (BinaryFourRestoredMeasured.run_erasure store input hC hAd K outer scalar pc hp).trans
    (BinaryFourRestoredLifetime.runWithTrace_erasure store input hC hAd K outer scalar pc hp).symm

set_option cleanup.letToHave false in
def mixedThreeRunWithFactoryExtras {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  let factory := BinaryFourRestoredMeasured.runWithFactoryExtras store (mixedFour input) (mixedFour_canonical input hC)
    (mixedFour_admissible input hC hAd) K outer scalar pc hp
  let all := factory.1
  let produced := all.1
  let emitted := afterMixedWithRouteExtras store routes pivot produced.1
  ((((emitted.1,produced.2),emitted.2),all.2),factory.2)

def mixedThreeRunWithControlExtras {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ) × ℕ) × ℕ :=
  (mixedThreeRunWithFactoryExtras store input hC hAd routes pivot K outer scalar pc hp).1

theorem mixedThreeRunWithFactoryExtras_compat {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedThreeRunWithFactoryExtras store input hC hAd routes pivot K outer scalar pc hp).1 = mixedThreeRunWithControlExtras store input hC hAd routes pivot K outer scalar pc hp := rfl

theorem mixedThreeRunWithControlExtras_record {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    mixedThreeRunWithControlExtras store input hC hAd routes pivot K outer scalar pc hp =

  let all := BinaryFourRestoredMeasured.runWithControlExtras store (mixedFour input) (mixedFour_canonical input hC)
    (mixedFour_admissible input hC hAd) K outer scalar pc hp
  let produced := all.1
  let emitted := afterMixedWithRouteExtras store routes pivot produced.1
  (((emitted.1,produced.2),emitted.2),all.2) := by
  simp only [mixedThreeRunWithControlExtras,mixedThreeRunWithFactoryExtras,BinaryFourRestoredMeasured.afterOrderWithFactoryExtras_compat,BinaryFourRestoredMeasured.runWithFactoryExtras_compat,BinaryWordGroupDrawMeasured.uniformRunWithFactoryExtras_compat,BinaryWordGroupDrawMeasured.mixedTwoRunWithFactoryExtras_compat,uniformRunWithFactoryExtras_compat,mixedTwoRunWithFactoryExtras_compat]

def mixedThreeRunWithRouteExtras {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ) × ℕ :=
  (mixedThreeRunWithControlExtras store input hC hAd routes pivot K outer scalar pc hp).1

theorem mixedThreeRunWithControlExtras_compat {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedThreeRunWithControlExtras store input hC hAd routes pivot K outer scalar pc hp).1 = mixedThreeRunWithRouteExtras store input hC hAd routes pivot K outer scalar pc hp := rfl

theorem mixedThreeRunWithRouteExtras_record {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    mixedThreeRunWithRouteExtras store input hC hAd routes pivot K outer scalar pc hp =
  let produced := BinaryFourRestoredMeasured.runWithDrawExtras store (mixedFour input) (mixedFour_canonical input hC)
    (mixedFour_admissible input hC hAd) K outer scalar pc hp
  let emitted := afterMixedWithRouteExtras store routes pivot produced.1
  ((emitted.1,produced.2),emitted.2) := by
  simp only [mixedThreeRunWithRouteExtras,mixedThreeRunWithControlExtras_record]
  rfl

def mixedThreeRunWithDrawExtras {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ :=
  (mixedThreeRunWithRouteExtras store input hC hAd routes pivot K outer scalar pc hp).1

theorem mixedThreeRunWithRouteExtras_compat {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedThreeRunWithRouteExtras store input hC hAd routes pivot K outer scalar pc hp).1 = mixedThreeRunWithDrawExtras store input hC hAd routes pivot K outer scalar pc hp := rfl

theorem mixedThreeRunWithDrawExtras_record {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    mixedThreeRunWithDrawExtras store input hC hAd routes pivot K outer scalar pc hp =
  let produced := BinaryFourRestoredMeasured.runWithDrawExtras store (mixedFour input) (mixedFour_canonical input hC)
    (mixedFour_admissible input hC hAd) K outer scalar pc hp
  (afterMixed store routes pivot produced.1,produced.2) := by
  simp only [mixedThreeRunWithDrawExtras,mixedThreeRunWithRouteExtras_record]
  rfl

def mixedThreeRun {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ :=
  (mixedThreeRunWithDrawExtras store input hC hAd routes pivot K outer scalar pc hp).1

theorem mixedThreeRunWithDrawExtras_compat {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedThreeRunWithDrawExtras store input hC hAd routes pivot K outer scalar pc hp).1 = mixedThreeRun store input hC hAd routes pivot K outer scalar pc hp := rfl

theorem mixedThreeRun_record {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    mixedThreeRun store input hC hAd routes pivot K outer scalar pc hp =
  afterMixed store routes pivot (BinaryFourRestoredMeasured.run store (mixedFour input) (mixedFour_canonical input hC)
    (mixedFour_admissible input hC hAd) K outer scalar pc hp) := by
  simp only [mixedThreeRun,mixedThreeRunWithDrawExtras_record]
  rfl

theorem mixedThreeRun_data {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedThreeRun store input hC hAd routes pivot K outer scalar pc hp).1.1 =
      (BinaryWordMixedThreeLifetime.runWithTrace store input hC hAd routes pivot K outer scalar pc hp).1 := by
  simp only [mixedThreeRun_record,afterMixed_record,collect,BinaryWordMixedThreeLifetime.runWithTrace,
    BinaryWordMixedThreeLifetime.drawWithTrace,BinaryGroupEmissionMeasured.emitMixedOption_data,
    four_data]

def mixedThreePrice (n s K i cap : ℕ) : ℕ := BinaryFourRestoredMeasured.workEnvelope s K i cap+
  BinaryGroupEmissionMeasured.mixedWorkEnvelope n 3 (BinaryWordGroupEmissionLifetime.groupHeight s K)+12

def mixedThreeEnvelope (n s K i cap : ℕ) : ℕ := BinaryFourRestoredMeasured.envelope s K i cap+
  BinaryGroupEmissionMeasured.mixedEnvelope n 3 (BinaryWordGroupEmissionLifetime.groupHeight s K)+128

theorem mixedThreeRun_bounds {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s)
    (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedThreeRun store input hC hAd routes pivot K outer scalar pc hp).2 ≤ mixedThreePrice n s K store.width store.cap.value ∧
      usage (mixedThreeRun store input hC hAd routes pivot K outer scalar pc hp).1.2 ≤ mixedThreeEnvelope n s K store.width store.cap.value := by
  rw [mixedThreeRun_record]
  let drawn := BinaryFourRestoredMeasured.run store (mixedFour input) (mixedFour_canonical input hC)
    (mixedFour_admissible input hC hAd) K outer scalar pc hp
  have hData : drawn.1.1 = (BinaryWordMixedThreeLifetime.drawWithTrace store input hC hAd K outer scalar pc hp).1 :=
    four_data store _ _ _ K outer scalar pc hp
  have hRowsC : ∀ row,drawn.1.1.1 = some row → ∀ j,CanonicalWord (row.read j) := by
    rw [hData]
    exact BinaryWordMixedThreeLifetime.drawWithTrace_canonical store input hC hAd K outer scalar pc hp
  have hRows : ∀ row,drawn.1.1.1 = some row → ∀ j,RationalHeight (value (row.read j)) (BinaryWordGroupEmissionLifetime.groupHeight s K) := by
    rw [hData]
    exact BinaryWordMixedThreeLifetime.drawWithTrace_height store input hC hAd s (by omega) hHeight K outer scalar pc hp
  obtain ⟨source,hRef⟩ := hAd
  have hDraw := BinaryFourRestoredMeasured.run_bounds store (mixedFour input) source.fourInput (mixedFour_canonical input hC)
    (mixedFour_refines input source hRef) (mixedFour_admissible input hC ⟨source,hRef⟩) s hs
    (BinaryCachedFourParameterWork.source_four_heights input source hRef s hHeight) K outer scalar pc hp
  have hResult := afterMixed_bounds store routes pivot drawn hRoutesC hRowsC _
    (hs.trans ((le_max_left _ _).trans (expressionHeightBudget_ge_input _ _)))
    (fun j => (hRoutes j).mono (BinaryWordGroupEmissionLifetime.route_height_le s K)) hRows _ _ hDraw
  simp only [mixedThreePrice,mixedThreeEnvelope]
  dsimp only [BinaryWordGroupEmissionLifetime.groupHeight]
  with_reducible exact hResult

end Blotto.BinaryWordGroupCompleteMeasured
