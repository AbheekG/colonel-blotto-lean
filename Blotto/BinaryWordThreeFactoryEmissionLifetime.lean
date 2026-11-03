import Blotto.BinaryScalarTape
import Blotto.BinaryWordTerminalLifetimePolynomial
import Blotto.BinaryQuadraticThreeFactoryOutputLifetime

/-! The actual regular three-variable factory feeds Boolean-PC selection,
quadratic interpolation and cached-route emission. Source environment heights
derive all later weights/endpoints/rows; other factory regimes remain separate. -/
namespace Blotto.BinaryWordThreeFactoryEmissionLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinarySyntaxUniformWork BinaryThreeDescriptorCompiler
open BinaryQuadraticThreeFactoryOutputLifetime (preparedWithTrace prepared)
set_option maxHeartbeats 2000000

def uniformRun {n : ℕ} (store : BinarySeedLookupTree.Store) (env : FixedArrayTable 4 SignedWord)
    (hC : ∀ j,CanonicalWord (env.read j)) (hN : ∀ slot,0 ≤ value ((descriptor env).weight.read slot))
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (fallback : Fin 9) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerSegment.Result store n × Trace :=
  let factory := preparedWithTrace env hC hN
  let drawn := BinaryWordSegmentEmissionLifetime.uniformRun store factory.1 fallback routes K scalar pc hp
  (drawn.1,wrap 32 2 [factory.2,drawn.2])

def mixedRun {n : ℕ} (store : BinarySeedLookupTree.Store) (env : FixedArrayTable 4 SignedWord)
    (hC : ∀ j,CanonicalWord (env.read j)) (hN : ∀ slot,0 ≤ value ((descriptor env).weight.read slot))
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n) (fallback : Fin 9) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerSegment.Result store n × Trace :=
  let factory := preparedWithTrace env hC hN
  let drawn := BinaryWordSegmentEmissionLifetime.mixedRun store factory.1 fallback routes pivot K scalar pc hp
  (drawn.1,wrap 32 2 [factory.2,drawn.2])

theorem uniformRun_erasure {n : ℕ} (store : BinarySeedLookupTree.Store) (env : FixedArrayTable 4 SignedWord)
    (hC : ∀ j,CanonicalWord (env.read j)) (hN : ∀ slot,0 ≤ value ((descriptor env).weight.read slot))
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (hRC : ∀ j,CanonicalWord (routes.read j).2)
    (fallback : Fin 9) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store env hC hN routes fallback K scalar pc hp).1 =
      let drawn := BinaryPRGWordControllerSegment.run store (prepared env hC hN) fallback K scalar pc hp
      (drawn.1.map (BinaryGroupRoutes.emit routes),drawn.2) := by
  unfold uniformRun
  dsimp only
  rw [BinaryWordSegmentEmissionLifetime.uniformRun_erasure _ _ _ _ hRC,
    BinaryQuadraticThreeFactoryOutputLifetime.preparedWithTrace_erases]

theorem mixedRun_erasure {n : ℕ} (store : BinarySeedLookupTree.Store) (env : FixedArrayTable 4 SignedWord)
    (hC : ∀ j,CanonicalWord (env.read j)) (hN : ∀ slot,0 ≤ value ((descriptor env).weight.read slot))
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n) (hRC : ∀ j,CanonicalWord (routes.read j).2)
    (fallback : Fin 9) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedRun store env hC hN routes pivot fallback K scalar pc hp).1 =
      let drawn := BinaryPRGWordControllerSegment.run store (prepared env hC hN) fallback K scalar pc hp
      (drawn.1.map (BinaryGroupRoutes.emitMixed routes pivot),drawn.2) := by
  unfold mixedRun
  dsimp only
  rw [BinaryWordSegmentEmissionLifetime.mixedRun_erasure _ _ _ _ _ hRC,
    BinaryQuadraticThreeFactoryOutputLifetime.preparedWithTrace_erases]

def uniformEnvelope (n s K indexWidth seedCap : ℕ) : ℕ :=
  BinaryQuadraticThreeFactoryLifetime.bound s + BinaryQuadraticThreeFactoryLifetime.frames s +
    BinaryWordSegmentEmissionBound.uniformEnvelope n 3 9 (expressionHeightBudget s 16) K indexWidth seedCap + 64

def mixedEnvelope (n s K indexWidth seedCap : ℕ) : ℕ :=
  BinaryQuadraticThreeFactoryLifetime.bound s + BinaryQuadraticThreeFactoryLifetime.frames s +
    BinaryWordSegmentEmissionBound.mixedEnvelope n 2 9 (expressionHeightBudget s 16) K indexWidth seedCap + 64

theorem uniformRun_usage {n : ℕ} (store : BinarySeedLookupTree.Store) (env : FixedArrayTable 4 SignedWord)
    (hC : ∀ j,CanonicalWord (env.read j)) (hN : ∀ slot,0 ≤ value ((descriptor env).weight.read slot))
    (source : RationalSegmentLottery 3 9) (hR : (descriptor env).Refines source)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (hRC : ∀ j,CanonicalWord (routes.read j).2)
    (s : ℕ) (hs : 3 ≤ s) (hEnv : EnvHeight env s) (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) s)
    (fallback : Fin 9) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (uniformRun store env hC hN routes fallback K scalar pc hp).2 ≤ uniformEnvelope n s K store.width store.cap.value := by
  let factory := preparedWithTrace env hC hN
  have hFactory := BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace_bounds env hC s hs hEnv
  have hF : usage factory.2 ≤ BinaryQuadraticThreeFactoryLifetime.bound s + BinaryQuadraticThreeFactoryLifetime.frames s := by
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    exact Nat.add_le_add hFactory.1 hFactory.2
  have hHeight := BinaryThreeFactoryWork.descriptor_height env hC s hs hEnv
  have hWeight : ∀ slot,RationalHeight (source.weight slot) (expressionHeightBudget s 16) := by
    intro slot; rw [← hR.1 slot]; exact hHeight.1 slot
  have hEndpoints : ∀ slot j,RationalHeight (source.P slot j) (expressionHeightBudget s 16) ∧
      RationalHeight (source.Q slot j) (expressionHeightBudget s 16) := by
    intro slot j; rw [← hR.2.1 slot j,← hR.2.2 slot j]; exact hHeight.2 slot j
  have hFR : factory.1.table.Refines source := by
    dsimp only [factory]
    rw [BinaryQuadraticThreeFactoryOutputLifetime.preparedWithTrace_erases]
    exact hR
  have hDraw := BinaryWordSegmentEmissionBound.uniformRun_usage store factory.1 fallback source hFR routes hRC
    (expressionHeightBudget s 16) (hs.trans (expressionHeightBudget_ge_input s 16))
    (fun j => (hRoutes j).mono (expressionHeightBudget_ge_input s 16)) hWeight hEndpoints K scalar pc hp
  have hw := wrap_usage 32 2 [factory.2,(BinaryWordSegmentEmissionLifetime.uniformRun store factory.1 fallback routes K scalar pc hp).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [factory.2,(BinaryWordSegmentEmissionLifetime.uniformRun store factory.1 fallback routes K scalar pc hp).2]) ≤ _
  unfold uniformEnvelope
  omega

theorem mixedRun_usage {n : ℕ} (store : BinarySeedLookupTree.Store) (env : FixedArrayTable 4 SignedWord)
    (hC : ∀ j,CanonicalWord (env.read j)) (hN : ∀ slot,0 ≤ value ((descriptor env).weight.read slot))
    (source : RationalSegmentLottery 3 9) (hR : (descriptor env).Refines source)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n) (hRC : ∀ j,CanonicalWord (routes.read j).2)
    (s : ℕ) (hs : 3 ≤ s) (hEnv : EnvHeight env s) (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) s)
    (fallback : Fin 9) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (mixedRun store env hC hN routes pivot fallback K scalar pc hp).2 ≤ mixedEnvelope n s K store.width store.cap.value := by
  let factory := preparedWithTrace env hC hN
  have hFactory := BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace_bounds env hC s hs hEnv
  have hF : usage factory.2 ≤ BinaryQuadraticThreeFactoryLifetime.bound s + BinaryQuadraticThreeFactoryLifetime.frames s := by
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    exact Nat.add_le_add hFactory.1 hFactory.2
  have hHeight := BinaryThreeFactoryWork.descriptor_height env hC s hs hEnv
  have hWeight : ∀ slot,RationalHeight (source.weight slot) (expressionHeightBudget s 16) := by
    intro slot; rw [← hR.1 slot]; exact hHeight.1 slot
  have hEndpoints : ∀ slot j,RationalHeight (source.P slot j) (expressionHeightBudget s 16) ∧
      RationalHeight (source.Q slot j) (expressionHeightBudget s 16) := by
    intro slot j; rw [← hR.2.1 slot j,← hR.2.2 slot j]; exact hHeight.2 slot j
  have hFR : factory.1.table.Refines source := by
    dsimp only [factory]
    rw [BinaryQuadraticThreeFactoryOutputLifetime.preparedWithTrace_erases]
    exact hR
  have hDraw := BinaryWordSegmentEmissionBound.mixedRun_usage store factory.1 fallback source hFR routes pivot hRC
    (expressionHeightBudget s 16) (hs.trans (expressionHeightBudget_ge_input s 16))
    (fun j => (hRoutes j).mono (expressionHeightBudget_ge_input s 16)) hWeight hEndpoints K scalar pc hp
  have hw := wrap_usage 32 2 [factory.2,(BinaryWordSegmentEmissionLifetime.mixedRun store factory.1 fallback routes pivot K scalar pc hp).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [factory.2,(BinaryWordSegmentEmissionLifetime.mixedRun store factory.1 fallback routes pivot K scalar pc hp).2]) ≤ _
  unfold mixedEnvelope
  omega

end Blotto.BinaryWordThreeFactoryEmissionLifetime
