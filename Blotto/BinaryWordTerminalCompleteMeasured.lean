import Blotto.BinaryWordGroupCompleteMeasured
import Blotto.BinaryWordTerminalEmissionMeasured
import Blotto.BinaryWordTerminalLifetime

/-! Complete cached terminal dispatch executes measured factories, optional
categorical/physical-point draws and measured route emission in every regime.
Actual returned cache fields and cursors are consumed once. Source work and
retained storage are joined; native-machine and global fallback joins remain. -/

namespace Blotto.BinaryWordTerminalCompleteMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryCachedTerminalPreparation BinaryCachedThreeDescriptorWork BinaryGroupInputs BinaryGroupSamplers
set_option autoImplicit false
set_option maxHeartbeats 3500000

def branch {α : Type*} (drawn : (α × Trace) × ℕ) : (α × Trace) × ℕ :=
  ((drawn.1.1,wrap 24 2 [wrap 32 2 [drawn.1.2]]),drawn.2+16)

set_option cleanup.letToHave false in
def drawTwoWithFactoryExtras {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ) × ℕ) × ℕ :=
  by
  subst m
  exact BinaryWordGroupCompleteMeasured.mixedTwoRunWithFactoryExtras store input hC hAd routes pivot K scalar pc hp

def drawTwoWithRouteExtras {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ) × ℕ :=
  (drawTwoWithFactoryExtras store input hC hAd hTwo routes pivot K scalar pc hp).1

theorem drawTwoWithFactoryExtras_compat {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawTwoWithFactoryExtras store input hC hAd hTwo routes pivot K scalar pc hp).1 = drawTwoWithRouteExtras store input hC hAd hTwo routes pivot K scalar pc hp := rfl

theorem drawTwoWithRouteExtras_record {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    drawTwoWithRouteExtras store input hC hAd hTwo routes pivot K scalar pc hp =
  by
  subst m
  exact BinaryWordGroupCompleteMeasured.mixedTwoRunWithRouteExtras store input hC hAd routes pivot K scalar pc hp := by
  subst m
  rfl

def drawTwoWithDrawExtras {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ :=
  (drawTwoWithRouteExtras store input hC hAd hTwo routes pivot K scalar pc hp).1

theorem drawTwoWithRouteExtras_compat {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawTwoWithRouteExtras store input hC hAd hTwo routes pivot K scalar pc hp).1 = drawTwoWithDrawExtras store input hC hAd hTwo routes pivot K scalar pc hp := rfl

theorem drawTwoWithDrawExtras_record {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    drawTwoWithDrawExtras store input hC hAd hTwo routes pivot K scalar pc hp =
  by
  subst m
  exact BinaryWordGroupCompleteMeasured.mixedTwoRunWithDrawExtras store input hC hAd routes pivot K scalar pc hp := by
  subst m
  rfl

def drawTwo {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ :=
  (drawTwoWithDrawExtras store input hC hAd hTwo routes pivot K scalar pc hp).1

theorem drawTwoWithDrawExtras_compat {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawTwoWithDrawExtras store input hC hAd hTwo routes pivot K scalar pc hp).1 = drawTwo store input hC hAd hTwo routes pivot K scalar pc hp := rfl

theorem drawTwo_record {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    drawTwo store input hC hAd hTwo routes pivot K scalar pc hp = by
  subst m
  exact BinaryWordGroupCompleteMeasured.mixedTwoRun store input hC hAd routes pivot K scalar pc hp := by
  subst m
  rfl

theorem drawTwo_data {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawTwo store input hC hAd hTwo routes pivot K scalar pc hp).1.1 =
      (BinaryWordMixedTwoTerminalLifetime.drawWithTrace store input hC hAd hTwo routes pivot K scalar pc hp).1 := by
  subst m
  exact BinaryWordGroupCompleteMeasured.mixedTwoRun_data store input hC hAd routes pivot K scalar pc hp

set_option cleanup.letToHave false in
def drawThreeWithFactoryExtras {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  by
  subst m
  exact BinaryWordGroupCompleteMeasured.mixedThreeRunWithFactoryExtras store input hC hAd routes pivot K outer scalar pc hp

def drawThreeWithControlExtras {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ) × ℕ) × ℕ :=
  (drawThreeWithFactoryExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1

theorem drawThreeWithFactoryExtras_compat {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawThreeWithFactoryExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1 = drawThreeWithControlExtras store input hC hAd hThree routes pivot K outer scalar pc hp := rfl

theorem drawThreeWithControlExtras_record {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    drawThreeWithControlExtras store input hC hAd hThree routes pivot K outer scalar pc hp =

  by
  subst m
  exact BinaryWordGroupCompleteMeasured.mixedThreeRunWithControlExtras store input hC hAd routes pivot K outer scalar pc hp := by
  subst m
  rfl

def drawThreeWithRouteExtras {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ) × ℕ :=
  (drawThreeWithControlExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1

theorem drawThreeWithControlExtras_compat {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawThreeWithControlExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1 = drawThreeWithRouteExtras store input hC hAd hThree routes pivot K outer scalar pc hp := rfl

theorem drawThreeWithRouteExtras_record {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    drawThreeWithRouteExtras store input hC hAd hThree routes pivot K outer scalar pc hp =
  by
  subst m
  exact BinaryWordGroupCompleteMeasured.mixedThreeRunWithRouteExtras store input hC hAd routes pivot K outer scalar pc hp := by
  subst m
  rfl

def drawThreeWithDrawExtras {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ :=
  (drawThreeWithRouteExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1

theorem drawThreeWithRouteExtras_compat {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawThreeWithRouteExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1 = drawThreeWithDrawExtras store input hC hAd hThree routes pivot K outer scalar pc hp := rfl

theorem drawThreeWithDrawExtras_record {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    drawThreeWithDrawExtras store input hC hAd hThree routes pivot K outer scalar pc hp =
  by
  subst m
  exact BinaryWordGroupCompleteMeasured.mixedThreeRunWithDrawExtras store input hC hAd routes pivot K outer scalar pc hp := by
  subst m
  rfl

def drawThree {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ :=
  (drawThreeWithDrawExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1

theorem drawThreeWithDrawExtras_compat {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawThreeWithDrawExtras store input hC hAd hThree routes pivot K outer scalar pc hp).1 = drawThree store input hC hAd hThree routes pivot K outer scalar pc hp := rfl

theorem drawThree_record {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    drawThree store input hC hAd hThree routes pivot K outer scalar pc hp = by
  subst m
  exact BinaryWordGroupCompleteMeasured.mixedThreeRun store input hC hAd routes pivot K outer scalar pc hp := by
  subst m
  rfl

theorem drawThree_data {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawThree store input hC hAd hThree routes pivot K outer scalar pc hp).1.1 =
      (BinaryWordMixedThreeTerminalLifetime.drawWithTrace store input hC hAd hThree routes pivot K outer scalar pc hp).1 := by
  subst m
  exact BinaryWordGroupCompleteMeasured.mixedThreeRun_data store input hC hAd routes pivot K outer scalar pc hp

set_option cleanup.letToHave false in
def runWithFactoryExtras {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  match hPivot : prepared.pivot with
  | none =>
      let factory := BinaryWordGroupCompleteMeasured.uniformRunWithFactoryExtras store prepared.uniform (prepared.uniform_canonical hC)
        (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot)
        (prepared.count_bound hC hAd) prepared.routes K scalar pc hp
      let produced := factory.1
      ((((branch produced.1.1,produced.1.2),produced.2),0),factory.2)
  | some selected =>
      if hTwo : prepared.count = 2 then
        let factory := drawTwoWithFactoryExtras store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
          (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
          hTwo prepared.routes selected K scalar pc hp
        let produced := factory.1
        ((((branch produced.1.1,produced.1.2),produced.2),0),factory.2)
      else
        let factory := drawThreeWithFactoryExtras store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
          (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
          ((prepared.count_bound hC hAd).resolve_left hTwo) prepared.routes selected K outer scalar pc hp
        let all := factory.1
        let produced := all.1
        ((((branch produced.1.1,produced.1.2),produced.2),all.2),factory.2)

def runWithControlExtras {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ) × ℕ) × ℕ :=
  (runWithFactoryExtras store prepared hC hAd K outer scalar pc hp).1

theorem runWithFactoryExtras_compat {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store prepared hC hAd K outer scalar pc hp).1 = runWithControlExtras store prepared hC hAd K outer scalar pc hp := rfl

theorem runWithControlExtras_record {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    runWithControlExtras store prepared hC hAd K outer scalar pc hp =



  match hPivot : prepared.pivot with
  | none =>
      let produced := BinaryWordGroupCompleteMeasured.uniformRunWithRouteExtras store prepared.uniform (prepared.uniform_canonical hC)
        (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot)
        (prepared.count_bound hC hAd) prepared.routes K scalar pc hp
      (((branch produced.1.1,produced.1.2),produced.2),0)
  | some selected =>
      if hTwo : prepared.count = 2 then
        let produced := drawTwoWithRouteExtras store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
          (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
          hTwo prepared.routes selected K scalar pc hp
        (((branch produced.1.1,produced.1.2),produced.2),0)
      else
        let all := drawThreeWithControlExtras store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
          (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
          ((prepared.count_bound hC hAd).resolve_left hTwo) prepared.routes selected K outer scalar pc hp
        let produced := all.1
        (((branch produced.1.1,produced.1.2),produced.2),all.2) := by
  simp only [runWithControlExtras,runWithFactoryExtras,BinaryWordGroupCompleteMeasured.uniformRunWithFactoryExtras_compat,BinaryWordGroupCompleteMeasured.mixedTwoRunWithFactoryExtras_compat,BinaryWordGroupCompleteMeasured.mixedThreeRunWithFactoryExtras_compat,drawTwoWithFactoryExtras_compat,drawThreeWithFactoryExtras_compat]
  split <;> first | rfl | (split <;> rfl)

def runWithRouteExtras {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ) × ℕ :=
  (runWithControlExtras store prepared hC hAd K outer scalar pc hp).1

theorem runWithControlExtras_compat {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithControlExtras store prepared hC hAd K outer scalar pc hp).1 = runWithRouteExtras store prepared hC hAd K outer scalar pc hp := rfl

theorem runWithRouteExtras_record {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    runWithRouteExtras store prepared hC hAd K outer scalar pc hp =


  match hPivot : prepared.pivot with
  | none =>
      let produced := BinaryWordGroupCompleteMeasured.uniformRunWithRouteExtras store prepared.uniform (prepared.uniform_canonical hC)
        (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot)
        (prepared.count_bound hC hAd) prepared.routes K scalar pc hp
      ((branch produced.1.1,produced.1.2),produced.2)
  | some selected =>
      if hTwo : prepared.count = 2 then
        let produced := drawTwoWithRouteExtras store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
          (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
          hTwo prepared.routes selected K scalar pc hp
        ((branch produced.1.1,produced.1.2),produced.2)
      else
        let produced := drawThreeWithRouteExtras store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
          (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
          ((prepared.count_bound hC hAd).resolve_left hTwo) prepared.routes selected K outer scalar pc hp
        ((branch produced.1.1,produced.1.2),produced.2) := by
  simp only [runWithRouteExtras,runWithControlExtras_record]
  split
  · rfl
  · split <;> rfl

def runWithDrawExtras {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ) × ℕ :=
  (runWithRouteExtras store prepared hC hAd K outer scalar pc hp).1

theorem runWithRouteExtras_compat {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithRouteExtras store prepared hC hAd K outer scalar pc hp).1 = runWithDrawExtras store prepared hC hAd K outer scalar pc hp := rfl

theorem runWithDrawExtras_record {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    runWithDrawExtras store prepared hC hAd K outer scalar pc hp =

  match hPivot : prepared.pivot with
  | none =>
      let produced := BinaryWordGroupCompleteMeasured.uniformRunWithDrawExtras store prepared.uniform (prepared.uniform_canonical hC)
        (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot)
        (prepared.count_bound hC hAd) prepared.routes K scalar pc hp
      (branch produced.1,produced.2)
  | some selected =>
      if hTwo : prepared.count = 2 then
        let produced := drawTwoWithDrawExtras store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
          (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
          hTwo prepared.routes selected K scalar pc hp
        (branch produced.1,produced.2)
      else
        let produced := drawThreeWithDrawExtras store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
          (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
          ((prepared.count_bound hC hAd).resolve_left hTwo) prepared.routes selected K outer scalar pc hp
        (branch produced.1,produced.2) := by
  simp only [runWithDrawExtras,runWithRouteExtras_record]
  split
  · rfl
  · split <;> rfl

def run {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerTerminal.Result store n × Trace) × ℕ :=
  (runWithDrawExtras store prepared hC hAd K outer scalar pc hp).1

theorem runWithDrawExtras_compat {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithDrawExtras store prepared hC hAd K outer scalar pc hp).1 = run store prepared hC hAd K outer scalar pc hp := rfl

theorem run_record {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    run store prepared hC hAd K outer scalar pc hp =
  match hPivot : prepared.pivot with
  | none => branch (BinaryWordGroupCompleteMeasured.uniformRun store prepared.uniform (prepared.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot)
      (prepared.count_bound hC hAd) prepared.routes K scalar pc hp)
  | some selected =>
      if hTwo : prepared.count = 2 then
        branch (drawTwo store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
          (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
          hTwo prepared.routes selected K scalar pc hp)
      else
        branch (drawThree store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
          (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
          ((prepared.count_bound hC hAd).resolve_left hTwo) prepared.routes selected K outer scalar pc hp) := by
  simp only [run,runWithDrawExtras_record]
  split
  · rfl
  · split <;> rfl

theorem run_data {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store prepared hC hAd K outer scalar pc hp).1.1 =
      (BinaryWordTerminalLifetime.runWithTrace store prepared hC hAd K outer scalar pc hp).1 := by
  rw [BinaryWordTerminalLifetime.runWithTrace_erasure]
  simp only [run_record]
  split
  · rename_i hPivot
    exact (BinaryWordGroupCompleteMeasured.uniformRun_data store prepared.uniform (prepared.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot)
      (prepared.count_bound hC hAd) prepared.routes K scalar pc hp).trans
      (BinaryWordUniformTerminalLifetime.runWithTrace_erasure store prepared hC hAd hPivot K outer scalar pc hp)
  · rename_i selected hPivot
    split
    · rename_i hTwo
      exact (drawTwo_data store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        hTwo prepared.routes selected K scalar pc hp).trans
        (BinaryWordMixedTwoTerminalLifetime.runWithTrace_erasure store prepared hC hAd hTwo selected hPivot K outer scalar pc hp)
    · rename_i hTwo
      exact (drawThree_data store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        ((prepared.count_bound hC hAd).resolve_left hTwo) prepared.routes selected K outer scalar pc hp).trans
        (BinaryWordMixedThreeTerminalLifetime.runWithTrace_erasure store prepared hC hAd
          ((prepared.count_bound hC hAd).resolve_left hTwo) selected hPivot K outer scalar pc hp)

theorem branch_bounds {α : Type*} (drawn : (α × Trace) × ℕ) (P U : ℕ)
    (h : drawn.2 ≤ P ∧ usage drawn.1.2 ≤ U) :
    (branch drawn).2 ≤ P+16 ∧ usage (branch drawn).1.2 ≤ U+64 := by
  have hi := wrap_usage 32 2 [drawn.1.2]
  have ho := wrap_usage 24 2 [wrap 32 2 [drawn.1.2]]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hi ho
  change drawn.2+16 ≤ _ ∧ usage (wrap 24 2 [wrap 32 2 [drawn.1.2]]) ≤ _
  exact ⟨by omega,by omega⟩

theorem drawTwo_bounds {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s)
    (hHeight : MixedHeights input s) (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawTwo store input hC hAd hTwo routes pivot K scalar pc hp).2 ≤
      BinaryWordGroupCompleteMeasured.mixedTwoPrice n s K store.width store.cap.value ∧
    usage (drawTwo store input hC hAd hTwo routes pivot K scalar pc hp).1.2 ≤
      BinaryWordGroupCompleteMeasured.mixedTwoEnvelope n s K store.width store.cap.value := by
  subst m
  exact BinaryWordGroupCompleteMeasured.mixedTwoRun_bounds store input hC hAd routes pivot hRoutesC s hs hHeight hRoutes K scalar pc hp

theorem drawThree_bounds {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (hRoutesC : ∀ j,CanonicalWord (routes.read j).2) (s : ℕ) (hs : 3 ≤ s)
    (hHeight : MixedHeights input s) (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (drawThree store input hC hAd hThree routes pivot K outer scalar pc hp).2 ≤
      BinaryWordGroupCompleteMeasured.mixedThreePrice n s K store.width store.cap.value ∧
    usage (drawThree store input hC hAd hThree routes pivot K outer scalar pc hp).1.2 ≤
      BinaryWordGroupCompleteMeasured.mixedThreeEnvelope n s K store.width store.cap.value := by
  subst m
  exact BinaryWordGroupCompleteMeasured.mixedThreeRun_bounds store input hC hAd routes pivot hRoutesC s hs hHeight hRoutes K outer scalar pc hp

def workEnvelope (n s K i cap : ℕ) : ℕ :=
  BinaryWordGroupCompleteMeasured.uniformPrice n 2 s K i cap+BinaryWordGroupCompleteMeasured.uniformPrice n 3 s K i cap+
    BinaryWordGroupCompleteMeasured.mixedTwoPrice n s K i cap+BinaryWordGroupCompleteMeasured.mixedThreePrice n s K i cap+32

def envelope (n s K i cap : ℕ) : ℕ :=
  BinaryWordGroupCompleteMeasured.uniformEnvelope n 2 s K i cap+BinaryWordGroupCompleteMeasured.uniformEnvelope n 3 s K i cap+
    BinaryWordGroupCompleteMeasured.mixedTwoEnvelope n s K i cap+BinaryWordGroupCompleteMeasured.mixedThreeEnvelope n s K i cap+256

theorem uniform_sums (n m s K i cap : ℕ) (hm : m = 2 ∨ m = 3) :
    BinaryWordGroupCompleteMeasured.uniformPrice n m s K i cap ≤
      BinaryWordGroupCompleteMeasured.uniformPrice n 2 s K i cap+BinaryWordGroupCompleteMeasured.uniformPrice n 3 s K i cap ∧
    BinaryWordGroupCompleteMeasured.uniformEnvelope n m s K i cap ≤
      BinaryWordGroupCompleteMeasured.uniformEnvelope n 2 s K i cap+BinaryWordGroupCompleteMeasured.uniformEnvelope n 3 s K i cap := by
  rcases hm with rfl | rfl <;> exact ⟨by omega,by omega⟩

theorem run_bounds {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hUniform : UniformHeights prepared.uniform s)
    (hMixed : ∀ selected,prepared.pivot = some selected → MixedHeights prepared.mixed s)
    (hRoutes : ∀ j,RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store prepared hC hAd K outer scalar pc hp).2 ≤ workEnvelope n s K store.width store.cap.value ∧
      usage (run store prepared hC hAd K outer scalar pc hp).1.2 ≤ envelope n s K store.width store.cap.value := by
  have hRC := BinaryCachedTerminalPromises.Prepared.routes_canonical prepared hC
  simp only [run_record]
  split
  · rename_i hPivot
    have hDraw := BinaryWordGroupCompleteMeasured.uniformRun_bounds store prepared.uniform (prepared.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hPivot)
      (prepared.count_bound hC hAd) prepared.routes hRC s hs hUniform hRoutes K scalar pc hp
    have hBranch := branch_bounds _ _ _ hDraw
    have hDim := uniform_sums n prepared.count s K store.width store.cap.value (prepared.count_bound hC hAd)
    unfold workEnvelope envelope
    exact ⟨by omega,by omega⟩
  · rename_i selected hPivot
    split
    · rename_i hTwo
      have hDraw := drawTwo_bounds store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        hTwo prepared.routes selected hRC s hs (hMixed selected hPivot) hRoutes K scalar pc hp
      have hBranch := branch_bounds _ _ _ hDraw
      unfold workEnvelope envelope
      exact ⟨by omega,by omega⟩
    · rename_i hNot
      have hDraw := drawThree_bounds store prepared.mixed (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        ((prepared.count_bound hC hAd).resolve_left hNot) prepared.routes selected hRC s hs
        (hMixed selected hPivot) hRoutes K outer scalar pc hp
      have hBranch := branch_bounds _ _ _ hDraw
      unfold workEnvelope envelope
      exact ⟨by omega,by omega⟩

theorem run_erasure {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store prepared hC hAd K outer scalar pc hp).1.1 =
      BinaryPRGWordControllerTerminal.runPrepared store prepared hC hAd K outer scalar pc hp := by
  rw [run_data]
  exact BinaryWordTerminalLifetime.runWithTrace_erasure store prepared hC hAd K outer scalar pc hp

theorem run_position {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store prepared hC hAd K outer scalar pc hp).1.1.2.value ∧
      (run store prepared hC hAd K outer scalar pc hp).1.1.2.value ≤ store.cap.value := by
  rw [run_data]
  exact BinaryWordTerminalLifetime.runWithTrace_position store prepared hC hAd K outer scalar pc hp

theorem all_prefix {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hUniform : UniformHeights prepared.uniform s)
    (hMixed : ∀ selected,prepared.pivot = some selected → MixedHeights prepared.mixed s)
    (hRoutes : ∀ j,RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (run store prepared hC hAd K outer scalar pc hp).1.2 steps ≤
      borrowed+envelope n s K store.width store.cap.value ∧
    framePeak ((run store prepared hC hAd K outer scalar pc hp).1.2.take steps) ≤ envelope n s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (run_bounds store prepared hC hAd s hs hUniform hMixed hRoutes K outer scalar pc hp).2 borrowed steps

end Blotto.BinaryWordTerminalCompleteMeasured

