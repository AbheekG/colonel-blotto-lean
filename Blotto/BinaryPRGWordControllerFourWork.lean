import Blotto.BinaryPRGWordControllerReflectedWork
import Blotto.BinarySmallUniformFactoryDraw
import Blotto.BinaryGluingDrawWork
import Blotto.BinaryFourNativeOrderWork

/-! All ordered four branches join the actual source factory, concrete Store
root/categorical work and selected interpolation/emission backend.  Reflected
production includes the reached duplicate profile.  Source height bounds are
derived from the original six fields; no primitive-price oracle is supplied.
The declared source ledger keeps logical fixed-table/control/copy visits;
complete physical-address/compiler/space interpretation remains separate. -/

namespace Blotto.BinaryPRGWordControllerFourWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding

theorem smallPrepared_state (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) :
    (BinarySmallUniformFactoryDraw.preparedWithWork input hC hAd).1 =
      BinaryPRGWordControllerFour.uniformPrepared input hC hAd := by
  rw [BinarySmallUniformFactoryDraw.preparedWithWork_state]
  rfl

def uniformRun (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerFour.Result store × ℕ :=
  let factory := BinarySmallUniformFactoryDraw.preparedWithWork input hC hAd
  let drawn := BinaryPRGWordControllerWork.segmentWithWork store factory.1 0 K scalar pc hp
  (drawn.1, factory.2 + drawn.2 + 20)

theorem uniformRun_erasure (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store input hC hAd K scalar pc hp).1 =
      BinaryPRGWordControllerSegment.run store (BinaryPRGWordControllerFour.uniformPrepared input hC hAd) 0 K scalar pc hp := by
  unfold uniformRun
  dsimp only
  rw [BinaryPRGWordControllerWork.segmentWithWork_erasure, smallPrepared_state]

def uniformBound (s K indexWidth remaining : ℕ) : ℕ :=
  BinarySmallUniformFactoryWork.bound s + BinaryPRGWordControllerWork.segmentBound 4 9
    (expressionHeightBudget s 35) K indexWidth remaining + 20

theorem uniformRun_bound (store : Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinarySmallRootSample.Admissible input)
    (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store input hC hAd K scalar pc hp).2 ≤ uniformBound s K store.width (store.cap.value - pc.value) := by
  let prepared := (BinarySmallUniformFactoryDraw.preparedWithWork input hC hAd).1
  have hPrepared := smallPrepared_state input hC hAd
  have hRef := BinarySmallUniformCompiler.fromOriginal_refines input source hC hR hCase
  have hHeight := hH.smallUniformLottery hs hCase
  have hRTable : prepared.table.Refines (source.smallUniformLottery hCase) := by
    dsimp only [prepared]
    rw [hPrepared]
    exact hRef
  have hDraw := BinaryPRGWordControllerWork.segmentWithWork_bound store prepared (source.smallUniformLottery hCase)
    hRTable (expressionHeightBudget s 35) (hs.trans (expressionHeightBudget_ge_input s 35)) hHeight.1
    (fun slot j => by rw [hRTable.2.1 slot j, hRTable.2.2 slot j]; exact hHeight.2 slot j)
    0 K scalar pc hp
  have hFactory := BinarySmallUniformFactoryWork.fromOriginalWithWork_bound input source hC hR hCase s hs hH
  unfold uniformRun uniformBound
  dsimp only
  change (BinarySmallUniformFactoryWork.fromOriginalWithWork input).2 +
    (BinaryPRGWordControllerWork.segmentWithWork store prepared 0 K scalar pc hp).2 + 20 ≤ _
  omega

def gluingRun (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerFour.Result store × ℕ :=
  let prepared := BinaryGluingSampler.prepare input hC hAd
  let drawn := BinaryPRGWordControllerWork.segmentWithWork store
    ⟨prepared.table, prepared.canonical, prepared.nonnegative⟩ 0 K scalar pc hp
  (drawn.1, BinaryFourParentCompiler.descriptorWork input + drawn.2 + 20)

theorem gluingRun_erasure (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (gluingRun store input hC hAd K scalar pc hp).1 =
      let prepared := BinaryGluingSampler.prepare input hC hAd
      BinaryPRGWordControllerSegment.run store ⟨prepared.table, prepared.canonical, prepared.nonnegative⟩ 0 K scalar pc hp := by
  unfold gluingRun
  dsimp only
  exact BinaryPRGWordControllerWork.segmentWithWork_erasure _ _ _ _ _ _ _

def gluingBound (s K indexWidth remaining : ℕ) : ℕ :=
  BinaryFourParentCompiler.workBound s + BinaryPRGWordControllerWork.segmentBound 4 81
    (expressionHeightBudget s 36) K indexWidth remaining + 20

theorem gluingRun_bound (store : Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryGluingSampler.Admissible input)
    (hCase : (1 - source.p) * source.ell ≤ source.w) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (gluingRun store input hC hAd K scalar pc hp).2 ≤ gluingBound s K store.width (store.cap.value - pc.value) := by
  have hTable := BinaryGluingSampler.prepare_refines input source hC hAd hR hCase
  have hHeight := hH.gluingDescriptor hs hCase
  have hDescriptor := BinaryFourParentCompiler.descriptorWork_bound input source hC hR hCase s hs hH
  let prepared := BinaryGluingSampler.prepare input hC hAd
  let table : BinaryStoredSegmentProgram.Prepared 4 81 := ⟨prepared.table, prepared.canonical, prepared.nonnegative⟩
  have hDraw := BinaryPRGWordControllerWork.segmentWithWork_bound store table (source.gluingDescriptor hCase)
    hTable (expressionHeightBudget s 36) (hs.trans (expressionHeightBudget_ge_input s 36)) hHeight.1
    (fun slot j => by rw [hTable.2.1 slot j, hTable.2.2 slot j]; exact hHeight.2 slot j)
    0 K scalar pc hp
  unfold gluingRun gluingBound
  dsimp only
  change BinaryFourParentCompiler.descriptorWork input +
    (BinaryPRGWordControllerWork.segmentWithWork store table 0 K scalar pc hp).2 + 20 ≤ _
  omega

def root (store : Store) (input : BinaryFourParameters.Input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (Option Bool × FixedBinaryWord store.width) × ℕ :=
  let probability := BinaryQuadraticNormalization.canonicalizeWithWork input.p
  let selected := BinaryWordIndexCoinController.sample store probability.1 pc hp
  (selected.1, probability.2 + selected.2 + 2)

theorem root_erasure (store : Store) (input : BinaryFourParameters.Input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (root store input pc hp).1 = BinaryPRGWordControllerDataCoin.sample store (BinaryPRGWordControllerFour.probability input) pc hp := by
  unfold root BinaryPRGWordControllerFour.probability
  dsimp only
  rw [BinaryQuadraticData.canonicalize_erasure, BinaryPRGWordControllerDataCoin.sample_erasure]

def rootBound (s indexWidth remaining : ℕ) : ℕ :=
  600 * (2 * s + 2)^2 + 12 * (2 * s + 2) +
    BinaryWordIndexCoinController.allowance (1 + 2 * s) indexWidth * (remaining + 1) + 2

theorem root_bound (store : Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (root store input pc hp).2 ≤ rootBound s store.width (store.cap.value - pc.value) := by
  have hpHeight : RationalHeight (value input.p) s := by rw [hR.2.2.2.2.2]; exact hH.2.2.2.2.2
  have hWidth := hC.2.2.2.2.2.2.trans (rationalWordWidth_of_height hpHeight)
  have hNormalize := (BinaryQuadraticNormalization.canonicalizeWithWork_bound input.p).trans
    (Nat.mul_le_mul_left 600 (Nat.pow_le_pow_left (Nat.add_le_add_right hWidth 1) 2))
  have hProbability : width (BinaryQuadraticNormalization.canonicalizeWithWork input.p).1 ≤ 1 + 2 * s := by
    rw [BinaryQuadraticNormalization.canonicalizeWithWork_state input.p hC.2.2.2.2.2.1]
    exact (BinaryPRGPreparationWork.canonicalize_stored_width input.p).trans hWidth
  have hCoin := BinaryPRGWordControllerCoinConsumption.sample_bound store
    (BinaryQuadraticNormalization.canonicalizeWithWork input.p).1 pc hp
  have hPosition := BinaryWordIndexCoinController.sample_position_bounds store
    (BinaryQuadraticNormalization.canonicalizeWithWork input.p).1 pc hp
  have hSpan := Nat.sub_le_sub_right hPosition.2 pc.value
  unfold root rootBound
  dsimp only
  have hCoin' : (BinaryWordIndexCoinController.sample store
      (BinaryQuadraticNormalization.canonicalizeWithWork input.p).1 pc hp).2 ≤
      12 * (2 * s + 2) + BinaryWordIndexCoinController.allowance (1 + 2 * s) store.width *
        (store.cap.value - pc.value + 1) := by
    apply hCoin.trans
    have hPadding : 12 * (width (BinaryQuadraticNormalization.canonicalizeWithWork input.p).1 + 1) ≤
        12 * (2 * s + 2) := by omega
    have hAllowance : BinaryWordIndexCoinController.allowance
        (width (BinaryQuadraticNormalization.canonicalizeWithWork input.p).1) store.width ≤
        BinaryWordIndexCoinController.allowance (1 + 2 * s) store.width := by
      unfold BinaryWordIndexCoinController.allowance
      omega
    exact Nat.add_le_add hPadding (Nat.mul_le_mul hAllowance (Nat.add_le_add_right hSpan 1))
  have hNormalize' : (BinaryQuadraticNormalization.canonicalizeWithWork input.p).2 ≤ 600 * (2 * s + 2)^2 := by
    simpa only [show 1 + 2 * s + 1 = 2 * s + 2 by omega] using hNormalize
  omega

theorem uniformBound_span_mono (s K indexWidth : ℕ) {first second : ℕ} (h : first ≤ second) :
    uniformBound s K indexWidth first ≤ uniformBound s K indexWidth second := by
  unfold uniformBound BinaryPRGWordControllerWork.segmentBound BinaryPRGWordControllerWork.selectionBound
  dsimp only
  gcongr

theorem reflectedBound_span_mono (s K indexWidth : ℕ) {first second : ℕ} (h : first ≤ second) :
    BinaryPRGWordControllerReflectedWork.bound s K indexWidth first ≤
      BinaryPRGWordControllerReflectedWork.bound s K indexWidth second := by
  unfold BinaryPRGWordControllerReflectedWork.bound BinaryPRGWordControllerReflectedWork.selectionBound
    BinaryPRGWordControllerReflectedSetupWork.bound
    BinaryPRGWordControllerBooleanResourceThreeWork.sourceBound BinaryPRGWordControllerBooleanResourceThreeWork.sourceEnvelope
    BinaryPRGWordControllerBooleanResourceThreeWork.bound BinaryPRGWordControllerThreeResourceWork.bound
    BinaryPRGWordControllerWork.selectionBound
  dsimp only
  gcongr

def smallRun (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerFour.Result store × ℕ :=
  let chosen := root store input pc hp
  have hPosition : chosen.1.2.value ≤ store.cap.value := by
    rw [root_erasure]
    exact (BinaryPRGWordControllerDataCoin.sample_position store (BinaryPRGWordControllerFour.probability input) pc hp).2
  match chosen.1.1 with
  | none => ((none, chosen.1.2), chosen.2 + 2)
  | some true =>
      let drawn := uniformRun store input hC hAd K scalar chosen.1.2 hPosition
      (drawn.1, chosen.2 + drawn.2 + 2)
  | some false =>
      let drawn := BinaryPRGWordControllerReflectedWork.run store input hC hAd K outer scalar chosen.1.2 hPosition
      (drawn.1, chosen.2 + drawn.2 + 2)

set_option maxHeartbeats 1000000 in
theorem smallRun_erasure (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (smallRun store input hC hAd K outer scalar pc hp).1 = BinaryPRGWordControllerFour.smallRun store input hC hAd K outer scalar pc hp := by
  unfold smallRun BinaryPRGWordControllerFour.smallRun
  dsimp only
  simp only [root_erasure]
  split
  · rename_i hNone
    simp only [hNone]
  · rename_i hTrue
    simp only [hTrue]
    exact uniformRun_erasure _ _ _ _ _ _ _ _
  · rename_i hFalse
    simp only [hFalse]
    exact BinaryPRGWordControllerReflectedWork.run_erasure _ _ _ _ _ _ _ _ _

def smallBound (s K indexWidth remaining : ℕ) : ℕ := rootBound s indexWidth remaining +
  uniformBound s K indexWidth remaining + BinaryPRGWordControllerReflectedWork.bound s K indexWidth remaining + 2

theorem smallRun_bound (store : Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinarySmallRootSample.Admissible input)
    (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (smallRun store input hC hAd K outer scalar pc hp).2 ≤ smallBound s K store.width (store.cap.value - pc.value) := by
  have hRoot := root_bound store input source hC hR s hH pc hp
  have hPosition := BinaryPRGWordControllerDataCoin.sample_position store (BinaryPRGWordControllerFour.probability input) pc hp
  rw [← root_erasure] at hPosition
  have hRemaining := Nat.sub_le_sub_left hPosition.1 store.cap.value
  unfold smallRun
  dsimp only
  split
  · unfold smallBound; omega
  · have hDraw := (uniformRun_bound store input source hC hR hAd hCase s hs hH K scalar
        (root store input pc hp).1.2 hPosition.2).trans (uniformBound_span_mono s K store.width hRemaining)
    unfold smallBound
    omega
  · have hDraw := (BinaryPRGWordControllerReflectedWork.run_bound store input source hC hR hCase hAd s hs hH K outer scalar
        (root store input pc hp).1.2 hPosition.2).trans (reflectedBound_span_mono s K store.width hRemaining)
    unfold smallBound
    omega

def run (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerFour.Result store × ℕ :=
  let guard := BinaryFourNativeOrderWork.guardWithWork input
  if hg : guard.1 = true then
    let drawn := gluingRun store input hC (BinaryFourAdmissibility.gluing_guard input hC hAd
      ((BinaryFourNativeOrderWork.guardWithWork_state input).symm.trans hg)) K scalar pc hp
    (drawn.1, guard.2 + drawn.2 + 2)
  else
    let drawn := smallRun store input hC (BinaryFourAdmissibility.small_guard input hC hAd
      (fun h => hg ((BinaryFourNativeOrderWork.guardWithWork_state input).trans h))) K outer scalar pc hp
    (drawn.1, guard.2 + drawn.2 + 2)

set_option maxHeartbeats 1000000 in
theorem run_erasure (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1 = BinaryPRGWordControllerFour.run store input hC hAd K outer scalar pc hp := by
  unfold run BinaryPRGWordControllerFour.run
  dsimp only
  simp only [BinaryFourNativeOrderWork.guardWithWork_state]
  split
  · rename_i hg
    simp only
    exact gluingRun_erasure _ _ _ _ _ _ _ _
  · rename_i hg
    simp only
    exact smallRun_erasure _ _ _ _ _ _ _ _ _

def runBound (s K indexWidth remaining : ℕ) : ℕ := BinaryFourNativeOrderWork.guardBound (max s 3) +
  gluingBound s K indexWidth remaining + smallBound s K indexWidth remaining + 2

theorem run_bound (store : Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourAdmissibility.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).2 ≤ runBound s K store.width (store.cap.value - pc.value) := by
  have hGuard := BinaryFourOrderedRetainedWork.guard_bound input source hC hR s hH
  unfold run
  dsimp only
  split
  · rename_i hg
    have hOld := (BinaryFourNativeOrderWork.guardWithWork_state input).symm.trans hg
    have hCase := (BinaryFourParentCompiler.gluingCase_iff input source hC hR).mp hOld
    have hDraw := gluingRun_bound store input source hC hR (BinaryFourAdmissibility.gluing_guard input hC hAd hOld)
      hCase s hs hH K scalar pc hp
    unfold runBound
    omega
  · rename_i hg
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := fun h => hg
      ((BinaryFourNativeOrderWork.guardWithWork_state input).trans h)
    have hCase : source.w < (1 - source.p) * source.ell := lt_of_not_ge (fun h => hOld
      ((BinaryFourParentCompiler.gluingCase_iff input source hC hR).mpr h))
    have hDraw := smallRun_bound store input source hC hR (BinaryFourAdmissibility.small_guard input hC hAd hOld)
      hCase s hs hH K outer scalar pc hp
    unfold runBound
    omega

def restoredRun (store : Store) (input : BinaryFourSpecSampler.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerFour.Result store × ℕ :=
  let ordered := BinaryFourSpecRetainedWork.prepareOrdered input hC hAd
  let drawn := run store ordered.ordered ordered.canonical ordered.admissible K outer scalar pc hp
  match drawn.1.1 with
  | none => ((none, drawn.1.2), ordered.orderWork + drawn.2 + 2)
  | some row =>
      ((some (FixedArrayTable.ofFn (fun j => row.read (BinaryFourSpecSampler.permutation input j))), drawn.1.2),
        5 * ordered.orderWork + drawn.2 + 20)

/- The actual restored caller recomputes the original permutation inside each
of the four selected output coordinates.  Its annotation includes five sorts:
one for ordering and four for reached inverse restoration. -/
theorem restoredRun_erasure (store : Store) (input : BinaryFourSpecSampler.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (restoredRun store input hC hAd K outer scalar pc hp).1 = BinaryPRGWordControllerFour.restoredRun store input hC hAd K outer scalar pc hp := by
  unfold restoredRun BinaryPRGWordControllerFour.restoredRun
  dsimp only
  rw [run_erasure]
  have hOrdered := (BinaryFourSpecRetainedWork.prepareOrdered input hC hAd).ordered_correct
  simp only [hOrdered]
  split
  · rename_i hNone
    simp only [hNone, Option.map_none]
  · rename_i row hRow
    simp only [hRow, Option.map_some]

def restoredBound (s K indexWidth remaining : ℕ) : ℕ := 15 * BinaryFactoryHeight.compareBound s +
  runBound s K indexWidth remaining + 20

theorem restoredRun_bound (store : Store) (input : BinaryFourSpecSampler.Input) (source : RationalFourSpec)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (restoredRun store input hC hAd K outer scalar pc hp).2 ≤ restoredBound s K store.width (store.cap.value - pc.value) := by
  let ordered := BinaryFourSpecRetainedWork.prepareOrdered input hC hAd
  have hOrder := BinaryFourSpecRetainedWork.prepareOrdered_bound input source hC hR hAd s hH
  have hRef : ordered.ordered.Refines source.input := by
    rw [ordered.ordered_correct]
    exact BinaryFourSpecSampler.orderedInput_refines input source hC hR
  have hDraw := run_bound store ordered.ordered source.input ordered.canonical hRef ordered.admissible
    s hs hH.input K outer scalar pc hp
  unfold restoredRun
  dsimp only
  split <;> unfold restoredBound <;> dsimp only [ordered] at hDraw <;> omega

end Blotto.BinaryPRGWordControllerFourWork
