import Blotto.BinaryPRGWordControllerThreeResourceWork
import Blotto.BinaryPRGWordControllerBooleanResourceThreeWork
import Blotto.BinaryReflectedSetupWork

/-! The executed reflected setup includes its actual parameter/system
production and both syntactic native capacity producers. The reached resource
source builds one cached Boolean capacity/resource tree pair, initializes Boolean
identifiers and executes the selected Boolean tree/coin loop. Native output
materialization and its capped index decoding have derived prices.  Fixed table accesses,
control cells and conservative copy cells remain in the declared source model.
This source does not assume that duplicate capacity expressions are shared. -/

namespace Blotto.BinaryPRGWordControllerReflectedSetupWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryReflectedFourSetup BinaryThreeResourceHeight
open BinaryPRGWordControllerResourceWork (total)

def initialCells (capacity resource : FixedArrayTable 3 SignedWord) : ℕ :=
  total (BinaryGeneralResourceExecution.scanWithCharge capacity resource (List.finRange 3)).2 + 4

theorem initialCells_bound (capacity resource : FixedArrayTable 3 SignedWord) (W : ℕ) (hW : 1 ≤ W)
    (hC : ∀ j, width (capacity.read j) ≤ W) (hR : ∀ j, width (resource.read j) ≤ W) :
    initialCells capacity resource ≤ 3 * (1000 * (W + 1)^2) + 26 := by
  obtain ⟨hb,hr,hw,hl,hcopy⟩ := BinaryGeneralResourceExecution.scanWithCharge_bound capacity resource
    (List.finRange 3) W hW hC hR
  simp only [List.length_finRange] at hb hr hw hl hcopy
  unfold initialCells total
  omega

/-- Pure `prepare` computes this same scale inside each initial coordinate.
The measured system factory charges one evaluation; these two additional
prices account for the other two actual source evaluations. -/
def extraScaleWork (input : BinaryFourParameters.Input) : ℕ :=
  let parameters := BinaryFourParameters.prepare input
  2 * (BinaryRationalOpcode.applyWithWork .mul (parameters.read 6) (parameters.read 5)).2

def extraScaleBound (s : ℕ) : ℕ := 2 * (12000 * (2 + 4 * expressionHeightBudget s 12)^3)

theorem extraScaleWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    extraScaleWork input ≤ extraScaleBound s := by
  let T := expressionHeightBudget s 12
  have hParameters : ∀ j,RationalHeight (value ((BinaryFourParameters.prepare input).read j)) T := by
    intro j
    rw [BinaryFourParameters.prepare_value input source hC hR]
    exact hH.scalar hs j
  have hw : ∀ j,width ((BinaryFourParameters.prepare input).read j) ≤ 1 + 4 * T := by
    intro j
    exact (BinaryFourParameters.prepare_canonical input hC j).2.trans
      ((rationalWordWidth_of_height (hParameters j)).trans (by omega))
  have hp := BinaryPRGPreparationWork.operation_uniform_bound .mul _ _ (1 + 4 * T) (hw 6) (hw 5)
  unfold extraScaleWork extraScaleBound
  dsimp only
  exact Nat.mul_le_mul_left 2 (by simpa only [show 1 + 4 * T + 1 = 2 + 4 * T by omega] using hp)

def run (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity × ℕ :=
  let prepared := prepare input
  let drawn := BinaryPRGWordControllerBooleanResourceThreeWork.sourceRun store prepared.capacity prepared.initial
    (capacity_canonical prepared (prepare_canonical input hC)) (prepare_canonical input hC).2.2.2 pc hp
  (drawn.1, (BinaryReflectedSetupWork.prepareWithWork input).2 + extraScaleWork input +
    2 * (BinaryReflectedSetupWork.capacityWithWork prepared).2 + drawn.2 + 4)

theorem run_erasure (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC pc hp).1 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp := by
  unfold run BinaryPRGWordControllerThreeResource.setupIndexed
  dsimp only
  exact BinaryPRGWordControllerBooleanResourceThreeWork.sourceRun_erasure _ _ _ _ _ _ _

def bound (s indexWidth remaining : ℕ) : ℕ :=
  BinaryReflectedSetupWork.bound s + extraScaleBound s +
    2 * (3 * (12000 * (2 + 2 * expressionHeightBudget s 14)^3)) +
      3 * (1000 * (2 + 2 * expressionHeightBudget s 15)^2) + 30 +
        BinaryPRGWordControllerThreeResourceWork.bound 2 (expressionHeightBudget s 15) indexWidth 3 remaining +
          BinaryPRGWordControllerBooleanResourceThreeWork.sourceBound (expressionHeightBudget s 15) indexWidth remaining

theorem run_bound (store : Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC pc hp).2 ≤ bound s store.width (store.cap.value - pc.value) := by
  have hSetup := BinaryReflectedSetupWork.prepareWithWork_bound input source hC hR s hs hH
  have hScale := extraScaleWork_bound input source hC hR s hs hH
  have hCapacity := BinaryReflectedSetupWork.actual_capacityWithWork_bound input source hC hR hCase s hs hH
  have hCap := BinaryReflectedResourceWork.capacity_height input source hC hR hCase s hs hH
  have hInitial := BinaryReflectedResourceWork.initial_resource_height input source hC hR hCase s hs hH
  have hRun := BinaryPRGWordControllerBooleanResourceThreeWork.sourceRun_bound (expressionHeightBudget s 15)
    (hs.trans (expressionHeightBudget_ge_input s 15)) store (prepare input).capacity (prepare input).initial
    (capacity_canonical _ (prepare_canonical input hC)) (prepare_canonical input hC).2.2.2 hCap hInitial pc hp
  unfold run bound
  dsimp only
  omega

end Blotto.BinaryPRGWordControllerReflectedSetupWork
