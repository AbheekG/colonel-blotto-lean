import Blotto.BinaryThreeResourceRunWork
import Blotto.BinaryReflectedSetupWork
import Blotto.BinaryCachedFourBranchWork

/-! Actual original six-word reflected inputs derive initial/capacity heights
for the measured initial scan and shared-cap resource loop. C=2 bounds the
local phase. Result, none and absolute position equal the old setup runner.
The ledger records scan/resource primitive work; setup factory, terminal,
bookkeeping/metadata and physical compiler/ownership joins remain separate. -/

namespace Blotto.BinaryReflectedResourceWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinaryThreeResourcePair BinarySharedResourceRun BinaryThreeResourceHeight
open BinaryGeneralResourceExecution

def initialWithCharge (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (hR : ∀ j, CanonicalWord (resource.read j)) : Certified capacity × Charge :=
  let scan := scanWithCharge capacity resource (List.finRange 3)
  (⟨⟨resource,scan.1⟩, hR,
    (by rw [scanWithCharge_state]; exact (List.nodup_finRange 3).filter _),
    (by intro j; rw [scanWithCharge_state]; simp [List.mem_finRange,
      BinaryResourceState.fractional_iff capacity resource hC hR j])⟩,
    scan.2.add ⟨0,0,0,4,0⟩)

theorem initialWithCharge_state (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (hR : ∀ j, CanonicalWord (resource.read j)) :
    (initialWithCharge capacity resource hC hR).1 = initial capacity resource hC hR := by
  unfold initialWithCharge initial BinaryThreeResourceState.initial
  simp only [scanWithCharge_state]
  rfl

theorem initialWithCharge_bound (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (hR : ∀ j, CanonicalWord (resource.read j)) (W : ℕ)
    (hW : 1 ≤ W) (hCap : ∀ j, width (capacity.read j) ≤ W) (hResource : ∀ j, width (resource.read j) ≤ W) :
    (initialWithCharge capacity resource hC hR).2.booleanWork ≤ 3000 * (W + 1) ^ 2 := by
  have hScan := (scanWithCharge_bound capacity resource (List.finRange 3) W hW hCap hResource).1
  simp only [List.length_finRange] at hScan
  dsimp only [initialWithCharge,Charge.add]
  simp only [Nat.add_zero]
  exact hScan.trans_eq (by ring)

def runWithCharge (input : BinaryFourParameters.Input) (hC : input.Canonical) (N : ℕ) (bits : Fin N → Bool) :
    (Option (Certified (prepare input).capacity) × ℕ) × Charge :=
  let system := prepare input
  let initial := initialWithCharge system.capacity system.initial (capacity_canonical system (prepare_canonical input hC))
    (prepare_canonical input hC).2.2.2
  let later := BinaryThreeResourceRunWork.runIndexed N bits
    (.ready initial.1 : Cursor system.capacity (capacity_canonical system (prepare_canonical input hC))) 0 (Nat.zero_le N)
  (later.1, initial.2.add later.2)

theorem runWithCharge_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (N : ℕ) (bits : Fin N → Bool) :
    (runWithCharge input hC N bits).1 = setupRun input hC N bits := by
  unfold runWithCharge
  dsimp only
  rw [initialWithCharge_state, BinaryThreeResourceRunWork.runIndexed_state]
  rfl

theorem capacity_height (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (j : Fin 3) :
    RationalHeight (value ((prepare input).capacity.read j)) (expressionHeightBudget s 15) := by
  rw [capacity_value _ _ (prepare_canonical input hC) (prepare_refines input source hC hR hCase)]
  have h := (hH.reflectedResourceSystem hs hCase).capacity j
  rw [expressionHeightBudget_comp] at h
  exact h

theorem initial_resource_height (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (j : Fin 3) :
    RationalHeight (value ((prepare input).initial.read j)) (expressionHeightBudget s 15) := by
  rw [(prepare_refines input source hC hR hCase).2.2.2 j]
  exact ((hH.reflectedResourceSystem hs hCase).2.2.2 j).mono (expressionHeightBudget_mono s (by decide : 14 ≤ 15))

def bound (s N : ℕ) : ℕ :=
  3000 * (2 + 2 * expressionHeightBudget s 15) ^ 2 +
    2 * BinaryThreeResourceRunWork.pairTotalBound 2 (expressionHeightBudget s 15) +
      N * BinaryThreeResourceRunWork.bodyBound 2 (expressionHeightBudget s 15)

theorem runWithCharge_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool) :
    (runWithCharge input hC N bits).2.booleanWork ≤ bound s N := by
  let system := prepare input
  let hc := capacity_canonical system (prepare_canonical input hC)
  let hr := (prepare_canonical input hC).2.2.2
  let initial := initialWithCharge system.capacity system.initial hc hr
  have hCapacity := fun j => capacity_height input source hC hR hCase s hs hH j
  have hResource := fun j => initial_resource_height input source hC hR hCase s hs hH j
  have hWCap := fun j => (hc j).2.trans (rationalWordWidth_of_height (hCapacity j))
  have hWResource := fun j => (hr j).2.trans (rationalWordWidth_of_height (hResource j))
  have hScan := (scanWithCharge_bound system.capacity system.initial (List.finRange 3)
    (1 + 2 * expressionHeightBudget s 15) (by omega) hWCap hWResource).1
  simp only [List.length_finRange, show 1 + 2 * expressionHeightBudget s 15 + 1 = 2 + 2 * expressionHeightBudget s 15 by omega] at hScan
  have hInitial : StateHeight system.capacity 2 (expressionHeightBudget s 15) initial.1 := by
    rw [initialWithCharge_state]
    exact initial_height system.capacity system.initial hc hr _ hResource
  have hLoop := BinaryThreeResourceRunWork.runIndexed_bound 2 (expressionHeightBudget s 15)
    (hs.trans (expressionHeightBudget_ge_input s 15)) hCapacity N bits
    (.ready initial.1 : Cursor system.capacity hc) 0 (Nat.zero_le N) hInitial
  have hLength : initial.1.state.active.length - 1 ≤ 2 := hInitial.1
  simp only [BinaryThreeResourceRunWork.allowance, Nat.sub_zero] at hLoop
  have hScale := Nat.mul_le_mul_right (BinaryThreeResourceRunWork.pairTotalBound 2 (expressionHeightBudget s 15)) hLength
  have hInitialPrice := initialWithCharge_bound system.capacity system.initial hc hr
    (1 + 2 * expressionHeightBudget s 15) (by omega) hWCap hWResource
  simp only [show 1 + 2 * expressionHeightBudget s 15 + 1 = 2 + 2 * expressionHeightBudget s 15 by omega] at hInitialPrice
  change initial.2.booleanWork ≤ 3000 * (2 + 2 * expressionHeightBudget s 15) ^ 2 at hInitialPrice
  change initial.2.booleanWork + (BinaryThreeResourceRunWork.runIndexed N bits
    (.ready initial.1 : Cursor system.capacity hc) 0 (Nat.zero_le N)).2.booleanWork ≤ bound s N
  unfold bound
  omega

def runIndexedWithCharge (input : BinaryFourParameters.Input) (hC : input.Canonical) (N : ℕ) (bits : Fin N → Bool)
    (pos : ℕ) (hp : pos ≤ N) : (Option (Certified (prepare input).capacity) × ℕ) × Charge :=
  let later := runWithCharge input hC (N - pos) (WordStateMachine.inputWindow bits pos (N - pos) (by omega))
  ((later.1.1,pos + later.1.2),later.2)

theorem runIndexedWithCharge_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (N : ℕ) (bits : Fin N → Bool)
    (pos : ℕ) (hp : pos ≤ N) :
    (runIndexedWithCharge input hC N bits pos hp).1 =
      let later := setupRun input hC (N - pos) (WordStateMachine.inputWindow bits pos (N - pos) (by omega))
      (later.1,pos + later.2) := by
  unfold runIndexedWithCharge
  dsimp only
  rw [runWithCharge_state]

theorem runIndexedWithCharge_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (runIndexedWithCharge input hC N bits pos hp).2.booleanWork ≤ bound s (N - pos) :=
  runWithCharge_bound input source hC hR hCase s hs hH (N - pos) _

theorem checked_bound (checked : BinaryCachedFourBranchWork.Checked) (s : ℕ) (hs : 2 ≤ s)
    (hH : BinaryCachedThreeDescriptorWork.MixedHeights checked.input s)
    (hGuard : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true) (N : ℕ) (bits : Fin N → Bool) :
    (runWithCharge checked.ordered checked.ordered_canonical N bits).2.booleanWork ≤ bound s N := by
  obtain ⟨source,hr⟩ := checked.admissible
  have hR := BinaryFourSpecSampler.orderedInput_refines (BinaryGroupInputs.mixedFour checked.input) source.fourInput
    (BinaryGroupInputs.mixedFour_canonical checked.input checked.canonical) (BinaryGroupInputs.mixedFour_refines checked.input source hr)
  have hHeight := (BinaryCachedFourParameterWork.source_four_heights checked.input source hr s hH).input
  have hCase := lt_of_not_ge (fun he => hGuard ((BinaryFourParentCompiler.gluingCase_iff checked.ordered source.fourInput.input
    checked.ordered_canonical hR).mpr he))
  exact runWithCharge_bound checked.ordered source.fourInput.input checked.ordered_canonical hR hCase s hs hHeight N bits

theorem cached_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (BinaryPRGResourceWork.resourceInput request rich).length)
    (h : (BinaryPRGResourceWork.resourceWork request rich N bits).1.1 = some state)
    (hCount : (BinaryCachedTerminalPreparation.prepare (BinaryPRGTerminalWork.terminalInput request rich state)).count = 3)
    (selected : Fin n)
    (hPivot : (BinaryCachedTerminalPreparation.prepare (BinaryPRGTerminalWork.terminalInput request rich state)).pivot = some selected)
    (hGuard : ¬BinaryFourParentCompiler.gluingCase
      (BinaryCachedFourBranchWork.cached request rich N bits state h hCount selected hPivot).ordered = true) :
    (runWithCharge (BinaryCachedFourBranchWork.cached request rich N bits state h hCount selected hPivot).ordered
      (BinaryCachedFourBranchWork.cached request rich N bits state h hCount selected hPivot).ordered_canonical N bits).2.booleanWork ≤
        bound (BinaryCachedGroupInputHeight.inputHeight request) N :=
  checked_bound _ _ (BinaryCachedGroupInputHeight.inputHeight_two request)
    (BinaryCachedFourBranchWork.cached_heights request rich N bits state h hCount selected hPivot) hGuard N bits

end Blotto.BinaryReflectedResourceWork
