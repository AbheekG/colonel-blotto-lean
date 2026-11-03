import Blotto.BinaryThreeFactoryLifetime
import Blotto.BinaryStoredSegmentLifetime

/-! Concrete regular-three factory-to-selected-draw lifetime composition.
The traced factory's actual table is retained by the categorical/point runner.
Its original environment heights and checked ASTs derive every selected
weight/endpoint height; no intermediate-height or execution trace is supplied.
Exact native table/row/none/absolute-position correspondence is proved.
This endpoint covers a regular-three continuation, not the full mixed-three
reflected/nested regimes or original-field route/output/request lifetimes. -/
set_option autoImplicit false
namespace Blotto.BinaryThreeFactoryDrawLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinarySyntaxUniformWork BinaryStoredSegmentProgram BinaryThreeDescriptorCompiler

def prepared (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot)) : Prepared 3 9 :=
  ⟨descriptor env,descriptor_canonical env hC,hN⟩

def preparedWithTrace (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot)) : Prepared 3 9×Trace :=
  let factory := BinaryThreeFactoryLifetime.descriptorWithTrace env
  (⟨factory.1,(by rw [BinaryThreeFactoryLifetime.descriptorWithTrace_erases]; exact descriptor_canonical env hC),
    (by rw [BinaryThreeFactoryLifetime.descriptorWithTrace_erases]; exact hN)⟩,factory.2)

@[simp] theorem preparedWithTrace_erases (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot)) :
    (preparedWithTrace env hC hN).1=prepared env hC hN := by
  unfold preparedWithTrace prepared
  simp only [BinaryThreeFactoryLifetime.descriptorWithTrace_erases]

def runWithTrace (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot))
    (fallback : Fin 9) (K N : ℕ) (scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    (Option (FixedArrayTable 3 SignedWord)×ℕ)×Trace :=
  let factory := preparedWithTrace env hC hN
  let drawn := BinaryStoredSegmentLifetime.runWithTrace factory.1 fallback K N scalar bits pos hp
  (drawn.1,[.frames 2,.arrayAllocation 8] ++ under 2 factory.2 ++ under 2 drawn.2)

@[simp] theorem runWithTrace_erases (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot))
    (fallback : Fin 9) (K N : ℕ) (scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    (runWithTrace env hC hN fallback K N scalar bits pos hp).1=
      (prepared env hC hN).runIndexed fallback K N scalar bits pos hp := by
  simp only [runWithTrace,BinaryStoredSegmentLifetime.runWithTrace_erases,preparedWithTrace_erases]

def bound (s K remaining : ℕ) : ℕ := BinaryThreeFactoryLifetime.bound s+
  BinaryStoredSegmentLifetime.bound 3 9 (expressionHeightBudget s 16) K remaining+8

def frames (s K remaining : ℕ) : ℕ := 307+
  BinaryStoredSegmentLifetime.frames 3 9 (expressionHeightBudget s 16) K remaining

theorem runWithTrace_bounds (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot))
    (source : RationalSegmentLottery 3 9) (hR : (descriptor env).Refines source)
    (s : ℕ) (hs : 3≤s) (hH : EnvHeight env s)
    (fallback : Fin 9) (K N : ℕ) (scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    listCells (runWithTrace env hC hN fallback K N scalar bits pos hp).2+
      arraySlots (runWithTrace env hC hN fallback K N scalar bits pos hp).2 ≤ bound s K (N-pos) ∧
    framePeak (runWithTrace env hC hN fallback K N scalar bits pos hp).2 ≤ frames s K (N-pos) := by
  have hFactory := BinaryThreeFactoryLifetime.descriptorWithTrace_bounds env hC s hs hH
  have hFactoryFrames := framePeak_under 2 (preparedWithTrace env hC hN).2
  have hHeight := BinaryThreeFactoryWork.descriptor_height env hC s hs hH
  have hWeight : ∀ slot,RationalHeight (source.weight slot) (expressionHeightBudget s 16) := by
    intro slot; rw [← hR.1 slot]; exact hHeight.1 slot
  have hEndpoint : ∀ slot j,RationalHeight (source.P slot j) (expressionHeightBudget s 16) ∧
      RationalHeight (source.Q slot j) (expressionHeightBudget s 16) := by
    intro slot j; rw [← hR.2.1 slot j,← hR.2.2 slot j]; exact hHeight.2 slot j
  have hPreparedR : (preparedWithTrace env hC hN).1.table.Refines source := by
    rw [preparedWithTrace_erases]; exact hR
  have hDraw := BinaryStoredSegmentLifetime.runWithTrace_bounds (preparedWithTrace env hC hN).1 source hPreparedR
    (expressionHeightBudget s 16) (hs.trans (expressionHeightBudget_ge_input s 16)) hWeight hEndpoint
    fallback K N scalar bits pos hp
  have hDrawFrames := framePeak_under 2 (BinaryStoredSegmentLifetime.runWithTrace
    (preparedWithTrace env hC hN).1 fallback K N scalar bits pos hp).2
  change listCells (preparedWithTrace env hC hN).2+arraySlots (preparedWithTrace env hC hN).2 ≤
    BinaryThreeFactoryLifetime.bound s ∧ framePeak (preparedWithTrace env hC hN).2 ≤ 303 at hFactory
  unfold runWithTrace bound frames
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

theorem runWithTrace_position (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot))
    (fallback : Fin 9) (K N : ℕ) (scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    pos≤(runWithTrace env hC hN fallback K N scalar bits pos hp).1.2 ∧
    (runWithTrace env hC hN fallback K N scalar bits pos hp).1.2≤N :=
  BinaryStoredSegmentLifetime.runWithTrace_position _ fallback K N scalar bits pos hp

theorem all_prefix_heap (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot))
    (source : RationalSegmentLottery 3 9) (hR : (descriptor env).Refines source)
    (s : ℕ) (hs : 3≤s) (hH : EnvHeight env s)
    (fallback : Fin 9) (K N : ℕ) (scalar : Fin K→Bool) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N)
    (borrowedInputCells originalSeedCells steps : ℕ) :
    retainedHeap (borrowedInputCells+originalSeedCells)
      (runWithTrace env hC hN fallback K N scalar bits pos hp).2 steps ≤
      borrowedInputCells+originalSeedCells+bound s K (N-pos) := by
  have hb := (runWithTrace_bounds env hC hN source hR s hs hH fallback K N scalar bits pos hp).1
  have hl := listCells_take_le (runWithTrace env hC hN fallback K N scalar bits pos hp).2 steps
  have ha := arraySlots_take_le (runWithTrace env hC hN fallback K N scalar bits pos hp).2 steps
  unfold retainedHeap
  omega

end Blotto.BinaryThreeFactoryDrawLifetime
