import Blotto.BinaryScalarTape
import Blotto.BinaryQuadraticThreeFactoryLifetime
import Blotto.BinaryQuadraticSegmentOutputLifetime

/-! Concrete regular-three quadratic factory-to-original-budget-frame lifetime composition.
The traced factory's actual table is retained by the categorical/point runner.
Its original environment heights and checked ASTs derive every selected
weight/endpoint height; no intermediate-height or execution trace is supplied.
Exact native table/frame/none/absolute-position correspondence is proved.
This endpoint covers a regular-three continuation, not the full mixed-three
reflected/nested regimes or original-field route/request lifetimes. -/
set_option autoImplicit false
namespace Blotto.BinaryQuadraticThreeFactoryOutputLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinarySyntaxUniformWork BinaryStoredSegmentProgram BinaryThreeDescriptorCompiler
open scoped BigOperators

def prepared (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot)) : Prepared 3 9 :=
  ⟨descriptor env,descriptor_canonical env hC,hN⟩

def preparedWithTrace (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot)) : Prepared 3 9×Trace :=
  let factory := BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace env
  (⟨factory.1,(by rw [BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace_erases env hC]; exact descriptor_canonical env hC),
    (by rw [BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace_erases env hC]; exact hN)⟩,factory.2)

@[simp] theorem preparedWithTrace_erases (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot)) :
    (preparedWithTrace env hC hN).1=prepared env hC hN := by
  unfold preparedWithTrace prepared
  simp only [BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace_erases env hC]

def runWithTrace (budget : SignedWord) (header : List Bool) (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot))
    (fallback : Fin 9) (K N : ℕ) (scalar : BinaryScalarTape K) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    (Option (List Bool)×ℕ)×Trace :=
  let factory := preparedWithTrace env hC hN
  let drawn := BinaryQuadraticSegmentOutputLifetime.runWithTrace budget header factory.1 fallback K N scalar bits pos hp
  (drawn.1,[.frames 2,.arrayAllocation 8] ++ under 2 factory.2 ++ under 2 drawn.2)

@[simp] theorem runWithTrace_erases (budget : SignedWord) (header : List Bool) (hB : BinaryRationalOpcode.Valid budget) (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot))
    (fallback : Fin 9) (K N : ℕ) (scalar : BinaryScalarTape K) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    (runWithTrace budget header env hC hN fallback K N scalar bits pos hp).1=
      BinaryQuadraticSegmentOutputLifetime.reference budget header (prepared env hC hN) fallback K N scalar bits pos hp := by
  simp only [runWithTrace,BinaryQuadraticSegmentOutputLifetime.runWithTrace_erases budget header hB,preparedWithTrace_erases]

def widthBound (budget : SignedWord) (s K : ℕ) : ℕ :=
  BinaryQuadraticPointOutputLifetime.widthBound budget (expressionHeightBudget s 16) K

def bound (s K remaining W headerLength : ℕ) : ℕ := BinaryQuadraticThreeFactoryLifetime.bound s+
  BinaryQuadraticSegmentOutputLifetime.bound 3 9 (expressionHeightBudget s 16) K remaining W headerLength+8

def frames (s K remaining W headerLength : ℕ) : ℕ := BinaryQuadraticThreeFactoryLifetime.frames s+4+
  BinaryQuadraticSegmentOutputLifetime.frames 3 9 (expressionHeightBudget s 16) K remaining W headerLength

theorem runWithTrace_bounds (budget : SignedWord) (header : List Bool) (hB : BinaryRationalOpcode.Valid budget) (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot))
    (source : RationalSegmentLottery 3 9) (hR : (descriptor env).Refines source)
    (s : ℕ) (hs : 3≤s) (hH : EnvHeight env s)
    (fallback : Fin 9) (K N : ℕ) (scalar : BinaryScalarTape K) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    listCells (runWithTrace budget header env hC hN fallback K N scalar bits pos hp).2+
      arraySlots (runWithTrace budget header env hC hN fallback K N scalar bits pos hp).2 ≤ bound s K (N-pos) (widthBound budget s K) header.length ∧
    framePeak (runWithTrace budget header env hC hN fallback K N scalar bits pos hp).2 ≤ frames s K (N-pos) (widthBound budget s K) header.length := by
  have hFactory := BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace_bounds env hC s hs hH
  have hFactoryFrames := framePeak_under 2 (preparedWithTrace env hC hN).2
  have hHeight := BinaryThreeFactoryWork.descriptor_height env hC s hs hH
  have hWeight : ∀ slot,RationalHeight (source.weight slot) (expressionHeightBudget s 16) := by
    intro slot; rw [← hR.1 slot]; exact hHeight.1 slot
  have hEndpoint : ∀ slot j,RationalHeight (source.P slot j) (expressionHeightBudget s 16) ∧
      RationalHeight (source.Q slot j) (expressionHeightBudget s 16) := by
    intro slot j; rw [← hR.2.1 slot j,← hR.2.2 slot j]; exact hHeight.2 slot j
  have hPreparedR : (preparedWithTrace env hC hN).1.table.Refines source := by
    rw [preparedWithTrace_erases]; exact hR
  have hDraw := BinaryQuadraticSegmentOutputLifetime.runWithTrace_bounds budget header hB (preparedWithTrace env hC hN).1 source hPreparedR
    (expressionHeightBudget s 16) (hs.trans (expressionHeightBudget_ge_input s 16)) hWeight hEndpoint
    fallback K N scalar bits pos hp
  have hDrawFrames := framePeak_under 2 (BinaryQuadraticSegmentOutputLifetime.runWithTrace
    budget header (preparedWithTrace env hC hN).1 fallback K N scalar bits pos hp).2
  change listCells (preparedWithTrace env hC hN).2+arraySlots (preparedWithTrace env hC hN).2 ≤
    BinaryQuadraticThreeFactoryLifetime.bound s ∧ framePeak (preparedWithTrace env hC hN).2 ≤ BinaryQuadraticThreeFactoryLifetime.frames s at hFactory
  unfold runWithTrace bound frames widthBound
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

theorem runWithTrace_position (budget : SignedWord) (header : List Bool) (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot))
    (fallback : Fin 9) (K N : ℕ) (scalar : BinaryScalarTape K) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) :
    pos≤(runWithTrace budget header env hC hN fallback K N scalar bits pos hp).1.2 ∧
    (runWithTrace budget header env hC hN fallback K N scalar bits pos hp).1.2≤N :=
  BinaryQuadraticSegmentOutputLifetime.runWithTrace_position budget header _ fallback K N scalar bits pos hp

def environmentCells (env : FixedArrayTable 4 SignedWord) : ℕ := 8+∑ j,BinaryRationalOpcodeAllocation.payload (env.read j)

theorem all_prefix_heap (budget : SignedWord) (header : List Bool) (hB : BinaryRationalOpcode.Valid budget) (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot))
    (source : RationalSegmentLottery 3 9) (hR : (descriptor env).Refines source)
    (s : ℕ) (hs : 3≤s) (hH : EnvHeight env s)
    (fallback : Fin 9) (K N : ℕ) (scalar : BinaryScalarTape K) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N)
    (borrowedOtherCells originalSeedCells steps : ℕ) :
    retainedHeap (BinaryRationalOpcodeAllocation.payload budget+header.length+environmentCells env+borrowedOtherCells+originalSeedCells)
      (runWithTrace budget header env hC hN fallback K N scalar bits pos hp).2 steps ≤
      BinaryRationalOpcodeAllocation.payload budget+header.length+environmentCells env+borrowedOtherCells+originalSeedCells+bound s K (N-pos) (widthBound budget s K) header.length := by
  have hb := (runWithTrace_bounds budget header hB env hC hN source hR s hs hH fallback K N scalar bits pos hp).1
  have hl := listCells_take_le (runWithTrace budget header env hC hN fallback K N scalar bits pos hp).2 steps
  have ha := arraySlots_take_le (runWithTrace budget header env hC hN fallback K N scalar bits pos hp).2 steps
  unfold retainedHeap
  omega

theorem all_prefix_frames (budget : SignedWord) (header : List Bool) (hB : BinaryRationalOpcode.Valid budget)
    (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (hN : ∀ slot,0≤value ((descriptor env).weight.read slot))
    (source : RationalSegmentLottery 3 9) (hR : (descriptor env).Refines source)
    (s : ℕ) (hs : 3≤s) (hH : EnvHeight env s)
    (fallback : Fin 9) (K N : ℕ) (scalar : BinaryScalarTape K) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N) (steps : ℕ) :
    framePeak ((runWithTrace budget header env hC hN fallback K N scalar bits pos hp).2.take steps)≤
      frames s K (N-pos) (widthBound budget s K) header.length :=
  (framePeak_take_le _ _).trans
    (runWithTrace_bounds budget header hB env hC hN source hR s hs hH fallback K N scalar bits pos hp).2

theorem geometry_nonnegative (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (g : RationalThreeGeometry)
    (hInputs : BinaryRationalExpression.interpretedEnvironment env=RationalThreeGeometryCode.environment g) :
    ∀ slot,0≤value ((descriptor env).weight.read slot) := by
  have hr := descriptor_refines env g (fun j => (hC j).1) hInputs
  intro slot
  rw [hr.1 slot]
  exact (RationalThreeGeometryCode.compiledLottery g).nonnegative slot

/-- Geometry correctness supplies normalization/nonnegativity. Only the actual
four source words and reached reader cap supply the lifetime bound. -/
theorem geometry_all_prefix (budget : SignedWord) (header : List Bool) (hB : BinaryRationalOpcode.Valid budget)
    (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j)) (g : RationalThreeGeometry)
    (hInputs : BinaryRationalExpression.interpretedEnvironment env=RationalThreeGeometryCode.environment g)
    (s : ℕ) (hs : 3≤s) (hH : EnvHeight env s)
    (fallback : Fin 9) (K N : ℕ) (scalar : BinaryScalarTape K) (bits : Fin N→Bool) (pos : ℕ) (hp : pos≤N)
    (borrowedOtherCells originalSeedCells steps : ℕ) :
    retainedHeap (BinaryRationalOpcodeAllocation.payload budget+header.length+environmentCells env+
      borrowedOtherCells+originalSeedCells)
      (runWithTrace budget header env hC (geometry_nonnegative env hC g hInputs) fallback K N scalar bits pos hp).2 steps≤
      BinaryRationalOpcodeAllocation.payload budget+header.length+environmentCells env+borrowedOtherCells+originalSeedCells+
        bound s K (N-pos) (widthBound budget s K) header.length :=
  all_prefix_heap budget header hB env hC _ (RationalThreeGeometryCode.compiledLottery g)
    (descriptor_refines env g (fun j => (hC j).1) hInputs) s hs hH fallback K N scalar bits pos hp
    borrowedOtherCells originalSeedCells steps

end Blotto.BinaryQuadraticThreeFactoryOutputLifetime
