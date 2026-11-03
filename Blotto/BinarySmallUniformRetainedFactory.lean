import Blotto.BinaryReflectedSetupCache
import Blotto.BinarySmallUniformFactoryDraw

/-! The small uniform continuation consumes the actual parameter table held by
the common reflected setup cache. Three scale products and one full descriptor
are retained for selection/interpolation; parameter production is charged by
the cache prefix. Original table/row/position semantics and primitive bounds
hold without a supplied parameter or descriptor oracle. -/

namespace Blotto.BinarySmallUniformRetainedFactory
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinarySmallRootSample

def prepareWithWork {input : BinaryFourParameters.Input} (cached : BinaryReflectedSetupCache.Prepared input) :
    BinarySmallUniformCompiler.Input × ℕ :=
  let first := applyWithWork .mul (cached.parameters.read 5) input.u
  let second := applyWithWork .mul (cached.parameters.read 5) input.v
  let third := applyWithWork .mul (cached.parameters.read 5) input.w
  (⟨input.B,first.1,second.1,third.1,input.ell⟩,first.2 + second.2 + third.2)

theorem prepareWithWork_state {input : BinaryFourParameters.Input} (cached : BinaryReflectedSetupCache.Prepared input) :
    (prepareWithWork cached).1 = BinarySmallUniformCompiler.prepare input := by
  unfold prepareWithWork BinarySmallUniformCompiler.prepare
  simp only [cached.parameters_correct,applyWithWork_state]

theorem prepareWithWork_prefix_price {input : BinaryFourParameters.Input} (cached : BinaryReflectedSetupCache.Prepared input) :
    (prepareWithWork cached).2 + BinaryFourParameters.prepareWork input = (BinarySmallUniformFactoryWork.prepareWithWork input).2 := by
  unfold prepareWithWork BinarySmallUniformFactoryWork.prepareWithWork BinaryFourParameters.prepareWithWork
  simp only [cached.parameters_correct]
  omega

def descriptorWithWork {input : BinaryFourParameters.Input} (cached : BinaryReflectedSetupCache.Prepared input) :
    BinaryStoredOverlapEnvironment.Segment 4 9 × ℕ :=
  let prepared := prepareWithWork cached
  let table := BinarySmallUniformFactoryWork.descriptorWithWork prepared.1
  (table.1,prepared.2 + table.2)

theorem descriptorWithWork_state {input : BinaryFourParameters.Input} (cached : BinaryReflectedSetupCache.Prepared input) :
    (descriptorWithWork cached).1 = BinarySmallUniformCompiler.fromOriginal input := by
  unfold descriptorWithWork BinarySmallUniformCompiler.fromOriginal
  rw [BinarySmallUniformFactoryWork.descriptorWithWork_state,prepareWithWork_state]

theorem descriptorWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (cached : BinaryReflectedSetupCache.Prepared input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    (descriptorWithWork cached).2 ≤ BinarySmallUniformFactoryWork.bound s := by
  have hPrice := prepareWithWork_prefix_price cached
  have hPrepare := BinarySmallUniformFactoryWork.prepareWithWork_bound input source hC hR s hs hH
  have hs13 : 3 ≤ expressionHeightBudget s 13 := by unfold expressionHeightBudget; omega
  have hDescriptor := BinarySmallUniformFactoryWork.descriptorWithWork_bound _ (BinarySmallUniformCompiler.prepare_canonical input hC)
    _ hs13 (BinarySmallUniformFactoryWork.prepare_height input source hC hR hCase s hs hH)
  unfold descriptorWithWork
  dsimp only
  rw [prepareWithWork_state]
  unfold BinarySmallUniformFactoryWork.bound
  omega

def preparedWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (cached : BinaryReflectedSetupCache.Prepared input) : BinaryStoredSegmentProgram.Prepared 4 9 × ℕ :=
  let factory := descriptorWithWork cached
  have hc : factory.1.Canonical := by rw [descriptorWithWork_state]; exact BinarySmallUniformCompiler.fromOriginal_canonical input hC
  have hn : ∀ slot, 0 ≤ value (factory.1.weight.read slot) := by rw [descriptorWithWork_state]; exact uniform_nonnegative input hC hAd
  (⟨factory.1,hc,hn⟩,factory.2)

theorem preparedWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (cached : BinaryReflectedSetupCache.Prepared input) :
    (preparedWithWork input hC hAd cached).1 = BinarySmallUniformDrawWork.prepared input hC hAd := by
  unfold preparedWithWork BinarySmallUniformDrawWork.prepared
  simp only [descriptorWithWork_state]

def runIndexedWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (cached : BinaryReflectedSetupCache.Prepared input) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (Option (FixedArrayTable 4 SignedWord) × ℕ) × ℕ :=
  let prepared := preparedWithWork input hC hAd cached
  let drawn := BinaryStoredSegmentDrawWork.runIndexedWork prepared.1 0 K N scalar bits pos hp
  (drawn.1,prepared.2 + drawn.2)

theorem runIndexedWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (cached : BinaryReflectedSetupCache.Prepared input) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (runIndexedWithWork input hC hAd cached K N scalar bits pos hp).1 = uniformRun input hC hAd K N scalar bits pos hp := by
  unfold runIndexedWithWork
  dsimp only
  rw [preparedWithWork_state]
  exact BinarySmallUniformDrawWork.runIndexedWithWork_state input hC hAd K N scalar bits pos hp

theorem runIndexedWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input)
    (hCase : source.w < (1 - source.p) * source.ell) (cached : BinaryReflectedSetupCache.Prepared input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (runIndexedWithWork input hC hAd cached K N scalar bits pos hp).2 ≤ BinarySmallUniformFactoryDraw.bound s K (N - pos) := by
  have hFactory := descriptorWithWork_bound input source hC hR hCase cached s hs hH
  have hDraw := BinarySmallUniformDrawWork.runIndexedWithWork_bound input source hC hR hAd hCase s hs hH K N scalar bits pos hp
  unfold runIndexedWithWork
  dsimp only
  rw [preparedWithWork_state]
  exact Nat.add_le_add hFactory hDraw

end Blotto.BinarySmallUniformRetainedFactory
