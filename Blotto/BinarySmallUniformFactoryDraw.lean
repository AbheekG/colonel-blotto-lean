import Blotto.BinarySmallUniformFactoryWork

/-! The measured small-uniform factory builds one table reused by categorical
selection and interpolation. The recorded primitive price includes both table
production and the indexed draw; exact retained bytes and positions transfer. -/

namespace Blotto.BinarySmallUniformFactoryDraw
open BinaryRationalNormalization BinaryRationalEncoding BinarySmallRootSample

def preparedWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) :
    BinaryStoredSegmentProgram.Prepared 4 9 × ℕ :=
  let factory := BinarySmallUniformFactoryWork.fromOriginalWithWork input
  have hc : factory.1.Canonical := by rw [BinarySmallUniformFactoryWork.fromOriginalWithWork_state]; exact BinarySmallUniformCompiler.fromOriginal_canonical input hC
  have hn : ∀ slot, 0 ≤ value (factory.1.weight.read slot) := by rw [BinarySmallUniformFactoryWork.fromOriginalWithWork_state]; exact uniform_nonnegative input hC hAd
  (⟨factory.1,hc,hn⟩,factory.2)

theorem preparedWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) :
    (preparedWithWork input hC hAd).1 = BinarySmallUniformDrawWork.prepared input hC hAd := by
  unfold preparedWithWork BinarySmallUniformDrawWork.prepared
  simp only [BinarySmallUniformFactoryWork.fromOriginalWithWork_state]

def runIndexedWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (Option (FixedArrayTable 4 SignedWord) × ℕ) × ℕ :=
  let prepared := preparedWithWork input hC hAd
  let drawn := BinaryStoredSegmentDrawWork.runIndexedWork prepared.1 0 K N scalar bits pos hp
  (drawn.1,prepared.2 + drawn.2)

theorem runIndexedWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (runIndexedWithWork input hC hAd K N scalar bits pos hp).1 = uniformRun input hC hAd K N scalar bits pos hp := by
  unfold runIndexedWithWork
  dsimp only
  rw [preparedWithWork_state]
  exact BinarySmallUniformDrawWork.runIndexedWithWork_state input hC hAd K N scalar bits pos hp

def bound (s K remaining : ℕ) : ℕ := BinarySmallUniformFactoryWork.bound s + BinarySmallUniformDrawWork.bound s K remaining

theorem runIndexedWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input)
    (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (runIndexedWithWork input hC hAd K N scalar bits pos hp).2 ≤ bound s K (N - pos) := by
  have hFactory := BinarySmallUniformFactoryWork.fromOriginalWithWork_bound input source hC hR hCase s hs hH
  have hDraw := BinarySmallUniformDrawWork.runIndexedWithWork_bound input source hC hR hAd hCase s hs hH K N scalar bits pos hp
  unfold runIndexedWithWork
  dsimp only
  rw [preparedWithWork_state]
  exact Nat.add_le_add hFactory hDraw

end Blotto.BinarySmallUniformFactoryDraw
