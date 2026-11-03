import Blotto.PlayerSpecificRationalFiniteDraw

/-! The actual original-input entry prepares recognition, initial data,
the positive minimum and all three numerical precisions once. A draw
then consumes a bounded packet and returns a native rational array.
Probability-error and complete source-cost joins are still separate. -/
namespace Blotto.PlayerSpecificFiniteSampler
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] PlayerSpecificMinimumSearch.search

structure Prepared (N : ℕ) where
  base : PlayerSpecificInitialMinimumExecution.Prepared N
  budget : ℚ
  accuracy : PlayerSpecificFiniteAccuracy.Parameters

def ofBase {N : ℕ} (B : ℚ) (base : PlayerSpecificInitialMinimumExecution.Prepared N) (epsilon : ℚ) : Prepared N :=
  ⟨base,B,PlayerSpecificFiniteAccuracy.prepare N base.minimum.exponent epsilon⟩

def prepare {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) : Option (Prepared N) :=
  (PlayerSpecificInitialMinimumExecution.run i).1.map (fun base => ofBase i.budget base epsilon)

def bitCount {N : ℕ} (p : Prepared N) : ℕ :=
  PlayerSpecificAlgebraicFiniteDraw.bitCount N p.accuracy.coinBits p.accuracy.scalarBits

def draw {N : ℕ} (p : Prepared N) (player : Bool) (bits : Fin (bitCount p) → Bool) : FixedArrayTable N ℚ :=
  PlayerSpecificRationalFiniteDraw.draw p.base.initial p.budget player p.accuracy.coinBits p.accuracy.scalarBits p.accuracy.outputBits bits

theorem selected {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (p : Prepared N)
    (hp : prepare i epsilon=some p) :
    ∃ base,(PlayerSpecificInitialMinimumExecution.run i).1=some base ∧ p=ofBase i.budget base epsilon := by
  obtain ⟨base,hb,he⟩ := Option.map_eq_some_iff.mp hp
  exact ⟨base,hb,he.symm⟩

theorem none_iff {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) :
    prepare i epsilon=none ↔ (PlayerSpecificInitialMinimumExecution.run i).1=none :=
  Option.map_eq_none_iff

theorem rejection_iff {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) :
    prepare i epsilon=none ↔ ¬∃ gamma sigma,
      PlayerSpecificRecognition.ValidParameters i.valuesA.values i.valuesB.values (i.budget:ℝ) gamma sigma :=
  (none_iff i epsilon).trans (PlayerSpecificInitialMinimumContract.rejection_iff i)

end Blotto.PlayerSpecificFiniteSampler
