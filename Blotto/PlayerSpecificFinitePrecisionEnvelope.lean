import Blotto.PlayerSpecificRationalFiniteOutputEnvelope
import Blotto.PlayerSpecificFiniteSamplerContract
import Blotto.PlayerSpecificFiniteSamplerMeasuredExecution

/-! The actual accepted fair-bit and rounding precisions are bounded by
the original rational input and epsilon word width. -/
namespace Blotto.PlayerSpecificFinitePrecisionEnvelope
open PlayerSpecificFiniteSampler PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def size (N L : ℕ) (epsilon : ℚ) : ℕ :=
  PlayerSpecificFiniteAccuracySourcePolynomial.inputSize N
    (PlayerSpecificFiniteSamplerPreparationPolynomial.exponentBound N L) epsilon

theorem prepared_bits (N s : ℕ) (epsilon : ℚ) (he : 0<epsilon) :
    let a := PlayerSpecificFiniteAccuracy.prepare N s epsilon
    let X := PlayerSpecificFiniteAccuracySourcePolynomial.inputSize N s epsilon
    a.coinBits≤34*X ∧ a.scalarBits≤2*X ∧ a.outputBits≤2*X := by
  let X:=PlayerSpecificFiniteAccuracySourcePolynomial.inputSize N s epsilon
  let C:=32*(N+1000)
  have hXshape : X=N+s+rationalWordWidth epsilon+1000 := rfl
  have hX : N+1000≤X ∧ s≤X ∧ rationalWordWidth epsilon≤X ∧ 1≤X := by
    dsimp only [X,PlayerSpecificFiniteAccuracySourcePolynomial.inputSize]
    omega
  have hC : 0<C := by dsimp only [C]; omega
  have hCbound : binaryWordWidth C≤32*X+1 := by
    have hc : C≤32*X := Nat.mul_le_mul_left 32 hX.1
    have hw := control_width C
    omega
  have hc:=PlayerSpecificRationalPrecisionSourceSizes.precision_bound C epsilon hC he
  have hs:=PlayerSpecificRationalPrecisionSourceSizes.precision_bound 48 epsilon
    (by decide) he
  have hp:=PlayerSpecificRationalPrecisionSourceSizes.precision_bound 32 epsilon
    (by decide) he
  have h48 : binaryWordWidth 48=6 := by decide
  have h32 : binaryWordWidth 32=6 := by decide
  dsimp only [PlayerSpecificFiniteAccuracy.prepare,
    PlayerSpecificRationalPrecisionSourceSizes.inputWidth] at hc hs hp
  rw [h48] at hs
  rw [h32] at hp
  dsimp only [PlayerSpecificFiniteAccuracy.prepare]
  constructor
  · dsimp only [C] at hc hCbound
    omega
  constructor
  · omega
  · omega

theorem accepted_bits {N : ℕ} (i : RationalPlayerSpecificInput N)
    (epsilon : ℚ) (he : 0<epsilon) (p : Prepared N)
    (hp : (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p) :
    p.accuracy.coinBits≤34*size N (PlayerSpecificInitialPositivePrecision.inputSize i) epsilon ∧
    p.accuracy.scalarBits≤2*size N (PlayerSpecificInitialPositivePrecision.inputSize i) epsilon ∧
    p.accuracy.outputBits≤2*size N (PlayerSpecificInitialPositivePrecision.inputSize i) epsilon := by
  have hpublic : PlayerSpecificFiniteSampler.prepare i epsilon=some p := by
    rw [←PlayerSpecificFiniteSamplerMeasuredExecution.prepare_value i epsilon he]
    exact hp
  obtain ⟨base,hb,hpbase⟩ := PlayerSpecificFiniteSampler.selected i epsilon p hpublic
  have hmeta := PlayerSpecificFiniteSamplerContract.numerical_metadata i epsilon he p hpublic
  have hexp : base.minimum.exponent≤
      PlayerSpecificFiniteSamplerPreparationPolynomial.exponentBound N
        (PlayerSpecificInitialPositivePrecision.inputSize i) := by
    rw [hpbase] at hmeta
    exact hmeta.2.2.1
  have hbits := prepared_bits N base.minimum.exponent epsilon he
  have hX : PlayerSpecificFiniteAccuracySourcePolynomial.inputSize N
      base.minimum.exponent epsilon≤
      size N (PlayerSpecificInitialPositivePrecision.inputSize i) epsilon := by
    dsimp only [size,PlayerSpecificFiniteAccuracySourcePolynomial.inputSize]
    omega
  rw [hpbase]
  dsimp only [PlayerSpecificFiniteSampler.ofBase]
  exact ⟨(hbits.1).trans (Nat.mul_le_mul_left 34 hX),
    (hbits.2.1).trans (Nat.mul_le_mul_left 2 hX),
    (hbits.2.2).trans (Nat.mul_le_mul_left 2 hX)⟩

end Blotto.PlayerSpecificFinitePrecisionEnvelope
