import Blotto.PlayerSpecificFiniteSamplerMeasuredPreparationCost
import Blotto.PlayerSpecificFiniteAccuracySourcePolynomial

/-! A polynomial envelope for the accepted public preparation source
expression, parameterized first by the computed positive-minimum exponent.
The source program and every computed precision value are retained. -/
namespace Blotto.PlayerSpecificFiniteSamplerPreparationPolynomial
open PlayerSpecificFiniteSampler PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frameBound (N L s : ℕ) (epsilon : ℚ) : ℕ :=
  let X:=PlayerSpecificFiniteAccuracySourcePolynomial.inputSize N s epsilon
  3*L+(N+1000)*(34*X)+100*X+100

def polynomial (N L s : ℕ) (epsilon : ℚ) : ℕ :=
  PlayerSpecificInitialMinimumCost.totalBound N L+
    PlayerSpecificFiniteAccuracySourcePolynomial.polynomial N s epsilon+
    27*RationalCostModel.schoolbook.rat (frameBound N L s epsilon)+2

def exponentBound (N L : ℕ) : ℕ :=
  PlayerSpecificInitialPositivePrecision.coefficient*(N+1)*(L+1)

def originalPolynomial (N L : ℕ) (epsilon : ℚ) : ℕ :=
  polynomial N L (exponentBound N L) epsilon

theorem polynomial_mono_exponent (N L : ℕ) (epsilon : ℚ) {s t : ℕ}
    (h : s≤t) : polynomial N L s epsilon≤polynomial N L t epsilon := by
  have hX : PlayerSpecificFiniteAccuracySourcePolynomial.inputSize N s epsilon≤
      PlayerSpecificFiniteAccuracySourcePolynomial.inputSize N t epsilon := by
    dsimp only [PlayerSpecificFiniteAccuracySourcePolynomial.inputSize]
    omega
  have hf : frameBound N L s epsilon≤frameBound N L t epsilon := by
    simp only [frameBound]
    gcongr
  have ha:=PlayerSpecificFiniteAccuracySourcePolynomial.polynomial_mono_exponent
    N epsilon h
  have hr:=RationalCostModel.schoolbook.monotone hf
  have hc:=Nat.mul_le_mul_left 27 hr
  have hsum:=Nat.add_le_add
    (Nat.add_le_add_left ha (PlayerSpecificInitialMinimumCost.totalBound N L)) hc
  simpa only [polynomial] using Nat.add_le_add_right hsum 2

private theorem precision_sizes (N s : ℕ) (epsilon : ℚ) (he : 0<epsilon) :
    let a:=PlayerSpecificFiniteAccuracy.prepare N s epsilon
    let X:=PlayerSpecificFiniteAccuracySourcePolynomial.inputSize N s epsilon
    a.coinBits≤34*X ∧ a.scalarBits≤2*X ∧ a.outputBits≤2*X := by
  let X:=PlayerSpecificFiniteAccuracySourcePolynomial.inputSize N s epsilon
  let C:=32*(N+1000)
  have hXshape : X=N+s+rationalWordWidth epsilon+1000 := rfl
  have hX : N+1000≤X ∧ s≤X ∧ rationalWordWidth epsilon≤X ∧ 1≤X := by
    dsimp only [X,PlayerSpecificFiniteAccuracySourcePolynomial.inputSize]
    omega
  have hC : 0<C := by dsimp only [C]; omega
  have hCW:=control_width C
  have hCbound : binaryWordWidth C≤32*X+1 := by
    have hc : C≤32*X := Nat.mul_le_mul_left 32 hX.1
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

theorem frame_width {N : ℕ} (i : RationalPlayerSpecificInput N)
    (epsilon : ℚ) (he : 0<epsilon)
    (base : PlayerSpecificInitialMinimumExecution.Prepared N) :
    PlayerSpecificFiniteSamplerMeasuredPreparationCost.frameWidth i epsilon base
      (PlayerSpecificFiniteAccuracy.prepare N base.minimum.exponent epsilon)≤
    frameBound N (PlayerSpecificInitialPositivePrecision.inputSize i)
      base.minimum.exponent epsilon := by
  let s:=base.minimum.exponent
  let L:=PlayerSpecificInitialPositivePrecision.inputSize i
  let X:=PlayerSpecificFiniteAccuracySourcePolynomial.inputSize N s epsilon
  let a:=PlayerSpecificFiniteAccuracy.prepare N s epsilon
  have hsize : N+1000≤X ∧ s≤X ∧ rationalWordWidth epsilon≤X := by
    dsimp only [X,PlayerSpecificFiniteAccuracySourcePolynomial.inputSize]
    omega
  have hprecision : a.coinBits≤34*X ∧ a.scalarBits≤2*X ∧
      a.outputBits≤2*X := precision_sizes N s epsilon he
  have hbudget : rationalWordWidth i.budget≤3*L := by
    have h:=rationalWordWidth_of_height
      (PlayerSpecificRecognitionInputHeights.original_fields i).1
    have hL:=PlayerSpecificRecognitionInputHeights.input_positive i
    have hLshape : L=PlayerSpecificRecognitionInputHeights.inputHeight i := rfl
    omega
  have hbit:=PlayerSpecificAlgebraicFiniteDraw.random_bit_budget N a.coinBits a.scalarBits
  have hmul:=Nat.mul_le_mul_left (N+1000) hprecision.1
  have hbitBound : PlayerSpecificAlgebraicFiniteDraw.bitCount N a.coinBits a.scalarBits≤
      (N+1000)*(34*X)+4*X := by omega
  have hwords :
      binaryWordWidth N≤N+1 ∧
      binaryWordWidth s≤s+1 ∧
      binaryWordWidth a.coinBits≤a.coinBits+1 ∧
      binaryWordWidth a.scalarBits≤a.scalarBits+1 ∧
      binaryWordWidth a.outputBits≤a.outputBits+1 ∧
      binaryWordWidth (PlayerSpecificAlgebraicFiniteDraw.bitCount N a.coinBits a.scalarBits)≤
        PlayerSpecificAlgebraicFiniteDraw.bitCount N a.coinBits a.scalarBits+1 := by
    exact ⟨control_width N,control_width s,control_width a.coinBits,
      control_width a.scalarBits,control_width a.outputBits,
      control_width _⟩
  dsimp only [PlayerSpecificFiniteSamplerMeasuredPreparationCost.frameWidth,frameBound]
  dsimp only [s,L,X,a] at *
  omega

theorem accepted_work {N : ℕ} (i : RationalPlayerSpecificInput N)
    (epsilon : ℚ) (he : 0<epsilon) (p : Prepared N)
    (hp : (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p) :
    PlayerSpecificFiniteSamplerMeasuredPreparationCost.acceptedWork i epsilon p≤
      polynomial N (PlayerSpecificInitialPositivePrecision.inputSize i)
        p.base.minimum.exponent epsilon := by
  have hpublic : PlayerSpecificFiniteSampler.prepare i epsilon=some p := by
    rw [←PlayerSpecificFiniteSamplerMeasuredExecution.prepare_value i epsilon he]
    exact hp
  obtain ⟨base,hb,rfl⟩:=PlayerSpecificFiniteSampler.selected i epsilon p hpublic
  let s:=base.minimum.exponent
  let L:=PlayerSpecificInitialPositivePrecision.inputSize i
  have ha:=PlayerSpecificFiniteAccuracySourcePolynomial.work_bound N s epsilon
  have hf:=frame_width i epsilon he base
  have hr:=RationalCostModel.schoolbook.monotone hf
  have hframe:=Nat.mul_le_mul_left 27 hr
  have hsum:=Nat.add_le_add
    (Nat.add_le_add (le_refl (PlayerSpecificInitialMinimumCost.totalBound N L)) ha)
    hframe
  dsimp only [PlayerSpecificFiniteSamplerMeasuredPreparationCost.acceptedWork,
    polynomial,ofBase]
  simpa only [s,L,Nat.add_assoc] using Nat.add_le_add_right hsum 2

theorem accepted_source_cost {N : ℕ} (i : RationalPlayerSpecificInput N)
    (epsilon : ℚ) (he : 0<epsilon) (p : Prepared N)
    (hp : (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p) :
    (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).2≤
      polynomial N (PlayerSpecificInitialPositivePrecision.inputSize i)
        p.base.minimum.exponent epsilon :=
  (PlayerSpecificFiniteSamplerMeasuredPreparationCost.accepted_cost i epsilon he p hp).trans
    (accepted_work i epsilon he p hp)

theorem accepted_original_source_cost {N : ℕ} (i : RationalPlayerSpecificInput N)
    (epsilon : ℚ) (he : 0<epsilon) (p : Prepared N)
    (hp : (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p) :
    (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).2≤
      originalPolynomial N (PlayerSpecificInitialPositivePrecision.inputSize i) epsilon := by
  have hpublic : PlayerSpecificFiniteSampler.prepare i epsilon=some p := by
    rw [←PlayerSpecificFiniteSamplerMeasuredExecution.prepare_value i epsilon he]
    exact hp
  have hnum:=PlayerSpecificFiniteSamplerContract.numerical_metadata i epsilon he p hpublic
  have hs : p.base.minimum.exponent≤
      exponentBound N (PlayerSpecificInitialPositivePrecision.inputSize i) := by
    simpa only [exponentBound] using hnum.2.2.1
  exact (accepted_source_cost i epsilon he p hp).trans
    (polynomial_mono_exponent N (PlayerSpecificInitialPositivePrecision.inputSize i)
      epsilon hs)

end Blotto.PlayerSpecificFiniteSamplerPreparationPolynomial
