import Blotto.PlayerSpecificFinitePrecisionEnvelope
import Blotto.PlayerSpecificFiniteSamplerPartialPolynomial

/-! One polynomial source bound for the measured public preparation and
every accepted fair-bit packet, using the precisions computed by that return. -/
namespace Blotto.PlayerSpecificFiniteSamplerCostEnvelope
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

structure Profile where
  n : ℕ
  inputLength : ℕ
  epsilon : ℚ
  coinBits : ℕ
  scalarBits : ℕ
  outputBits : ℕ
  coin_bound : coinBits≤34*PlayerSpecificFinitePrecisionEnvelope.size n inputLength epsilon
  scalar_bound : scalarBits≤2*PlayerSpecificFinitePrecisionEnvelope.size n inputLength epsilon
  output_bound : outputBits≤2*PlayerSpecificFinitePrecisionEnvelope.size n inputLength epsilon

def size (q : Profile) : ℕ := q.n+q.inputLength+rationalWordWidth q.epsilon
private abbrev E (f : Profile → ℕ) := NaturalPolynomialEnvelope size f
private theorem c (n : ℕ) : E (fun _ => n) := NaturalPolynomialEnvelope.constant _ n
private theorem add {f g : Profile → ℕ} (hf : E f) (hg : E g) :
    E (fun q => f q+g q) := NaturalPolynomialEnvelope.add hf hg
private theorem mul {f g : Profile → ℕ} (hf : E f) (hg : E g) :
    E (fun q => f q*g q) := NaturalPolynomialEnvelope.mul hf hg

private theorem n : E (fun q => q.n) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro q; dsimp [size]; omega)
private theorem length : E (fun q => q.inputLength) :=
  NaturalPolynomialEnvelope.of_le_size _ _ (by intro q; dsimp [size]; omega)

private theorem precision_size : E (fun q =>
    PlayerSpecificFinitePrecisionEnvelope.size q.n q.inputLength q.epsilon) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := size) (sizeB := PlayerSpecificFiniteSamplerPreparationEnvelope.size)
    (g := fun q : Profile => (q.n,q.inputLength,q.epsilon))
    PlayerSpecificFiniteSamplerPreparationEnvelope.input_size
    (NaturalPolynomialEnvelope.of_le_size _ _ (by intro q; exact le_rfl))

private theorem coin : E (fun q => q.coinBits) :=
  NaturalPolynomialEnvelope.dominated (mul (c 34) precision_size)
    (fun q => q.coin_bound)
private theorem scalar : E (fun q => q.scalarBits) :=
  NaturalPolynomialEnvelope.dominated (mul (c 2) precision_size)
    (fun q => q.scalar_bound)
private theorem output : E (fun q => q.outputBits) :=
  NaturalPolynomialEnvelope.dominated (mul (c 2) precision_size)
    (fun q => q.output_bound)

theorem random_bits : E (fun q =>
    PlayerSpecificAlgebraicFiniteDraw.bitCount q.n q.coinBits q.scalarBits) := by
  have hsub := NaturalPolynomialEnvelope.sub
    (g := fun _ : Profile => 1) n
  have h := add (mul hsub coin)
    (add (add (mul (c 80) coin) scalar) scalar)
  simpa only [PlayerSpecificAlgebraicFiniteDraw.bitCount,
    PlayerSpecificAlgebraicTerminalCoreDraw.bitCount] using h

private theorem preparation : E (fun q =>
    PlayerSpecificFiniteSamplerPreparationPolynomial.originalPolynomial
      q.n q.inputLength q.epsilon) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := size) (sizeB := PlayerSpecificFiniteSamplerPreparationEnvelope.size)
    (g := fun q : Profile => (q.n,q.inputLength,q.epsilon))
    PlayerSpecificFiniteSamplerPreparationEnvelope.work
    (NaturalPolynomialEnvelope.of_le_size _ _ (by intro q; exact le_rfl))

private theorem lift_draw {a b h k : Profile → ℕ}
    (ha : E a) (hb : E b) (hh : E h) (hk : E k) :
    E (fun q =>
      2*PlayerSpecificBitSlicePolynomial.coefficient*
        (PlayerSpecificAlgebraicFiniteDraw.bitCount (a q) (h q) (k q)+1)^3+
      PlayerSpecificResourceEntryPriceProfile.coefficient*(a q+1)^7*(b q+h q+1)^3+
      PlayerSpecificTerminalLeafMeasuredSourceCost.work (a q)
        (PlayerSpecificResourceEntryInput.height (a q) (b q)) (h q) (k q)+2) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := size) (sizeB := PlayerSpecificPolynomialQuadrupleTerms.size)
    (g := fun q : Profile => (a q,b q,h q,k q))
    PlayerSpecificFiniteDrawMeasuredEnvelope.work
    (add (add (add ha hb) hh) hk)

private theorem lift_output {a b k p : Profile → ℕ}
    (ha : E a) (hb : E b) (hk : E k) (hp : E p) :
    E (fun q => 2*PlayerSpecificRationalOutputSourcePolynomial.polynomial (a q)
      (PlayerSpecificRationalFiniteOutputPolynomial.heightCoefficient*(a q+1)^3*
        (b q+k q+a q+1)) (p q)) :=
  PlayerSpecificPolynomialSubstitution.substitute
    (sizeA := size) (sizeB := PlayerSpecificPolynomialQuadrupleTerms.size)
    (g := fun q : Profile => (a q,b q,k q,p q))
    PlayerSpecificRationalFiniteOutputEnvelope.work
    (add (add (add ha hb) hk) hp)

def work (q : Profile) : ℕ :=
  PlayerSpecificFiniteSamplerPreparationPolynomial.originalPolynomial
    q.n q.inputLength q.epsilon+
  (2*PlayerSpecificBitSlicePolynomial.coefficient*
    (PlayerSpecificAlgebraicFiniteDraw.bitCount q.n q.coinBits q.scalarBits+1)^3+
   PlayerSpecificResourceEntryPriceProfile.coefficient*(q.n+1)^7*
     (q.inputLength+q.coinBits+1)^3+
   PlayerSpecificTerminalLeafMeasuredSourceCost.work q.n
     (PlayerSpecificResourceEntryInput.height q.n q.inputLength)
     q.coinBits q.scalarBits+2)+
  2*PlayerSpecificRationalOutputSourcePolynomial.polynomial q.n
    (PlayerSpecificRationalFiniteOutputPolynomial.heightCoefficient*(q.n+1)^3*
      (q.inputLength+q.scalarBits+q.n+1)) q.outputBits

theorem work_polynomial : E work := by
  have hall := add (add preparation (lift_draw n length coin scalar))
    (lift_output n length scalar output)
  change E (fun q =>
    PlayerSpecificFiniteSamplerPreparationPolynomial.originalPolynomial
      q.n q.inputLength q.epsilon+
    (2*PlayerSpecificBitSlicePolynomial.coefficient*
      (PlayerSpecificAlgebraicFiniteDraw.bitCount q.n q.coinBits q.scalarBits+1)^3+
     PlayerSpecificResourceEntryPriceProfile.coefficient*(q.n+1)^7*
       (q.inputLength+q.coinBits+1)^3+
     PlayerSpecificTerminalLeafMeasuredSourceCost.work q.n
       (PlayerSpecificResourceEntryInput.height q.n q.inputLength)
       q.coinBits q.scalarBits+2)+
    2*PlayerSpecificRationalOutputSourcePolynomial.polynomial q.n
      (PlayerSpecificRationalFiniteOutputPolynomial.heightCoefficient*(q.n+1)^3*
        (q.inputLength+q.scalarBits+q.n+1)) q.outputBits)
  exact hall

theorem accepted_cost :
    ∃ C d : ℕ, ∀ {N : ℕ} (i : RationalPlayerSpecificInput N)
      (epsilon : ℚ) (_he : 0<epsilon) (p : PlayerSpecificFiniteSampler.Prepared N)
      (_hp : (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p)
      (player : Bool) (bits : Fin (PlayerSpecificFiniteSampler.bitCount p) → Bool),
      (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).2+
        (PlayerSpecificFiniteSamplerMeasuredExecution.draw p player bits).2≤
      C*(N+PlayerSpecificInitialPositivePrecision.inputSize i+
        rationalWordWidth epsilon+1)^d := by
  obtain ⟨C,d,hbound⟩ := work_polynomial
  refine ⟨C,d,?_⟩
  intro N i epsilon he p hp player bits
  have hprecision := PlayerSpecificFinitePrecisionEnvelope.accepted_bits i epsilon he p hp
  let q : Profile := {
    n := N
    inputLength := PlayerSpecificInitialPositivePrecision.inputSize i
    epsilon := epsilon
    coinBits := p.accuracy.coinBits
    scalarBits := p.accuracy.scalarBits
    outputBits := p.accuracy.outputBits
    coin_bound := hprecision.1
    scalar_bound := hprecision.2.1
    output_bound := hprecision.2.2 }
  have hs := PlayerSpecificFiniteSamplerPartialPolynomial.accepted_work
    i epsilon he p hp player bits
  have hsource :
      PlayerSpecificFiniteSamplerPreparationPolynomial.originalPolynomial N
        (PlayerSpecificInitialPositivePrecision.inputSize i) epsilon+
      PlayerSpecificFiniteDrawMeasuredSourceCost.work i
        p.accuracy.coinBits p.accuracy.scalarBits+
      PlayerSpecificRationalFiniteOutputPolynomial.outputWork i
        p.accuracy.scalarBits p.accuracy.outputBits=work q := rfl
  rw [hsource] at hs
  have hq := hbound q
  change work q≤C*(N+PlayerSpecificInitialPositivePrecision.inputSize i+
    rationalWordWidth epsilon+1)^d at hq
  exact hs.trans hq

theorem accepted_random_bits :
    ∃ C d : ℕ, ∀ {N : ℕ} (i : RationalPlayerSpecificInput N)
      (epsilon : ℚ) (_he : 0<epsilon) (p : PlayerSpecificFiniteSampler.Prepared N)
      (_hp : (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p),
      PlayerSpecificFiniteSampler.bitCount p≤
        C*(N+PlayerSpecificInitialPositivePrecision.inputSize i+
          rationalWordWidth epsilon+1)^d := by
  obtain ⟨C,d,hbound⟩ := random_bits
  refine ⟨C,d,?_⟩
  intro N i epsilon he p hp
  have hprecision := PlayerSpecificFinitePrecisionEnvelope.accepted_bits i epsilon he p hp
  let q : Profile := {
    n := N
    inputLength := PlayerSpecificInitialPositivePrecision.inputSize i
    epsilon := epsilon
    coinBits := p.accuracy.coinBits
    scalarBits := p.accuracy.scalarBits
    outputBits := p.accuracy.outputBits
    coin_bound := hprecision.1
    scalar_bound := hprecision.2.1
    output_bound := hprecision.2.2 }
  have hq := hbound q
  change PlayerSpecificFiniteSampler.bitCount p≤
    C*(N+PlayerSpecificInitialPositivePrecision.inputSize i+
      rationalWordWidth epsilon+1)^d at hq
  exact hq

end Blotto.PlayerSpecificFiniteSamplerCostEnvelope
