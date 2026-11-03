import Blotto.PlayerSpecificFourSmallDrawSourceCost
import Blotto.PlayerSpecificFourGluingDrawSourceCost
import Blotto.PlayerSpecificAlgebraicOrderedFourDraw

/-! The ordered four-variable dispatch computes the actual guard from the
retained field rows, then executes only the selected draw. -/
namespace Blotto.PlayerSpecificOrderedFourDrawExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def guard (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) : Bool × ℕ :=
  let model := RationalCostModel.schoolbook
  let complement := PlayerSpecificMixtureScalarExecution.complement model r.root a.probability
  let threshold := PlayerSpecificMixtureScalarExecution.scale model r.root complement.1 a.length
  let compared := PlayerSpecificAlgebraicComparisonExecution.run model r.root threshold.1 a.third
  (compared.1, complement.2 + threshold.2 + compared.2 + price model [.control 1])

theorem guard_value (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) :
    (guard r a).1 = PlayerSpecificAlgebraicOrderedFourDraw.normal r a := by
  simp only [guard, PlayerSpecificMixtureScalarExecution.complement_value,
    PlayerSpecificMixtureScalarExecution.scale_value,
    PlayerSpecificAlgebraicComparisonExecution.value,
    PlayerSpecificAlgebraicOrderedFourDraw.normal]

def run (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin ((80*H+K)+K) → Bool) : FixedArrayTable 4 Data × ℕ :=
  let model := RationalCostModel.schoolbook
  let g := guard r a
  if g.1 then
    let headBits := PlayerSpecificBitSliceExecution.run model ((80*H+K)+K) 0 (80*H+K)
      (by omega) bits
    let drawn := PlayerSpecificFourGluingDrawExecution.run model r.root a H K headBits.1
    (drawn.1, g.2 + headBits.2 + drawn.2 + price model [.control 1])
  else
    let headBits := PlayerSpecificBitSliceExecution.run model ((80*H+K)+K) 0
      (PlayerSpecificAlgebraicFourSmallDraw.bitCount H K)
      (by simpa only [Nat.zero_add] using PlayerSpecificAlgebraicOrderedFourDraw.small_bit_bound H K) bits
    let drawn := PlayerSpecificFourSmallDrawExecution.run r a H K headBits.1
    (drawn.1, g.2 + headBits.2 + drawn.2 + price model [.control 1])

theorem normal_bits (H K : ℕ) (bits : Fin ((80*H+K)+K) → Bool) :
    (PlayerSpecificBitSliceExecution.run RationalCostModel.schoolbook ((80*H+K)+K) 0
      (80*H+K) (by omega) bits).1 = firstBitBlock (80*H+K) K bits := by
  exact PlayerSpecificBitSliceExecution.first_value RationalCostModel.schoolbook (80*H+K) K bits

theorem small_bits (H K : ℕ) (bits : Fin ((80*H+K)+K) → Bool) :
    (PlayerSpecificBitSliceExecution.run RationalCostModel.schoolbook ((80*H+K)+K) 0
      (PlayerSpecificAlgebraicFourSmallDraw.bitCount H K)
      (by simpa only [Nat.zero_add] using PlayerSpecificAlgebraicOrderedFourDraw.small_bit_bound H K) bits).1 =
      PlayerSpecificAlgebraicFourSmallDraw.takeBits
        (PlayerSpecificAlgebraicOrderedFourDraw.small_bit_bound H K) bits := by
  rw [PlayerSpecificBitSliceExecution.value]
  funext j
  simp only [PlayerSpecificBitSliceExecution.address,
    PlayerSpecificAlgebraicFourSmallDraw.takeBits, Nat.zero_add]

theorem value (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin ((80*H+K)+K) → Bool) :
    (run r a H K bits).1 = PlayerSpecificAlgebraicOrderedFourDraw.draw r a H K bits := by
  simp only [run, guard_value, PlayerSpecificAlgebraicOrderedFourDraw.draw]
  split
  · simp only [normal_bits, PlayerSpecificFourGluingDrawExecution.value]
  · simp only [small_bits, PlayerSpecificFourSmallDrawExecution.value]

end Blotto.PlayerSpecificOrderedFourDrawExecution
