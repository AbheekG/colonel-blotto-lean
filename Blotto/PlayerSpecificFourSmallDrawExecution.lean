import Blotto.PlayerSpecificFourReflectedDrawSourceCost
import Blotto.PlayerSpecificFourMergedDrawSourceCost
import Blotto.PlayerSpecificAlgebraicCoinCost
import Blotto.PlayerSpecificAlgebraicFourSmallDraw

/-! One measured midpoint coin selects the reached small component.
The merged prefix is addressed only in the selected uniform branch. -/
namespace Blotto.PlayerSpecificFourSmallDrawExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem head_value (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicFourSmallDraw.bitCount H K) → Bool) :
    (PlayerSpecificBitSliceExecution.run RationalCostModel.schoolbook
      (PlayerSpecificAlgebraicFourSmallDraw.bitCount H K) 0 H
      (by unfold PlayerSpecificAlgebraicFourSmallDraw.bitCount; omega) bits).1=
      firstBitBlock H (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) bits := by
  simpa only [PlayerSpecificAlgebraicFourSmallDraw.bitCount] using
    PlayerSpecificBitSliceExecution.first_value RationalCostModel.schoolbook H
      (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) bits

theorem rest_value (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicFourSmallDraw.bitCount H K) → Bool) :
    (PlayerSpecificBitSliceExecution.run RationalCostModel.schoolbook
      (PlayerSpecificAlgebraicFourSmallDraw.bitCount H K) H
      (PlayerSpecificAlgebraicFourSmallDraw.remaining H K)
      (by unfold PlayerSpecificAlgebraicFourSmallDraw.bitCount; omega) bits).1=
      secondBitBlock H (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) bits := by
  simpa only [PlayerSpecificAlgebraicFourSmallDraw.bitCount] using
    PlayerSpecificBitSliceExecution.second_value RationalCostModel.schoolbook H
      (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) bits

theorem prefix_value (H K : ℕ) (bits : Fin (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) → Bool) :
    (PlayerSpecificBitSliceExecution.run RationalCostModel.schoolbook
      (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) 0 (8*H+K)
      (by simpa only [Nat.zero_add] using PlayerSpecificAlgebraicFourSmallDraw.uniform_bit_bound H K) bits).1=
      PlayerSpecificAlgebraicFourSmallDraw.takeBits
        (PlayerSpecificAlgebraicFourSmallDraw.uniform_bit_bound H K) bits := by
  rw [PlayerSpecificBitSliceExecution.value]
  funext j
  simp only [PlayerSpecificBitSliceExecution.address,
    PlayerSpecificAlgebraicFourSmallDraw.takeBits,Nat.zero_add]

def run (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicFourSmallDraw.bitCount H K) → Bool) :
    FixedArrayTable 4 Data×ℕ :=
  let model:=RationalCostModel.schoolbook
  let R:=PlayerSpecificAlgebraicFourSmallDraw.remaining H K
  let M:=PlayerSpecificAlgebraicFourSmallDraw.bitCount H K
  let head:=PlayerSpecificBitSliceExecution.run model M 0 H (by dsimp only [M,PlayerSpecificAlgebraicFourSmallDraw.bitCount]; omega) bits
  let rest:=PlayerSpecificBitSliceExecution.run model M H R (by dsimp only [M,PlayerSpecificAlgebraicFourSmallDraw.bitCount]; omega) bits
  let coin:=PlayerSpecificAlgebraicCoinExecution.run model r.root a.probability H head.1
  if coin.1 then
    let headBits:=PlayerSpecificBitSliceExecution.run model R 0 (8*H+K)
      (by simpa only [Nat.zero_add] using PlayerSpecificAlgebraicFourSmallDraw.uniform_bit_bound H K) rest.1
    let drawn:=PlayerSpecificFourMergedDrawExecution.run model r.root a H K headBits.1
    (drawn.1,head.2+rest.2+coin.2+headBits.2+drawn.2+price model [.control 1])
  else
    let drawn:=PlayerSpecificFourReflectedDrawExecution.run r a H K rest.1
    (drawn.1,head.2+rest.2+coin.2+drawn.2+price model [.control 1])

theorem value (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicFourSmallDraw.bitCount H K) → Bool) :
    (run r a H K bits).1=PlayerSpecificAlgebraicFourSmallDraw.draw r a H K bits := by
  dsimp only [run]
  simp only [head_value,rest_value,PlayerSpecificAlgebraicCoinExecution.value,
    PlayerSpecificAlgebraicFourSmallDraw.draw]
  split
  · simp only [prefix_value,PlayerSpecificFourMergedDrawExecution.value]
  · exact PlayerSpecificFourReflectedDrawExecution.value r a H K
      (secondBitBlock H (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) bits)

end Blotto.PlayerSpecificFourSmallDrawExecution
