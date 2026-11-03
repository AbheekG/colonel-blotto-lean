import Blotto.PlayerSpecificInterpolationCoordinateSourceCost

/-! Actual measured interpolation computes the rational complement
and both scalar field rows once, retains both chosen endpoint arrays,
and caches each measured affine coordinate before returning the array. -/
namespace Blotto.PlayerSpecificSegmentInterpolationExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame {N slots : ℕ} (root : Candidate) (first second result : FixedArrayTable N Data) (slot : Fin slots)
    (q complement : ℚ) (left right : Data) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run
    ([root.polynomial,[root.interval.lo,root.interval.hi],[q,complement],left,right]++
      List.ofFn first.read++List.ofFn second.read++List.ofFn result.read)
    ([N,slots,slot.val,slot.val,1]++List.range N++List.range N++List.range N)

def run {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots) (slot : Fin slots) (q : ℚ) : FixedArrayTable N Data×ℕ :=
  let complement:=scalar .subtract 1 q
  let left:=PlayerSpecificFieldCombinationContract.constant root.polynomial complement.1
  let right:=PlayerSpecificFieldCombinationContract.constant root.polynomial q
  let first:=d.first.read slot
  let second:=d.second.read slot
  let coordinates:=FixedArrayTable.ofFn (fun j => PlayerSpecificInterpolationCoordinateExecution.run model root left.1 right.1 (first.read j) (second.read j))
  let result:=FixedArrayTable.ofFn (fun j => (coordinates.read j).1)
  (result,price model complement.2+price model left.2+price model right.2+(∑ j : Fin N,(coordinates.read j).2)+
    price model (frame root first second result slot q complement.1 left.1 right.1))

theorem value {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots) (slot : Fin slots) (q : ℚ) :
    (run model root d slot q).1=PlayerSpecificAlgebraicSegment.interpolate root d slot q := by
  simp only [run,FixedArrayTable.read_ofFn,PlayerSpecificInterpolationCoordinateExecution.value,
    PlayerSpecificFieldCombinationContract.constant_value,PlayerSpecificAlgebraicSegment.interpolate]
  rfl

end Blotto.PlayerSpecificSegmentInterpolationExecution
