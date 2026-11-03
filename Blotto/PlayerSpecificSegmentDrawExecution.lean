import Blotto.PlayerSpecificBitSlicePolynomial

/-! Complete measured finite segment draw. Packet counts and both
actual addressed slices are computed once, followed by measured choice,
midpoint and interpolation on exactly those cached packets. -/
namespace Blotto.PlayerSpecificSegmentDrawExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (H K headBits count : ℕ)
    (choice : Fin slots×ℕ) (result : FixedArrayTable N Data) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run
    ([root.polynomial,[root.interval.lo,root.interval.hi]]++PlayerSpecificDescriptorProgramExecution.rows d++List.ofFn result.read)
    ([N,slots,H,K,headBits,count,choice.1.val,choice.2,1]++List.range N++List.range slots)

def run {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots) (fallback : Fin slots) (H K : ℕ)
    (bits : Fin ((slots-1)*H+K) → Bool) : FixedArrayTable N Data×ℕ :=
  let headBits:=PlayerSpecificNaturalExecution.binary model (fun a b => a*b) (slots-1) H
  let count:=PlayerSpecificNaturalExecution.binary model (fun a b => a+b) headBits.1 K
  let coins:=PlayerSpecificBitSliceExecution.run model count.1 0 headBits.1 (by change 0+(slots-1)*H≤(slots-1)*H+K; omega) bits
  let scalar:=PlayerSpecificBitSliceExecution.run model count.1 headBits.1 K (Nat.le_refl _) bits
  let choice:=PlayerSpecificSegmentSelectionEntryExecution.run model root d fallback H coins.1
  let midpoint:=PlayerSpecificMidpointExecution.run model K scalar.1
  let result:=PlayerSpecificSegmentInterpolationExecution.run model root d choice.1.1 midpoint.1
  (result.1,headBits.2+count.2+coins.2+scalar.2+choice.2+midpoint.2+result.2+
    price model (frame root d H K headBits.1 count.1 choice.1 result.1))

theorem value {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots) (fallback : Fin slots) (H K : ℕ)
    (bits : Fin ((slots-1)*H+K) → Bool) :
    (run model root d fallback H K bits).1=PlayerSpecificAlgebraicSegmentSample.sample model root d fallback H K bits := by
  dsimp only [run,PlayerSpecificNaturalExecution.binary]
  simp only [PlayerSpecificSegmentInterpolationExecution.value,PlayerSpecificSegmentSelectionEntryExecution.value,
    PlayerSpecificMidpointExecution.value,PlayerSpecificBitSliceExecution.first_value,PlayerSpecificBitSliceExecution.second_value,
    PlayerSpecificAlgebraicSegmentSample.sample]

end Blotto.PlayerSpecificSegmentDrawExecution
