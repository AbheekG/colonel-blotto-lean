import Blotto.GeneralPaperPartitionExecution

/-! Boundary materialization, descriptor-derived count subtraction and
the complete adjacent-cell fill. The local word includes the proved input
size cap; the explicit global reference word W remains in all profiles.
-/
namespace Blotto.GeneralPaperPartitionAssemblyPrice
open GeneralPaperPartitionExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def profile (primitive : ℕ → ℕ) (W N : ℕ) : ℕ :=
  64*(N+3)*arrayWord W (N+2)+GeneralPaperBoundaryCellPrice.profile primitive W (N+2)+
    2*primitive (GeneralPaperBoundaryCellPrice.width (N+2))+64*W

def arithmeticProfile (N : ℕ) : ℕ :=
  64*(N+3)+GeneralPaperBoundaryCellPrice.arithmeticProfile (N+2)+66

theorem count_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (N size : ℕ) (hSize : size≤N+2) :
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) size 1≤
      2*primitive (GeneralPaperBoundaryCellPrice.width (N+2)) := by
  have hWord : 1+binaryWordWidth (N+3)≤GeneralPaperBoundaryCellPrice.width (N+2) := by
    have h := binaryWordWidth_mono (show N+3≤N+2+2 by omega)
    unfold GeneralPaperBoundaryCellPrice.width
    omega
  exact (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono _ size 1 (N+3)
    (by omega) (by omega) (by omega)).trans (Nat.mul_le_mul_left 2 (hMono hWord))

theorem bit_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W U : ℕ) (points values : List ℕ)
    (hValues : values=GeneralPaperSortedBreakpoints.ordered U points) :
    (assemble true (fun w => w) primitive W U points values hValues).2≤profile primitive W points.length := by
  let A := localWord W points
  let array := PaperListReferenceArray.run (fun w => w) A values
  have hN : values.length≤points.length+2 := by rw [hValues]; exact GeneralPaperSortedBreakpoints.ordered_length U points
  have hSize : array.1.size=values.length := PaperListReferenceArray.size _ _ _
  have hPositive : 0<array.1.size := by rw [hSize,hValues]; exact GeneralPaperSortedBreakpoints.ordered_positive U points
  let boundary := table array.1 hPositive
  have hArray := PaperListReferenceArray.bit_work A values
    (GeneralPaperSummaryArrayControls.array_word_positive W (points.length+2))
    (GeneralPaperSummaryArrayControls.array_index W (points.length+2) values.length hN)
  have hArrayCap := Nat.mul_le_mul_right A (Nat.mul_le_mul_left 64 (show values.length+1≤points.length+3 by omega))
  have hCells := (GeneralPaperBoundaryCellPrice.bit_work primitive hMono W boundary).trans
    (GeneralPaperBoundaryCellPrice.profile_mono primitive hMono W (array.1.size-1) (points.length+2) (by omega))
  have hCount := count_work primitive hMono points.length array.1.size (by omega)
  change array.2+(GeneralPaperBoundaryCellPrice.run true (fun w => w) primitive W boundary).2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) array.1.size 1+64*W≤_
  change array.2≤_ at hArray
  unfold profile
  change _≤64*(points.length+3)*A+GeneralPaperBoundaryCellPrice.profile primitive W (points.length+2)+
    2*primitive (GeneralPaperBoundaryCellPrice.width (points.length+2))+64*W
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (hArray.trans hArrayCap) hCells) hCount) _

theorem arithmetic_work (U : ℕ) (points values : List ℕ) (hValues : values=GeneralPaperSortedBreakpoints.ordered U points) :
    (assemble false (fun _ => 1) (fun _ => 1) 1 U points values hValues).2≤arithmeticProfile points.length := by
  let array := PaperListReferenceArray.run (fun _ => 1) 1 values
  have hN : values.length≤points.length+2 := by rw [hValues]; exact GeneralPaperSortedBreakpoints.ordered_length U points
  have hSize : array.1.size=values.length := PaperListReferenceArray.size _ _ _
  have hPositive : 0<array.1.size := by rw [hSize,hValues]; exact GeneralPaperSortedBreakpoints.ordered_positive U points
  let boundary := table array.1 hPositive
  have hArray := PaperListReferenceArray.arithmetic_work values
  have hCells := (GeneralPaperBoundaryCellPrice.arithmetic_work boundary).trans
    (GeneralPaperBoundaryCellPrice.arithmetic_profile_mono (array.1.size-1) (points.length+2) (by omega))
  change array.2+(GeneralPaperBoundaryCellPrice.run false (fun _ => 1) (fun _ => 1) 1 boundary).2+2+64≤_
  change array.2≤_ at hArray
  unfold arithmeticProfile
  omega

end Blotto.GeneralPaperPartitionAssemblyPrice
