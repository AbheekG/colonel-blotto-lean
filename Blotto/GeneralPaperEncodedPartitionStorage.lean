import Blotto.GeneralPaperEncodedSignedPlans

/-! Retained partitions own boundaries, adjacent endpoint pairs and the
literal count. Actual sorted/clamped construction derives all endpoint caps. -/
namespace Blotto.GeneralPaperEncodedPartitionStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def pairBits (W : ℕ) (cell : ℕ × ℕ) : ℕ := (1+binaryWordWidth cell.1)+(1+binaryWordWidth cell.2)+8*W

def footprint (W : ℕ) (part : GeneralPaperPreparedPartition.Prepared) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W part.boundaries+
    GeneralPaperEncodedFixedVector.footprint W (pairBits W) part.intervals+(1+binaryWordWidth part.count)+64*W

def profile (W L B : ℕ) : ℕ := (B+1)*(L+W)+B*(2*L+9*W)+128*W+B+2

theorem bounded (W L B : ℕ) (part : GeneralPaperPreparedPartition.Prepared) (hn : part.count≤B)
    (hb : ∀ i,1+binaryWordWidth (part.boundaries.read i)≤L)
    (hi : ∀ i,1+binaryWordWidth (part.intervals.read i).1≤L ∧ 1+binaryWordWidth (part.intervals.read i).2≤L) :
    footprint W part≤profile W L B := by
  have hBoundary := GeneralPaperEncodedNatArray.bounded_length W L (B+1) part.boundaries (Nat.add_le_add_right hn 1) hb
  have hCells := GeneralPaperEncodedFixedVector.bounded_length W (2*L+8*W) B (pairBits W) part.intervals hn (by
    intro i
    have h := hi i
    unfold pairBits
    omega)
  have hCount := GeneralPaperEncodedFixedVector.annotation part.count B hn
  unfold footprint profile
  nlinarith only [hBoundary,hCells,hCount]

theorem constructed (W L B U : ℕ) (points : List ℕ)
    (hn : (GeneralPaperPreparedPartition.build U points).count≤B) (hU : 1+binaryWordWidth U≤L) :
    footprint W (GeneralPaperPreparedPartition.build U points)≤profile W L B := by
  apply bounded W L B _ hn
  · intro i
    exact (Nat.add_le_add_left (binaryWordWidth_mono
      (GeneralPaperSortedBreakpoints.ordered_bound U points _ (GeneralPaperPreparedPartition.boundary_member U points i))) 1).trans hU
  · intro i
    have h := GeneralPaperActualEpochInstructions.bounds_of_build U points (GeneralPaperPreparedPartition.build U points) rfl i
    exact ⟨(Nat.add_le_add_left (binaryWordWidth_mono h.1) 1).trans hU,
      (Nat.add_le_add_left (binaryWordWidth_mono h.2) 1).trans hU⟩

end Blotto.GeneralPaperEncodedPartitionStorage
