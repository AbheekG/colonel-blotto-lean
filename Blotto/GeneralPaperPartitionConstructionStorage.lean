import Blotto.GeneralPaperBoundaryConstructionStorage

/-! Complete native ordered-partition construction at its actual local
array word: natural ordering, list packing, adjacent-cell fill, descriptors,
returned arrays and primitive scratch. Global word calibration is separate. -/
namespace Blotto.GeneralPaperPartitionConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def packingProfile (A U N : ℕ) : ℕ :=
  N*(natBits U+2*A)+32*A+2*(N*(natBits U+A)+64*A)+
    GeneralPaperGridArrayConstructionStorage.frames A N+128*A

theorem packing_bound (A U N copied : ℕ) (xs : List ℕ) (hn : xs.length≤N) (hx : ∀ x∈xs,x≤U) :
    GeneralPaperGridArrayConstructionStorage.packingWindow A copied xs≤packingProfile A U N := by
  have h := GeneralPaperGridArrayConstructionStorage.packing_window A U copied xs hx
  have h0 := Nat.mul_le_mul_right (natBits U+2*A) hn
  have h1 := Nat.mul_le_mul_right (natBits U+A) hn
  have h2 := GeneralPaperBoundaryConstructionStorage.frames_mono A xs.length N hn
  unfold packingProfile
  omega

def metadata (A U : ℕ) (points : List ℕ) : ℕ :=
  fields A [points.length,(GeneralPaperSortedBreakpoints.ordered U points).length,
    (GeneralPaperPreparedPartition.build U points).count]

theorem metadata_bound (A U : ℕ) (points : List ℕ) : metadata A U points≤
    3*(natBits (points.length+2)+A)+32*A := by
  have hlen := GeneralPaperSortedBreakpoints.ordered_length U points
  have hc := GeneralPaperPreparedPartition.count_bound U points
  apply fields_bound A (natBits (points.length+2))
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl <;> unfold natBits <;>
    exact Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1

def window (model : RationalCostModel) (W U : ℕ) (points : List ℕ) (copied count : ℕ)
    (hc : count≤(GeneralPaperPreparedPartition.build U points).count) : ℕ :=
  let A := GeneralPaperPartitionExecution.localWord W points
  let part := GeneralPaperPreparedPartition.build U points
  GeneralPaperNaturalOrderConstructionStorage.window model A U points+
    GeneralPaperGridArrayConstructionStorage.packingWindow A copied (GeneralPaperSortedBreakpoints.ordered U points)+
    GeneralPaperBoundaryConstructionStorage.window model W A U part.boundaries count hc+
    GeneralPaperEncodedPartitionStorage.footprint A (GeneralPaperPartitionExecution.run true (fun w => w) model.rat W U points).1+
    metadata A U points+(GeneralPaperPartitionExecution.run true (fun w => w) model.rat W U points).2+256*A

def profile (model : RationalCostModel) (W U n : ℕ) : ℕ :=
  let A := GeneralPaperSummaryArrayExecution.arrayWord W (n+2)
  GeneralPaperNaturalOrderConstructionStorage.profile model A U n+packingProfile A U (n+2)+
    GeneralPaperBoundaryConstructionStorage.profile model W A U (n+1)+
    GeneralPaperEncodedPartitionStorage.profile A (natBits U) (n+1)+3*(natBits (n+2)+A)+32*A+
    GeneralPaperPartitionPrice.profile model.rat W n U+256*A

theorem bounded (model : RationalCostModel) (W U : ℕ) (points : List ℕ)
    (hx : ∀ x∈points,x≤U) (copied count : ℕ) (hc : count≤(GeneralPaperPreparedPartition.build U points).count) :
    window model W U points copied count hc≤profile model W U points.length := by
  let A := GeneralPaperPartitionExecution.localWord W points
  let part := GeneralPaperPreparedPartition.build U points
  have hcount : part.count≤points.length+1 := GeneralPaperPreparedPartition.count_bound U points
  have hbound : ∀ i,part.boundaries.read i≤U := fun i =>
    GeneralPaperSortedBreakpoints.ordered_bound U points _ (GeneralPaperPreparedPartition.boundary_member U points i)
  have hs := GeneralPaperNaturalOrderConstructionStorage.bounded model A U points hx
  have hp := packing_bound A U (points.length+2) copied (GeneralPaperSortedBreakpoints.ordered U points)
    (GeneralPaperSortedBreakpoints.ordered_length U points) (GeneralPaperSortedBreakpoints.ordered_bound U points)
  have hb := GeneralPaperBoundaryConstructionStorage.bounded model W A U (points.length+1) part.boundaries hcount hbound count hc
  have hr := GeneralPaperEncodedPartitionStorage.constructed A (natBits U) (points.length+1) U points hcount (Nat.le_refl _)
  have hm := metadata_bound A U points
  have hw := GeneralPaperPartitionPrice.bit_work model.rat model.monotone W U points hx
  unfold window profile
  dsimp only
  rw [GeneralPaperPartitionExecution.data]
  change GeneralPaperNaturalOrderConstructionStorage.window model A U points+
    GeneralPaperGridArrayConstructionStorage.packingWindow A copied (GeneralPaperSortedBreakpoints.ordered U points)+
    GeneralPaperBoundaryConstructionStorage.window model W A U part.boundaries count hc+
    GeneralPaperEncodedPartitionStorage.footprint A part+metadata A U points+
    (GeneralPaperPartitionExecution.run true (fun w => w) model.rat W U points).2+256*A≤_
  dsimp only [A,part,GeneralPaperPartitionExecution.localWord] at *
  omega

theorem returned (model : RationalCostModel) (W U : ℕ) (points : List ℕ) :
    GeneralPaperEncodedPartitionStorage.footprint (GeneralPaperPartitionExecution.localWord W points)
      (GeneralPaperPartitionExecution.run true (fun w => w) model.rat W U points).1≤
      GeneralPaperEncodedPartitionStorage.profile (GeneralPaperPartitionExecution.localWord W points) (natBits U) (points.length+1) := by
  rw [GeneralPaperPartitionExecution.data]
  exact GeneralPaperEncodedPartitionStorage.constructed _ _ _ U points
    (GeneralPaperPreparedPartition.count_bound U points) (Nat.le_refl _)

end Blotto.GeneralPaperPartitionConstructionStorage
