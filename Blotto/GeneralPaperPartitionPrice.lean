import Blotto.GeneralPaperPartitionAssemblyPrice

/-! Complete sorting, deduplication, boundary materialization and adjacent
cell construction. Calibration and array-size equalities are erased;
the actual ordered list and both native arrays are returned exactly.
-/
namespace Blotto.GeneralPaperPartitionPrice
open GeneralPaperPartitionExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def profile (primitive : ℕ → ℕ) (W N U : ℕ) : ℕ :=
  GeneralPaperNaturalOrderPrice.profile N (arrayWord W (N+2)) (primitive (1+binaryWordWidth U))+
    GeneralPaperPartitionAssemblyPrice.profile primitive W N

def arithmeticProfile (N : ℕ) : ℕ :=
  GeneralPaperNaturalOrderPrice.profile N 1 1+GeneralPaperPartitionAssemblyPrice.arithmeticProfile N

theorem bit_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W U : ℕ) (points : List ℕ)
    (hPoints : ∀ x∈points,x≤U) :
    (run true (fun w => w) primitive W U points).2≤profile primitive W points.length U := by
  let A := localWord W points
  let ordered := GeneralPaperNaturalOrderPrice.run primitive A U points
  have hOrder := GeneralPaperNaturalOrderPrice.work primitive hMono A U points hPoints
  have hAssembly := GeneralPaperPartitionAssemblyPrice.bit_work primitive hMono W U points ordered.1
    (GeneralPaperNaturalOrderPrice.data primitive A U points)
  exact Nat.add_le_add hOrder hAssembly

theorem arithmetic_work (U : ℕ) (points : List ℕ) (hPoints : ∀ x∈points,x≤U) :
    (run false (fun _ => 1) (fun _ => 1) 1 U points).2≤arithmeticProfile points.length := by
  let ordered := GeneralPaperNaturalOrderPrice.run (fun _ => 1) 1 U points
  have hOrder := GeneralPaperNaturalOrderPrice.work (fun _ => 1) (fun _ _ _ => Nat.le_refl 1) 1 U points hPoints
  have hAssembly := GeneralPaperPartitionAssemblyPrice.arithmetic_work U points ordered.1
    (GeneralPaperNaturalOrderPrice.data (fun _ => 1) 1 U points)
  exact Nat.add_le_add hOrder hAssembly

theorem same_data (primitive : ℕ → ℕ) (W U : ℕ) (points : List ℕ) :
    (run true (fun w => w) primitive W U points).1=(run false (fun _ => 1) (fun _ => 1) 1 U points).1 := by
  rw [data,data]

end Blotto.GeneralPaperPartitionPrice
