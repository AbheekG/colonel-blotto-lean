import Blotto.PlayerSpecificSegmentSelectionSourceCost

/-! Complete measured segment choice: constant-one mass, fair-block
offsets/materialization, actual selected loop and returned choice frame. -/
namespace Blotto.PlayerSpecificSegmentSelectionEntryExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots) (fallback : Fin slots)
    (H : ℕ) (bits : Fin ((slots-1)*H) → Bool) : (Fin slots×ℕ)×ℕ :=
  let initial:=PlayerSpecificFieldCombinationContract.constant root.polynomial 1
  let blocks:=PlayerSpecificResourceBlockExecution.blocks model (slots-1) H bits
  let items:=(List.finRange slots).take (slots-1)
  let result:=PlayerSpecificSegmentSelectionExecution.select model root d.weights fallback H items initial.1 blocks.1
  (result.1,price model initial.2+blocks.2+result.2+
    price model (PlayerSpecificSegmentSelectionExecution.frame root d.weights fallback H items initial.1 [] [] blocks.1.length result.1))

theorem value {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots) (fallback : Fin slots)
    (H : ℕ) (bits : Fin ((slots-1)*H) → Bool) :
    (run model root d fallback H bits).1=PlayerSpecificAlgebraicSegmentSample.selected model root d fallback H bits := by
  simp only [run,PlayerSpecificSegmentSelectionExecution.value,PlayerSpecificFieldCombinationContract.constant_value,
    PlayerSpecificResourceBlockExecution.blocks_value,PlayerSpecificAlgebraicSegmentSample.selected]

end Blotto.PlayerSpecificSegmentSelectionEntryExecution
