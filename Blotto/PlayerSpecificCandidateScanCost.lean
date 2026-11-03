import Blotto.PlayerSpecificCandidateScanCopyCost

/-! All finite candidate prefixes, whether accepted or rejected, have a
complete scan price. The public contract supplies these local bounds from
the executed cubic candidates and the checked exact acceptance caller. -/
namespace Blotto.PlayerSpecificCandidateScanCost
open PlayerSpecificRationalCells PlayerSpecificRationalCellHeights PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace
open PlayerSpecificCandidateScanExecution
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem run_cost (model : RationalCostModel) (c : Cell) (rows : List Candidate) (H W C : ℕ)
    (hc : CellHeight c H) (hW : 128*(H+1)≤W) (hlen : rows.length≤3)
    (hrows : ∀ r∈rows,price model (PlayerSpecificCandidateSelection.copyCandidate r)≤81*model.rat W)
    (htest : ∀ r∈rows,(PlayerSpecificCandidateTestExecution.run model c r).2≤C*(H+1)*model.rat W) :
    (run model c rows).2≤(C*(H+1)+500)*(rows.length+1)*model.rat W := by
  induction rows with
  | nil =>
    have hf:=PlayerSpecificCandidateScanCopyCost.frame_cost model c H W hc hW [] hlen hrows none (by simp)
    simp only [PlayerSpecificCandidateScanExecution.run,List.length_nil,Nat.zero_add,Nat.mul_one]
    exact hf.trans (Nat.mul_le_mul_right _ (by omega))
  | cons r rs ih =>
    have ht:=htest r List.mem_cons_self
    have hi:=ih (by simp only [List.length_cons] at hlen; omega)
      (fun d hd => hrows d (List.mem_cons_of_mem r hd))
      (fun d hd => htest d (List.mem_cons_of_mem r hd))
    have hfSome:=PlayerSpecificCandidateScanCopyCost.frame_cost model c H W hc hW (r::rs) hlen hrows (some r) (by
      intro d hd
      have he : r=d := by simpa only [Option.mem_def,Option.some.injEq] using hd
      rw [←he]
      exact List.mem_cons_self)
    have hfRest:=PlayerSpecificCandidateScanCopyCost.frame_cost model c H W hc hW (r::rs) hlen hrows (run model c rs).1 (by
      intro d hd
      exact List.mem_cons_of_mem r (returned_mem model c rs d hd))
    rw [PlayerSpecificCandidateScanExecution.run]
    dsimp only
    split <;> simp only [List.length_cons]
    · nlinarith only [ht,hfSome]
    · nlinarith only [ht,hi,hfRest]

end Blotto.PlayerSpecificCandidateScanCost
