import Blotto.PlayerSpecificSweepPreparationBudget

/-! Complete cached/input/output copies in the one-time sweep caller,
with all record sizes derived from the actual input field row. -/
namespace Blotto.PlayerSpecificSweepPreparationCopyCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificRationalSweepHeights PlayerSpecificRationalTrace
open PlayerSpecificSweepPreparationBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cell_heights (model : RationalCostModel) (fields : List (ℚ×ℚ)) (H : ℕ)
    (hf : FieldsHeight fields H) (hH : 1≤H) :
    ∀ c∈(PlayerSpecificSweepPreparationExecution.run model fields).1,CellHeight c (height fields.length H) := by
  rw [PlayerSpecificSweepPreparationExecution.value]
  have hi:=PlayerSpecificRationalSweepHeights.initial_height fields H hf hH
  have hx:=suffix_height fields H hf hH
  have hb:=build_height (PlayerSpecificSweep.initial fields) 0 (PlayerSpecificSweepBounds.suffixes fields).2.1
    (initialBound fields.length H) H hi (zero_height.mono (by unfold initialBound; omega)) hx
  have hlen:=PlayerSpecificSuffixExecution.rows_length fields
  rw [(PlayerSpecificSuffixExecution.values fields).2] at hlen
  rw [hlen] at hb
  intro c hc
  exact PlayerSpecificRationalCellHeights.mono c _ _ (hb c hc) (profiles fields.length H).2.1

theorem frame_cost (model : RationalCostModel) (fields : List (ℚ×ℚ)) (H : ℕ)
    (hf : FieldsHeight fields H) (hH : 1≤H) :
    price model (PlayerSpecificSweepPreparationExecution.frame fields (PlayerSpecificSweepExecution.initial fields).1
      (PlayerSpecificSuffixExecution.run fields).1 (PlayerSpecificSweepPreparationExecution.run model fields).1)≤
      1000*(fields.length+2)*model.rat (width fields.length H) := by
  let N:=fields.length
  let G:=height N H
  let W:=width N H
  have hp:=profiles N H
  have hW : 6≤W := by dsimp only [W]; omega
  have hGW : 1+2*G≤W := by dsimp only [G,W]; omega
  have hinput:=price_bound model W (by omega) _ (PlayerSpecificSweepTraceFits.copy_fields_fits fields G W
    (fun x hx => ⟨(hf x hx).1.mono hp.2.2.2.2.2.2.2,(hf x hx).2.mono hp.2.2.2.2.2.2.2⟩)
    hGW (by dsimp only [N] at hp; dsimp only [W,N]; omega) (by omega))
  rw [PlayerSpecificSweepExecution.copy_fields_length] at hinput
  have hi:=PlayerSpecificSweepTraceFits.initial_height fields N H hf (by rfl) hH
  have hstate:=price_bound model W (by omega) _ (PlayerSpecificSweepTraceFits.copy_state_fits _ G W
    (state_mono _ _ _ hi hp.1) hGW hW)
  rw [PlayerSpecificSweepExecution.copy_state_length] at hstate
  have hs:=PlayerSpecificSuffixCost.returned_heights fields H hf hH
  have hmax:=price_bound model W (by omega) _ (copyRow_fits W [(PlayerSpecificSuffixExecution.run fields).1.1]
    (fun q hq => (rationalWordWidth_of_height ((cons_height (hs.1.mono hp.2.2.2.2.2.2.2) (nil_height _)) q hq)).trans hGW)
    (by simp; omega))
  rw [copyRow_length] at hmax
  have hrows:=price_bound model W (by omega) _ (PlayerSpecificSuffixCost.copy_fits (PlayerSpecificSuffixExecution.run fields).1.2 G W
    (fun x hx => ⟨(hs.2 x hx).1.mono hp.2.2.2.2.2.2.2,(hs.2 x hx).2.1.mono hp.2.2.2.2.2.2.2,
      (hs.2 x hx).2.2.mono hp.2.2.2.2.2.2.2⟩) hGW
    (by rw [PlayerSpecificSuffixExecution.rows_length]; dsimp only [N] at hp; dsimp only [W,N]; omega) (by omega))
  rw [PlayerSpecificSuffixExecution.copy_rows_length,PlayerSpecificSuffixExecution.rows_length] at hrows
  have hlen:=PlayerSpecificSweepPreparationExecution.count model fields
  have hcells:=PlayerSpecificCellConstructionCopyCost.cells_copy model _ G W (cell_heights model fields H hf hH)
    hp.2.2.2.2.2.1 (by rw [hlen]; dsimp only [N] at hp; dsimp only [W,N]; omega)
  rw [hlen] at hcells
  have hcontrols : Fits W [.control fields.length,.control (PlayerSpecificSweepPreparationExecution.run model fields).1.length] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · exact (PlayerSpecificRationalTrace.control_width _).trans (by dsimp only [N] at hp; dsimp only [W,N]; omega)
    · exact (PlayerSpecificRationalTrace.control_width _).trans (by rw [hlen]; dsimp only [N] at hp; dsimp only [W,N]; omega)
  have hctrl:=price_bound model W (by omega) _ hcontrols
  simp only [List.length_cons,List.length_nil] at hmax hctrl
  simp only [PlayerSpecificSweepPreparationExecution.frame,price_append]
  nlinarith only [hinput,hstate,hmax,hrows,hcells,hctrl]

end Blotto.PlayerSpecificSweepPreparationCopyCost
