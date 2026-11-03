import Blotto.PlayerSpecificFieldMaterializationExecution

/-! Full materialization costs follow from the actual indexed rational
reads, measured control fee and returned-row copies at every prefix. -/
namespace Blotto.PlayerSpecificFieldMaterializationCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificFieldMaterializationExecution PlayerSpecificBitRatioSortBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem frame_cost {N : ℕ} (model : RationalCostModel) (j : Fin N) (ids : List (Fin N))
    (fields : List (ℚ×ℚ)) (H : ℕ) (hf : PlayerSpecificRationalSweepHeights.FieldsHeight fields H)
    (hids : ids.length≤N) (hfields : fields.length≤N) :
    price model (frame j ids fields)≤9*(fields.length+1)*model.rat (width N H) := by
  have hW : 6≤width N H := by unfold width; omega
  have hcopy:=PlayerSpecificSweepTraceFits.copy_fields_fits fields H (width N H) hf
    (by unfold width; omega) (by unfold width; omega) (by omega)
  have hctrl : Fits (width N H) [.control j.val,.control ids.length] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · exact (PlayerSpecificRationalTrace.control_width _).trans (by have hj:=j.isLt; unfold width; omega)
    · exact (PlayerSpecificRationalTrace.control_width _).trans (by unfold width; omega)
  have hp:=price_bound model (width N H) (by omega) _ ((fits_append _ _ _).mpr ⟨hcopy,hctrl⟩)
  change price model (frame j ids fields)≤_ at hp
  simp only [frame,List.length_append,PlayerSpecificSweepExecution.copy_fields_length,List.length_cons,List.length_nil] at hp
  unfold frame
  nlinarith only [hp]

theorem price_profile (n R tail copied A frame : ℕ) (ht : tail≤2000*(n+1)^2*R)
    (hc : copied≤9*R) (hA : A≤64*R) (hf : frame≤9*((n+1)+1)*R) :
    tail+copied+12*A+frame≤2000*((n+1)+1)^2*R := by
  have hnr : 0≤n*R := Nat.zero_le _
  nlinarith only [ht,hc,hA,hf,hnr]

theorem source_cost {N : ℕ} (model : RationalCostModel) (A H : ℕ) (v w : FixedArrayTable N ℚ)
    (hv : ∀ j,RationalHeight (v.read j) H) (hw : ∀ j,RationalHeight (w.read j) H)
    (hA : A≤64*model.rat (width N H)) (ids : List (Fin N)) (hids : ids.length≤N) :
    (run model A v w ids).2≤2000*(ids.length+1)^2*model.rat (width N H) := by
  induction ids with
  | nil =>
    have hp:=event_price model (width N H) (by unfold width; omega) (.control 0)
      ((PlayerSpecificRationalTrace.control_width 0).trans (by unfold width; omega))
    change price model [.control 0]≤3*model.rat (width N H) at hp
    exact hp.trans (Nat.mul_le_mul_right _ (by decide : 3≤2000*(0+1)^2))
  | cons j js ih =>
    have ht:=ih (by simp only [List.length_cons] at hids; omega)
    have hrow : HasHeight [v.read j,w.read j] H := cons_height (hv j) (cons_height (hw j) (nil_height _))
    have hc:=price_bound model (width N H) (by unfold width; omega) _ (copyRow_fits _ _
      (fun q hq => (rationalWordWidth_of_height (hrow q hq)).trans (by unfold width; omega)) (by simp; unfold width; omega))
    rw [copyRow_length] at hc
    simp only [List.length_cons,List.length_nil] at hc
    have hh:=heights model A H v w hv hw (j::js)
    have hlen:=length model A v w (j::js)
    have hf:=frame_cost model j (j::js) (run model A v w (j::js)).1 H hh hids (by rw [hlen]; exact hids)
    rw [hlen] at hf
    simp only [run] at hf ⊢
    simpa only [List.length_cons] using price_profile js.length _ _ _ A _ ht hc hA hf

end Blotto.PlayerSpecificFieldMaterializationCost
