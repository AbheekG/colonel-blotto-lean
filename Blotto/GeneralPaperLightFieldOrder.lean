import Blotto.GeneralPaperLightFieldClassification

/-! Both native index arrays preserve original battlefield order, including
every reached prefix. The reduced-value and circle reconstruction phases
can therefore use their actual returned indices without sorting or a new
original-weight lookup pass. -/
namespace Blotto.GeneralPaperLightFieldOrder
open GeneralPaperLightFieldScan
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem heavy_ordered {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) :
    (scan bits model W r Q weights count hc).1.heavy.toList.Pairwise (fun i j => i<j) := by
  induction count with
  | zero => exact List.Pairwise.nil
  | succ count ih =>
    have h := ih (by omega)
    rw [state_step]
    split_ifs
    · exact h
    · rw [Array.toList_push,List.pairwise_append]
      refine ⟨h,by simp,?_⟩
      intro i hi j hj
      simp only [List.mem_singleton] at hj
      subst j
      exact ((heavy_mem bits model W r Q weights count (by omega) i).mp (Array.mem_toList_iff.mp hi)).1

theorem light_ordered {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) :
    (scan bits model W r Q weights count hc).1.light.toList.Pairwise (fun i j => i<j) := by
  induction count with
  | zero => exact List.Pairwise.nil
  | succ count ih =>
    have h := ih (by omega)
    rw [state_step]
    split_ifs
    · rw [Array.toList_push,List.pairwise_append]
      refine ⟨h,by simp,?_⟩
      intro i hi j hj
      simp only [List.mem_singleton] at hj
      subst j
      exact ((light_mem bits model W r Q weights count (by omega) i).mp (Array.mem_toList_iff.mp hi)).1
    · exact h

def index {n : ℕ} (a : Array (Fin n)) (i : Fin a.size) : Fin n := a[i.val]

theorem index_strictMono {n : ℕ} (a : Array (Fin n)) (h : a.toList.Pairwise (fun i j => i<j)) :
    StrictMono (index a) := by
  intro i j hij
  have hr := h.rel_getElem_of_lt (i:=i.val) (j:=j.val) (by simpa only [Array.length_toList] using i.isLt)
    (by simpa only [Array.length_toList] using j.isLt) hij
  simpa only [Array.getElem_toList,index] using hr

theorem returned_order {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    let returned := (GeneralPaperLightFieldClassification.run bits model W k Q weights).1
    StrictMono (index returned.1.heavy) ∧ StrictMono (index returned.1.light) := by
  rw [GeneralPaperLightFieldClassification.data]
  exact ⟨index_strictMono _ (heavy_ordered bits model W _ Q weights n le_rfl),
    index_strictMono _ (light_ordered bits model W _ Q weights n le_rfl)⟩

end Blotto.GeneralPaperLightFieldOrder
