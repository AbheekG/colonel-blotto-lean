import Blotto.GeneralPaperNativeLightBids

/-! Exact field-by-field native arc metadata, with the same integer
weights and original order as the mathematical reconstruction. Prefix
sums here are erased proof observers of the one-pass native builder. -/
namespace Blotto.GeneralPaperCircleMetadataExact
open GeneralPaperCircleArcPartition GeneralPaperCircleHardBudget
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem before_tail {g : ℕ} (R : ℕ) (weights : Fin (g+1) → ℕ) (c : ℕ) (hc : c≤g) :
    before (lengths R weights) (c+1)=R*weights ⟨0,by omega⟩+
      before (lengths R (fun a:Fin g => weights a.succ)) c := by
  induction c with
  | zero =>
    rw [before_step _ 0 (by omega)]
    simp only [before,lengths,Nat.zero_add,Nat.add_zero]
  | succ c ih =>
    rw [before_step (lengths R weights) (c+1) (by omega),
      before_step (lengths R (fun a:Fin g => weights a.succ)) c (by omega),ih (by omega)]
    simp only [lengths,Fin.succ_mk]
    omega

theorem data {g : ℕ} (price : ℕ → ℕ) (A R : ℕ) (weights : Fin g → ℕ) (offset : ℕ) :
    (GeneralPaperCircleArcMetadata.run price A R (List.ofFn weights) offset).1.arcs=
      List.ofFn (fun j:Fin g => (offset+before (lengths R weights) j.val,R*weights j)) := by
  induction g generalizing offset with
  | zero => rfl
  | succ g ih =>
    rw [List.ofFn_succ,GeneralPaperCircleArcMetadata.run,ih,List.ofFn_succ]
    apply congrArg₂ List.cons
    · rfl
    · apply congrArg List.ofFn
      funext j
      rw [Fin.val_succ,before_tail R weights j.val j.isLt.le]
      simp only [Fin.mk_zero]
      apply Prod.ext
      · omega
      · rfl

theorem selected_indices {g : ℕ} (model : RationalCostModel) (price : ℕ → ℕ) (A R W S : ℕ)
    (hR : 0<R) (hW : 0<W) (hS : 0<S) (l : Fin S) (weights : FixedArrayTable g ℕ)
    (hs : ∑ j,weights.read j=W) :
    let arcs := (GeneralPaperCircleArcMetadata.run price A R (List.ofFn weights.read) 0).1.arcs
    (GeneralPaperNativeCircleControlDraw.run model R W S l.val arcs).1.indices=
      List.ofFn (fun j:Fin g =>
        (GeneralPaperCircleCell.choice R W hR hW
          (GeneralPaperCircleCell.cell (R*W) (Nat.mul_pos hR hW)
            (GeneralPaperSelectedShift.selected (R*W) S (Nat.mul_pos hR hW) hS l).val
              (before (lengths R weights.read) j.val)) (R*weights.read j)).val) := by
  dsimp only
  have hSum : (List.ofFn weights.read).sum=W := by rw [List.sum_ofFn];exact hs
  rw [GeneralPaperNativeCircleControlDraw.prepared_correct model price A R W S hR hW hS l _ hSum,
    data,List.map_ofFn]
  simp only [Nat.zero_add,Function.comp_def]

end Blotto.GeneralPaperCircleMetadataExact
