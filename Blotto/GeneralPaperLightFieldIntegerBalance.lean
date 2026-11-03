import Blotto.GeneralPaperLightFieldOrder

/-! Erased conservation of the native classifier's short integer weights.
The heavy-index sum is a proof observer, never an extra executed pass. -/
namespace Blotto.GeneralPaperLightFieldIntegerBalance
open GeneralPaperLightFieldScan GeneralPaperLightFieldOrder
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000

noncomputable def weightSum {n : ℕ} (weights : FixedArrayTable n ℕ) (a : Array (Fin n)) : ℕ :=
  (a.toList.map weights.read).sum

theorem fin_sum {n : ℕ} (weights : FixedArrayTable n ℕ) (a : Array (Fin n)) :
    (∑ i:Fin a.size,weights.read (index a i))=weightSum weights a := by
  have ha : List.ofFn (index a)=a.toList := by
    rw [←Array.toList_ofFn]
    exact congrArg Array.toList (Array.ofFn_getElem (xs:=a))
  have h := congrArg (fun xs : List (Fin n) => (xs.map weights.read).sum) ha
  simpa only [List.map_ofFn,Function.comp_def,Fin.sum_ofFn,weightSum] using h

theorem empty {n : ℕ} (weights : FixedArrayTable n ℕ) : weightSum weights #[]=0 := rfl

theorem push {n : ℕ} (weights : FixedArrayTable n ℕ) (a : Array (Fin n)) (j : Fin n) :
    weightSum weights (a.push j)=weightSum weights a+weights.read j := by
  simp only [weightSum,Array.toList_push,List.map_append,List.map_cons,List.map_nil,List.sum_append,
    List.sum_cons,List.sum_nil,Nat.add_zero]

theorem prefix_balance {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) :
    weightSum weights (scan bits model W r Q weights count hc).1.heavy+
      (scan bits model W r Q weights count hc).1.lightWeight=
        (GeneralPaperValueWeightSum.scan bits model W weights count hc).1 := by
  rw [GeneralPaperValueWeightSum.data]
  induction count with
  | zero => simp only [scan,empty,Finset.univ_eq_empty,Finset.sum_empty,Nat.add_zero]
  | succ count ih =>
    have h := ih (by omega)
    rw [state_step,Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    split_ifs
    · dsimp only
      omega
    · simp only [push]
      omega

theorem classified {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) :
    let returned := (GeneralPaperLightFieldClassification.run bits model W k Q weights).1
    weightSum weights returned.1.heavy+returned.1.lightWeight=Q := by
  rw [GeneralPaperLightFieldClassification.data]
  have h := prefix_balance bits model W (GeneralPaperLightFieldScanContract.multiplier k) Q weights n le_rfl
  rw [GeneralPaperValueWeightSum.total,hs] at h
  exact h

theorem classified_light_positive {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q)
    (hl : 0<(GeneralPaperLightFieldClassification.run bits model W k Q weights).1.1.light.size) :
    0<(GeneralPaperLightFieldClassification.run bits model W k Q weights).1.1.lightWeight := by
  have hMass := GeneralPaperLightFieldClassification.light_mass bits model W k Q hQ weights hp hs
  have hSize := GeneralPaperLightFieldScanContract.light_size bits model W Q k hQ weights hp hs
  rw [GeneralPaperLightFieldClassification.data] at hl
  rw [hSize] at hl
  have h := GeneralPaperLightFieldReduction.mass_positive (GeneralPaperNativeRationalValues.selector Q hQ weights hp hs) k hl
  rw [←hMass] at h
  have hNum := (div_pos_iff.mp h).resolve_right (by intro hh; exact (not_lt_of_ge (Nat.cast_nonneg Q)) hh.2)
  exact_mod_cast hNum.1

end Blotto.GeneralPaperLightFieldIntegerBalance
