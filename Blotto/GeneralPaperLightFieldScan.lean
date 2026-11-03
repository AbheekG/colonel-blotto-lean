import Blotto.GeneralPaperLightFieldReduction

/-! Native one-pass classification of the retained first-round integer
weights. The threshold multiplier is constructed by the caller once. The
loop stores original indices in reference arrays and sums only short light
weights. Scalar primitives and loop/reference writes are explicitly priced. -/
namespace Blotto.GeneralPaperLightFieldScan
open GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

structure State (n : ℕ) where
  heavy : Array (Fin n)
  light : Array (Fin n)
  lightWeight : ℕ

def scan {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ) :
    (count : ℕ) → count≤n → State n × ℕ
  | 0,_ => (⟨#[],#[],0⟩,64*address bits W n)
  | count+1,hc =>
    let old := scan bits model W r Q weights count (by omega)
    let j : Fin n := ⟨count,by omega⟩
    let value := weights.read j
    let product := r*value
    let A := address bits W n
    let p := if bits then model.rat else fun _ => 1
    let overhead := GeneralPaperNaturalPrimitivePrice.binary p (fun a b => a*b) r value+
      GeneralPaperIntegerWordPrice.compare p product Q+PaperIndexedArrayConstruction.stepWork (index bits) A count+64*A
    if product≤Q then
      (⟨old.1.heavy,old.1.light.push j,old.1.lightWeight+value⟩,old.2+overhead+
        GeneralPaperNaturalPrimitivePrice.binary p (fun a b => a+b) old.1.lightWeight value)
    else (⟨old.1.heavy.push j,old.1.light,old.1.lightWeight⟩,old.2+overhead)

theorem state_step {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count+1≤n) :
    (scan bits model W r Q weights (count+1) hc).1=
      if r*weights.read ⟨count,by omega⟩≤Q then
        ⟨(scan bits model W r Q weights count (by omega)).1.heavy,
          (scan bits model W r Q weights count (by omega)).1.light.push ⟨count,by omega⟩,
          (scan bits model W r Q weights count (by omega)).1.lightWeight+weights.read ⟨count,by omega⟩⟩
      else ⟨(scan bits model W r Q weights count (by omega)).1.heavy.push ⟨count,by omega⟩,
        (scan bits model W r Q weights count (by omega)).1.light,
        (scan bits model W r Q weights count (by omega)).1.lightWeight⟩ := by
  rw [scan]
  split_ifs <;> rfl

theorem light_mem {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) (j : Fin n) :
    j∈(scan bits model W r Q weights count hc).1.light ↔ j.val<count ∧ r*weights.read j≤Q := by
  induction count with
  | zero => simp only [scan,Array.not_mem_empty,Nat.not_lt_zero,false_and]
  | succ count ih =>
    rw [state_step]
    split_ifs with he
    · simp only [Array.mem_push,ih (by omega)]
      constructor
      · rintro (⟨hj,hp⟩|rfl)
        · exact ⟨by omega,hp⟩
        · exact ⟨Nat.lt_succ_self count,he⟩
      · intro ⟨hj,hp⟩
        by_cases hlt : j.val<count
        · exact Or.inl ⟨hlt,hp⟩
        · right; apply Fin.ext; change j.val=count; omega
    · rw [ih (by omega)]
      constructor
      · intro ⟨hj,hp⟩; exact ⟨by omega,hp⟩
      · intro ⟨hj,hp⟩
        have hne : j.val≠count := by
          intro hh
          have hj' : j=⟨count,by omega⟩ := Fin.ext hh
          rw [hj'] at hp
          exact he hp
        exact ⟨by omega,hp⟩

theorem heavy_mem {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) (j : Fin n) :
    j∈(scan bits model W r Q weights count hc).1.heavy ↔ j.val<count ∧ Q<r*weights.read j := by
  induction count with
  | zero => simp only [scan,Array.not_mem_empty,Nat.not_lt_zero,false_and]
  | succ count ih =>
    rw [state_step]
    split_ifs with he
    · rw [ih (by omega)]
      constructor
      · intro ⟨hj,hp⟩; exact ⟨by omega,hp⟩
      · intro ⟨hj,hp⟩
        have hne : j.val≠count := by
          intro hh
          have hj' : j=⟨count,by omega⟩ := Fin.ext hh
          rw [hj'] at hp
          exact (Nat.not_lt_of_ge he) hp
        exact ⟨by omega,hp⟩
    · simp only [Array.mem_push,ih (by omega)]
      constructor
      · rintro (⟨hj,hp⟩|rfl)
        · exact ⟨by omega,hp⟩
        · exact ⟨Nat.lt_succ_self count,by omega⟩
      · intro ⟨hj,hp⟩
        by_cases hlt : j.val<count
        · exact Or.inl ⟨hlt,hp⟩
        · right; apply Fin.ext; change j.val=count; omega

theorem sizes {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) :
    (scan bits model W r Q weights count hc).1.heavy.size+(scan bits model W r Q weights count hc).1.light.size=count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have h := ih (by omega)
    rw [state_step]
    split_ifs <;> simp only [Array.size_push] <;> omega

theorem light_weight {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) :
    (scan bits model W r Q weights count hc).1.lightWeight=
      ∑ i:Fin count,if r*weights.read ⟨i.val,by omega⟩≤Q then weights.read ⟨i.val,by omega⟩ else 0 := by
  induction count with
  | zero => simp only [scan,Finset.univ_eq_empty,Finset.sum_empty]
  | succ count ih =>
    rw [state_step]
    split_ifs with he
    · rw [ih (by omega),Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last,ite_eq_left he]
    · rw [ih (by omega),Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last,ite_eq_right he,Nat.add_zero]

theorem light_weight_le {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) :
    (scan bits model W r Q weights count hc).1.lightWeight≤(GeneralPaperValueWeightSum.scan bits model W weights count hc).1 := by
  rw [light_weight,GeneralPaperValueWeightSum.data]
  exact Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)

theorem light_nodup {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) : (scan bits model W r Q weights count hc).1.light.toList.Nodup := by
  induction count with
  | zero => simp only [scan,Array.toList_empty,List.nodup_nil]
  | succ count ih =>
    have h := ih (by omega)
    have hnot : (⟨count,by omega⟩:Fin n)∉(scan bits model W r Q weights count (by omega)).1.light.toList := by
      intro hm
      have hp := (light_mem bits model W r Q weights count (by omega) ⟨count,by omega⟩).mp
        (Array.mem_toList_iff.mp hm)
      exact (Nat.lt_irrefl count) hp.1
    rw [state_step]
    split_ifs
    · simpa only [Array.toList_push,List.concat_eq_append] using List.Nodup.concat hnot h
    · exact h

theorem heavy_nodup {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) : (scan bits model W r Q weights count hc).1.heavy.toList.Nodup := by
  induction count with
  | zero => simp only [scan,Array.toList_empty,List.nodup_nil]
  | succ count ih =>
    have h := ih (by omega)
    have hnot : (⟨count,by omega⟩:Fin n)∉(scan bits model W r Q weights count (by omega)).1.heavy.toList := by
      intro hm
      have hp := (heavy_mem bits model W r Q weights count (by omega) ⟨count,by omega⟩).mp
        (Array.mem_toList_iff.mp hm)
      exact (Nat.lt_irrefl count) hp.1
    rw [state_step]
    split_ifs
    · exact h
    · simpa only [Array.toList_push,List.concat_eq_append] using List.Nodup.concat hnot h

theorem models_data {n : ℕ} (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) :
    (scan true model W r Q weights count hc).1=(scan false model 1 r Q weights count hc).1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [state_step,state_step]
    rw [ih (by omega)]

end Blotto.GeneralPaperLightFieldScan
