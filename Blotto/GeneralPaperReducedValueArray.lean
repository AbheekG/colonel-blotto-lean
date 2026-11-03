import Blotto.GeneralPaperLightFieldIntegerBalance

/-! Native reduced-value arrays. A retained field reads its original short
integer weight by the returned index. The common representative value is
constructed once and copied by reference. No original-rational denominator
combination or second classifier pass is executed. -/
namespace Blotto.GeneralPaperReducedValueArray
open GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
open GeneralPaperDecodeBucketExecution (primitive)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def coordinate {n : ℕ} (bits : Bool) (model : RationalCostModel) (A : ℕ) (q representative : ℚ)
    (weights : FixedArrayTable n ℕ) (heavy : Array (Fin n)) {R : ℕ} (j : Fin (heavy.size+R)) : ℚ × ℕ :=
  let compare := GeneralPaperIntegerWordPrice.compare (index bits) j.val heavy.size
  if h : j.val<heavy.size then
    let w := weights.read heavy[j.val]
    ((w:ℚ)/q,primitive bits model (rationalWordWidth (w:ℚ))+
      GeneralPaperRationalPrimitivePrice.binary (primitive bits model) (fun a b => a/b) w q+compare+32*A)
  else (representative,compare+32*A)

def replaced {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q R lightWeight : ℕ)
    (weights : FixedArrayTable n ℕ) (heavy : Array (Fin n)) : FixedArrayTable (heavy.size+R) ℚ × ℕ :=
  let A := address bits W (n+heavy.size+R)
  let denominator := Q*R
  let q : ℚ := Q
  let rep : ℚ := (lightWeight:ℚ)/denominator
  let constructed := PaperIndexedArrayConstruction.run (index bits) A (coordinate bits model A q rep weights heavy)
  (constructed.1,constructed.2+
    GeneralPaperNaturalPrimitivePrice.binary (primitive bits model) (fun a b => a*b) Q R+
    primitive bits model (rationalWordWidth (denominator:ℚ))+
    primitive bits model (rationalWordWidth (lightWeight:ℚ))+
    primitive bits model (rationalWordWidth q)+
    GeneralPaperRationalPrimitivePrice.binary (primitive bits model) (fun a b => a/b) lightWeight denominator+128*A)

def identity {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q : ℕ) (weights : FixedArrayTable n ℕ) :
    FixedArrayTable n ℚ × ℕ :=
  let A := address bits W n
  let q : ℚ := Q
  let constructed := PaperIndexedArrayConstruction.run (index bits) A (fun j =>
    let w := weights.read j
    ((w:ℚ)/q,primitive bits model (rationalWordWidth (w:ℚ))+
      GeneralPaperRationalPrimitivePrice.binary (primitive bits model) (fun a b => a/b) w q+32*A))
  (constructed.1,constructed.2+primitive bits model (rationalWordWidth q)+128*A)

theorem replaced_data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q R lightWeight : ℕ)
    (weights : FixedArrayTable n ℕ) (heavy : Array (Fin n)) :
    (replaced bits model W Q R lightWeight weights heavy).1=FixedArrayTable.ofFn
      (fun j => if h:j.val<heavy.size then (weights.read heavy[j.val]:ℚ)/Q else (lightWeight:ℚ)/(Q*R:ℕ)) := by
  unfold replaced
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data]
  congr 1
  funext j
  unfold coordinate
  split_ifs <;> rfl

theorem identity_data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q : ℕ) (weights : FixedArrayTable n ℕ) :
    (identity bits model W Q weights).1=FixedArrayTable.ofFn (fun j => (weights.read j:ℚ)/Q) := by
  unfold identity
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data]

theorem heavy_read {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q R lightWeight : ℕ)
    (weights : FixedArrayTable n ℕ) (heavy : Array (Fin n)) (i : Fin heavy.size) :
    (replaced bits model W Q R lightWeight weights heavy).1.read (Fin.castAdd R i)=
      (weights.read heavy[i.val]:ℚ)/Q := by
  rw [replaced_data,FixedArrayTable.read_ofFn]
  simp only [Fin.val_castAdd,dite_eq_left i.isLt]

theorem representative_read {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q R lightWeight : ℕ)
    (weights : FixedArrayTable n ℕ) (heavy : Array (Fin n)) (i : Fin R) :
    (replaced bits model W Q R lightWeight weights heavy).1.read (Fin.natAdd heavy.size i)=
      (lightWeight:ℚ)/(Q*R:ℕ) := by
  rw [replaced_data,FixedArrayTable.read_ofFn]
  simp only [Fin.val_natAdd]
  rw [dite_eq_right (not_lt.mpr (Nat.le_add_right _ _))]

theorem replaced_positive {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q R lightWeight : ℕ)
    (hQ : 0<Q) (hR : 0<R) (hL : 0<lightWeight) (weights : FixedArrayTable n ℕ)
    (hp : ∀ j,0<weights.read j) (heavy : Array (Fin n)) (j : Fin (heavy.size+R)) :
    0<(replaced bits model W Q R lightWeight weights heavy).1.read j := by
  rw [replaced_data,FixedArrayTable.read_ofFn]
  split_ifs
  · exact div_pos (by exact_mod_cast hp _) (by exact_mod_cast hQ)
  · exact div_pos (by exact_mod_cast hL) (by exact_mod_cast Nat.mul_pos hQ hR)

theorem identity_positive {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hp : ∀ j,0<weights.read j) (j : Fin n) :
    0<(identity bits model W Q weights).1.read j := by
  rw [identity_data,FixedArrayTable.read_ofFn]
  exact div_pos (by exact_mod_cast hp j) (by exact_mod_cast hQ)

theorem replaced_sum {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q R lightWeight : ℕ)
    (hQ : 0<Q) (hR : 0<R) (weights : FixedArrayTable n ℕ) (heavy : Array (Fin n))
    (hs : GeneralPaperLightFieldIntegerBalance.weightSum weights heavy+lightWeight=Q) :
    (∑ j,(replaced bits model W Q R lightWeight weights heavy).1.read j)=1 := by
  rw [Fin.sum_univ_add]
  simp only [heavy_read,representative_read,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [←Finset.sum_div]
  have hWeights : (∑ i:Fin heavy.size,(weights.read heavy[i.val]:ℚ))=
      (GeneralPaperLightFieldIntegerBalance.weightSum weights heavy:ℚ) := by
    exact_mod_cast GeneralPaperLightFieldIntegerBalance.fin_sum weights heavy
  rw [hWeights]
  have hq : (Q:ℚ)≠0 := by exact_mod_cast hQ.ne'
  have hr : (R:ℚ)≠0 := by exact_mod_cast hR.ne'
  have hs' : (GeneralPaperLightFieldIntegerBalance.weightSum weights heavy:ℚ)+lightWeight=Q := by exact_mod_cast hs
  push_cast
  field_simp
  nlinarith only [hs']

theorem identity_sum {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Q : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hs : ∑ j,weights.read j=Q) :
    (∑ j,(identity bits model W Q weights).1.read j)=1 := by
  simp only [identity_data,FixedArrayTable.read_ofFn,←Finset.sum_div]
  have hh : (∑ j,(weights.read j:ℚ))=(Q:ℚ) := by exact_mod_cast hs
  rw [hh,div_self (by exact_mod_cast hQ.ne')]

theorem replaced_models {n : ℕ} (model : RationalCostModel) (W Q R lightWeight : ℕ)
    (weights : FixedArrayTable n ℕ) (heavy : Array (Fin n)) :
    (replaced true model W Q R lightWeight weights heavy).1=(replaced false model 1 Q R lightWeight weights heavy).1 := by
  rw [replaced_data,replaced_data]

theorem identity_models {n : ℕ} (model : RationalCostModel) (W Q : ℕ) (weights : FixedArrayTable n ℕ) :
    (identity true model W Q weights).1=(identity false model 1 Q weights).1 := by rw [identity_data,identity_data]

end Blotto.GeneralPaperReducedValueArray
