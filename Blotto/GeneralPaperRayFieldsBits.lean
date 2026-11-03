import Blotto.GeneralPaperRayCostBits

/-! Materialize each fixed-probe ray field once, reusing the stored score
matrix. All ray costs and array/reference/control traffic are priced. The
data are exactly the fields of the selected native fixed-point query.
-/
namespace Blotto.GeneralPaperRayFieldsBits
open RationalOrderCell GeneralPaperExactScoreDP GeneralPaperRayRationalBound
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000

def fieldRun {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ) (j : Fin m) : Field K × ℕ :=
  PaperIndexedArrayConstruction.run (fun w => w) W (fun l =>
    let value := GeneralPaperRayCostBits.run model W x w t j l
    ((GeneralPaperRayQueryWork.scores matrix j l,value.1),value.2+8*W))

theorem field_data {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ) (j : Fin m) :
    (fieldRun model W matrix x w t j).1=FixedArrayTable.ofFn
      (fun l => (GeneralPaperRayQueryWork.scores matrix j l,GeneralPaperRayAnchorCosts.costs x w t j l)) := by
  simp only [fieldRun,PaperIndexedArrayConstruction.run_data,GeneralPaperRayCostBits.data]

theorem field_work {m K : ℕ} (model : RationalCostModel) (W D E X V : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a)) (t : ℚ) (ht : 0≤t ∧ t≤1)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (j : Fin m) :
    (fieldRun model W matrix x w t j).2≤128*(K+1)*
      (W+model.rat (GeneralPaperCommonLatticeDPBits.width (D*t.den) (X+V+1) m)) := by
  let P := model.rat (GeneralPaperCommonLatticeDPBits.width (D*t.den) (X+V+1) m)
  have hEach (l : Fin K) : (GeneralPaperRayCostBits.run model W x w t j l).2+8*W≤32*W+4*P := by
    have hh := GeneralPaperRayCostBits.work model W D E X V hD hED x w hx hw t ht j l
    omega
  have hs := Finset.sum_le_sum (fun l (_ : l∈Finset.univ) => hEach l)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have ha := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fun l => let value := GeneralPaperRayCostBits.run model W x w t j l
      ((GeneralPaperRayQueryWork.scores matrix j l,value.1),value.2+8*W))
  change (fieldRun model W matrix x w t j).2≤_ at ha
  simp only [Nat.mul_one] at ha
  have ho : 6*W+10*binaryWordWidth (K+1)+28≤44*W := by omega
  have hb := Nat.mul_le_mul_left (K+1) ho
  nlinarith only [ha,hs,hb]

def matrixRun {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ) : FixedArrayTable m (Field K) × ℕ :=
  PaperIndexedArrayConstruction.run (fun w => w) W (fieldRun model W matrix x w t)

theorem matrix_data {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ) :
    (matrixRun model W matrix x w t).1=FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn
      (fun l => (GeneralPaperRayQueryWork.scores matrix j l,GeneralPaperRayAnchorCosts.costs x w t j l))) := by
  simp only [matrixRun,PaperIndexedArrayConstruction.run_data,field_data]

theorem matrix_work {m K : ℕ} (model : RationalCostModel) (W D E X V : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a)) (t : ℚ) (ht : 0≤t ∧ t≤1)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) :
    (matrixRun model W matrix x w t).2≤256*(m+1)*(K+1)*
      (W+model.rat (GeneralPaperCommonLatticeDPBits.width (D*t.den) (X+V+1) m)) := by
  let P := model.rat (GeneralPaperCommonLatticeDPBits.width (D*t.den) (X+V+1) m)
  have hs := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) =>
    field_work model W D E X V hD hED matrix x w hx hw t ht hW hK j)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have ha := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fieldRun model W matrix x w t)
  change (matrixRun model W matrix x w t).2≤_ at ha
  have ho : 6*W+10*binaryWordWidth (m+1)+28≤44*W := by omega
  have hb := Nat.mul_le_mul_left (m+1) ho
  have hc : (m+1)*W≤(m+1)*(K+1)*(W+P) := by
    nlinarith only [Nat.zero_le ((m+1)*K*W),Nat.zero_le ((m+1)*(K+1)*P)]
  change (∑ j,(fieldRun model W matrix x w t j).2)≤m*(128*(K+1)*(W+P)) at hs
  nlinarith only [ha,hs,hb,hc,Nat.zero_le ((K+1)*(W+P))]

def fieldsRun {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ) : List (Field K) × ℕ :=
  let result := matrixRun model W matrix x w t
  (result.1.data.toList,result.2+(8*m+4)*W)

theorem fields_data {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ) :
    (fieldsRun model W matrix x w t).1=
      fields (GeneralPaperRayQueryWork.scores matrix) (GeneralPaperRayAnchorCosts.costs x w t) := by
  simp only [fieldsRun,matrix_data,FixedArrayTable.ofFn,Array.toList_ofFn,fields]

theorem fields_work {m K : ℕ} (model : RationalCostModel) (W D E X V : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a)) (t : ℚ) (ht : 0≤t ∧ t≤1)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) :
    (fieldsRun model W matrix x w t).2≤512*(m+1)*(K+1)*
      (W+model.rat (GeneralPaperCommonLatticeDPBits.width (D*t.den) (X+V+1) m)) := by
  let P := model.rat (GeneralPaperCommonLatticeDPBits.width (D*t.den) (X+V+1) m)
  have hm := matrix_work model W D E X V hD hED matrix x w hx hw t ht hW hK hM
  have hc : (m+1)*W≤(m+1)*(K+1)*(W+P) := by
    nlinarith only [Nat.zero_le ((m+1)*K*W),Nat.zero_le ((m+1)*(K+1)*P)]
  change (matrixRun model W matrix x w t).2+(8*m+4)*W≤_
  change (matrixRun model W matrix x w t).2≤256*(m+1)*(K+1)*(W+P) at hm
  nlinarith only [hm,hc]

theorem fields_bounded {m K : ℕ} (model : RationalCostModel) (W D E X V : ℕ) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a)) (t : ℚ) (ht : 0≤t ∧ t≤1) :
    ∀ f∈(fieldsRun model W matrix x w t).1,∀ l,Bounded (D*t.den) (X+V+1) (f.read l).2 := by
  rw [fields_data]
  intro f hf l
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf
  simpa only [FixedArrayTable.read_ofFn] using
    (GeneralPaperRayCostBits.operands D E X V hED x w hx hw t ht j l).2.2.2.2

end Blotto.GeneralPaperRayFieldsBits
