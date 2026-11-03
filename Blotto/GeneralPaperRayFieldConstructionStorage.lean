import Blotto.GeneralPaperRayCostStorage

/-! Actual ray-field construction with one outer and one current-field
reservation, both constructor stacks, a complete current arithmetic window
and borrowed list nodes. All native parent/return counters are encoded.
The input score matrix, point and direction belong to the enclosing query. -/
namespace Blotto.GeneralPaperRayFieldConstructionStorage
open RationalOrderCell GeneralPaperExactScoreDP GeneralPaperRayRationalBound
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedReferenceVector
open GeneralPaperEncodedScoreMatrixStorage GeneralPaperScoreConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

def entry {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ) (j : Fin m) (l : Fin K) : (ℕ×ℚ)×ℕ :=
  let value := GeneralPaperRayCostBits.run model W x w t j l
  ((GeneralPaperRayQueryWork.scores matrix j l,value.1),value.2+8*W)

def fieldPrice (model : RationalCostModel) (W K D M m : ℕ) : ℕ :=
  128*(K+1)*(W+model.rat (GeneralPaperCommonLatticeDPBits.width D M m))

def matrixPrice (model : RationalCostModel) (W m K D M : ℕ) : ℕ :=
  256*(m+1)*(K+1)*(W+model.rat (GeneralPaperCommonLatticeDPBits.width D M m))

def fieldsPrice (model : RationalCostModel) (W m K D M : ℕ) : ℕ :=
  512*(m+1)*(K+1)*(W+model.rat (GeneralPaperCommonLatticeDPBits.width D M m))

def metadataCap (model : RationalCostModel) (W m K S D M : ℕ) : ℕ :=
  m+K+S+1+fieldPrice model W K D M m+matrixPrice model W m K D M+
    fieldsPrice model W m K D M+(8*m+4)*W

theorem entry_bound {m K : ℕ} (model : RationalCostModel) (W S D E X V : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (hs : ∀ j l,((matrix.read j).read l).1≤S)
    (x w : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a))
    (t : ℚ) (ht : 0≤t ∧ t≤1) (j : Fin m) (l : Fin K) :
    entryFootprint W (entry model W matrix x w t j l).1≤
      entryProfile W S (GeneralPaperRayMinimumStorage.height (D*t.den) (X+V+1)) :=
  GeneralPaperEncodedScoreMatrixStorage.entry_bound W S _ _ (hs j l)
    ((GeneralPaperRayCostBits.operands D E X V hED x w hx hw t ht j l).2.2.2.2.height (Nat.mul_pos hD t.den_pos))

theorem field_bound {m K : ℕ} (model : RationalCostModel) (W S D E X V : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (hs : ∀ j l,((matrix.read j).read l).1≤S)
    (x w : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a))
    (t : ℚ) (ht : 0≤t ∧ t≤1) (j : Fin m) :
    fieldFootprint W (GeneralPaperRayFieldsBits.fieldRun model W matrix x w t j).1≤
      fieldProfile W K S (GeneralPaperRayMinimumStorage.height (D*t.den) (X+V+1)) := by
  rw [GeneralPaperRayFieldsBits.field_data]
  apply GeneralPaperEncodedScoreMatrixStorage.field_bound
  · intro l
    simpa only [FixedArrayTable.read_ofFn,GeneralPaperRayQueryWork.scores] using hs j l
  · intro l
    simp only [FixedArrayTable.read_ofFn]
    exact (GeneralPaperRayCostBits.operands D E X V hED x w hx hw t ht j l).2.2.2.2.height (Nat.mul_pos hD t.den_pos)

def window {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ)
    (outer : ℕ) (ho : outer≤m) (j : Fin m) (inner : ℕ) (hi : inner≤K) (l : Fin K) : ℕ :=
  let generated := GeneralPaperRayFieldsBits.matrixRun model W matrix x w t
  let inputs := GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t
  reservedFootprint W m (fieldFootprint W) (PaperIndexedArrayConstruction.fill (fun w => w) W
      (GeneralPaperRayFieldsBits.fieldRun model W matrix x w t) outer ho).1+
    reservedFootprint W K (entryFootprint W) (PaperIndexedArrayConstruction.fill (fun w => w) W
      (entry model W matrix x w t j) inner hi).1+
    constructorFrames (fun w => w) W W (GeneralPaperRayFieldsBits.fieldRun model W matrix x w t) outer ho+
    constructorFrames (fun w => w) W W (entry model W matrix x w t j) inner hi+
    GeneralPaperRayCostStorage.window model W (GeneralPaperRayQueryWork.scores matrix j l) x w t j l+
    listFootprint W (fun _ : Field K => 0) inputs.1+
    fields W [m,K,(GeneralPaperRayFieldsBits.fieldRun model W matrix x w t j).2,
      generated.2,inputs.2,(8*m+4)*W,generated.2+(8*m+4)*W]+256*W

def profile (model : RationalCostModel) (W m K S D M : ℕ) : ℕ :=
  matrixProfile W m K S (GeneralPaperRayMinimumStorage.height D M)+
    fieldProfile W K S (GeneralPaperRayMinimumStorage.height D M)+
    constructorProfile W m (matrixPrice model W m K D M)+constructorProfile W K (fieldPrice model W K D M m)+
    GeneralPaperRayCostStorage.profile model W m K S D M+m*(2*W)+32*W+
    7*(natBits (metadataCap model W m K S D M)+W)+32*W+256*W

theorem bounded {m K : ℕ} (model : RationalCostModel) (W S D E X V : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (hs : ∀ j l,((matrix.read j).read l).1≤S)
    (x w : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a))
    (t : ℚ) (ht : 0≤t ∧ t≤1) (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (outer : ℕ) (ho : outer≤m) (j : Fin m) (inner : ℕ) (hi : inner≤K) (l : Fin K) :
    window model W matrix x w t outer ho j inner hi l≤profile model W m K S (D*t.den) (X+V+1) := by
  let generated := GeneralPaperRayFieldsBits.matrixRun model W matrix x w t
  let inputs := GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t
  have hOuter := indexed_reserved_prefix (fun w => w) W W
    (fieldProfile W K S (GeneralPaperRayMinimumStorage.height (D*t.den) (X+V+1))) (fieldFootprint W)
    (GeneralPaperRayFieldsBits.fieldRun model W matrix x w t)
    (fun j => field_bound model W S D E X V hD hED matrix hs x w hx hw t ht j) outer ho
  have hInner := indexed_reserved_prefix (fun w => w) W W
    (entryProfile W S (GeneralPaperRayMinimumStorage.height (D*t.den) (X+V+1))) (entryFootprint W)
    (entry model W matrix x w t j)
    (fun l => entry_bound model W S D E X V hD hED matrix hs x w hx hw t ht j l) inner hi
  have hFW := GeneralPaperRayFieldsBits.field_work model W D E X V hD hED matrix x w hx hw t ht hW hK j
  have hMW := GeneralPaperRayFieldsBits.matrix_work model W D E X V hD hED matrix x w hx hw t ht hW hK hM
  have hLW := GeneralPaperRayFieldsBits.fields_work model W D E X V hD hED matrix x w hx hw t ht hW hK hM
  change (GeneralPaperRayFieldsBits.fieldRun model W matrix x w t j).2≤fieldPrice model W K (D*t.den) (X+V+1) m at hFW
  change generated.2≤matrixPrice model W m K (D*t.den) (X+V+1) at hMW
  change inputs.2≤fieldsPrice model W m K (D*t.den) (X+V+1) at hLW
  have hOC := constructor_bound (fun w => w) W W (matrixPrice model W m K (D*t.den) (X+V+1))
    (GeneralPaperRayFieldsBits.fieldRun model W matrix x w t) hMW outer ho
  have hIC := constructor_bound (fun w => w) W W (fieldPrice model W K (D*t.den) (X+V+1) m)
    (entry model W matrix x w t j) hFW inner hi
  have hCost := GeneralPaperRayCostStorage.bounded model W _ S D E X V (hs j l) hD hED x w hx hw t ht j l
  change GeneralPaperRayCostStorage.window model W (GeneralPaperRayQueryWork.scores matrix j l) x w t j l≤
    GeneralPaperRayCostStorage.profile model W m K S (D*t.den) (X+V+1) at hCost
  have hList : listFootprint W (fun _ : Field K => 0) inputs.1=m*(2*W)+32*W := borrowed_fields W generated.1
  have hShape : inputs.2=generated.2+(8*m+4)*W := rfl
  have hf := fields_bound W (natBits (metadataCap model W m K S (D*t.den) (X+V+1)))
    [m,K,(GeneralPaperRayFieldsBits.fieldRun model W matrix x w t j).2,
      generated.2,inputs.2,(8*m+4)*W,generated.2+(8*m+4)*W] (by
      intro n hn
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤
    7*(natBits (metadataCap model W m K S (D*t.den) (X+V+1))+W)+32*W at hf
  change reservedFootprint W m (fieldFootprint W) (PaperIndexedArrayConstruction.fill (fun w => w) W
      (GeneralPaperRayFieldsBits.fieldRun model W matrix x w t) outer ho).1≤
    matrixProfile W m K S (GeneralPaperRayMinimumStorage.height (D*t.den) (X+V+1)) at hOuter
  change reservedFootprint W K (entryFootprint W) (PaperIndexedArrayConstruction.fill (fun w => w) W
      (entry model W matrix x w t j) inner hi).1≤fieldProfile W K S (GeneralPaperRayMinimumStorage.height (D*t.den) (X+V+1)) at hInner
  change reservedFootprint W m (fieldFootprint W) (PaperIndexedArrayConstruction.fill (fun w => w) W
      (GeneralPaperRayFieldsBits.fieldRun model W matrix x w t) outer ho).1+
    reservedFootprint W K (entryFootprint W) (PaperIndexedArrayConstruction.fill (fun w => w) W
      (entry model W matrix x w t j) inner hi).1+
    constructorFrames (fun w => w) W W (GeneralPaperRayFieldsBits.fieldRun model W matrix x w t) outer ho+
    constructorFrames (fun w => w) W W (entry model W matrix x w t j) inner hi+
    GeneralPaperRayCostStorage.window model W (GeneralPaperRayQueryWork.scores matrix j l) x w t j l+
    listFootprint W (fun _ : Field K => 0) inputs.1+
    fields W [m,K,(GeneralPaperRayFieldsBits.fieldRun model W matrix x w t j).2,
      generated.2,inputs.2,(8*m+4)*W,generated.2+(8*m+4)*W]+256*W≤_
  unfold profile
  omega

end Blotto.GeneralPaperRayFieldConstructionStorage
