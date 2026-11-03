import Blotto.BinaryBorrowDropMetadata

/-! Addition and multiplication carry widths through actual returned states.
The old Boolean/allocation/held/work records remain exact, with tail reversal
and no recursive list-length observer. Entry counting is stated separately:
it must not be hidden in the old constant empty-multiplication work. The
combined source-case bound is distinct from native scalar/reference/GC costs. -/
namespace Blotto.BinaryAddMultiplyMetadata
open BinaryCompareBitsMeasured (Result)
open BinaryBorrowDropMetadata (countFrom reverseFrom)
set_option autoImplicit false
set_option maxHeartbeats 4000000

def addAt : List Bool → List Bool → Bool → List Bool → ℕ → ℕ → ℕ → Result (List Bool) × ℕ
  | [],[],carry,acc,_n,_m,k =>
      let back := reverseFrom (if carry then true::acc else acc) [] 2
      (⟨back.1,if carry then 1+(k+1) else k,k+2,back.2+(if carry then 16 else 20)⟩,
        if carry then k+1 else k)
  | bit::rest,[],carry,acc,n,_m,k =>
      let later := addAt rest [] (BinaryAddition.nextCarry bit false carry)
        (BinaryAddition.sumBit bit false carry::acc) (n-1) 0 (k+1)
      (⟨later.1.data,2+later.1.allocated,n+k+2+later.1.held,later.1.work+18⟩,later.2)
  | [],bit::rest,carry,acc,_n,m,k =>
      let later := addAt [] rest (BinaryAddition.nextCarry false bit carry)
        (BinaryAddition.sumBit false bit carry::acc) 0 (m-1) (k+1)
      (⟨later.1.data,2+later.1.allocated,m+k+2+later.1.held,later.1.work+18⟩,later.2)
  | a::as,b::bs,carry,acc,n,m,k =>
      let later := addAt as bs (BinaryAddition.nextCarry a b carry)
        (BinaryAddition.sumBit a b carry::acc) (n-1) (m-1) (k+1)
      (⟨later.1.data,2+later.1.allocated,n+m+k+2+later.1.held,later.1.work+18⟩,later.2)

theorem addAt_record (a b : List Bool) (carry : Bool) (acc : List Bool) (n m k : ℕ)
    (hA : n=a.length) (hB : m=b.length) (hK : k=acc.length) :
    (addAt a b carry acc n m k).1 = BinaryCompareBitsMeasured.addLoop a b carry acc := by
  subst n; subst m; subst k
  induction a generalizing b carry acc with
  | nil => induction b generalizing carry acc with
    | nil => simp only [addAt,BinaryCompareBitsMeasured.addLoop,BinaryBorrowDropMetadata.reverse_exact]
    | cons bit rest ih =>
        have h := ih (BinaryAddition.nextCarry false bit carry) (BinaryAddition.sumBit false bit carry::acc)
        simp only [List.length_cons,List.length_nil] at h
        simp only [addAt,BinaryCompareBitsMeasured.addLoop,List.length_cons,Nat.add_sub_cancel,h]
  | cons bit rest ih => cases b with
    | nil =>
        have h := ih [] (BinaryAddition.nextCarry bit false carry) (BinaryAddition.sumBit bit false carry::acc)
        simp only [List.length_cons,List.length_nil] at h
        simp only [addAt,BinaryCompareBitsMeasured.addLoop,List.length_cons,Nat.add_sub_cancel,h]
    | cons other tail =>
        have h := ih tail (BinaryAddition.nextCarry bit other carry) (BinaryAddition.sumBit bit other carry::acc)
        simp only [List.length_cons,List.length_nil] at h
        simp only [addAt,BinaryCompareBitsMeasured.addLoop,List.length_cons,Nat.add_sub_cancel,h]

theorem addAt_width (a b : List Bool) (carry : Bool) (acc : List Bool) (n m k : ℕ)
    (hK : k=acc.length) :
    (addAt a b carry acc n m k).2 = (addAt a b carry acc n m k).1.data.length := by
  induction a generalizing b carry acc n m k with
  | nil => induction b generalizing carry acc n m k with
    | nil => cases carry <;> simp [addAt,BinaryBorrowDropMetadata.reverse_data,hK]
    | cons bit rest ih =>
        simp only [addAt]
        exact ih _ _ _ _ _ (by simp [hK])
  | cons bit rest ih => cases b with
    | nil =>
        simp only [addAt]
        exact ih [] _ _ _ _ _ (by simp [hK])
    | cons other tail =>
        simp only [addAt]
        exact ih tail _ _ _ _ _ (by simp [hK])

def addProduced (a b : List Bool) : (Result (List Bool) × ℕ) × (ℕ × ℕ) :=
  let n := countFrom a 0
  let m := countFrom b 0
  (addAt a b false [] n m 0,(n,m))

theorem addProduced_record (a b : List Bool) :
    (addProduced a b).1.1 = BinaryCompareBitsMeasured.add a b := by
  apply addAt_record
  · simp [BinaryBorrowDropMetadata.count_exact]
  · simp [BinaryBorrowDropMetadata.count_exact]
  · rfl

theorem addProduced_lengths (a b : List Bool) :
    (addProduced a b).2 = (a.length,b.length) := by
  simp only [addProduced,BinaryBorrowDropMetadata.count_exact,Nat.zero_add]

theorem addProduced_width (a b : List Bool) :
    (addProduced a b).1.2 = (addProduced a b).1.1.data.length :=
  addAt_width a b false [] _ _ 0 rfl

theorem add_setup_work_bound (a b : List Bool) :
    (addProduced a b).2.1+(addProduced a b).2.2+2 ≤ (addProduced a b).1.1.work := by
  rw [addProduced_lengths,addProduced_record,BinaryCompareBitsMeasured.add_work]
  simp only [BinaryAddition.bitWork,BinaryAddition.visits_eq]
  omega

def add (a b : List Bool) : Result (List Bool) := (addProduced a b).1.1

theorem add_exact (a b : List Bool) : add a b = BinaryCompareBitsMeasured.add a b :=
  addProduced_record a b

def multiplyAt : List Bool → List Bool → ℕ → ℕ → Result (List Bool) × ℕ
  | [],_other,_n,m => (⟨[],1,m+2,1⟩,0)
  | bit::rest,other,n,m =>
      let earlier := multiplyAt rest other (n-1) m
      let shifted := false::earlier.1.data
      let width := earlier.2+1
      if bit then
        let added := addAt other shifted false [] m width 0
        (⟨added.1.data,earlier.1.allocated+3+added.1.allocated,
          n+m+width+3+earlier.1.held+added.1.held,earlier.1.work+3+added.1.work⟩,added.2)
      else (⟨shifted,earlier.1.allocated+3,n+m+width+3+earlier.1.held,earlier.1.work+3⟩,width)

theorem multiplyAt_width (a b : List Bool) (n m : ℕ) :
    (multiplyAt a b n m).2 = (multiplyAt a b n m).1.data.length := by
  induction a generalizing n with
  | nil => rfl
  | cons bit rest ih =>
      simp only [multiplyAt]
      split
      · exact addAt_width b _ false [] m _ 0 rfl
      · simp only [List.length_cons,ih]

theorem multiplyAt_record (a b : List Bool) (n m : ℕ) (hA : n=a.length) (hB : m=b.length) :
    (multiplyAt a b n m).1 = BinaryCompareBitsMeasured.multiply a b := by
  subst n; subst m
  induction a with
  | nil => rfl
  | cons bit rest ih =>
      have hw := multiplyAt_width rest b rest.length b.length
      have ha := addAt_record b (false::(multiplyAt rest b rest.length b.length).1.data)
        false [] b.length ((multiplyAt rest b rest.length b.length).2+1) 0 rfl (by simp [hw]) rfl
      simp only [multiplyAt,BinaryCompareBitsMeasured.multiply,List.length_cons,Nat.add_sub_cancel]
      split
      · rw [ha]
        simp only [hw,ih,List.length_cons,BinaryCompareBitsMeasured.add]
      · simp only [hw,ih,List.length_cons]

def multiplyProduced (a b : List Bool) : (Result (List Bool) × ℕ) × (ℕ × ℕ) :=
  let n := countFrom a 0
  let m := countFrom b 0
  (multiplyAt a b n m,(n,m))

theorem multiplyProduced_record (a b : List Bool) :
    (multiplyProduced a b).1.1 = BinaryCompareBitsMeasured.multiply a b := by
  apply multiplyAt_record
  · simp [BinaryBorrowDropMetadata.count_exact]
  · simp [BinaryBorrowDropMetadata.count_exact]

theorem multiplyProduced_lengths (a b : List Bool) :
    (multiplyProduced a b).2 = (a.length,b.length) := by
  simp only [multiplyProduced,BinaryBorrowDropMetadata.count_exact,Nat.zero_add]

theorem multiplyProduced_width (a b : List Bool) :
    (multiplyProduced a b).1.2 = (multiplyProduced a b).1.1.data.length :=
  multiplyAt_width a b _ _

theorem multiply_case_work_bound (a b : List Bool) (W : ℕ)
    (hA : a.length ≤ W) (hB : b.length ≤ W) :
    (multiplyProduced a b).2.1+(multiplyProduced a b).2.2+2+(multiplyProduced a b).1.1.work ≤
      100*(W+1)^2 := by
  rw [multiplyProduced_lengths,multiplyProduced_record,BinaryCompareBitsMeasured.multiply_work]
  have h := BinaryMultiplication.work_bound a b
  have hm := Nat.mul_le_mul hA (show 22*(2*a.length+b.length+2)+3 ≤ 22*(3*W+2)+3 by omega)
  nlinarith

def multiply (a b : List Bool) : Result (List Bool) := (multiplyProduced a b).1.1

theorem multiply_exact (a b : List Bool) : multiply a b = BinaryCompareBitsMeasured.multiply a b :=
  multiplyProduced_record a b

attribute [irreducible] multiplyAt addProduced multiplyProduced

end Blotto.BinaryAddMultiplyMetadata
