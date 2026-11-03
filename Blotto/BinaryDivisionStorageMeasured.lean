import Blotto.BinaryDivisionMeasured
import Blotto.BinaryCompareBitsMeasured
import Blotto.BinaryBorrowDropMetadata

/-! Restoring division joins actual borrow/drop/quotient/remainder production
with allocation, held buffers and the previous compatibility source counter.
The returned primitive-work charge also pays the reached measured reversals
and structural control. Its factor-four comparison is distinct from native
observer/length/reference/allocator/GC pricing, which remains open. -/
namespace Blotto.BinaryDivisionStorageMeasured
open BinarySeedPreparationSpace
set_option autoImplicit false
set_option maxHeartbeats 3000000

structure Result (α : Type) where
  data : α
  allocated : ℕ
  held : ℕ
  source : ℕ
  work : ℕ

def Result.storage {α : Type} (result : Result α) : ℕ := result.held+result.allocated

theorem dropHeld_acc_length (bits first second : List Bool) (h : first.length = second.length) :
    BinaryDivisionAllocation.dropHeld bits first = BinaryDivisionAllocation.dropHeld bits second := by
  induction bits generalizing first second with
  | nil => simpa only [BinaryDivisionAllocation.dropHeld] using congrArg (fun n => n+1) h
  | cons bit rest ih => cases rest with
    | nil => simp only [BinaryDivisionAllocation.dropHeld,h]
    | cons next tail =>
        simp only [BinaryDivisionAllocation.dropHeld,h]
        rw [ih (false::first) (false::second) (by simpa using h)]

def drop (bits acc : List Bool) : BinaryCompareBitsMeasured.Result (List Bool) :=
  let n := BinaryBorrowDropMetadata.countFrom bits 0
  let k := BinaryBorrowDropMetadata.countFrom acc 0
  BinaryBorrowDropMetadata.dropAt bits acc n k

theorem drop_data (bits acc : List Bool) : (drop bits acc).data = BinaryWordHighBit.loop bits acc := by
  exact BinaryBorrowDropMetadata.drop_data bits acc
    (BinaryBorrowDropMetadata.countFrom bits 0) (BinaryBorrowDropMetadata.countFrom acc 0)

theorem drop_allocated (bits acc : List Bool) :
    (drop bits acc).allocated = BinaryDivisionAllocation.dropAllocated bits acc := by
  exact BinaryBorrowDropMetadata.drop_allocated bits acc
    (BinaryBorrowDropMetadata.countFrom bits 0) (BinaryBorrowDropMetadata.countFrom acc 0)
    (by simp only [BinaryBorrowDropMetadata.count_exact,Nat.zero_add])

theorem drop_held (bits acc : List Bool) :
    (drop bits acc).held = BinaryDivisionAllocation.dropHeld bits acc := by
  exact BinaryBorrowDropMetadata.drop_held bits acc
    (BinaryBorrowDropMetadata.countFrom bits 0) (BinaryBorrowDropMetadata.countFrom acc 0)
    (by simp only [BinaryBorrowDropMetadata.count_exact,Nat.zero_add])
    (by simp only [BinaryBorrowDropMetadata.count_exact,Nat.zero_add])

theorem drop_erases (bits acc : List Bool) :
    ((drop bits acc).data,(drop bits acc).allocated) =
      BinaryDivisionAllocation.dropWithAllocation bits acc := by
  rw [BinaryDivisionAllocation.dropWithAllocation_refines,drop_data,drop_allocated]

theorem drop_work (bits acc : List Bool) :
    (drop bits acc).work = 8*(bits.length-1)+4*acc.length+4 := by
  exact BinaryBorrowDropMetadata.drop_work bits acc
    (BinaryBorrowDropMetadata.countFrom bits 0) (BinaryBorrowDropMetadata.countFrom acc 0)

theorem drop_record (bits acc : List Bool) :
    drop bits acc = ⟨BinaryWordHighBit.loop bits acc,BinaryDivisionAllocation.dropAllocated bits acc,
      BinaryDivisionAllocation.dropHeld bits acc,8*(bits.length-1)+4*acc.length+4⟩ := by
  apply BinaryBorrowDropMetadata.record_ext
  · exact drop_data bits acc
  · exact drop_allocated bits acc
  · exact drop_held bits acc
  · exact drop_work bits acc

theorem dropAt_compat (bits acc : List Bool) (n k : ℕ) (hN : n=bits.length) (hK : k=acc.length) :
    BinaryBorrowDropMetadata.dropAt bits acc n k = drop bits acc := by
  rw [drop_record]
  apply BinaryBorrowDropMetadata.record_ext
  · exact BinaryBorrowDropMetadata.drop_data bits acc n k
  · exact BinaryBorrowDropMetadata.drop_allocated bits acc n k hK
  · exact BinaryBorrowDropMetadata.drop_held bits acc n k hN hK
  · exact BinaryBorrowDropMetadata.drop_work bits acc n k

theorem drop_metadata_work_bound (bits acc : List Bool) :
    (BinaryBorrowDropMetadata.countFrom bits 0+1)+(BinaryBorrowDropMetadata.countFrom acc 0+1)+
      BinaryWordHighBit.visits bits+(acc.length+(bits.length-1)+1) ≤ 2*(drop bits acc).work := by
  rw [drop_work,BinaryDivisionMeasured.drop_visits]
  simp only [BinaryBorrowDropMetadata.count_exact,Nat.zero_add]
  omega

def step (incoming : Bool) (remainder divisor : List Bool) : Result (Bool × List Bool) :=
  let R := BinaryBorrowDropMetadata.countFrom remainder 0
  let padded := BinaryBorrowDropMetadata.appendFalse divisor
  let D := padded.1.2
  let shifted := incoming::remainder
  let difference := BinaryBorrowDropMetadata.borrowAt shifted padded.1.1 false [] (R+1) (D+1) 0
  let chosen := if difference.data.2 then shifted else difference.data.1
  let chosenWidth := if difference.data.2 then R+1 else min (R+1) (D+1)
  let dropped := BinaryBorrowDropMetadata.dropAt chosen [] chosenWidth 0
  ⟨(!difference.data.2,dropped.data),
    1+(D+1)+difference.allocated+dropped.allocated+4,
    R+D+(R+1)+(D+1)+4+difference.storage+dropped.held,
    2+(D+1)+8*(R+1)+2*(R+1)+2*(R+1)+
      (min (R+1) (D+1)+1)+max 1 chosenWidth+2*R+1,
    padded.2+difference.work+dropped.work+8⟩

theorem step_previous_record (incoming : Bool) (remainder divisor : List Bool) :
    step incoming remainder divisor = (
      let shifted := incoming::remainder
      let padded := divisor++[false]
      let difference := BinaryCompareBitsMeasured.borrow shifted padded false []
      let chosen := if difference.data.2 then shifted else difference.data.1
      let dropped := drop chosen []
      ⟨(!difference.data.2,dropped.data),
        1+(divisor.length+1)+difference.allocated+dropped.allocated+4,
        remainder.length+divisor.length+shifted.length+padded.length+4+difference.storage+dropped.held,
        2+(divisor.length+1)+8*(remainder.length+1)+2*(remainder.length+1)+2*(remainder.length+1)+
          (min shifted.length padded.length+1)+max 1 chosen.length+2*remainder.length+1,
        4*(divisor.length+1)+difference.work+dropped.work+8⟩) := by
  let difference := BinaryCompareBitsMeasured.borrow (incoming::remainder) (divisor++[false]) false []
  let chosen := if difference.data.2 then incoming::remainder else difference.data.1
  have hb := BinaryBorrowDropMetadata.borrow_exact (incoming::remainder) (divisor++[false]) false []
    (remainder.length+1) (divisor.length+1) 0 (by simp) (by simp) rfl
  have hl : difference.data.1.length = min (remainder.length+1) (divisor.length+1) := by
    simp only [difference,BinaryCompareBitsMeasured.borrow_data,BinaryBorrowDropMetadata.borrow_loop_length,
      List.length_cons,List.length_append,List.length_nil,Nat.zero_add,Nat.add_zero]
  have hc : (if difference.data.2 then remainder.length+1 else min (remainder.length+1) (divisor.length+1)) = chosen.length := by
    dsimp only [chosen]
    by_cases h : difference.data.2=true
    · simp only [h,ite_true,List.length_cons]
    · simp only [h,Bool.false_eq_true,ite_false,hl]
  have hd := dropAt_compat chosen []
    (if difference.data.2 then remainder.length+1 else min (remainder.length+1) (divisor.length+1)) 0 hc rfl
  dsimp only [chosen,difference] at hc hd
  simp only [step,BinaryBorrowDropMetadata.count_exact,Nat.zero_add,BinaryBorrowDropMetadata.appendFalse_record,
    hb,hd,←hc,List.length_cons,List.length_append,List.length_nil,Nat.add_zero]

theorem step_erases (incoming : Bool) (remainder divisor : List Bool) :
    ((step incoming remainder divisor).data,(step incoming remainder divisor).allocated) =
      BinaryDivisionAllocation.stepWithAllocation incoming remainder divisor := by
  simp only [step_previous_record,BinaryDivisionAllocation.stepWithAllocation,
    ← BinaryCompareBitsMeasured.borrow_erases,← drop_erases]

theorem step_data (incoming : Bool) (remainder divisor : List Bool) :
    (step incoming remainder divisor).data = BinaryDivisionWord.step incoming remainder divisor :=
  (congrArg Prod.fst (step_erases incoming remainder divisor)).trans
    (BinaryDivisionAllocation.stepWithAllocation_state incoming remainder divisor)

theorem step_storage (incoming : Bool) (remainder divisor : List Bool) :
    (step incoming remainder divisor).storage = BinaryDivisionAllocation.stepStorage incoming remainder divisor := by
  have hAlloc := congrArg Prod.snd (step_erases incoming remainder divisor)
  simp only [step_previous_record] at hAlloc
  simp only [Result.storage,step_previous_record]
  rw [hAlloc]
  simp only [BinaryDivisionAllocation.stepStorage,BinaryCompareBitsMeasured.borrow_storage,
    BinaryCompareBitsMeasured.borrow_data,drop_held,BinaryDivisionWord.chosenResidual,BinaryBorrowWord.subtract]
  rfl

theorem step_source (incoming : Bool) (remainder divisor : List Bool) :
    (step incoming remainder divisor).source = (BinaryDivisionMeasured.step incoming remainder divisor).2 := by
  simp only [step_previous_record,BinaryDivisionMeasured.step,← BinaryCompareBitsMeasured.borrow_erases,
    ← drop_erases]

theorem step_source_work (incoming : Bool) (remainder divisor : List Bool) :
    (step incoming remainder divisor).source = BinaryDivisionWord.bitWork incoming remainder divisor := by
  rw [step_source,BinaryDivisionMeasured.step_work]

theorem step_work_bound (incoming : Bool) (remainder divisor : List Bool)
    (hWidth : remainder.length = divisor.length) :
    (step incoming remainder divisor).work ≤ 4*(step incoming remainder divisor).source := by
  rw [step_previous_record]
  have hBorrow := BinaryCompareBitsMeasured.borrow_work (incoming::remainder) (divisor++[false])
    false [] (BinaryDivisionWord.input_lengths incoming remainder divisor hWidth)
  let chosen := if (BinaryCompareBitsMeasured.borrow (incoming::remainder) (divisor++[false]) false []).data.2
    then incoming::remainder
    else (BinaryCompareBitsMeasured.borrow (incoming::remainder) (divisor++[false]) false []).data.1
  have hChosen : chosen.length = remainder.length+1 := by
    dsimp only [chosen]
    rw [BinaryCompareBitsMeasured.borrow_data]
    exact BinaryDivisionWord.chosenResidual_length incoming remainder divisor hWidth
  change 4*(divisor.length+1)+
    (BinaryCompareBitsMeasured.borrow (incoming::remainder) (divisor++[false]) false []).work+
    (drop chosen []).work+8 ≤ 4*(2+(divisor.length+1)+8*(remainder.length+1)+
      2*(remainder.length+1)+2*(remainder.length+1)+
      (min (incoming::remainder).length (divisor++[false]).length+1)+max 1 chosen.length+2*remainder.length+1)
  rw [drop_work,hBorrow,hChosen]
  simp only [List.length_cons,List.length_append,List.length_nil,hWidth,Nat.min_self]
  omega

theorem highBit_loop_length (bits acc : List Bool) :
    (BinaryWordHighBit.loop bits acc).length = acc.length+(bits.length-1) := by
  induction bits generalizing acc with
  | nil => simp [BinaryWordHighBit.loop]
  | cons bit rest ih => cases rest with
    | nil => simp [BinaryWordHighBit.loop]
    | cons next tail => simp only [BinaryWordHighBit.loop,ih,List.length_cons]; omega

def stepAt (incoming : Bool) (remainder divisor : List Bool) (R D : ℕ) : Result (Bool × List Bool) × ℕ :=
  let padded := BinaryBorrowDropMetadata.appendFalse divisor
  let shifted := incoming::remainder
  let difference := BinaryBorrowDropMetadata.borrowAt shifted padded.1.1 false [] (R+1) (D+1) 0
  let chosen := if difference.data.2 then shifted else difference.data.1
  let chosenWidth := if difference.data.2 then R+1 else min (R+1) (D+1)
  let dropped := BinaryBorrowDropMetadata.dropAt chosen [] chosenWidth 0
  (⟨(!difference.data.2,dropped.data),
    1+(D+1)+difference.allocated+dropped.allocated+4,
    R+D+(R+1)+(D+1)+4+difference.storage+dropped.held,
    2+(D+1)+8*(R+1)+2*(R+1)+2*(R+1)+
      (min (R+1) (D+1)+1)+max 1 chosenWidth+2*R+1,
    padded.2+difference.work+dropped.work+8⟩,chosenWidth-1)

theorem stepAt_record (incoming : Bool) (remainder divisor : List Bool) (R D : ℕ)
    (hR : R=remainder.length) (hD : D=divisor.length) :
    (stepAt incoming remainder divisor R D).1 = step incoming remainder divisor := by
  subst R; subst D
  simp only [stepAt,step,BinaryBorrowDropMetadata.count_exact,Nat.zero_add,
    BinaryBorrowDropMetadata.appendFalse_record]

theorem stepAt_width (incoming : Bool) (remainder divisor : List Bool) (R D : ℕ)
    (hR : R=remainder.length) (hD : D=divisor.length) :
    (stepAt incoming remainder divisor R D).2 = (stepAt incoming remainder divisor R D).1.data.2.length := by
  subst R; subst D
  let difference := BinaryBorrowDropMetadata.borrowAt (incoming::remainder) (divisor++[false]) false []
    (remainder.length+1) (divisor.length+1) 0
  have hl : difference.data.1.length = min (remainder.length+1) (divisor.length+1) := by
    exact BinaryBorrowDropMetadata.borrow_length (incoming::remainder) (divisor++[false]) false []
      (remainder.length+1) (divisor.length+1) 0 (by simp) (by simp) rfl
  have hc : (if difference.data.2 then remainder.length+1 else min (remainder.length+1) (divisor.length+1)) =
      (if difference.data.2 then incoming::remainder else difference.data.1).length := by
    by_cases h : difference.data.2=true
    · simp only [h,ite_true,List.length_cons]
    · simp only [h,Bool.false_eq_true,ite_false,hl]
  simp only [stepAt,BinaryBorrowDropMetadata.appendFalse_record,BinaryBorrowDropMetadata.drop_data,
    highBit_loop_length,List.length_nil,Nat.zero_add]
  change _ = (if difference.data.2 then incoming::remainder else difference.data.1).length-1
  rw [←hc]

def loopReference (divisor : List Bool) : List Bool → List Bool → List Bool → Result (List Bool × List Bool)
  | [],quotient,remainder => ⟨(quotient,remainder),1,divisor.length+quotient.length+remainder.length+2,1,1⟩
  | incoming::rest,quotient,remainder =>
      let digit := step incoming remainder divisor
      let later := loopReference divisor rest (digit.data.1::quotient) digit.data.2
      ⟨later.data,digit.allocated+2+later.allocated,
        divisor.length+(incoming::rest).length+quotient.length+remainder.length+3+digit.storage+later.held,
        digit.source+4+later.source,digit.work+4+later.work⟩


def loopAt (divisor : List Bool) : List Bool → List Bool → List Bool → ℕ → ℕ → ℕ → ℕ → Result (List Bool × List Bool)
  | [],quotient,remainder,_,q,r,d => ⟨(quotient,remainder),1,d+q+r+2,1,1⟩
  | incoming::rest,quotient,remainder,n,q,r,d =>
      let digit := stepAt incoming remainder divisor r d
      let later := loopAt divisor rest (digit.1.data.1::quotient) digit.1.data.2 (n-1) (q+1) digit.2 d
      ⟨later.data,digit.1.allocated+2+later.allocated,
        d+n+q+r+3+digit.1.storage+later.held,
        digit.1.source+4+later.source,digit.1.work+4+later.work⟩

theorem loopAt_exact (divisor bits quotient remainder : List Bool) (n q r d : ℕ)
    (hN : n=bits.length) (hQ : q=quotient.length) (hR : r=remainder.length) (hD : d=divisor.length) :
    loopAt divisor bits quotient remainder n q r d = loopReference divisor bits quotient remainder := by
  induction bits generalizing quotient remainder n q r d with
  | nil => simp only [loopAt,loopReference,hQ,hR,hD]
  | cons incoming rest ih =>
      have hs := stepAt_record incoming remainder divisor r d hR hD
      have hw := stepAt_width incoming remainder divisor r d hR hD
      have hn : n-1=rest.length := by simp only [hN,List.length_cons,Nat.add_sub_cancel]
      have hq : q+1=((stepAt incoming remainder divisor r d).1.data.1::quotient).length := by simp only [List.length_cons,hQ]
      have h := ih ((stepAt incoming remainder divisor r d).1.data.1::quotient)
        (stepAt incoming remainder divisor r d).1.data.2 (n-1) (q+1) (stepAt incoming remainder divisor r d).2 d hn hq hw hD
      simp only [hs] at h
      simp only [loopAt,loopReference]
      simp only [hs,h]
      simp only [hN,hQ,hR,hD]

theorem loopAt_control_work (divisor bits quotient remainder : List Bool) (n q r d : ℕ) :
    4*bits.length+1 ≤ (loopAt divisor bits quotient remainder n q r d).work := by
  induction bits generalizing quotient remainder n q r d with
  | nil => simp [loopAt]
  | cons incoming rest ih =>
      have h := ih ((stepAt incoming remainder divisor r d).1.data.1::quotient)
        (stepAt incoming remainder divisor r d).1.data.2 (n-1) (q+1) (stepAt incoming remainder divisor r d).2 d
      simp only [loopAt,List.length_cons] at h ⊢
      omega

def loop (divisor : List Bool) : List Bool → List Bool → List Bool → Result (List Bool × List Bool)
  | bits,quotient,remainder => loopAt divisor bits quotient remainder
      (BinaryBorrowDropMetadata.countFrom bits 0) (BinaryBorrowDropMetadata.countFrom quotient 0)
      (BinaryBorrowDropMetadata.countFrom remainder 0) (BinaryBorrowDropMetadata.countFrom divisor 0)

theorem loop_compat (divisor bits quotient remainder : List Bool) :
    loop divisor bits quotient remainder = loopReference divisor bits quotient remainder := by
  exact loopAt_exact divisor bits quotient remainder _ _ _ _
    (by simp only [BinaryBorrowDropMetadata.count_exact,Nat.zero_add])
    (by simp only [BinaryBorrowDropMetadata.count_exact,Nat.zero_add])
    (by simp only [BinaryBorrowDropMetadata.count_exact,Nat.zero_add])
    (by simp only [BinaryBorrowDropMetadata.count_exact,Nat.zero_add])

theorem loopAt_public (divisor bits quotient remainder : List Bool) (n q r d : ℕ)
    (hN : n=bits.length) (hQ : q=quotient.length) (hR : r=remainder.length) (hD : d=divisor.length) :
    loopAt divisor bits quotient remainder n q r d = loop divisor bits quotient remainder := by
  rw [loop_compat]
  exact loopAt_exact divisor bits quotient remainder n q r d hN hQ hR hD

theorem loop_nil (divisor quotient remainder : List Bool) :
    loop divisor [] quotient remainder = ⟨(quotient,remainder),1,divisor.length+quotient.length+remainder.length+2,1,1⟩ := by
  rw [loop_compat]; rfl

theorem loop_cons (divisor : List Bool) (incoming : Bool) (rest quotient remainder : List Bool) :
    loop divisor (incoming::rest) quotient remainder =
      (let digit := step incoming remainder divisor
       let later := loop divisor rest (digit.data.1::quotient) digit.data.2
       ⟨later.data,digit.allocated+2+later.allocated,
         divisor.length+(incoming::rest).length+quotient.length+remainder.length+3+digit.storage+later.held,
         digit.source+4+later.source,digit.work+4+later.work⟩) := by
  rw [loop_compat]
  simp only [loopReference,←loop_compat]

theorem loop_erases (divisor bits quotient remainder : List Bool) :
    ((loop divisor bits quotient remainder).data,(loop divisor bits quotient remainder).allocated) =
      BinaryDivisionAllocation.divisionLoopWithAllocation divisor bits quotient remainder := by
  induction bits generalizing quotient remainder with
  | nil => simp only [loop_nil,BinaryDivisionAllocation.divisionLoopWithAllocation]
  | cons incoming rest ih =>
      simp only [loop_nil,loop_cons,BinaryDivisionAllocation.divisionLoopWithAllocation,← step_erases,← ih]

theorem loop_data (divisor bits quotient remainder : List Bool) :
    (loop divisor bits quotient remainder).data = BinaryLongDivision.loop divisor bits quotient remainder := by
  have h := congrArg Prod.fst (loop_erases divisor bits quotient remainder)
  simpa only [BinaryDivisionAllocation.divisionLoopWithAllocation_refines] using h

theorem loop_held (divisor bits quotient remainder : List Bool) :
    (loop divisor bits quotient remainder).held = BinaryDivisionAllocation.divisionLoopHeld divisor bits quotient remainder := by
  induction bits generalizing quotient remainder with
  | nil => simp only [loop_nil,BinaryDivisionAllocation.divisionLoopHeld]
  | cons incoming rest ih =>
      simp only [loop_nil,loop_cons,BinaryDivisionAllocation.divisionLoopHeld,ih,step_storage,step_data]

theorem loop_source (divisor bits quotient remainder : List Bool) :
    (loop divisor bits quotient remainder).source = (BinaryLongDivision.loopWithWork divisor bits quotient remainder).2 := by
  induction bits generalizing quotient remainder with
  | nil => simp only [loop_nil,BinaryLongDivision.loopWithWork]
  | cons incoming rest ih =>
      simp only [loop_nil,loop_cons,BinaryLongDivision.loopWithWork,ih,step_source_work,step_data]

theorem loop_work_bound (divisor bits quotient remainder : List Bool)
    (hWidth : remainder.length = divisor.length) :
    (loop divisor bits quotient remainder).work ≤ 4*(loop divisor bits quotient remainder).source := by
  induction bits generalizing quotient remainder with
  | nil => simp [loop_nil,loop_cons]
  | cons incoming rest ih =>
      have hStep := step_work_bound incoming remainder divisor hWidth
      have hNext := ih ((step incoming remainder divisor).data.1::quotient)
        (step incoming remainder divisor).data.2
        (by rw [step_data]; exact (BinaryDivisionWord.step_length incoming remainder divisor hWidth).trans hWidth)
      simp only [loop_nil,loop_cons]
      omega

def zeros : List Bool → List Bool × ℕ
  | [] => ([],2)
  | _::rest =>
      let later := zeros rest
      (false::later.1,later.2+4)

theorem zeros_data (ruler : List Bool) : (zeros ruler).1 = BinaryLongDivision.zeroRemainder ruler := by
  induction ruler with
  | nil => rfl
  | cons bit rest ih => simp only [zeros,BinaryLongDivision.zeroRemainder,List.length_cons,List.replicate_succ] at ih ⊢; rw [ih]

theorem zeros_work (ruler : List Bool) : (zeros ruler).2 = 4*ruler.length+2 := by
  induction ruler with
  | nil => rfl
  | cons bit rest ih => simp only [zeros,ih,List.length_cons]; omega

def reverseCount : List Bool → List Bool → ℕ → ℕ → (List Bool × ℕ) × ℕ
  | [],acc,count,work => ((acc,count),work)
  | bit::rest,acc,count,work => reverseCount rest (bit::acc) (count+1) (work+4)

theorem reverseCount_data (bits acc : List Bool) (count work : ℕ) :
    (reverseCount bits acc count work).1.1 = bits.reverse++acc := by
  induction bits generalizing acc count work with
  | nil => rfl
  | cons bit rest ih => simp [reverseCount,ih,List.reverse_cons,List.append_assoc]

theorem reverseCount_length (bits acc : List Bool) (count work : ℕ) :
    (reverseCount bits acc count work).1.2 = count+bits.length := by
  induction bits generalizing acc count work with
  | nil => rfl
  | cons bit rest ih => simp only [reverseCount,ih,List.length_cons]; omega

theorem reverseCount_work (bits acc : List Bool) (count work : ℕ) :
    (reverseCount bits acc count work).2 = work+4*bits.length := by
  induction bits generalizing acc count work with
  | nil => rfl
  | cons bit rest ih => simp only [reverseCount,ih,List.length_cons]; omega

def zerosProduced : List Bool → (List Bool × ℕ) × ℕ
  | [] => (([],0),2)
  | _::rest =>
      let later := zerosProduced rest
      ((false::later.1.1,later.1.2+1),later.2+4)

theorem zerosProduced_record (ruler : List Bool) :
    zerosProduced ruler = (((zeros ruler).1,ruler.length),(zeros ruler).2) := by
  induction ruler with
  | nil => rfl
  | cons bit rest ih => simp only [zerosProduced,zeros,ih,List.length_cons]

def divideProduced (dividend divisor : List Bool) : Result (List Bool × List Bool) × (ℕ × ℕ) :=
  let reversed := reverseCount dividend [] 0 2
  let zeroed := zerosProduced divisor
  let n := reversed.1.2
  let m := zeroed.1.2
  let result := loopAt divisor reversed.1.1 [] zeroed.1.1 n 0 m m
  (⟨result.data,2*n+m+result.allocated+2,
    n+m+2*n+m+result.held,
    2*n+2*m+result.source+2,reversed.2+zeroed.2+result.work+2⟩,(n,m))

theorem divideProduced_compat (dividend divisor : List Bool) :
    (divideProduced dividend divisor).1 = (
      let reversed := BinaryCompareBitsMeasured.reverse dividend []
      let zeroed := zeros divisor
      let result := loop divisor reversed.1 [] zeroed.1
      ⟨result.data,2*dividend.length+divisor.length+result.allocated+2,
        dividend.length+divisor.length+2*dividend.length+divisor.length+result.held,
        2*dividend.length+2*divisor.length+result.source+2,reversed.2+zeroed.2+result.work+2⟩) := by
  have h := loopAt_public divisor dividend.reverse [] (zeros divisor).1
    dividend.length 0 divisor.length divisor.length (by simp) rfl
    (by rw [zeros_data,BinaryLongDivision.zeroRemainder_length]) rfl
  simp only [divideProduced,reverseCount_data,reverseCount_length,reverseCount_work,zerosProduced_record,
    BinaryCompareBitsMeasured.reverse_data,BinaryCompareBitsMeasured.reverse_work,
    List.append_nil,Nat.zero_add,h]
  rw [Nat.add_comm 2 (4*dividend.length)]

theorem divideProduced_lengths (dividend divisor : List Bool) :
    (divideProduced dividend divisor).2 = (dividend.length,divisor.length) := by
  simp only [divideProduced,reverseCount_length,zerosProduced_record,Nat.zero_add]

attribute [irreducible] loopAt divideProduced

def divide (dividend divisor : List Bool) : Result (List Bool × List Bool) :=
  (divideProduced dividend divisor).1

theorem divide_previous_record (dividend divisor : List Bool) :
    divide dividend divisor = (
      let reversed := BinaryCompareBitsMeasured.reverse dividend []
      let zeroed := zeros divisor
      let result := loop divisor reversed.1 [] zeroed.1
      ⟨result.data,2*dividend.length+divisor.length+result.allocated+2,
        dividend.length+divisor.length+2*dividend.length+divisor.length+result.held,
        2*dividend.length+2*divisor.length+result.source+2,reversed.2+zeroed.2+result.work+2⟩) := divideProduced_compat dividend divisor

theorem divide_erases (dividend divisor : List Bool) :
    ((divide dividend divisor).data,(divide dividend divisor).allocated) =
      BinaryDivisionAllocation.divideWithAllocation dividend divisor := by
  simp only [divide_previous_record,BinaryDivisionAllocation.divideWithAllocation,BinaryCompareBitsMeasured.reverse_data,
    List.append_nil,zeros_data,← loop_erases]

theorem divide_data (dividend divisor : List Bool) :
    (divide dividend divisor).data = BinaryLongDivision.divide dividend divisor :=
  (congrArg Prod.fst (divide_erases dividend divisor)).trans
    (BinaryDivisionAllocation.divideWithAllocation_state dividend divisor)

theorem divide_storage (dividend divisor : List Bool) :
    (divide dividend divisor).storage = BinaryDivisionAllocation.divideStorage dividend divisor := by
  have hAlloc := congrArg Prod.snd (divide_erases dividend divisor)
  change (divide dividend divisor).allocated = _ at hAlloc
  unfold Result.storage
  rw [hAlloc]
  simp only [divide_previous_record,BinaryDivisionAllocation.divideStorage,BinaryCompareBitsMeasured.reverse_data,
    List.append_nil,zeros_data,loop_held]

theorem divide_source (dividend divisor : List Bool) :
    (divide dividend divisor).source = (BinaryLongDivision.divideWithWork dividend divisor).2 := by
  simp only [divide_previous_record,BinaryLongDivision.divideWithWork,BinaryCompareBitsMeasured.reverse_data,
    List.append_nil,zeros_data,loop_source]

theorem divide_work_bound (dividend divisor : List Bool) :
    (divide dividend divisor).work ≤ 4*(divide dividend divisor).source := by
  have h := loop_work_bound divisor dividend.reverse [] (BinaryLongDivision.zeroRemainder divisor)
    (BinaryLongDivision.zeroRemainder_length divisor)
  simp only [divide_previous_record,BinaryCompareBitsMeasured.reverse_data,BinaryCompareBitsMeasured.reverse_work,
    List.append_nil,zeros_data,zeros_work]
  omega

theorem divide_work_quadratic (dividend divisor : List Bool) :
    (divide dividend divisor).work ≤ 120*(dividend.length+1)*(divisor.length+1) := by
  have h := divide_work_bound dividend divisor
  rw [divide_source,BinaryLongDivision.divideWithWork_refines] at h
  have hOld := BinaryLongDivision.bitWork_quadratic dividend divisor
  nlinarith

def tracedMeasured (dividend divisor : List Bool) : (((List Bool × List Bool) × Trace) × ℕ) × ℕ :=
  let produced := divideProduced dividend divisor
  let result := produced.1
  (((result.data,[.frames (produced.2.1+2*produced.2.2+16),.arrayAllocation 8,
    .listAllocation result.storage]),result.source),result.work)

theorem tracedMeasured_previous_record (dividend divisor : List Bool) :
    tracedMeasured dividend divisor = (
      let result := divide dividend divisor
      (((result.data,[.frames (dividend.length+2*divisor.length+16),.arrayAllocation 8,
        .listAllocation result.storage]),result.source),result.work)) := by
  simp only [tracedMeasured,divide,divideProduced_lengths]

def traced (dividend divisor : List Bool) : ((List Bool × List Bool) × Trace) × ℕ :=
  (tracedMeasured dividend divisor).1

theorem tracedMeasured_compat (dividend divisor : List Bool) :
    (tracedMeasured dividend divisor).1 = traced dividend divisor := rfl

theorem traced_erases (dividend divisor : List Bool) :
    (traced dividend divisor).1 = BinaryBooleanPrimitiveLifetime.divideWithTrace dividend divisor := by
  simp only [traced,tracedMeasured_previous_record,BinaryBooleanPrimitiveLifetime.divideWithTrace,
    divide_data,divide_storage,BinaryDivisionAllocation.divideWithAllocation_state]

theorem traced_data (dividend divisor : List Bool) :
    (traced dividend divisor).1.1 = (BinaryLongDivision.divideWithWork dividend divisor).1 := by
  rw [traced_erases,BinaryBooleanPrimitiveLifetime.divideWithTrace_erases,BinaryLongDivision.divideWithWork_refines]

theorem traced_work (dividend divisor : List Bool) :
    (traced dividend divisor).2 = (BinaryLongDivision.divideWithWork dividend divisor).2 := divide_source _ _

theorem traced_eq_reference (dividend divisor : List Bool) :
    traced dividend divisor = BinaryDivisionMeasured.traced dividend divisor := by
  apply Prod.ext
  · rw [traced_erases,BinaryDivisionMeasured.traced_erases]
  · rw [traced_work,BinaryDivisionMeasured.traced_work]

theorem tracedMeasured_work_bound (dividend divisor : List Bool) :
    (tracedMeasured dividend divisor).2 ≤ 4*(traced dividend divisor).2 := divide_work_bound _ _

theorem traced_all_prefix (dividend divisor : List Bool) (W : ℕ)
    (hA : dividend.length ≤ W) (hB : divisor.length ≤ W) (borrowed steps : ℕ) :
    retainedHeap borrowed (traced dividend divisor).1.2 steps ≤ borrowed+500*(W+2)^3+8 ∧
    framePeak ((traced dividend divisor).1.2.take steps) ≤ 3*W+16 := by
  rw [traced_erases]
  exact ⟨BinaryBooleanPrimitiveLifetime.divide_all_prefix dividend divisor W hA hB borrowed steps,
    (framePeak_take_le _ _).trans (BinaryBooleanPrimitiveLifetime.divideWithTrace_bounds dividend divisor W hA hB).2⟩

end Blotto.BinaryDivisionStorageMeasured
