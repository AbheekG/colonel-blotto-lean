import Blotto.BinaryBooleanPrimitiveLifetime
import Blotto.BinarySteinGCD
import Blotto.BinaryPRGOutputLifetime

/-! The actual Boolean-ruler Stein GCD has a reached source allocation trace.
Only reached scans and odd-pair borrow differences are produced; even-pair
output conses, reconstructed input conses, ruler append and final trimming
are reserved explicitly. Every old reservation remains live. The canonical
result erases exactly to the quadratic backend's Boolean GCD, including zero
and high-zero padding. Inputs are borrowed and added separately to space. -/
set_option autoImplicit false
namespace Blotto.BinarySteinGCDLifetime
open BinarySeedPreparationSpace BinaryBooleanPrimitiveLifetime

def firstTrace (first : List Bool) : Trace :=
  [.frames 2,.arrayAllocation 8] ++ under 2 (scanWithTrace first).2
def bothTrace (first second : List Bool) : Trace :=
  firstTrace first ++ under 2 (scanWithTrace second).2

def loopWithTrace : List Bool → List Bool → List Bool → List Bool×Trace
  | [],first,second =>
      let scan := scanWithTrace first
      (if scan.1 then first else second,firstTrace first)
  | _::ruler,first,second =>
      let scanFirst := scanWithTrace first
      if scanFirst.1 then
        let scanSecond := scanWithTrace second
        if scanSecond.1 then
          match first,second with
          | false::a,false::b =>
              let later := loopWithTrace ruler a b
              (false::later.1,bothTrace (false::a) (false::b) ++ [.listAllocation 1] ++ under 1 later.2)
          | false::a,true::b =>
              let later := loopWithTrace ruler a (true::b)
              (later.1,bothTrace (false::a) (true::b) ++ [.listAllocation 1] ++ under 1 later.2)
          | true::a,false::b =>
              let later := loopWithTrace ruler (true::a) b
              (later.1,bothTrace (true::a) (false::b) ++ [.listAllocation 1] ++ under 1 later.2)
          | true::a,true::b =>
              let difference := differenceWithTrace (true::a) (true::b)
              let later := if difference.1.negative then loopWithTrace ruler (true::a) difference.1.bits.tail
                else loopWithTrace ruler difference.1.bits.tail (true::b)
              (later.1,bothTrace (true::a) (true::b) ++ [.listAllocation 2] ++ under 2 difference.2 ++ under 1 later.2)
          | _,_ => ([],bothTrace first second)
        else (first,bothTrace first second)
      else (second,firstTrace first)

@[simp] theorem loopWithTrace_erases (ruler first second : List Bool) :
    (loopWithTrace ruler first second).1=BinarySteinGCD.loop ruler first second := by
  induction ruler generalizing first second with
  | nil => simp [loopWithTrace,BinarySteinGCD.loop]
  | cons unused ruler ih =>
      simp only [loopWithTrace,BinarySteinGCD.loop,scanWithTrace_erases]
      split
      · split
        · cases first with
          | nil => rfl
          | cons a first =>
              cases second with
              | nil => cases a <;> rfl
              | cons b second =>
                  cases a <;> cases b <;> dsimp only <;> simp only [differenceWithTrace_erases,ih]
                  split <;> simp only [ih]
        · rfl
      · rfl

def stepBound (W : ℕ) : ℕ := 40*(W+1)^2+8*(W+1)+32

theorem firstTrace_bounds (first : List Bool) (W : ℕ) (h : first.length≤W) :
    listCells (firstTrace first)+arraySlots (firstTrace first)≤8+4*(W+1) ∧
    framePeak (firstTrace first)≤W+3 := by
  have hs := scanWithTrace_bounds first
  have hf := framePeak_under 2 (scanWithTrace first).2
  simp only [firstTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

theorem bothTrace_bounds (first second : List Bool) (W : ℕ) (hA : first.length≤W) (hB : second.length≤W) :
    listCells (bothTrace first second)+arraySlots (bothTrace first second)≤8+8*(W+1) ∧
    framePeak (bothTrace first second)≤W+3 := by
  have ha := firstTrace_bounds first W hA
  have hb := scanWithTrace_bounds second
  have hf := framePeak_under 2 (scanWithTrace second).2
  simp only [bothTrace,listCells_append,arraySlots_append,framePeak_append,listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

set_option maxHeartbeats 2000000 in
theorem loopWithTrace_bounds (ruler first second : List Bool) (W : ℕ)
    (hA : first.length≤W) (hB : second.length≤W) :
    listCells (loopWithTrace ruler first second).2+arraySlots (loopWithTrace ruler first second).2≤
      (ruler.length+1)*stepBound W ∧ framePeak (loopWithTrace ruler first second).2≤ruler.length+2*W+12 := by
  induction ruler generalizing first second with
  | nil =>
      have hs := firstTrace_bounds first W hA
      simp only [loopWithTrace,List.length_nil,Nat.zero_add,Nat.one_mul]
      unfold stepBound
      exact ⟨by omega,by omega⟩
  | cons unused ruler ih =>
      have hFirst := firstTrace_bounds first W hA
      have hBoth := bothTrace_bounds first second W hA hB
      unfold loopWithTrace
      dsimp only
      split
      · split
        · cases first with
          | nil =>
              simp_all [scanWithTrace]
          | cons a first =>
              cases second with
              | nil =>
                  simp_all [scanWithTrace]
              | cons b second =>
                  have hfa : first.length≤W := by simp only [List.length_cons] at hA; omega
                  have hsb : second.length≤W := by simp only [List.length_cons] at hB; omega
                  cases a <;> cases b <;> dsimp only
                  · have hLater := ih first second hfa hsb
                    have hf := framePeak_under 1 (loopWithTrace ruler first second).2
                    simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
                      listCells_under,arraySlots_under,List.length_cons]
                    unfold stepBound at *
                    exact ⟨by nlinarith only [hLater.1,hBoth.1],by omega⟩
                  · have hLater := ih first (true::second) hfa hB
                    have hf := framePeak_under 1 (loopWithTrace ruler first (true::second)).2
                    simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
                      listCells_under,arraySlots_under,List.length_cons]
                    unfold stepBound at *
                    exact ⟨by nlinarith only [hLater.1,hBoth.1],by omega⟩
                  · have hLater := ih (true::first) second hA hsb
                    have hf := framePeak_under 1 (loopWithTrace ruler (true::first) second).2
                    simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
                      listCells_under,arraySlots_under,List.length_cons]
                    unfold stepBound at *
                    exact ⟨by nlinarith only [hLater.1,hBoth.1],by omega⟩
                  · have hDiff := differenceWithTrace_bounds (true::first) (true::second) W hA hB
                    have hDiffFrames := framePeak_under 2 (differenceWithTrace (true::first) (true::second)).2
                    have hDiffLength : (differenceWithTrace (true::first) (true::second)).1.bits.tail.length≤W := by
                      rw [differenceWithTrace_erases]
                      exact BinarySteinGCD.difference_tail_length _ _ W hA hB
                    split
                    · have hLater := ih (true::first) _ hA hDiffLength
                      have hf := framePeak_under 1 (loopWithTrace ruler (true::first)
                        (differenceWithTrace (true::first) (true::second)).1.bits.tail).2
                      simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
                        listCells_under,arraySlots_under,List.length_cons]
                      unfold stepBound at *
                      exact ⟨by nlinarith only [hLater.1,hBoth.1,hDiff.1],by omega⟩
                    · have hLater := ih _ (true::second) hDiffLength hB
                      have hf := framePeak_under 1 (loopWithTrace ruler
                        (differenceWithTrace (true::first) (true::second)).1.bits.tail (true::second)).2
                      simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
                        listCells_under,arraySlots_under,List.length_cons]
                      unfold stepBound at *
                      exact ⟨by nlinarith only [hLater.1,hBoth.1,hDiff.1],by omega⟩
        · simp only [List.length_cons]
          unfold stepBound
          exact ⟨by nlinarith only [hBoth.1],by omega⟩
      · simp only [List.length_cons]
        unfold stepBound
        exact ⟨by nlinarith only [hFirst.1],by omega⟩

def gcdWithTrace (first second : List Bool) : List Bool×Trace :=
  let ruler := BinaryPRGOutputLifetime.appendWithTrace first second
  let result := loopWithTrace ruler.1 first second
  let trimmed := trimWithTrace result.1
  (trimmed.1,[.frames 2,.arrayAllocation 16] ++ under 2 ruler.2 ++ under 2 result.2 ++ under 2 trimmed.2)

@[simp] theorem gcdWithTrace_erases (first second : List Bool) :
    (gcdWithTrace first second).1=BinarySteinGCD.canonicalGcd first second := by
  simp only [gcdWithTrace,trimWithTrace_erases,loopWithTrace_erases,
    BinaryPRGOutputLifetime.appendWithTrace_state,BinarySteinGCD.canonicalGcd,BinarySteinGCD.gcd]

theorem gcdWithTrace_bounds (first second : List Bool) :
    listCells (gcdWithTrace first second).2+arraySlots (gcdWithTrace first second).2≤500*(max first.length second.length+2)^3 ∧
    framePeak (gcdWithTrace first second).2≤6*max first.length second.length+24 := by
  let W := max first.length second.length
  have hA : first.length≤W := Nat.le_max_left _ _
  have hB : second.length≤W := Nat.le_max_right _ _
  have hRuler := BinaryPRGOutputLifetime.appendWithTrace_frames first second
  have hRulerFrames := framePeak_under 2 (BinaryPRGOutputLifetime.appendWithTrace first second).2
  have hLoop := loopWithTrace_bounds (first++second) first second W hA hB
  have hLoopFrames := framePeak_under 2 (loopWithTrace (first++second) first second).2
  have hLength := BinarySteinGCD.loop_length (first++second) first second W hA hB
  have hTrim := trimWithTrace_bounds (loopWithTrace (first++second) first second).1
  rw [loopWithTrace_erases] at hTrim
  have hTrimFrames := framePeak_under 2 (trimWithTrace (loopWithTrace (first++second) first second).1).2
  rw [loopWithTrace_erases] at hTrimFrames
  simp only [List.length_append] at hLoop hLength
  have hLoopTop := hLoop.1.trans (Nat.mul_le_mul_right (stepBound W)
    (show first.length+second.length+1≤2*W+1 by omega))
  unfold gcdWithTrace
  simp only [BinaryPRGOutputLifetime.appendWithTrace_state,listCells_append,arraySlots_append,framePeak_append,
    listCells,arraySlots,framePeak,listCells_under,arraySlots_under,BinaryPRGOutputLifetime.appendWithTrace_cells,
    loopWithTrace_erases]
  have hRulerArrays : arraySlots (BinaryPRGOutputLifetime.appendWithTrace first second).2=0 := by
    induction first with
    | nil => rfl
    | cons bit rest ih => simp [BinaryPRGOutputLifetime.appendWithTrace,arraySlots,ih]
  rw [hRulerArrays]
  change _≤500*(W+2)^3 ∧ _≤6*W+24
  unfold stepBound at hLoopTop
  exact ⟨by nlinarith only [hA,hB,hLoopTop,hTrim.1,hLength],by omega⟩

theorem gcd_all_prefix (first second : List Bool) (borrowedOtherCells steps : ℕ) :
    retainedHeap (first.length+second.length+borrowedOtherCells) (gcdWithTrace first second).2 steps≤
      first.length+second.length+borrowedOtherCells+500*(max first.length second.length+2)^3 :=
  prefix_heap _ _ _ _ (gcdWithTrace_bounds first second).1

theorem gcd_all_prefix_frames (first second : List Bool) (steps : ℕ) :
    framePeak ((gcdWithTrace first second).2.take steps)≤6*max first.length second.length+24 :=
  (framePeak_take_le _ _).trans (gcdWithTrace_bounds first second).2

end Blotto.BinarySteinGCDLifetime
