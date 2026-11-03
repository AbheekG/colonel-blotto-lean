import Blotto.BinarySignedMeasured
import Blotto.BinaryCanonicalTrimMeasured
import Blotto.BinarySteinGCDLifetime
import Blotto.BooleanFreshSeedMeasured

/-! The selected Stein loop carries the reached scan/difference data, the old
retained trace and the old source-work reservation together. Ruler append and
final trim are consumed once. Native evaluation of all observer fields remains
separate; numeric values occur only in semantic proofs. -/

namespace Blotto.BinarySteinGCDMeasured
open BinarySeedPreparationSpace
set_option autoImplicit false
set_option maxHeartbeats 3500000

def loop : List Bool → List Bool → List Bool → (List Bool × Trace) × ℕ
  | [],first,second =>
      let tested := BooleanFreshSeedMeasured.scan first
      ((if tested.1.1 then first else second,[.frames 2,.arrayAllocation 8]++under 2 tested.1.2),
        3*(first.length+1)+3*(second.length+1)+1)
  | _::ruler,first,second =>
      let testedFirst := BooleanFreshSeedMeasured.scan first
      let firstTrace := [.frames 2,.arrayAllocation 8]++under 2 testedFirst.1.2
      let base := 3*(first.length+1)+3*(second.length+1)+4
      if testedFirst.1.1 then
        let testedSecond := BooleanFreshSeedMeasured.scan second
        let bothTrace := firstTrace++under 2 testedSecond.1.2
        if testedSecond.1.1 then
          match first,second with
          | false::a,false::b =>
              let later := loop ruler a b
              ((false::later.1.1,bothTrace++[.listAllocation 1]++under 1 later.1.2),base+(3+later.2))
          | false::a,true::b =>
              let later := loop ruler a (true::b)
              ((later.1.1,bothTrace++[.listAllocation 1]++under 1 later.1.2),base+(2+later.2))
          | true::a,false::b =>
              let later := loop ruler (true::a) b
              ((later.1.1,bothTrace++[.listAllocation 1]++under 1 later.1.2),base+(2+later.2))
          | true::a,true::b =>
              let difference := BinarySignedMeasured.differenceTraced (true::a) (true::b)
              let later := if difference.1.1.negative then loop ruler (true::a) difference.1.1.bits.tail
                else loop ruler difference.1.1.bits.tail (true::b)
              ((later.1.1,bothTrace++[.listAllocation 2]++under 2 difference.1.2++under 1 later.1.2),
                base+(difference.2+8+later.2))
          | _,_ => (([],bothTrace),base+0)
        else ((first,bothTrace),base+0)
      else ((second,firstTrace),base+0)

theorem loop_erases (ruler first second : List Bool) :
    (loop ruler first second).1 = BinarySteinGCDLifetime.loopWithTrace ruler first second := by
  induction ruler generalizing first second with
  | nil => simp only [loop,BinarySteinGCDLifetime.loopWithTrace,BinarySteinGCDLifetime.firstTrace,
      BooleanFreshSeedMeasured.scan_erases]
  | cons unused ruler ih =>
      simp only [loop,BinarySteinGCDLifetime.loopWithTrace,BinarySteinGCDLifetime.firstTrace,
        BinarySteinGCDLifetime.bothTrace,BooleanFreshSeedMeasured.scan_erases]
      by_cases ha : (BinaryBooleanPrimitiveLifetime.scanWithTrace first).1 = true
      · simp only [ha,ite_true]
        by_cases hb : (BinaryBooleanPrimitiveLifetime.scanWithTrace second).1 = true
        · simp only [hb,ite_true]
          cases first with
          | nil => rfl
          | cons a first => cases second with
            | nil => cases a <;> rfl
            | cons b second =>
                cases a <;> cases b <;> dsimp only <;>
                  simp only [BinarySignedMeasured.differenceTraced_erases,ih]
                split <;> rename_i hd <;> simp only [hd,ite_true,ite_false,ih]
        · simp only [hb,Bool.false_eq_true,ite_false]
      · simp only [ha,Bool.false_eq_true,ite_false]

theorem loop_data (ruler first second : List Bool) :
    (loop ruler first second).1.1 = BinarySteinGCD.loop ruler first second := by
  rw [loop_erases,BinarySteinGCDLifetime.loopWithTrace_erases]

theorem loop_work (ruler first second : List Bool) :
    (loop ruler first second).2 = BinarySteinGCD.loopWork ruler first second := by
  induction ruler generalizing first second with
  | nil => rfl
  | cons unused ruler ih =>
      simp only [loop,BinarySteinGCD.loopWork,BooleanFreshSeedMeasured.scan_erases,
        BinaryBooleanPrimitiveLifetime.scanWithTrace_erases]
      by_cases ha : BinaryEuclideanGCD.nonzero first = true
      · simp only [ha,ite_true]
        by_cases hb : BinaryEuclideanGCD.nonzero second = true
        · simp only [hb,ite_true]
          cases first with
          | nil => rfl
          | cons a first => cases second with
            | nil => cases a <;> rfl
            | cons b second =>
                cases a <;> cases b <;> dsimp only <;>
                  simp only [BinarySignedMeasured.differenceTraced_data,BinarySignedMeasured.differenceTraced_work,ih]
                split <;> rename_i hd <;> simp only [hd,ite_true,ite_false,ih]
        · simp only [hb,Bool.false_eq_true,ite_false]
      · simp only [ha,Bool.false_eq_true,ite_false]

def gcd (first second : List Bool) : (List Bool × Trace) × ℕ :=
  let ruler := BinaryPRGOutputLifetime.appendWithTrace first second
  let result := loop ruler.1 first second
  let trimmed := BinaryCanonicalTrimMeasured.traced result.1.1
  ((trimmed.1.1,[.frames 2,.arrayAllocation 16]++under 2 ruler.2++under 2 result.1.2++under 2 trimmed.1.2),
    2*(first.length+second.length+1)+result.2+trimmed.2)

theorem gcd_erases (first second : List Bool) :
    (gcd first second).1 = BinarySteinGCDLifetime.gcdWithTrace first second := by
  simp only [gcd,BinarySteinGCDLifetime.gcdWithTrace,loop_erases,BinaryCanonicalTrimMeasured.traced_erases]

theorem gcd_data (first second : List Bool) :
    (gcd first second).1.1 = (BinarySteinGCD.gcdWithWork first second).1 := by
  rw [gcd_erases,BinarySteinGCDLifetime.gcdWithTrace_erases,BinarySteinGCD.gcdWithWork_state]

theorem gcd_work (first second : List Bool) :
    (gcd first second).2 = (BinarySteinGCD.gcdWithWork first second).2 := by
  simp only [gcd,BinarySteinGCD.gcdWithWork,BinaryPRGOutputLifetime.appendWithTrace_state,
    loop_work,loop_data,BinaryCanonicalTrimMeasured.traced_work]

theorem gcd_bound (first second : List Bool) :
    (gcd first second).2 ≤ 400*(max first.length second.length+1)^2 := by
  rw [gcd_work]
  exact BinarySteinGCD.gcdWithWork_bound first second

theorem gcd_all_prefix (first second : List Bool) (borrowed steps : ℕ) :
    retainedHeap (first.length+second.length+borrowed) (gcd first second).1.2 steps ≤
      first.length+second.length+borrowed+500*(max first.length second.length+2)^3 := by
  rw [gcd_erases]
  exact BinarySteinGCDLifetime.gcd_all_prefix first second borrowed steps

end Blotto.BinarySteinGCDMeasured
