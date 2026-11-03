import Blotto.BinarySignedMagnitude
import Blotto.BinaryDirectDyadicMidpoint

/-! Native binary GCD uses zero/parity tests, Boolean signed differences and
list-tail halving. One source Boolean ruler cell is consumed per transition;
input lengths derive a sufficient ruler via a halving-product invariant.
Leading zeros and zero inputs are included. Numerical gcd/products/values occur
only in proofs. The erased Boolean/list-cell work observer is quadratic; a
whole-machine address/control/lifetime composition remains separate. -/

namespace Blotto.BinarySteinGCD
open BinaryBigEndian BinarySignedMagnitude

theorem tail_value (bits : List Bool) : littleValue bits.tail = littleValue bits / 2 := by
  cases bits with
  | nil => rfl
  | cons bit rest => cases bit <;> simp only [List.tail_cons,littleValue,ite_true,Bool.false_eq_true,ite_false] <;> omega

theorem tail_double_le (bits : List Bool) : 2 * littleValue bits.tail ≤ littleValue bits := by
  rw [tail_value]
  omega

theorem difference_unsigned (first second : List Bool) :
    if (difference first second).negative then
      littleValue (difference first second).bits = littleValue second - littleValue first ∧
        littleValue first ≤ littleValue second
    else
      littleValue (difference first second).bits = littleValue first - littleValue second ∧
        littleValue second ≤ littleValue first := by
  have hv := difference_value first second
  unfold BinarySignedMagnitude.value signedValue at hv
  cases hs : (difference first second).negative <;> simp only [hs,Bool.false_eq_true,ite_false,ite_true] at hv ⊢ <;> omega

theorem odd_step (first second : List Bool) :
    let a := true :: first
    let b := true :: second
    let d := difference a b
    if d.negative then
      Nat.gcd (littleValue a) (littleValue d.bits.tail) = Nat.gcd (littleValue a) (littleValue b) ∧
        2 * (littleValue a * littleValue d.bits.tail) ≤ littleValue a * littleValue b
    else
      Nat.gcd (littleValue d.bits.tail) (littleValue b) = Nat.gcd (littleValue a) (littleValue b) ∧
        2 * (littleValue d.bits.tail * littleValue b) ≤ littleValue a * littleValue b := by
  dsimp only
  have hd := difference_unsigned (true :: first) (true :: second)
  have ht := tail_value (difference (true :: first) (true :: second)).bits
  cases hs : (difference (true :: first) (true :: second)).negative <;>
    simp only [hs,Bool.false_eq_true,ite_false,ite_true] at hd ⊢
  · have hEven : 2 * littleValue (difference (true :: first) (true :: second)).bits.tail =
        littleValue (true :: first) - littleValue (true :: second) := by
      simp only [littleValue,ite_true] at hd ⊢
      omega
    have hc : Nat.Coprime 2 (littleValue (true :: second)) := by simp [littleValue,Nat.coprime_comm]
    constructor
    · rw [← hc.gcd_mul_left_cancel, hEven,Nat.gcd_sub_self_left hd.2]
    · calc
        _ = (2 * littleValue (difference (true :: first) (true :: second)).bits.tail) * littleValue (true :: second) := by ring
        _ = (littleValue (true :: first) - littleValue (true :: second)) * littleValue (true :: second) := by rw [hEven]
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  · have hEven : 2 * littleValue (difference (true :: first) (true :: second)).bits.tail =
        littleValue (true :: second) - littleValue (true :: first) := by
      simp only [littleValue,ite_true] at hd ⊢
      omega
    have hc : Nat.Coprime 2 (littleValue (true :: first)) := by simp [littleValue,Nat.coprime_comm]
    constructor
    · rw [Nat.gcd_comm,← hc.gcd_mul_left_cancel,hEven,Nat.gcd_sub_self_left hd.2,Nat.gcd_comm]
    · calc
        _ = littleValue (true :: first) * (2 * littleValue (difference (true :: first) (true :: second)).bits.tail) := by ring
        _ = littleValue (true :: first) * (littleValue (true :: second) - littleValue (true :: first)) := by rw [hEven]
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.sub_le _ _)

-- Each transition consumes one actual input-ruler cell. Numerical values and
-- the product measure are used exclusively to prove sufficient ruler length.
def loop : List Bool → List Bool → List Bool → List Bool
  | [],first,second => if BinaryEuclideanGCD.nonzero first then first else second
  | _ :: ruler,first,second =>
      if BinaryEuclideanGCD.nonzero first then
        if BinaryEuclideanGCD.nonzero second then
          match first,second with
          | false :: a,false :: b => false :: loop ruler a b
          | false :: a,true :: b => loop ruler a (true :: b)
          | true :: a,false :: b => loop ruler (true :: a) b
          | true :: a,true :: b =>
              let d := difference (true :: a) (true :: b)
              if d.negative then loop ruler (true :: a) d.bits.tail
              else loop ruler d.bits.tail (true :: b)
          | _,_ => []
        else first
      else second

theorem loop_correct (ruler first second : List Bool)
    (hProduct : littleValue first * littleValue second < 2 ^ ruler.length) :
    littleValue (loop ruler first second) = Nat.gcd (littleValue first) (littleValue second) := by
  induction ruler generalizing first second with
  | nil =>
      have hz : littleValue first = 0 ∨ littleValue second = 0 :=
        Nat.mul_eq_zero.mp (by
          have h : littleValue first * littleValue second < 1 := by simpa using hProduct
          omega)
      rcases hz with hz | hz
      · simp only [loop,(BinaryEuclideanGCD.nonzero_false_iff first).mpr hz,Bool.false_eq_true,ite_false,hz,Nat.gcd_zero_left]
      · by_cases hn : BinaryEuclideanGCD.nonzero first = true
        · rw [loop,ite_eq_left hn,hz,Nat.gcd_zero_right]
        · have ha : littleValue first = 0 := by
            apply (BinaryEuclideanGCD.nonzero_false_iff first).mp
            cases hc : BinaryEuclideanGCD.nonzero first <;> simp_all
          rw [loop,ite_eq_right hn,ha,Nat.gcd_zero_left]
  | cons unused ruler ih =>
      conv_lhs => unfold loop
      by_cases ha : BinaryEuclideanGCD.nonzero first = true
      · rw [ite_eq_left ha]
        by_cases hb : BinaryEuclideanGCD.nonzero second = true
        · rw [ite_eq_left hb]
          cases first with
          | nil => simp [BinaryEuclideanGCD.nonzero] at ha
          | cons a first =>
            cases second with
            | nil => simp [BinaryEuclideanGCD.nonzero] at hb
            | cons b second =>
              have hp := hProduct
              simp only [List.length_cons,pow_succ] at hp
              cases a <;> cases b
              · have hNext : littleValue first * littleValue second < 2 ^ ruler.length := by
                  simp only [littleValue,Bool.false_eq_true,ite_false,Nat.add_zero] at hp
                  nlinarith
                change 2 * littleValue (loop ruler first second) = _
                rw [ih first second hNext]
                simp only [littleValue,Bool.false_eq_true,ite_false,Nat.add_zero,Nat.gcd_mul_left]
              · have hNext : littleValue first * littleValue (true :: second) < 2 ^ ruler.length := by
                  change (2 * littleValue first) * littleValue (true :: second) < _ at hp
                  nlinarith
                rw [ih first (true :: second) hNext]
                have hc : Nat.Coprime 2 (littleValue (true :: second)) := by simp [littleValue,Nat.coprime_comm]
                exact (hc.gcd_mul_left_cancel _).symm
              · have hNext : littleValue (true :: first) * littleValue second < 2 ^ ruler.length := by
                  change littleValue (true :: first) * (2 * littleValue second) < _ at hp
                  nlinarith
                rw [ih (true :: first) second hNext]
                have hc : Nat.Coprime 2 (littleValue (true :: first)) := by simp [littleValue,Nat.coprime_comm]
                exact (hc.gcd_mul_left_cancel_right _).symm
              · have hStep := odd_step first second
                dsimp only at hStep ⊢
                cases hs : (difference (true :: first) (true :: second)).negative <;>
                  simp only [hs,Bool.false_eq_true,ite_false,ite_true] at hStep ⊢
                · have hNext : littleValue (difference (true :: first) (true :: second)).bits.tail *
                      littleValue (true :: second) < 2 ^ ruler.length := by omega
                  rw [ih _ _ hNext]
                  exact hStep.1
                · have hNext : littleValue (true :: first) *
                      littleValue (difference (true :: first) (true :: second)).bits.tail < 2 ^ ruler.length := by omega
                  rw [ih _ _ hNext]
                  exact hStep.1
        · have hz : littleValue second = 0 := by
            apply (BinaryEuclideanGCD.nonzero_false_iff second).mp
            cases hc : BinaryEuclideanGCD.nonzero second <;> simp_all
          rw [ite_eq_right hb,hz,Nat.gcd_zero_right]
      · have hz : littleValue first = 0 := by
          apply (BinaryEuclideanGCD.nonzero_false_iff first).mp
          cases hc : BinaryEuclideanGCD.nonzero first <;> simp_all
        rw [ite_eq_right ha,hz,Nat.gcd_zero_left]

def gcd (first second : List Bool) : List Bool := loop (first ++ second) first second

theorem gcd_value (first second : List Bool) : littleValue (gcd first second) =
    Nat.gcd (littleValue first) (littleValue second) := by
  apply loop_correct
  have ha := BinaryBorrowWord.littleValue_bounds first
  have hb := BinaryBorrowWord.littleValue_bounds second
  rw [List.length_append,pow_add]
  nlinarith [Nat.two_pow_pos first.length,Nat.two_pow_pos second.length]

theorem difference_tail_length (first second : List Bool) (W : ℕ)
    (ha : first.length ≤ W) (hb : second.length ≤ W) :
    (difference first second).bits.tail.length ≤ W := by
  rw [List.length_tail,difference_length]
  omega

theorem loop_length (ruler first second : List Bool) (W : ℕ)
    (ha : first.length ≤ W) (hb : second.length ≤ W) :
    (loop ruler first second).length ≤ W + ruler.length := by
  induction ruler generalizing first second with
  | nil => simp only [loop,List.length_nil,Nat.add_zero]; split <;> assumption
  | cons unused ruler ih =>
      conv_lhs => unfold loop
      split
      · split
        · cases first with
          | nil => simp
          | cons a first =>
            cases second with
            | nil => simp
            | cons b second =>
              have hfa : first.length ≤ W := by simp only [List.length_cons] at ha; omega
              have hsb : second.length ≤ W := by simp only [List.length_cons] at hb; omega
              cases a <;> cases b
              · have hi := ih first second hfa hsb
                simp only [List.length_cons] at *
                omega
              · exact (ih first (true :: second) hfa hb).trans (by simp only [List.length_cons]; omega)
              · exact (ih (true :: first) second ha hsb).trans (by simp only [List.length_cons]; omega)
              · dsimp only
                have hd := difference_tail_length (true :: first) (true :: second) W ha hb
                split
                · exact (ih (true :: first) _ ha hd).trans (by simp only [List.length_cons]; omega)
                · exact (ih _ (true :: second) hd hb).trans (by simp only [List.length_cons]; omega)
        · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega

-- Erasable work observer for the same Boolean/list operations and branches.
def loopWork : List Bool → List Bool → List Bool → ℕ
  | [],first,second => 3 * (first.length + 1) + 3 * (second.length + 1) + 1
  | _ :: ruler,first,second =>
      3 * (first.length + 1) + 3 * (second.length + 1) + 4 +
      if BinaryEuclideanGCD.nonzero first then
        if BinaryEuclideanGCD.nonzero second then
          match first,second with
          | false :: a,false :: b => 3 + loopWork ruler a b
          | false :: a,true :: b => 2 + loopWork ruler a (true :: b)
          | true :: a,false :: b => 2 + loopWork ruler (true :: a) b
          | true :: a,true :: b =>
              let d := difference (true :: a) (true :: b)
              differenceWork (true :: a) (true :: b) + 8 +
                if d.negative then loopWork ruler (true :: a) d.bits.tail
                else loopWork ruler d.bits.tail (true :: b)
          | _,_ => 0
        else 0
      else 0

theorem loopWork_bound (ruler first second : List Bool) (W : ℕ)
    (ha : first.length ≤ W) (hb : second.length ≤ W) :
    loopWork ruler first second ≤ 100 * (W + 1) * (ruler.length + 1) := by
  induction ruler generalizing first second with
  | nil => simp only [loopWork,List.length_nil]; omega
  | cons unused ruler ih =>
      conv_lhs => unfold loopWork
      split
      · split
        · cases first with
          | nil => simp_all [BinaryEuclideanGCD.nonzero]
          | cons a first =>
            cases second with
            | nil => simp_all [BinaryEuclideanGCD.nonzero]
            | cons b second =>
              have hfa : first.length ≤ W := by simp only [List.length_cons] at ha; omega
              have hsb : second.length ≤ W := by simp only [List.length_cons] at hb; omega
              cases a <;> cases b
              · have hi := ih first second hfa hsb
                simp only [List.length_cons] at *
                nlinarith
              · have hi := ih first (true :: second) hfa hb
                simp only [List.length_cons] at *
                nlinarith
              · have hi := ih (true :: first) second ha hsb
                simp only [List.length_cons] at *
                nlinarith
              · have hd := difference_tail_length (true :: first) (true :: second) W ha hb
                have hc := differenceWork_bound (true :: first) (true :: second)
                have hw : max (true :: first).length (true :: second).length ≤ W := max_le ha hb
                dsimp only
                split
                · have hi := ih (true :: first) _ ha hd
                  simp only [List.length_cons] at *
                  nlinarith
                · have hi := ih _ (true :: second) hd hb
                  simp only [List.length_cons] at *
                  nlinarith
        · simp only [List.length_cons]; nlinarith
      · simp only [List.length_cons]; nlinarith

def canonicalGcd (first second : List Bool) : List Bool := BinaryCanonicalMagnitude.trim (gcd first second)

theorem canonicalGcd_value (first second : List Bool) : littleValue (canonicalGcd first second) =
    Nat.gcd (littleValue first) (littleValue second) := by
  rw [canonicalGcd,BinaryCanonicalMagnitude.trim_value,gcd_value]

theorem canonicalGcd_length (first second : List Bool) :
    (canonicalGcd first second).length ≤ max first.length second.length := by
  let W := max first.length second.length
  have hfa := BinaryBorrowWord.littleValue_bounds first
  have hsb := BinaryBorrowWord.littleValue_bounds second
  have ha : littleValue first < 2 ^ W := hfa.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have hb : littleValue second < 2 ^ W := hsb.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  have hBound : littleValue (gcd first second) < 2 ^ W := by
    rw [gcd_value]
    by_cases hz : littleValue first = 0
    · simpa [hz] using hb
    · exact (Nat.gcd_le_left _ (by omega)).trans_lt ha
  by_cases hz : littleValue (gcd first second) = 0
  · simp only [canonicalGcd,BinaryCanonicalMagnitude.trim_zero _ hz,List.length_nil]
    omega
  · rw [canonicalGcd,BinaryDirectDyadicMidpoint.trim_length_exact _ hz]
    have hl := (Nat.log2_lt hz).mpr hBound
    unfold binaryWordWidth
    change _ ≤ W
    omega

-- Ruler construction and final trimming are included. The annotation is
-- erased when interpreting the Boolean-list data algorithm; its evaluation
-- as a Lean Nat program is not asserted to run within this bit count.
def gcdWithWork (first second : List Bool) : List Bool × ℕ :=
  let ruler := first ++ second
  let result := loop ruler first second
  let trimmed := BinaryCanonicalMagnitude.trimWithWork result
  (trimmed.1,2 * (first.length + second.length + 1) + loopWork ruler first second + trimmed.2)

theorem gcdWithWork_state (first second : List Bool) : (gcdWithWork first second).1 = canonicalGcd first second := rfl

theorem gcdWithWork_bound (first second : List Bool) : (gcdWithWork first second).2 ≤
    400 * (max first.length second.length + 1) ^ 2 := by
  let W := max first.length second.length
  have ha : first.length ≤ W := Nat.le_max_left _ _
  have hb : second.length ≤ W := Nat.le_max_right _ _
  have hl := loop_length (first ++ second) first second W ha hb
  have hw := loopWork_bound (first ++ second) first second W ha hb
  have ht := BinaryCanonicalMagnitude.bitWork_bound (loop (first ++ second) first second)
  rw [List.length_append] at hl hw
  change 2 * (first.length + second.length + 1) + loopWork (first ++ second) first second +
    BinaryCanonicalMagnitude.bitWork (loop (first ++ second) first second) ≤ 400 * (W + 1) ^ 2
  nlinarith

theorem gcdWithWork_contract (first second : List Bool) :
    littleValue (gcdWithWork first second).1 = Nat.gcd (littleValue first) (littleValue second) ∧
      (gcdWithWork first second).1.length ≤ max first.length second.length ∧
      (gcdWithWork first second).2 ≤ 400 * (max first.length second.length + 1) ^ 2 :=
  ⟨canonicalGcd_value first second,canonicalGcd_length first second,gcdWithWork_bound first second⟩

end Blotto.BinarySteinGCD
