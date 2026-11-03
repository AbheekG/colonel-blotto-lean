import Blotto.BinaryWordPrecision
import Blotto.BinaryStoredNatHeader

/-! Precision selection cancels word tails to obtain a unary ruler, shifts
with its Boolean shape and compares word lengths/lexicographic bits directly.
No width-counter or accuracy-payload numeric decoder is called. The scalar
precision is the resulting ruler length; its small natural/physical/backend
realization remains separate from derived Boolean/cell visits. -/

namespace Blotto.BinaryRulerPrecision

def difference : List Bool → List Bool → List Bool
  | bits, [] => bits
  | [], _ :: _ => []
  | _ :: bits, _ :: other => difference bits other

theorem difference_length (bits other : List Bool) : (difference bits other).length = bits.length - other.length := by
  induction bits generalizing other with
  | nil => cases other <;> simp [difference]
  | cons bit rest ih => cases other with
    | nil => rfl
    | cons head tail => simpa only [difference,List.length_cons,Nat.add_sub_add_right] using ih tail

def differenceVisits : List Bool → List Bool → ℕ
  | _, [] => 1
  | [], _ :: _ => 1
  | _ :: bits, _ :: other => differenceVisits bits other + 1

theorem differenceVisits_bound (bits other : List Bool) : differenceVisits bits other ≤ bits.length + 1 := by
  induction bits generalizing other with
  | nil => cases other <;> rfl
  | cons bit rest ih => cases other with
    | nil => simp only [differenceVisits,List.length_cons]; omega
    | cons head tail => have ht := ih tail; simp only [differenceVisits,List.length_cons]; omega

def compareLength : List Bool → List Bool → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | _ :: bits, _ :: other => compareLength bits other

theorem compareLength_state (bits other : List Bool) : compareLength bits other =
    if bits.length < other.length then .lt else if other.length < bits.length then .gt else .eq := by
  induction bits generalizing other with
  | nil => cases other <;> simp [compareLength]
  | cons bit rest ih => cases other with
    | nil => simp [compareLength]
    | cons head tail => simpa only [compareLength,List.length_cons,Nat.add_lt_add_iff_right] using ih tail

def compareVisits : List Bool → List Bool → ℕ
  | [], _ => 1
  | _ :: _, [] => 1
  | _ :: bits, _ :: other => compareVisits bits other + 1

theorem compareVisits_bound (bits other : List Bool) : compareVisits bits other ≤ bits.length + 1 := by
  induction bits generalizing other with
  | nil => rfl
  | cons bit rest ih => cases other with
    | nil => simp only [compareVisits,List.length_cons]; omega
    | cons head tail => have ht := ih tail; simp only [compareVisits,List.length_cons]; omega

def le (a b : PositiveBinaryWord) : Bool := match compareLength a.tail b.tail with
  | .lt => true
  | .gt => false
  | .eq => PositiveBinaryWord.leScan a.bits b.bits

theorem le_state (a b : PositiveBinaryWord) : le a b = a.leNumeric b := by
  unfold le PositiveBinaryWord.leNumeric PositiveBinaryWord.width
  rw [compareLength_state]
  simp only [Nat.add_lt_add_iff_right]
  by_cases hFirst : a.tail.length < b.tail.length
  · simp [hFirst]
  · by_cases hSecond : b.tail.length < a.tail.length <;> simp [hFirst,hSecond]

def leWithWork (a b : PositiveBinaryWord) : Bool × ℕ :=
  let compared := compareLength a.tail b.tail
  let work := compareVisits a.tail b.tail
  match compared with
  | .lt => (true,work)
  | .gt => (false,work)
  | .eq => (PositiveBinaryWord.leScan a.bits b.bits,work + PositiveBinaryWord.leScanVisits a.bits b.bits)

theorem leWithWork_state (a b : PositiveBinaryWord) : (leWithWork a b).1 = le a b := by
  unfold leWithWork le
  cases hc : compareLength a.tail b.tail <;> rfl

theorem leWithWork_bound (a b : PositiveBinaryWord) : (leWithWork a b).2 ≤ 2 * a.width := by
  have hc := compareVisits_bound a.tail b.tail
  have hs := (PositiveBinaryWord.leScanVisits_bound a.bits b.bits).1
  change PositiveBinaryWord.leScanVisits a.bits b.bits ≤ a.width at hs
  unfold leWithWork
  dsimp only
  cases ho : compareLength a.tail b.tail <;> dsimp only <;>
    unfold PositiveBinaryWord.width at * <;> omega

def shifted (word : PositiveBinaryWord) (ruler : List Bool) : PositiveBinaryWord :=
  ⟨word.tail ++ ruler.map (fun _ => false)⟩

theorem shifted_state (word : PositiveBinaryWord) (ruler : List Bool) : shifted word ruler = word.shifted ruler.length := by
  unfold shifted PositiveBinaryWord.shifted
  rw [BinaryStoredNatHeader.falseMap_eq]

def prepare (a b : PositiveBinaryWord) : List Bool × ℕ :=
  let candidate := difference a.tail b.tail
  let aligned := shifted b candidate
  let compared := leWithWork a aligned
  let ruler := if compared.1 then candidate else true :: candidate
  let work := differenceVisits a.tail b.tail + (b.tail.length + 2 * candidate.length + 2) + compared.2 + 1
  (ruler,work)

theorem candidate_length (a b : PositiveBinaryWord) : (difference a.tail b.tail).length = a.width - b.width := by
  rw [difference_length]
  unfold PositiveBinaryWord.width
  omega

theorem prepare_length (a b : PositiveBinaryWord) : (prepare a b).1.length = a.ratioPrecision b := by
  rw [PositiveBinaryWord.ratioPrecision_refines]
  unfold prepare PositiveBinaryWord.ratioPrecisionNumeric
  dsimp only
  rw [leWithWork_state,le_state,shifted_state,candidate_length]
  split
  · exact candidate_length a b
  · exact congrArg (fun k : ℕ => k + 1) (candidate_length a b)

theorem prepare_length_bound (a b : PositiveBinaryWord) : (prepare a b).1.length ≤ a.width := by
  have hc : (difference a.tail b.tail).length ≤ a.tail.length := by rw [difference_length]; exact Nat.sub_le _ _
  unfold prepare
  dsimp only
  split
  · exact hc.trans (by unfold PositiveBinaryWord.width; omega)
  · change (difference a.tail b.tail).length + 1 ≤ a.width
    unfold PositiveBinaryWord.width
    omega

theorem prepare_bound (a b : PositiveBinaryWord) : (prepare a b).2 ≤ 5 * a.width + b.width + 2 := by
  have hd := differenceVisits_bound a.tail b.tail
  have hc : (difference a.tail b.tail).length ≤ a.tail.length := by rw [difference_length]; exact Nat.sub_le _ _
  have hl := leWithWork_bound a (shifted b (difference a.tail b.tail))
  unfold prepare
  dsimp only
  unfold PositiveBinaryWord.width at *
  omega

def precisionWithWork (a b : PositiveBinaryWord) : ℕ × ℕ :=
  let prepared := prepare a b
  (prepared.1.length,prepared.2 + prepared.1.length + 1)

theorem precisionWithWork_state (a b : PositiveBinaryWord) : (precisionWithWork a b).1 = a.ratioPrecision b := prepare_length a b

theorem precisionWithWork_bound (a b : PositiveBinaryWord) : (precisionWithWork a b).2 ≤ 8 * (a.width + b.width + 1) := by
  have hp := prepare_bound a b
  have hl := prepare_length_bound a b
  unfold precisionWithWork
  dsimp only
  omega

end Blotto.BinaryRulerPrecision
