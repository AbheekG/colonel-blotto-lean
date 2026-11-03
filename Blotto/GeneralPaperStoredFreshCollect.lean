import Blotto.GeneralPaperStoredRulerRead

/-! Fresh bits are scanned using an actually loaded count. The unsigned
countdown prices operands, result, arithmetic and control. It refines the
existing unary-ruler scan without constructing a new ruler during a draw. -/
namespace Blotto.GeneralPaperStoredFreshCollect
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

def previous (model : RationalCostModel) (A fuel : ℕ) : ℕ × ℕ :=
  let value := fuel - 1
  let width := GeneralPaperNaturalScalarStep.word
  (value,width fuel + width 1 + width value + 2 * model.rat (max (width fuel) (width 1)) + 64 * (A + 1))

theorem previous_data (model : RationalCostModel) (A fuel : ℕ) : (previous model A fuel).1 = fuel - 1 := rfl

theorem previous_work (model : RationalCostModel) (A fuel L : ℕ)
    (hFuel : GeneralPaperNaturalScalarStep.word fuel ≤ L)
    (hOne : GeneralPaperNaturalScalarStep.word 1 ≤ L)
    (hValue : GeneralPaperNaturalScalarStep.word (fuel - 1) ≤ L) :
    (previous model A fuel).2 ≤ 5 * model.rat L + 64 * (A + 1) := by
  have h1 := hFuel.trans (model.word_le L)
  have h2 := hOne.trans (model.word_le L)
  have h3 := hValue.trans (model.word_le L)
  have h4 := model.monotone (max_le hFuel hOne)
  unfold previous
  dsimp only
  omega

def collect {S : Type*} (model : RationalCostModel) (A : ℕ) (next : S → Bool × S) : ℕ → List Bool → S → GeneralPaperBooleanFreshWord.Result S
  | 0,acc,state =>
    let returned := BinaryCompareBitsMeasured.reverse (false :: acc) []
    ⟨returned.1,state,0,returned.2 + 64 * (A + 1)⟩
  | fuel + 1,acc,state =>
    let sampled := next state
    let remaining := previous model A (fuel + 1)
    let later := collect model A next remaining.1 (sampled.1 :: acc) sampled.2
    ⟨later.bits,later.state,later.reads + 1,remaining.2 + later.work + 64 * (A + 1)⟩

def price (model : RationalCostModel) (A : ℕ) : ℕ → ℕ → ℕ
  | 0,acc => 4 * acc + 6 + 64 * (A + 1)
  | fuel + 1,acc => (previous model A (fuel + 1)).2 + price model A fuel (acc + 1) + 64 * (A + 1)

theorem data {S : Type*} (model : RationalCostModel) (A : ℕ) (next : S → Bool × S)
    (ruler : List Unit) (acc : List Bool) (state : S) :
    (collect model A next ruler.length acc state).bits = (GeneralPaperBooleanFreshWord.collect next ruler acc state).bits ∧
      (collect model A next ruler.length acc state).state = (GeneralPaperBooleanFreshWord.collect next ruler acc state).state := by
  induction ruler generalizing acc state with
  | nil => exact ⟨rfl,rfl⟩
  | cons cell rest ih => exact ih ((next state).1 :: acc) (next state).2

theorem length {S : Type*} (model : RationalCostModel) (A : ℕ) (next : S → Bool × S)
    (fuel : ℕ) (acc : List Bool) (state : S) : (collect model A next fuel acc state).bits.length = fuel + acc.length + 1 := by
  have h := (data model A next (List.replicate fuel ()) acc state).1
  rw [List.length_replicate] at h
  rw [h,GeneralPaperBooleanFreshWord.collect_length,List.length_replicate]

theorem reads {S : Type*} (model : RationalCostModel) (A : ℕ) (next : S → Bool × S)
    (fuel : ℕ) (acc : List Bool) (state : S) : (collect model A next fuel acc state).reads = fuel := by
  induction fuel generalizing acc state with
  | zero => rfl
  | succ fuel ih => exact congrArg (fun n => n + 1) (ih ((next state).1 :: acc) (next state).2)

theorem work {S : Type*} (model : RationalCostModel) (A : ℕ) (next : S → Bool × S)
    (fuel : ℕ) (acc : List Bool) (state : S) : (collect model A next fuel acc state).work = price model A fuel acc.length := by
  induction fuel generalizing acc state with
  | zero =>
    simp only [collect,price,BinaryCompareBitsMeasured.reverse_work,List.length_cons]
    omega
  | succ fuel ih =>
    change (previous model A (fuel + 1)).2 + (collect model A next fuel ((next state).1 :: acc) (next state).2).work + 64 * (A + 1) = _
    rw [ih]
    rfl

end Blotto.GeneralPaperStoredFreshCollect
