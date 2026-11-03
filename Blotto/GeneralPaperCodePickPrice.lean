import Blotto.GeneralPaperLeastValidPointsPrice

/-! Exact optional-entry code minimum. Equal code costs retain the earlier
payload. Every Option/control/reference operation and code comparison is
priced; selected-code caps come from native decoder/scan soundness later.
-/
namespace Blotto.GeneralPaperCodePickPrice
open GeneralPaperCodeAlphabet
open GeneralPaperCodeMinimumScan (Entry)
open GeneralPaperDecoderControls
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run (primitive : ℕ → ℕ) (W : ℕ) : Option Entry → Option Entry → Option Entry × ℕ
  | none,b => (b,64*W)
  | a,none => (a,64*W)
  | some a,some b =>
    (if a.cost≤b.cost then some a else some b,GeneralPaperIntegerWordPrice.compare primitive a.cost b.cost+64*W)

theorem data (primitive : ℕ → ℕ) (W : ℕ) (a b : Option Entry) :
    (run primitive W a b).1=GeneralPaperOrderedMinimum.pick a b := by cases a <;> cases b <;> rfl

theorem bit_work (model : RationalCostModel) (W : ℕ) (alphabet : Alphabet) (a b : Option Entry)
    (hA : ∀ e,a=some e → e.cost≤8*alphabet.C) (hB : ∀ e,b=some e → e.cost≤8*alphabet.C) :
    (run model.rat W a b).2≤model.rat (operandWidth alphabet.lambda)+64*W := by
  cases a with
  | none => change 64*W≤_; omega
  | some a =>
    cases b with
    | none => change 64*W≤_; omega
    | some b =>
      exact Nat.add_le_add_right (GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone a.cost b.cost _
        (code_word alphabet a.cost (hA a rfl)) (code_word alphabet b.cost (hB b rfl))) _

theorem arithmetic_work (a b : Option Entry) : (run (fun _ => 1) 1 a b).2≤65 := by
  cases a <;> cases b <;> simp only [run,GeneralPaperIntegerWordPrice.compare,Nat.mul_one] <;> omega

end Blotto.GeneralPaperCodePickPrice
