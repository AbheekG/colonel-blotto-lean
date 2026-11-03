import Blotto.GeneralPaperQuotientBits
import Blotto.GeneralPaperIntegerWordPrice
import Blotto.GeneralPaperParameterCounterWords

/-! A complete operand-sensitive bounded quotient. Descent doubles the
divisor once; return computes the selected quotient bit and remainder once.
Native work fields and predecessor controls are priced as actual operations.
No built-in division or modulus is used in either model.
-/
namespace Blotto.GeneralPaperCompleteQuotientPrice
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def controlCost (price : ℕ → ℕ) (depth : ℕ) (higher : GeneralPaperBoundedQuotient.Result) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 higher.quotient+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) higher.work 12+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) (depth+1) 1

def selectedCost (price : ℕ → ℕ) (a : ℚ) (higher : GeneralPaperBoundedQuotient.Result) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (2*higher.quotient) 1+
    GeneralPaperRationalPrimitivePrice.binary price (fun a b => a-b) higher.remainder a

def run (price : ℕ → ℕ) (W : ℕ) (x a : ℚ) : ℕ → GeneralPaperBoundedQuotient.Result × ℕ
  | 0 => (⟨0,x,2⟩,price (GeneralPaperNaturalPrimitivePrice.word 0)+
      price (GeneralPaperNaturalPrimitivePrice.word 2)+price (rationalWordWidth x)+32*W)
  | depth+1 =>
    let doubled := 2*a
    let higher := run price W x doubled depth
    let common := higher.2+GeneralPaperRationalPrimitivePrice.binary price (fun a b => a*b) 2 a+
      price (RationalExpression.pairWidth a higher.1.remainder)+controlCost price depth higher.1+64*W
    if a≤higher.1.remainder then
      (⟨2*higher.1.quotient+1,higher.1.remainder-a,higher.1.work+12⟩,common+selectedCost price a higher.1)
    else (⟨2*higher.1.quotient,higher.1.remainder,higher.1.work+12⟩,common)

theorem data (price : ℕ → ℕ) (W : ℕ) (x a : ℚ) (depth : ℕ) :
    (run price W x a depth).1=GeneralPaperBoundedQuotient.run x a depth := by
  induction depth generalizing a with
  | zero => rfl
  | succ depth ih =>
    simp only [run,ih,GeneralPaperBoundedQuotient.run]
    split <;> rfl

def width (A t depth : ℕ) : ℕ := 64+16*GeneralPaperBoundedQuotient.heightBudget A t depth

theorem width_step (A t depth : ℕ) : width A (t+2) depth=width A t (depth+1) := by
  unfold width
  rw [GeneralPaperBoundedQuotient.budget_step]

theorem width_lower (A t depth : ℕ) : 64+16*(depth+1)≤width A t depth := by
  unfold width GeneralPaperBoundedQuotient.heightBudget
  omega

theorem constant_word (A t depth n : ℕ) (hn : n≤12) :
    1+binaryWordWidth n≤width A t depth := by
  have h := binaryWordWidth_mono hn
  have h12 : binaryWordWidth 12=4 := by decide
  have hw := width_lower A t depth
  omega

end Blotto.GeneralPaperCompleteQuotientPrice
