import Blotto.GeneralPaperSamplerRecordInstallation

/-! Priced header-target copying also computes the actual target count.
Padding and left-only concatenation have exact data/work identities. These
are executed passes over retained words, not supplied count/size observers. -/
namespace Blotto.GeneralPaperHeaderTargetCopy
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

structure Copied (A : ℕ) where
  values : List (FixedBinaryWord A)
  count : ℕ
  work : ℕ

def run (model : RationalCostModel) (S A : ℕ) : List (FixedBinaryWord A) → Copied A
  | [] => ⟨[],0,64 * (S + A + 1)⟩
  | value :: values =>
    let later := run model S A values
    let count := GeneralPaperNaturalScalarStep.run model S .add later.count 1
    ⟨value :: later.values,count.1,later.work + count.2 + A + 128 * (S + A + 1)⟩

theorem data (model : RationalCostModel) (S A : ℕ) (values : List (FixedBinaryWord A)) : (run model S A values).values = values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [run,ih]

theorem count (model : RationalCostModel) (S A : ℕ) (values : List (FixedBinaryWord A)) : (run model S A values).count = values.length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [run,GeneralPaperNaturalScalarStep.run,GeneralPaperNaturalScalarStep.Op.apply,ih,List.length_cons]

def price (model : RationalCostModel) (S A : ℕ) : ℕ → ℕ
  | 0 => 64 * (S + A + 1)
  | n + 1 => price model S A n + (GeneralPaperNaturalScalarStep.run model S .add n 1).2 + A + 128 * (S + A + 1)

theorem work (model : RationalCostModel) (S A : ℕ) (values : List (FixedBinaryWord A)) : (run model S A values).work = price model S A values.length := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [run,count,ih,List.length_cons,price]

def padding (S A : ℕ) (zero : FixedBinaryWord A) : ℕ → List (FixedBinaryWord A) × ℕ
  | 0 => ([],64 * (S + A + 1))
  | n + 1 =>
    let later := padding S A zero n
    (zero :: later.1,later.2 + A + 64 * (S + A + 1))

theorem padding_data (S A : ℕ) (zero : FixedBinaryWord A) (n : ℕ) : (padding S A zero n).1 = List.replicate n zero := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [padding,ih,List.replicate_succ]

theorem padding_work (S A : ℕ) (zero : FixedBinaryWord A) (n : ℕ) :
    (padding S A zero n).2 = n * (A + 64 * (S + A + 1)) + 64 * (S + A + 1) := by
  induction n with
  | zero => simp only [padding,Nat.zero_mul,Nat.zero_add]
  | succ n ih => simp only [padding,ih]; ring

def append (S A : ℕ) : List (FixedBinaryWord A) → List (FixedBinaryWord A) → List (FixedBinaryWord A) × ℕ
  | [],rest => (rest,64 * (S + A + 1))
  | value :: values,rest =>
    let later := append S A values rest
    (value :: later.1,later.2 + A + 64 * (S + A + 1))

theorem append_data (S A : ℕ) (first rest : List (FixedBinaryWord A)) : (append S A first rest).1 = first ++ rest := by
  induction first with
  | nil => rfl
  | cons value values ih => simp only [append,ih,List.cons_append]

theorem append_work (S A : ℕ) (first rest : List (FixedBinaryWord A)) :
    (append S A first rest).2 = first.length * (A + 64 * (S + A + 1)) + 64 * (S + A + 1) := by
  induction first with
  | nil => simp only [append,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons value values ih => simp only [append,ih,List.length_cons]; ring

end Blotto.GeneralPaperHeaderTargetCopy
