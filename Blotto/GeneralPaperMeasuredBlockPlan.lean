import Blotto.GeneralPaperEqualCopiedPreparationContract

/-! Executed block-size plans for the paper indexed-storage model. Scalar
sizes are measured by stored-word primitives; reference/header sizes use
priced scalar arithmetic. Joining plans executes a priced list traversal.
No erased retained-size observer is evaluated by these constructors. -/
namespace Blotto.GeneralPaperMeasuredBlockPlan
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

structure Plan where
  sizes : List ℕ
  work : ℕ

def natural (model : RationalCostModel) (S : ℕ) (n : ℕ) : Plan :=
  let length := GeneralPaperStoredWordLength.run S n
  let size := GeneralPaperNaturalScalarStep.run model S .add length.1 1
  ⟨[size.1],length.2 + size.2 + 64 * S + 64⟩

theorem natural_data (model : RationalCostModel) (S n : ℕ) : (natural model S n).sizes = [natBits n] := by
  simp only [natural,GeneralPaperNaturalScalarStep.run,GeneralPaperNaturalScalarStep.Op.apply,
    GeneralPaperStoredWordLength.run,natBits,Nat.add_comm]

def rational (model : RationalCostModel) (S : ℕ) (q : ℚ) : Plan :=
  let size := GeneralPaperStoredRationalWordLength.run model S q
  ⟨[size.1],size.2 + 64 * S + 64⟩

theorem rational_data (model : RationalCostModel) (S : ℕ) (q : ℚ) :
    (rational model S q).sizes = [rationalWordWidth q] := by
  simp only [rational,GeneralPaperStoredRationalWordLength.data]

def references (model : RationalCostModel) (S A count stride fixed : ℕ) : Plan :=
  let slots := GeneralPaperNaturalScalarStep.run model S .mul stride count
  let cells := GeneralPaperNaturalScalarStep.run model S .add slots.1 fixed
  let size := GeneralPaperNaturalScalarStep.run model S .mul A cells.1
  ⟨[size.1],slots.2 + cells.2 + size.2 + 64 * S + 64⟩

theorem references_data (model : RationalCostModel) (S A count stride fixed : ℕ) :
    (references model S A count stride fixed).sizes = [A * (stride * count + fixed)] := rfl

def append (S : ℕ) : List ℕ → List ℕ → List ℕ × ℕ
  | [],ys => (ys,64 * S + 64)
  | x :: xs,ys =>
    let later := append S xs ys
    (x :: later.1,later.2 + natBits x + 64 * S + 64)

theorem append_data (S : ℕ) (xs ys : List ℕ) : (append S xs ys).1 = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [append,ih,List.cons_append]

theorem append_work (S : ℕ) (xs ys : List ℕ) :
    (append S xs ys).2 = (xs.map natBits).sum + (xs.length + 1) * (64 * S + 64) := by
  induction xs with
  | nil => simp only [append,List.map_nil,List.sum_nil,List.length_nil]; omega
  | cons x xs ih => simp only [append,ih,List.map_cons,List.sum_cons,List.length_cons]; ring

def join (S : ℕ) (left right : Plan) : Plan :=
  let actual := append S left.sizes right.sizes
  ⟨actual.1,left.work + right.work + actual.2 + 64 * S + 64⟩

theorem join_data (S : ℕ) (left right : Plan) : (join S left right).sizes = left.sizes ++ right.sizes :=
  append_data S left.sizes right.sizes

theorem join_sum (S : ℕ) (left right : Plan) : (join S left right).sizes.sum = left.sizes.sum + right.sizes.sum := by
  rw [join_data,List.sum_append]

def sequence (S : ℕ) : List Plan → Plan
  | [] => ⟨[],64 * S + 64⟩
  | p :: plans => join S p (sequence S plans)

theorem sequence_data (S : ℕ) (plans : List Plan) :
    (sequence S plans).sizes = (plans.map Plan.sizes).flatten := by
  induction plans with
  | nil => rfl
  | cons p plans ih => simp only [sequence,join_data,ih,List.map_cons,List.flatten_cons]

theorem sequence_sum (S : ℕ) (plans : List Plan) :
    (sequence S plans).sizes.sum = (plans.map (fun p => p.sizes.sum)).sum := by
  induction plans with
  | nil => rfl
  | cons p plans ih => simp only [sequence,join_sum,ih,List.map_cons,List.sum_cons]

end Blotto.GeneralPaperMeasuredBlockPlan
