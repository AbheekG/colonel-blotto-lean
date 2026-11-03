import Blotto.GeneralPaperMeasuredListBlockPlan

/-! Actual measured block plans for retained route records and Boolean
words/labelled rows. Widths come from the stored scalar/list measurers; only
fixed datatype tags and fixed reference-header arities are constants. -/
namespace Blotto.GeneralPaperEqualMeasuredLeafPlans
open GeneralPaperMeasuredBlockPlan GeneralPaperEqualRetainedStorage GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def reserve (model : RationalCostModel) (S A arity : ℕ) : Plan := references model S A 0 0 arity

theorem reserve_sum (model : RationalCostModel) (S A arity : ℕ) :
    (reserve model S A arity).sizes.sum = arity * A := by
  rw [reserve,references_data]
  simp only [Nat.mul_zero,Nat.zero_add,List.sum_cons,List.sum_nil,Nat.add_zero]
  ring

def tag (S : ℕ) : Plan := ⟨[1],64 * S + 64⟩
def bit (S : ℕ) (_ : Bool) : Plan := tag S
def empty (S : ℕ) : Plan := ⟨[],64 * S + 64⟩
def unit (S : ℕ) (_ : Unit) : Plan := empty S

def route {m : ℕ} (model : RationalCostModel) (S A : ℕ) (x : GroupRoute m) : Plan :=
  let label := match x.1 with
    | none => empty S
    | some g => natural model S g.val
  sequence S [tag S,label,rational model S x.2,reserve model S A 16]

theorem route_sum {m : ℕ} (model : RationalCostModel) (S A : ℕ) (x : GroupRoute m) :
    (route model S A x).sizes.sum = routeFoot A x := by
  cases x with
  | mk label coefficient =>
    cases label <;>
      simp only [route,sequence_sum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        tag,empty,natural_data,rational_data,reserve_sum,Nat.add_zero,Nat.zero_add,Nat.add_assoc,routeFoot]

def word {w : ℕ} (model : RationalCostModel) (S A : ℕ) (x : FixedBinaryWord w) : Plan :=
  join S (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (bit S) x.bits) (reserve model S A 16)

theorem word_sum {w : ℕ} (model : RationalCostModel) (S A : ℕ) (x : FixedBinaryWord w) :
    (word model S A x).sizes.sum = wordFoot A x := by
  dsimp only [word]
  rw [join_sum,GeneralPaperMeasuredListBlockPlan.linked_sum model S A (bit S) (fun _ : Bool => 1) x.bits
    (by intro b _; rfl),reserve_sum]
  rfl

def row {r w : ℕ} (model : RationalCostModel) (S A : ℕ) (x : Fin r × FixedBinaryWord w) : Plan :=
  sequence S [natural model S x.1.val,word model S A x.2,reserve model S A 16]

theorem row_sum {r w : ℕ} (model : RationalCostModel) (S A : ℕ) (x : Fin r × FixedBinaryWord w) :
    (row model S A x).sizes.sum = natBits x.1.val + wordFoot A x.2 + 16 * A := by
  simp only [row,sequence_sum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,natural_data,word_sum,reserve_sum,
    Nat.add_zero]
  omega

end Blotto.GeneralPaperEqualMeasuredLeafPlans
