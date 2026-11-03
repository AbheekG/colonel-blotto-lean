import Blotto.GeneralPaperCodeSplitPrice

/-! The decoder's midpoint call preserves every native result field.
Bit execution reuses streaming CF at the derived metadata/control word.
Unit execution uses arithmetic-only constructed quotients and a fixed final
filter ledger: five casts, three divisions, successor/comparisons and writes.
-/
namespace Blotto.GeneralPaperDecoderMidpointPrice
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls
set_option autoImplicit false
set_option maxHeartbeats 6000000

def filterUnitCost (s : GeneralPaperRegularCFLoop.State) : ℕ :=
  match s.selected with | none => 64 | some _ => 111

def arithmetic (closed : Bool) (a : Alphabet) (bucket : ℕ) : GeneralPaperMidpointQuery.Result × ℕ :=
  let raw := GeneralPaperMidpointRawBits.run (fun _ => 1) 1 a.D a.C bucket a.lambda
  (GeneralPaperMidpointFilterBits.filter closed a.C bucket raw.1,raw.2+filterUnitCost raw.1+24)

def run (bits : Bool) (model : RationalCostModel) (W : ℕ) (closed : Bool) (a : Alphabet) (bucket : ℕ) :
    GeneralPaperMidpointQuery.Result × ℕ :=
  if bits then GeneralPaperStreamingMidpointQuery.run model (controlWord W a.lambda) closed a.D a.C bucket a.lambda
  else arithmetic closed a bucket

theorem arithmetic_strict_data (a : Alphabet) (bucket : ℕ) :
    (arithmetic false a bucket).1=GeneralPaperMidpointQuery.lookup a.D a.C bucket a.lambda := by
  unfold arithmetic
  dsimp only
  rw [GeneralPaperMidpointRawBits.data]
  exact GeneralPaperMidpointFilterBits.strict_data _ _ _ _

theorem arithmetic_closed_data (a : Alphabet) (bucket : ℕ) :
    (arithmetic true a bucket).1=GeneralPaperProxyRootQuery.lookup a.D a.C bucket a.lambda := by
  unfold arithmetic
  dsimp only
  rw [GeneralPaperMidpointRawBits.data]
  exact GeneralPaperMidpointFilterBits.closed_data _ _ _ _

theorem strict_data (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (bucket : ℕ) :
    (run bits model W false a bucket).1=GeneralPaperMidpointQuery.lookup a.D a.C bucket a.lambda := by
  cases bits
  · exact arithmetic_strict_data a bucket
  · exact GeneralPaperStreamingMidpointQuery.strict_data model _ _ _ _ _

theorem closed_data (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (bucket : ℕ) :
    (run bits model W true a bucket).1=GeneralPaperProxyRootQuery.lookup a.D a.C bucket a.lambda := by
  cases bits
  · exact arithmetic_closed_data a bucket
  · exact GeneralPaperStreamingMidpointQuery.closed_data model _ _ _ _ _

theorem bit_work (model : RationalCostModel) (W : ℕ) (closed : Bool) (a : Alphabet) (bucket : ℕ) (hBucket : bucket<a.C) :
    (run true model W closed a bucket).2≤2097152*(a.lambda+3)*
      (controlWord W a.lambda+model.rat (operandWidth a.lambda)) := by
  have h := GeneralPaperStreamingMidpointQuery.work model (controlWord W a.lambda) a.D a.C bucket a.lambda closed
    a.orderPositive a.scalePositive hBucket a.dyadic
  exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone (cf_width a)) _))

theorem filter_unit_work (s : GeneralPaperRegularCFLoop.State) : filterUnitCost s≤111 := by
  cases hs : s.selected <;> simp only [filterUnitCost,hs] <;> omega

theorem arithmetic_work (model : RationalCostModel) (closed : Bool) (a : Alphabet) (bucket : ℕ) (hBucket : bucket<a.C) :
    (run false model 1 closed a bucket).2≤4194304*(a.lambda+3) := by
  have hRaw := GeneralPaperMidpointRawBits.work (fun _ => 1) (fun _ _ _ => Nat.le_refl 1) 1 a.D a.C bucket a.lambda
    a.orderPositive a.scalePositive hBucket a.dyadic
  have hFilter := filter_unit_work (GeneralPaperMidpointRawBits.run (fun _ => 1) 1 a.D a.C bucket a.lambda).1
  change (GeneralPaperMidpointRawBits.run (fun _ => 1) 1 a.D a.C bucket a.lambda).2+
    filterUnitCost (GeneralPaperMidpointRawBits.run (fun _ => 1) 1 a.D a.C bucket a.lambda).1+24≤_
  change _≤1048576*(a.lambda+3)*2 at hRaw
  omega

theorem native_work (bits : Bool) (model : RationalCostModel) (W : ℕ) (closed : Bool) (a : Alphabet) (bucket : ℕ)
    (hBucket : bucket<a.C) : (run bits model W closed a bucket).1.work≤170*a.lambda+370 := by
  have h := GeneralPaperMidpointRealWork.lookup_real_work a.D a.C bucket a.lambda
    a.orderPositive a.scalePositive hBucket a.dyadic
  cases closed
  · rw [strict_data]
    exact h
  · rw [closed_data]
    exact h

end Blotto.GeneralPaperDecoderMidpointPrice
