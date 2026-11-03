import Blotto.GeneralPaperDecoderMidpointPrice

/-! Exact native bucket decoder. A shared branch-test allowance prices all
reachable scalar guards; only the selected midpoint call executes. Grid
fractions borrow the retained denominator and positivity certificate.
-/
namespace Blotto.GeneralPaperDecodeBucketExecution
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def primitive (bits : Bool) (model : RationalCostModel) : ℕ → ℕ := if bits then model.rat else fun _ => 1

def control (price : ℕ → ℕ) (W : ℕ) (a : Alphabet) (bucket slot : ℕ) : ℕ :=
  GeneralPaperIntegerWordPrice.compare price bucket a.C+
  GeneralPaperIntegerWordPrice.compare price slot 0+
  GeneralPaperIntegerWordPrice.compare price slot 1+
  GeneralPaperIntegerWordPrice.compare price bucket a.C+
  GeneralPaperIntegerWordPrice.compare price slot 2+
  GeneralPaperIntegerWordPrice.compare price slot 3+128*W

def run (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (bucket slot : ℕ) :
    GeneralPaperCodeDecode.Result × ℕ :=
  let common := control (primitive bits model) W a bucket slot
  if bucket≤a.C then
    if slot=0 then (⟨some ⟨grid a bucket,false⟩,32⟩,common+64*W) else
    if slot=1 then
      if response=true ∧ bucket<a.C then (⟨some ⟨grid a bucket,true⟩,32⟩,common+64*W)
      else (⟨none,32⟩,common+64*W)
    else if bucket<a.C ∧ (slot=2 ∨ (slot=3 ∧ response=true)) then
      let found := GeneralPaperDecoderMidpointPrice.run bits model W false a bucket
      (⟨found.1.fraction.map (fun f => ⟨f,decide (slot=3)⟩),found.1.work+48⟩,
        common+found.2+GeneralPaperNaturalPrimitivePrice.binary (primitive bits model) (fun a b => a+b) found.1.work 48+64*W)
    else (⟨none,32⟩,common+64*W)
  else (⟨none,32⟩,common+64*W)

theorem data (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (bucket slot : ℕ) :
    (run bits model W a response bucket slot).1=GeneralPaperCodeDecode.decodeBucket a response bucket slot := by
  unfold run GeneralPaperCodeDecode.decodeBucket
  split
  · split
    · rfl
    · split
      · split <;> rfl
      · split
        · dsimp only
          rw [GeneralPaperDecoderMidpointPrice.strict_data]
        · rfl
  · rfl

end Blotto.GeneralPaperDecodeBucketExecution
