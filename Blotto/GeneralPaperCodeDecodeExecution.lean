import Blotto.GeneralPaperDecodeBucketPrice

/-! Complete native decoder composition. Tail codes are rejected before
the constructed split, and only one bucket decoder runs. Input-limit and
native return-counter arithmetic have their own explicit prices.
-/
namespace Blotto.GeneralPaperCodeDecodeExecution
open GeneralPaperCodeAlphabet
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def control (price : ℕ → ℕ) (W : ℕ) (a : Alphabet) (code : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 4 a.C+
    GeneralPaperIntegerWordPrice.compare price code (4*a.C)+64*W

def additions (price : ℕ → ℕ) (splitWork bucketWork : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) splitWork bucketWork+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (splitWork+bucketWork) 16

def run (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (code : ℕ) :
    GeneralPaperCodeDecode.Result × ℕ :=
  let common := control (primitive bits model) W a code
  if code≤4*a.C then
    let split := GeneralPaperCodeSplitExecution.run bits model W code a.lambda
    let found := GeneralPaperDecodeBucketExecution.run bits model W a response split.1.bucket split.1.slot
    (⟨found.1.choice,split.1.work+found.1.work+16⟩,
      common+split.2+found.2+additions (primitive bits model) split.1.work found.1.work+64*W)
  else (⟨none,16⟩,common+64*W)

theorem data (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (code : ℕ) :
    (run bits model W a response code).1=GeneralPaperCodeDecode.decode a response code := by
  unfold run GeneralPaperCodeDecode.decode
  split
  · dsimp only
    simp only [GeneralPaperCodeSplitExecution.data,GeneralPaperDecodeBucketExecution.data]
  · rfl

theorem valid (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (code : ℕ) (choice : Choice)
    (hSome : (run bits model W a response code).1.choice=some choice) : Valid a response code := by
  rw [data] at hSome
  exact GeneralPaperCodeDecodeSound.decode_valid a response code choice hSome

theorem denominator (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (code : ℕ) (choice : Choice)
    (hSome : (run bits model W a response code).1.choice=some choice) : choice.threshold.den≤a.C := by
  rw [data] at hSome
  exact (GeneralPaperCodeDecodeSound.decode_sound a response code choice hSome).2

theorem candidate_closed (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) (choice : Choice)
    (hSome : (run bits model W a false code).1.choice=some choice) : choice.opened=false := by
  rw [data] at hSome
  exact GeneralPaperCodeDecodeSound.candidate_closed a code choice hSome

end Blotto.GeneralPaperCodeDecodeExecution
