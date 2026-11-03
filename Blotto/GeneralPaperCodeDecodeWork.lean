import Blotto.GeneralPaperCodeDecodeComplete

/-! Complete declared real-RAM source work of literal code decoding. Tail
rejection, arithmetic bucket splitting, branch tests, actual midpoint work
and returned records are charged. Bit/storage and surrounding prices remain
separate source joins.
-/
namespace Blotto.GeneralPaperCodeDecodeWork
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem bucket_work (a : Alphabet) (response : Bool) (t slot : ℕ) :
    (decodeBucket a response t slot).work≤170*a.lambda+418 := by
  dsimp only [decodeBucket]
  split
  · split
    · dsimp only
      omega
    · split
      · split <;> dsimp only <;> omega
      · split
        · rename_i hMode
          have he := GeneralPaperMidpointRealWork.lookup_real_work a.D a.C t a.lambda
            a.orderPositive a.scalePositive hMode.1 a.dyadic
          dsimp only
          omega
        · dsimp only
          omega
  · dsimp only
    omega

theorem decode_work (a : Alphabet) (response : Bool) (code : ℕ) : (decode a response code).work≤184*a.lambda+476 := by
  dsimp only [decode]
  split
  · have hs := GeneralPaperCodeSplit.run_work code a.lambda
    have hd := bucket_work a response (GeneralPaperCodeSplit.run code a.lambda).bucket (GeneralPaperCodeSplit.run code a.lambda).slot
    dsimp only
    omega
  · dsimp only
    omega

end Blotto.GeneralPaperCodeDecodeWork
