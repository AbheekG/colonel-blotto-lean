import Blotto.GeneralPaperEqualBooleanWordCopyLifetime

/-! The actual categorical row copy retains its label and tuple records,
word-copy frames/scratch and all saved parent prices. -/
namespace Blotto.GeneralPaperEqualBooleanRowCopyLifetime
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def price (S A r w : ℕ) : ℕ := natBits r + GeneralPaperEqualBooleanCopy.wordPrice S A w + 64 * (S + A + 1)
def parentCap (S A r w : ℕ) : ℕ := price S A r w + r

def window {r w : ℕ} (S A : ℕ) (source : Fin r × FixedBinaryWord w) : ℕ :=
  GeneralPaperEqualBooleanWordCopyLifetime.window S A source.2 + natBits source.1.val + 16 * (S + A) +
    fields S [source.1.val,(GeneralPaperEqualBooleanCopy.word S A source.2).2,
      (GeneralPaperEqualBooleanCopy.row S A source).2] + 128 * (S + A + 1)

def profile (S A r w : ℕ) : ℕ :=
  GeneralPaperEqualBooleanWordCopyLifetime.profile S A w + natBits r + 16 * (S + A) +
    3 * (natBits (parentCap S A r w) + S) + 32 * S + 128 * (S + A + 1)

theorem bounded {r w : ℕ} (S A : ℕ) (source : Fin r × FixedBinaryWord w) :
    window S A source ≤ profile S A r w := by
  have hChild := GeneralPaperEqualBooleanWordCopyLifetime.bounded S A source.2
  have hWord := GeneralPaperEqualBooleanCopy.word_work S A source.2
  have hWork := GeneralPaperEqualBooleanCopy.row_work S A source
  have hi : natBits source.1.val ≤ natBits r := Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
  have hf := fields_bound S (natBits (parentCap S A r w))
    [source.1.val,(GeneralPaperEqualBooleanCopy.word S A source.2).2,
      (GeneralPaperEqualBooleanCopy.row S A source).2] (by
        intro a ha
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl | rfl | rfl
        all_goals unfold parentCap price; omega)
  change fields S _ ≤ 3 * (natBits (parentCap S A r w) + S) + 32 * S at hf
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperEqualBooleanRowCopyLifetime
