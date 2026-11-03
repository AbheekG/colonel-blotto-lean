import Blotto.GeneralPaperMatrixCopyLifetime

/-! One conservative window covers every recursive bit-list cursor and its
one active scalar Boolean copy. The actual word-copy wrapper's saved prices,
source/target record references and controls are retained as well. -/
namespace Blotto.GeneralPaperEqualBooleanWordCopyLifetime
open GeneralPaperEncodedScalarStorage GeneralPaperEqualRetainedStorage
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def bitCopy (S A : ℕ) := GeneralPaperReferenceCopy.scalar S A (fun _ : Bool => 1)
def bitScratch (S A : ℕ) (x : Bool) := GeneralPaperScalarTableCopyLifetime.scalarWindow S A (fun _ : Bool => 1) x
def bitPrice (S A : ℕ) : ℕ := 1 + 32 * (S + A + 1)
def parentCap (S A w : ℕ) : ℕ := GeneralPaperEqualBooleanCopy.wordPrice S A w + w + S + A + 32 * (S + A + 1)

def window {w : ℕ} (S A : ℕ) (source : FixedBinaryWord w) : ℕ :=
  GeneralPaperReferenceListCopyLifetime.window S A (fun _ : Bool => 1) (fun _ : Bool => 1)
    (bitCopy S A) (fun _ => 0) source.bits none + bitScratch S A false + 16 * (S + A) +
    fields S [w,(GeneralPaperReferenceCopy.list S A (bitCopy S A) source.bits).2,
      (GeneralPaperEqualBooleanCopy.word S A source).2,32 * (S + A + 1),S,A] + 128 * (S + A + 1)

def profile (S A w : ℕ) : ℕ :=
  GeneralPaperReferenceListCopyLifetime.profile S A (w * (1 + 2 * S) + 32 * S) w 1 (bitPrice S A) 0 +
    GeneralPaperScalarTableCopyLifetime.scalarProfile S A 1 + 16 * (S + A) +
    6 * (natBits (parentCap S A w) + S) + 32 * S + 128 * (S + A + 1)

theorem active_bit (S A : ℕ) (x : Bool) : bitScratch S A x = bitScratch S A false := rfl

theorem bounded {w : ℕ} (S A : ℕ) (source : FixedBinaryWord w) : window S A source ≤ profile S A w := by
  have hOwner := list_bound S 1 (fun _ : Bool => 1) source.bits (fun _ _ => le_rfl)
  rw [source.size] at hOwner
  have hList := GeneralPaperReferenceListCopyLifetime.all_active S A _ w 1 (bitPrice S A) 0
    (fun _ : Bool => 1) (fun _ : Bool => 1) (bitCopy S A) (fun _ => 0) source.bits none
    hOwner (by rw [source.size]) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (by intro x h; cases h)
  have hScalar := GeneralPaperScalarTableCopyLifetime.scalar_bound S A 1 (fun _ : Bool => 1) false le_rfl
  have hWork := GeneralPaperEqualBooleanCopy.word_work S A source
  have hReturn : (GeneralPaperEqualBooleanCopy.word S A source).2 =
      (GeneralPaperReferenceCopy.list S A (bitCopy S A) source.bits).2 + 32 * (S + A + 1) := rfl
  have hf := fields_bound S (natBits (parentCap S A w))
    [w,(GeneralPaperReferenceCopy.list S A (bitCopy S A) source.bits).2,
      (GeneralPaperEqualBooleanCopy.word S A source).2,32 * (S + A + 1),S,A] (by
        intro a ha
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals unfold parentCap; omega)
  change fields S _ ≤ 6 * (natBits (parentCap S A w) + S) + 32 * S at hf
  dsimp only [window,profile,bitScratch]
  omega

theorem source_data {w : ℕ} (S A : ℕ) (source : FixedBinaryWord w) :
    (GeneralPaperReferenceCopy.list S A (bitCopy S A) source.bits).1 =
      (GeneralPaperEqualBooleanCopy.word S A source).1.bits := rfl

theorem source_work {w : ℕ} (S A : ℕ) (source : FixedBinaryWord w) :
    (GeneralPaperEqualBooleanCopy.word S A source).2 =
      (GeneralPaperReferenceCopy.list S A (bitCopy S A) source.bits).2 + 32 * (S + A + 1) := rfl

end Blotto.GeneralPaperEqualBooleanWordCopyLifetime
