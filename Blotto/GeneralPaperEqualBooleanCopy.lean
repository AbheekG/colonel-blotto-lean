import Blotto.GeneralPaperSequentialLayout

/-! Materialize every Boolean-list field at the destination width, with
source-width reads charged separately. This copies stored words; it does not
recompute categorical denominators, counts or rejection precision. -/
namespace Blotto.GeneralPaperEqualBooleanCopy
open GeneralPaperEncodedScalarStorage GeneralPaperEqualRetainedStorage
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def word {w : ℕ} (S A : ℕ) (source : FixedBinaryWord w) : FixedBinaryWord w × ℕ :=
  let copied := GeneralPaperReferenceCopy.list S A (GeneralPaperReferenceCopy.scalar S A (fun _ : Bool => 1)) source.bits
  let actual : FixedBinaryWord w := ⟨copied.1,by
    rw [GeneralPaperReferenceCopy.list_data S A _ (fun _ => rfl) source.bits]
    exact source.size⟩
  (actual,copied.2 + 32 * (S + A + 1))

theorem word_data {w : ℕ} (S A : ℕ) (source : FixedBinaryWord w) : (word S A source).1 = source := by
  apply GeneralPaperEqualBitCanonical.word_unique
  change BinaryBigEndian.littleValue (GeneralPaperReferenceCopy.list S A
    (GeneralPaperReferenceCopy.scalar S A (fun _ : Bool => 1)) source.bits).1 = BinaryBigEndian.littleValue source.bits
  rw [GeneralPaperReferenceCopy.list_data S A _ (fun _ => rfl)]

def wordPrice (S A w : ℕ) : ℕ :=
  w * (1 + 32 * (S + A + 1)) + (w + 1) * (64 * (S + A + 1)) + 32 * (S + A + 1)

theorem word_work {w : ℕ} (S A : ℕ) (source : FixedBinaryWord w) : (word S A source).2 ≤ wordPrice S A w := by
  have h := GeneralPaperReferenceCopy.list_bound S A (1 + 32 * (S + A + 1))
    (GeneralPaperReferenceCopy.scalar S A (fun _ : Bool => 1)) source.bits (fun _ _ => le_rfl)
  rw [source.size] at h
  dsimp only [word,wordPrice]
  omega

theorem word_charged {w : ℕ} (S A : ℕ) (source : FixedBinaryWord w) :
    wordFoot A (word S A source).1 ≤ 16 * (word S A source).2 := by
  have h := GeneralPaperReferenceCopy.list_charged S A 16
    (GeneralPaperReferenceCopy.scalar S A (fun _ : Bool => 1)) (fun _ : Bool => 1) source.bits (by decide)
    (by intro x _; dsimp only [GeneralPaperReferenceCopy.scalar]; omega)
  dsimp only [word,wordFoot]
  nlinarith

def row {r w : ℕ} (S A : ℕ) (source : Fin r × FixedBinaryWord w) : (Fin r × FixedBinaryWord w) × ℕ :=
  let copied := word S A source.2
  ((source.1,copied.1),natBits source.1.val + copied.2 + 64 * (S + A + 1))

theorem row_data {r w : ℕ} (S A : ℕ) (source : Fin r × FixedBinaryWord w) : (row S A source).1 = source := by
  dsimp only [row]
  rw [word_data]

theorem row_work {r w : ℕ} (S A : ℕ) (source : Fin r × FixedBinaryWord w) :
    (row S A source).2 ≤ natBits r + wordPrice S A w + 64 * (S + A + 1) := by
  have h := word_work S A source.2
  have hi : natBits source.1.val ≤ natBits r := Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
  dsimp only [row]
  omega

theorem row_charged {r w : ℕ} (S A : ℕ) (source : Fin r × FixedBinaryWord w) :
    natBits (row S A source).1.1.val + wordFoot A (row S A source).1.2 + 16 * A ≤ 64 * (row S A source).2 := by
  have h := word_charged S A source.2
  dsimp only [row]
  nlinarith

def run {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {p : GeneralPaperEqualPreparedCache.Prepared G l} (S A : ℕ) (source : GeneralPaperEqualBooleanCache.Cache p) :=
  let denominator := word S A source.denominator
  let rows := GeneralPaperReferenceCopy.list S A (row S A) source.rows
  let ruler := GeneralPaperReferenceCopy.list S A (GeneralPaperReferenceCopy.scalar S A (fun _ : Unit => 0)) source.ruler
  let actual : GeneralPaperEqualBooleanCache.Cache p :=
    ⟨denominator.1,(by rw [word_data]; exact source.denominator_value),
      rows.1,(by rw [GeneralPaperReferenceCopy.list_data S A _ (row_data S A)]; exact source.rows_correct),
      ruler.1,(by rw [GeneralPaperReferenceCopy.list_data S A _ (fun _ => rfl)]; exact source.ruler_length)⟩
  (actual,denominator.2 + rows.2 + ruler.2 + 128 * (S + A + 1))

theorem data {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {p : GeneralPaperEqualPreparedCache.Prepared G l} (S A : ℕ) (source : GeneralPaperEqualBooleanCache.Cache p) :
    (run S A source).1 = source := GeneralPaperEqualBitCanonical.boolean_unique _ _

def price (S A r w : ℕ) : ℕ :=
  wordPrice S A (w + 1) +
    (r * (natBits r + wordPrice S A (w + 1) + 64 * (S + A + 1)) + (r + 1) * (64 * (S + A + 1))) +
    (w * (32 * (S + A + 1)) + (w + 1) * (64 * (S + A + 1))) + 128 * (S + A + 1)

theorem work {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {p : GeneralPaperEqualPreparedCache.Prepared G l} (S A : ℕ) (source : GeneralPaperEqualBooleanCache.Cache p) :
    (run S A source).2 ≤ price S A (GeneralPaperPositiveSegmentCompaction.count l) p.rangeBits := by
  have hd := word_work S A source.denominator
  have hr := GeneralPaperReferenceCopy.list_bound S A
    (natBits (GeneralPaperPositiveSegmentCompaction.count l) + wordPrice S A (p.rangeBits + 1) + 64 * (S + A + 1))
    (row S A) source.rows (fun x _ => row_work S A x)
  rw [GeneralPaperEqualBooleanCache.rows_length] at hr
  have hu := GeneralPaperReferenceCopy.list_bound S A (32 * (S + A + 1))
    (GeneralPaperReferenceCopy.scalar S A (fun _ : Unit => 0)) source.ruler
    (by intro x _; dsimp only [GeneralPaperReferenceCopy.scalar]; omega)
  rw [source.ruler_length] at hu
  dsimp only [run,price]
  omega

theorem charged {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {p : GeneralPaperEqualPreparedCache.Prepared G l} (S A : ℕ) (source : GeneralPaperEqualBooleanCache.Cache p) :
    cacheFoot A (run S A source).1 ≤ 64 * (run S A source).2 := by
  have hd := word_charged S A source.denominator
  have hr := GeneralPaperReferenceCopy.list_charged S A 64 (row S A)
    (fun x => natBits x.1.val + wordFoot A x.2 + 16 * A) source.rows (by decide) (fun x _ => row_charged S A x)
  have hu := GeneralPaperReferenceCopy.list_charged S A 16
    (GeneralPaperReferenceCopy.scalar S A (fun _ : Unit => 0)) (fun _ : Unit => 0) source.ruler (by decide)
    (by intro x _; exact Nat.zero_le _)
  dsimp only [run,cacheFoot]
  nlinarith

end Blotto.GeneralPaperEqualBooleanCopy
