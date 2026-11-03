import Blotto.GeneralPaperEqualBooleanRowCopyLifetime

/-! Complete Boolean-cache copy reserve. The denominator, row list, active
row's entire word-copy window, ruler and parent controls coexist. Source
and destination list payloads use their respective reference widths. -/
namespace Blotto.GeneralPaperEqualBooleanCopyLifetime
open GeneralPaperEncodedScalarStorage GeneralPaperEqualRetainedStorage
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def rowPayload (A r w : ℕ) : ℕ := natBits r + wordProfile A w + 16 * A

theorem row_payload {r w : ℕ} (A : ℕ) (x : Fin r × FixedBinaryWord w) :
    natBits x.1.val + wordFoot A x.2 + 16 * A ≤ rowPayload A r w := by
  have hi : natBits x.1.val ≤ natBits r := Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
  have hw := word_bound A x.2
  unfold rowPayload
  omega

def parentCap (S A r w : ℕ) : ℕ := GeneralPaperEqualBooleanCopy.price S A r w + w + S + A

def window {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : GeneralPaperEqualPreparedCache.Prepared G l} (S A : ℕ) (source : GeneralPaperEqualBooleanCache.Cache p)
    (current : Option {x : Fin (count l) × FixedBinaryWord (p.rangeBits + 1) // x ∈ source.rows}) : ℕ :=
  GeneralPaperEqualBooleanWordCopyLifetime.window S A source.denominator +
    GeneralPaperReferenceListCopyLifetime.window S A
      (fun x => natBits x.1.val + wordFoot S x.2 + 16 * S)
      (fun x => natBits x.1.val + wordFoot A x.2 + 16 * A)
      (GeneralPaperEqualBooleanCopy.row S A) (GeneralPaperEqualBooleanRowCopyLifetime.window S A)
      source.rows (current.map Subtype.val) +
    GeneralPaperReferenceListCopyLifetime.window S A (fun _ : Unit => 0) (fun _ : Unit => 0)
      (GeneralPaperReferenceCopy.scalar S A (fun _ : Unit => 0)) (fun _ => 0) source.ruler none +
    GeneralPaperScalarTableCopyLifetime.scalarWindow S A (fun _ : Unit => 0) () + 64 * (S + A) +
    fields S [(GeneralPaperEqualBooleanCopy.word S A source.denominator).2,
      (GeneralPaperReferenceCopy.list S A (GeneralPaperEqualBooleanCopy.row S A) source.rows).2,
      (GeneralPaperReferenceCopy.list S A (GeneralPaperReferenceCopy.scalar S A (fun _ : Unit => 0)) source.ruler).2,
      p.rangeBits,(GeneralPaperEqualBooleanCopy.run S A source).2,S,A] + 256 * (S + A + 1)

def profile (S A r w : ℕ) : ℕ :=
  GeneralPaperEqualBooleanWordCopyLifetime.profile S A (w + 1) +
    GeneralPaperReferenceListCopyLifetime.profile S A
      (r * (rowPayload S r (w + 1) + 2 * S) + 32 * S) r (rowPayload A r (w + 1))
      (GeneralPaperEqualBooleanRowCopyLifetime.price S A r (w + 1))
      (GeneralPaperEqualBooleanRowCopyLifetime.profile S A r (w + 1)) +
    GeneralPaperReferenceListCopyLifetime.profile S A (w * (2 * S) + 32 * S) w 0 (32 * (S + A + 1)) 0 +
    GeneralPaperScalarTableCopyLifetime.scalarProfile S A 0 + 64 * (S + A) +
    7 * (natBits (parentCap S A r w) + S) + 32 * S + 256 * (S + A + 1)

theorem bounded {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : GeneralPaperEqualPreparedCache.Prepared G l} (S A : ℕ) (source : GeneralPaperEqualBooleanCache.Cache p)
    (current : Option {x : Fin (count l) × FixedBinaryWord (p.rangeBits + 1) // x ∈ source.rows}) :
    window S A source current ≤ profile S A (count l) p.rangeBits := by
  have hWord := GeneralPaperEqualBooleanWordCopyLifetime.bounded S A source.denominator
  have hRowsOwner := list_bound S (rowPayload S (count l) (p.rangeBits + 1))
    (fun x => natBits x.1.val + wordFoot S x.2 + 16 * S) source.rows (fun x _ => row_payload S x)
  rw [GeneralPaperEqualBooleanCache.rows_length] at hRowsOwner
  have hCurrent : ∀ x,current.map Subtype.val = some x → x ∈ source.rows := by
    intro x hx
    cases current with
    | none => cases hx
    | some y =>
      simp only [Option.map_some,Option.some.injEq] at hx
      rw [← hx]
      exact y.property
  have hRows := GeneralPaperReferenceListCopyLifetime.all_active S A _ (count l)
    (rowPayload A (count l) (p.rangeBits + 1))
    (GeneralPaperEqualBooleanRowCopyLifetime.price S A (count l) (p.rangeBits + 1))
    (GeneralPaperEqualBooleanRowCopyLifetime.profile S A (count l) (p.rangeBits + 1))
    (fun x => natBits x.1.val + wordFoot S x.2 + 16 * S)
    (fun x => natBits x.1.val + wordFoot A x.2 + 16 * A)
    (GeneralPaperEqualBooleanCopy.row S A) (GeneralPaperEqualBooleanRowCopyLifetime.window S A)
    source.rows (current.map Subtype.val) hRowsOwner (by rw [GeneralPaperEqualBooleanCache.rows_length])
    (by intro x _; rw [GeneralPaperEqualBooleanCopy.row_data]; exact row_payload A x)
    (fun x _ => GeneralPaperEqualBooleanCopy.row_work S A x)
    (fun x _ => GeneralPaperEqualBooleanRowCopyLifetime.bounded S A x) hCurrent
  have hRulerOwner := list_bound S 0 (fun _ : Unit => 0) source.ruler (fun _ _ => le_rfl)
  rw [source.ruler_length] at hRulerOwner
  have hRuler := GeneralPaperReferenceListCopyLifetime.all_active S A _ p.rangeBits 0 (32 * (S + A + 1)) 0
    (fun _ : Unit => 0) (fun _ : Unit => 0) (GeneralPaperReferenceCopy.scalar S A (fun _ : Unit => 0))
    (fun _ => 0) source.ruler none hRulerOwner (by rw [source.ruler_length])
    (fun _ _ => le_rfl) (by intro x _; dsimp only [GeneralPaperReferenceCopy.scalar]; omega)
    (fun _ _ => le_rfl) (by intro x hx; cases hx)
  simp only [zero_add] at hRuler
  have hScalar := GeneralPaperScalarTableCopyLifetime.scalar_bound S A 0 (fun _ : Unit => 0) () le_rfl
  have hWork := GeneralPaperEqualBooleanCopy.work S A source
  have hReturn : (GeneralPaperEqualBooleanCopy.run S A source).2 =
      (GeneralPaperEqualBooleanCopy.word S A source.denominator).2 +
      (GeneralPaperReferenceCopy.list S A (GeneralPaperEqualBooleanCopy.row S A) source.rows).2 +
      (GeneralPaperReferenceCopy.list S A (GeneralPaperReferenceCopy.scalar S A (fun _ : Unit => 0)) source.ruler).2 +
      128 * (S + A + 1) := rfl
  have hf := fields_bound S (natBits (parentCap S A (count l) p.rangeBits))
    [(GeneralPaperEqualBooleanCopy.word S A source.denominator).2,
      (GeneralPaperReferenceCopy.list S A (GeneralPaperEqualBooleanCopy.row S A) source.rows).2,
      (GeneralPaperReferenceCopy.list S A (GeneralPaperReferenceCopy.scalar S A (fun _ : Unit => 0)) source.ruler).2,
      p.rangeBits,(GeneralPaperEqualBooleanCopy.run S A source).2,S,A] (by
        intro a ha
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals unfold parentCap; omega)
  change fields S _ ≤ 7 * (natBits (parentCap S A (count l) p.rangeBits) + S) + 32 * S at hf
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperEqualBooleanCopyLifetime
