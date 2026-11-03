import Blotto.GeneralPaperEqualCopiedContract

/-! A conservative live reserve for the literal non-tail-recursive list
copy. Source tails share one source owner. Pending frames retain each copied
head once, plus their actual work/control words; only one callback is active.
This bound is intended for the short Boolean/control lists, not budget rows. -/
namespace Blotto.GeneralPaperReferenceListCopyLifetime
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def workCap (S D L C : ℕ) : ℕ := L * C + (L + 1) * (64 * (S + D + 1))
def metadataCap (S D L C : ℕ) : ℕ := S + D + L + C + 64 * (S + D + 1) + workCap S D L C

theorem work_bound {α : Type*} (S D L C : ℕ) (copy : α → α × ℕ) (xs : List α)
    (hL : xs.length ≤ L) (hC : ∀ x ∈ xs,(copy x).2 ≤ C) :
    (GeneralPaperReferenceCopy.list S D copy xs).2 ≤ workCap S D L C := by
  have h := GeneralPaperReferenceCopy.list_bound S D C copy xs hC
  have h₁ := Nat.mul_le_mul_right C hL
  have h₂ := Nat.mul_le_mul_right (64 * (S + D + 1)) (Nat.add_le_add_right hL 1)
  unfold workCap
  omega

def frames {α : Type*} (S D : ℕ) (encode : α → ℕ) (copy : α → α × ℕ) : List α → ℕ
  | [] => fields S [64 * (S + D + 1)] + 128 * S
  | x :: xs =>
    let head := copy x
    let tail := GeneralPaperReferenceCopy.list S D copy xs
    let result := GeneralPaperReferenceCopy.list S D copy (x :: xs)
    encode head.1 + fields S [head.2,tail.2,result.2,64 * (S + D + 1),xs.length] + 192 * S +
      frames S D encode copy xs

def frameProfile (S D L P C : ℕ) : ℕ := P + 5 * (natBits (metadataCap S D L C) + S) + 224 * S

theorem frames_bound {α : Type*} (S D L P C : ℕ) (encode : α → ℕ) (copy : α → α × ℕ) (xs : List α)
    (hL : xs.length ≤ L) (hP : ∀ x ∈ xs,encode (copy x).1 ≤ P) (hC : ∀ x ∈ xs,(copy x).2 ≤ C) :
    frames S D encode copy xs ≤ (xs.length + 1) * frameProfile S D L P C := by
  induction xs with
  | nil =>
    have hf := fields_bound S (natBits (metadataCap S D L C)) [64 * (S + D + 1)] (by
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      subst a
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      unfold metadataCap
      omega)
    change fields S _ ≤ 1 * (natBits (metadataCap S D L C) + S) + 32 * S at hf
    simp only [one_mul] at hf
    dsimp only [frames,frameProfile,List.length_nil]
    omega
  | cons x xs ih =>
    have hLength : xs.length + 1 ≤ L := hL
    have hTail : xs.length ≤ L := by omega
    have hPc := hP x (List.mem_cons_self ..)
    have hCc := hC x (List.mem_cons_self ..)
    have hPt := fun y hy => hP y (List.mem_cons_of_mem x hy)
    have hCt := fun y hy => hC y (List.mem_cons_of_mem x hy)
    have hRec := ih hTail hPt hCt
    have hTailWork := work_bound S D L C copy xs hTail hCt
    have hWork := work_bound S D L C copy (x :: xs) hL hC
    have hf := fields_bound S (natBits (metadataCap S D L C))
      [(copy x).2,(GeneralPaperReferenceCopy.list S D copy xs).2,
        (GeneralPaperReferenceCopy.list S D copy (x :: xs)).2,64 * (S + D + 1),xs.length] (by
          intro a ha
          apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
          simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl
          all_goals unfold metadataCap; omega)
    change fields S _ ≤ 5 * (natBits (metadataCap S D L C) + S) + 32 * S at hf
    dsimp only [frames,List.length_cons]
    unfold frameProfile at hRec ⊢
    nlinarith only [hRec,hPc,hf]

theorem returned_bound {α : Type*} (S D P : ℕ) (encode : α → ℕ) (copy : α → α × ℕ) (xs : List α)
    (hP : ∀ x ∈ xs,encode (copy x).1 ≤ P) :
    listFootprint D encode (GeneralPaperReferenceCopy.list S D copy xs).1 ≤ xs.length * (P + 2 * D) + 32 * D := by
  induction xs with
  | nil => simp only [GeneralPaperReferenceCopy.list,listFootprint,List.map_nil,List.sum_nil,List.length_nil]; omega
  | cons x xs ih =>
    have hh := hP x (List.mem_cons_self ..)
    have ht := ih (fun y hy => hP y (List.mem_cons_of_mem x hy))
    simp only [GeneralPaperReferenceCopy.list,listFootprint,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith only [hh,ht]

def active {α : Type*} (scratch : α → ℕ) : Option α → ℕ
  | none => 0
  | some x => scratch x

def window {α : Type*} (S D : ℕ) (sourceEncode targetEncode : α → ℕ) (copy : α → α × ℕ)
    (scratch : α → ℕ) (xs : List α) (current : Option α) : ℕ :=
  listFootprint S sourceEncode xs + 2 * listFootprint D targetEncode (GeneralPaperReferenceCopy.list S D copy xs).1 +
    frames S D targetEncode copy xs + active scratch current

def profile (S D O L P C Q : ℕ) : ℕ :=
  O + 2 * (L * (P + 2 * D) + 32 * D) + (L + 1) * frameProfile S D L P C + Q

theorem all_active {α : Type*} (S D O L P C Q : ℕ) (sourceEncode targetEncode : α → ℕ)
    (copy : α → α × ℕ) (scratch : α → ℕ) (xs : List α) (current : Option α)
    (hO : listFootprint S sourceEncode xs ≤ O) (hL : xs.length ≤ L)
    (hP : ∀ x ∈ xs,targetEncode (copy x).1 ≤ P) (hC : ∀ x ∈ xs,(copy x).2 ≤ C)
    (hQ : ∀ x ∈ xs,scratch x ≤ Q) (hCurrent : ∀ x,current = some x → x ∈ xs) :
    window S D sourceEncode targetEncode copy scratch xs current ≤ profile S D O L P C Q := by
  have hFrames := (frames_bound S D L P C targetEncode copy xs hL hP hC).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hL 1))
  have hReturned := (returned_bound S D P targetEncode copy xs hP).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hL) _)
  have hActive : active scratch current ≤ Q := by
    cases current with
    | none => exact Nat.zero_le _
    | some x => exact hQ x (hCurrent x rfl)
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperReferenceListCopyLifetime
