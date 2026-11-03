import Blotto.GeneralPaperHeaderTargetCopyLifetime

/-! Literal header padding and left-only concatenation activations. A
padding counter/price is encoded in every saved activation. Concatenation
retains only each left head and its prices; its returned right tail is the
unchanged shared suffix. Actual local lengths remain in the bounds. -/
namespace Blotto.GeneralPaperHeaderWordLoopsLifetime
open GeneralPaperEncodedScalarStorage
open GeneralPaperHeaderTargetCopy (padding append)
open GeneralPaperHeaderTargetCopyLifetime (cap)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def paddingControls (S A n : ℕ) (zero : FixedBinaryWord A) : List ℕ :=
  [S,A,n,n + 1,(padding S A zero n).2,(padding S A zero (n + 1)).2]

def paddingFrames (S A : ℕ) (zero : FixedBinaryWord A) : ℕ → ℕ
  | 0 => fields S [S,A,0,(padding S A zero 0).2] + 64 * S
  | n + 1 => A + fields S (paddingControls S A n zero) + 128 * S + paddingFrames S A zero n

def paddingFrameBound (S A B Q : ℕ) : ℕ := A + 6 * (natBits (cap S A B Q) + S) + 160 * S + 64

theorem padding_frames_bound (S A B Q n : ℕ) (zero : FixedBinaryWord A)
    (hLength : n ≤ B) (hWork : (padding S A zero n).2 ≤ Q) :
    paddingFrames S A zero n ≤ (n + 1) * paddingFrameBound S A B Q := by
  induction n with
  | zero =>
    have hFields := fields_bound S (natBits (cap S A B Q)) [S,A,0,(padding S A zero 0).2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 4 * (natBits (cap S A B Q) + S) + 32 * S at hFields
    simp only [paddingFrames,Nat.zero_add,Nat.one_mul]
    unfold paddingFrameBound
    omega
  | succ n ih =>
    have hWhole := hWork
    have hChildWork : (padding S A zero n).2 ≤ Q := by
      change (padding S A zero n).2 + A + 64 * (S + A + 1) ≤ Q at hWork
      omega
    have hChild := ih (by omega) hChildWork
    have hFields := fields_bound S (natBits (cap S A B Q)) (paddingControls S A n zero) (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [paddingControls,List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 6 * (natBits (cap S A B Q) + S) + 32 * S at hFields
    simp only [paddingFrames]
    unfold paddingFrameBound at hChild ⊢
    nlinarith only [hChild,hFields]

def paddingWindow (S A n : ℕ) (zero : FixedBinaryWord A) : ℕ :=
  paddingFrames S A zero n + listFootprint S (fun _ : FixedBinaryWord A => A) (padding S A zero n).1 +
    fields S [n,(padding S A zero n).2] + 64 * S

def paddingUnit (S A B Q : ℕ) : ℕ :=
  paddingFrameBound S A B Q + A + 2 * S + 2 * (natBits (cap S A B Q) + S) + 128 * S

theorem padding_window_bound (S A B Q n : ℕ) (zero : FixedBinaryWord A)
    (hLength : n ≤ B) (hWork : (padding S A zero n).2 ≤ Q) :
    paddingWindow S A n zero ≤ (n + 1) * paddingUnit S A B Q := by
  have hFrames := padding_frames_bound S A B Q n zero hLength hWork
  have hList := list_bound S A (fun _ : FixedBinaryWord A => A) (padding S A zero n).1 (fun _ _ => le_rfl)
  rw [GeneralPaperHeaderTargetCopy.padding_data,List.length_replicate] at hList
  have hFields := fields_bound S (natBits (cap S A B Q)) [n,(padding S A zero n).2] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl <;> omega)
  change fields S _ ≤ 2 * (natBits (cap S A B Q) + S) + 32 * S at hFields
  have hReserve := Nat.mul_le_mul_left n (show 0 ≤ 2 * (natBits (cap S A B Q) + S) + 128 * S by omega)
  unfold paddingWindow paddingUnit
  rw [GeneralPaperHeaderTargetCopy.padding_data]
  nlinarith only [hFrames,hList,hFields,hReserve]

def appendFrames (S A : ℕ) (first rest : List (FixedBinaryWord A)) : ℕ :=
  GeneralPaperUnifiedInstallationLifetime.liftFrames S A (fun _ : FixedBinaryWord A => A)
    (fun xs => (append S A xs rest).2) first

def appendUnit (S A Q : ℕ) : ℕ := A + GeneralPaperUnifiedInstallationLifetime.liftFrameBound S A Q

theorem append_frames_bound (S A Q : ℕ) (first rest : List (FixedBinaryWord A))
    (hWork : (append S A first rest).2 ≤ Q) :
    appendFrames S A first rest ≤ (first.length + 1) * appendUnit S A Q := by
  have h := GeneralPaperUnifiedInstallationLifetime.lift_frames_bound S A Q (fun _ : FixedBinaryWord A => A)
    (fun xs => (append S A xs rest).2) first (fun entry entries => by dsimp only [append]; omega) hWork
  simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id] at h
  unfold appendFrames appendUnit
  nlinarith only [h,Nat.zero_le A]

theorem append_shared_suffix (S A : ℕ) (first rest : List (FixedBinaryWord A)) :
    (append S A first rest).1.drop first.length = rest := by
  rw [GeneralPaperHeaderTargetCopy.append_data]
  exact List.drop_left

@[fun_prop]
theorem padding_unit_rate {α : Type*} (S A B Q L : α → ℕ) (hL : ∀ x,1 ≤ L x)
    (hS : Tight S L) (hA : Tight A L) (hB : Small B L) (hQ : Small Q L) :
    Polylog (fun x => paddingUnit (S x) (A x) (B x) (Q x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hSSmall := small_of_tight hS hL
  have hASmall := small_of_tight hA hL
  have hCap : Small (fun x => cap (S x) (A x) (B x) (Q x)) L := by unfold cap; fun_prop
  unfold paddingUnit paddingFrameBound
  fun_prop

@[fun_prop]
theorem append_unit_rate {α : Type*} (S A Q L : α → ℕ) (hL : ∀ x,1 ≤ L x)
    (hS : Tight S L) (hA : Tight A L) (hQ : Small Q L) :
    Polylog (fun x => appendUnit (S x) (A x) (Q x)) L := by
  have hAP := polylog_of_tight hA
  have hFrames := GeneralPaperUnifiedInstallationLifetime.lift_frame_rate S A Q L hL hS hA hQ
  unfold appendUnit
  fun_prop

end Blotto.GeneralPaperHeaderWordLoopsLifetime
