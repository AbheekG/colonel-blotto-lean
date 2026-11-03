import Blotto.GeneralPaperDualWidthFillStorage

/-! The source owner, destination buffers, recursive fill frames, active
payload-copy scratch and outer array-copy controls coexist. Source and
destination payload encoders are separate, including for nested rows. -/
namespace Blotto.GeneralPaperReferenceArrayCopyLifetime
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open PaperIndexedArrayConstruction
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def callback {α : Type*} {n : ℕ} (S : ℕ) (copy : α → α × ℕ)
    (source : FixedArrayTable n α) (j : Fin n) : α × ℕ :=
  let loaded := copy (source.read j)
  (loaded.1,loaded.2 + 32 * S + 32)

theorem source_data {α : Type*} {n : ℕ} (S D : ℕ) (copy : α → α × ℕ)
    (source : FixedArrayTable n α) :
    (run id D (callback S copy source)).1 = (GeneralPaperReferenceCopy.array S D copy source).1 := rfl

theorem source_work {α : Type*} {n : ℕ} (S D : ℕ) (copy : α → α × ℕ)
    (source : FixedArrayTable n α) :
    (GeneralPaperReferenceCopy.array S D copy source).2 =
      (run id D (callback S copy source)).2 + 64 * (S + D + 1) := rfl

def parentCap (S D n C : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.metadataCap D n (C + 32 * S + 32) + 64 * (S + D + 1) + S + D

def window {α : Type*} {n : ℕ} (S D : ℕ) (sourceEncode targetEncode : α → ℕ)
    (copy : α → α × ℕ) (source : FixedArrayTable n α) (scratch : Fin n → ℕ)
    (k : ℕ) (hk : k ≤ n) : ℕ :=
  arrayFootprint S sourceEncode source +
    GeneralPaperDualWidthFillStorage.window S D targetEncode (callback S copy source) scratch k hk +
    fields S [n,S,D,(run id D (callback S copy source)).2,
      (GeneralPaperReferenceCopy.array S D copy source).2,64 * (S + D + 1)] + 192 * S

def profile (S D O B P n C Q : ℕ) : ℕ :=
  O + GeneralPaperDualWidthFillStorage.profile S D B P n (C + 32 * S + 32) Q +
    6 * (natBits (parentCap S D n C) + S) + 224 * S

theorem all_cursors {α : Type*} {n : ℕ} (S D O B P C Q : ℕ)
    (sourceEncode targetEncode : α → ℕ) (copy : α → α × ℕ) (source : FixedArrayTable n α)
    (scratch : Fin n → ℕ) (hO : arrayFootprint S sourceEncode source ≤ O)
    (hB : (∑ j : Fin n,targetEncode (copy (source.read j)).1) ≤ B)
    (hP : ∀ j,targetEncode (copy (source.read j)).1 ≤ P)
    (hC : ∀ j,(copy (source.read j)).2 ≤ C) (hQ : ∀ j,scratch j ≤ Q)
    (hD : 1 ≤ D) (hIndex : binaryWordWidth (n + 1) ≤ D) (k : ℕ) (hk : k ≤ n) :
    window S D sourceEncode targetEncode copy source scratch k hk ≤ profile S D O B P n C Q := by
  have hRaw : ∀ j,(callback S copy source j).2 ≤ C + 32 * S + 32 := by
    intro j
    have h := hC j
    dsimp only [callback]
    omega
  have hFill := GeneralPaperDualWidthFillStorage.bounded S D B P (C + 32 * S + 32) Q targetEncode
    (callback S copy source) scratch hB hP hRaw hQ hD hIndex k hk
  have hWork := GeneralPaperNativePayloadFillStorage.prefix_work D (C + 32 * S + 32)
    (callback S copy source) hRaw hD hIndex n le_rfl
  change (run id D (callback S copy source)).2 ≤
    GeneralPaperNativePayloadFillStorage.workCap D n (C + 32 * S + 32) at hWork
  have hReturn := source_work S D copy source
  have hf := fields_bound S (natBits (parentCap S D n C))
    [n,S,D,(run id D (callback S copy source)).2,
      (GeneralPaperReferenceCopy.array S D copy source).2,64 * (S + D + 1)] (by
        intro x hx
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals unfold parentCap GeneralPaperNativePayloadFillStorage.metadataCap; omega)
  change fields S _ ≤ 6 * (natBits (parentCap S D n C) + S) + 32 * S at hf
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperReferenceArrayCopyLifetime
