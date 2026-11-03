import Blotto.BinarySignedAllocation

/-! Padding copies each supplied cell and fills only the missing false suffix.
The structural producers return exact old allocation records and reached
copy/fill work. No append, replicate or source-length observer produces data.
Nat metadata and physical ownership/allocator/GC remain separate obligations. -/
namespace Blotto.BinarySignedPaddingMeasured
set_option autoImplicit false

abbrev Record := (List Bool × ℕ) × ℕ

def zeros : ℕ → Record
  | 0 => (([],2),2)
  | count+1 =>
      let later := zeros count
      ((false::later.1.1,later.1.2+1),later.2+2)

theorem zeros_record (count : ℕ) :
    zeros count = ((List.replicate count false,count+2),2*(count+1)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [zeros,ih,List.replicate_succ]
      congr 2

def pad : ℕ → List Bool → Record
  | count,[] => zeros count
  | count,bit::rest =>
      let later := pad (count-1) rest
      ((bit::later.1.1,later.1.2+1),later.2+2)

theorem pad_record (count : ℕ) (bits : List Bool) :
    pad count bits =
      ((BinarySignedMagnitude.pad count bits,bits.length+(count-bits.length)+2),
        2*(bits.length+(count-bits.length)+1)) := by
  induction bits generalizing count with
  | nil => simp only [pad,zeros_record,BinarySignedMagnitude.pad,List.length_nil,
      List.nil_append,Nat.sub_zero,Nat.zero_add]
  | cons bit rest ih =>
      have hSub : count-1-rest.length = count-(rest.length+1) := by omega
      simp only [pad,ih,BinarySignedMagnitude.pad,List.length_cons,List.cons_append,hSub]
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · dsimp only; omega
      · dsimp only; omega

theorem pad_compat (count : ℕ) (bits : List Bool) :
    (pad count bits).1 = BinarySignedAllocation.padWithAllocation count bits := by
  rw [pad_record]
  rfl

theorem pad_work (count : ℕ) (bits : List Bool) :
    (pad count bits).2 = 2*(max bits.length count+1) := by
  rw [pad_record]
  dsimp only
  omega

theorem pad_width (count : ℕ) (bits : List Bool) (h : bits.length ≤ count) :
    (pad count bits).2 = 2*(count+1) := by
  rw [pad_work,Nat.max_eq_right h]

end Blotto.BinarySignedPaddingMeasured
