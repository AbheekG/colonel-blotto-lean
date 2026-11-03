import Blotto.GeneralPaperNativeFairIndex

/-! One stored fair vector supplies row and shift indices from disjoint
forward blocks. Runtime lengths and dyadic target counts are retained
controls; their power identities are erased proofs, never decoder calls. -/
namespace Blotto.GeneralPaperNativeDyadicBlocks
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Result (T S : ℕ) where
  row : Fin T
  shift : Fin S
  reads : ℕ
  work : ℕ

def run (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (buffer : FixedArrayTable (R+L) Bool) : Result T S :=
  let row := GeneralPaperNativeFairIndex.loop primitive A buffer 0 R (by omega) R le_rfl
  let shift := GeneralPaperNativeFairIndex.loop primitive A buffer R L le_rfl L le_rfl
  ⟨⟨row.value,by rw [hT];exact GeneralPaperNativeFairIndex.bounded primitive A buffer 0 R (by omega) R le_rfl⟩,
    ⟨shift.value,by rw [hS];exact GeneralPaperNativeFairIndex.bounded primitive A buffer R L le_rfl L le_rfl⟩,
    row.reads+shift.reads,row.work+shift.work+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) row.reads shift.reads+64*A⟩

theorem reads (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (buffer : FixedArrayTable (R+L) Bool) : (run primitive A R L T S hT hS buffer).reads=R+L := by
  simp only [run,GeneralPaperNativeFairIndex.reads]

theorem block_data {N : ℕ} (primitive : ℕ → ℕ) (A offset length : ℕ) (hCap : offset+length≤N)
    (bits : Fin N → Bool) :
    (GeneralPaperNativeFairIndex.loop primitive A (FixedArrayTable.ofFn bits) offset length hCap length le_rfl).value=
      (bitIndex length (fun j => bits ⟨offset+j.val,by omega⟩)).val := by
  rw [GeneralPaperNativeFairIndex.data]
  apply payload_value_eq_bitIndex
  intro j
  have h : offset+j.val<N := by have hj:=j.isLt;omega
  simp [FixedArrayTable.ofFn,Array.getD,h]

theorem row_data (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (bits : Fin (R+L) → Bool) :
    (run primitive A R L T S hT hS (FixedArrayTable.ofFn bits)).row=
      Fin.cast hT.symm (bitIndex R (firstBitBlock R L bits)) := by
  apply Fin.ext
  change (GeneralPaperNativeFairIndex.loop primitive A (FixedArrayTable.ofFn bits) 0 R (by omega) R le_rfl).value=_
  rw [block_data]
  change (bitIndex R (fun j => bits ⟨0+j.val,by omega⟩)).val=(bitIndex R (firstBitBlock R L bits)).val
  apply congrArg (fun f : Fin R → Bool => (bitIndex R f).val)
  funext j
  apply congrArg bits
  apply Fin.ext
  exact Nat.zero_add j.val

theorem shift_data (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (bits : Fin (R+L) → Bool) :
    (run primitive A R L T S hT hS (FixedArrayTable.ofFn bits)).shift=
      Fin.cast hS.symm (bitIndex L (secondBitBlock R L bits)) := by
  apply Fin.ext
  change (GeneralPaperNativeFairIndex.loop primitive A (FixedArrayTable.ofFn bits) R L le_rfl L le_rfl).value=_
  rw [block_data]
  rfl

theorem arithmetic_work (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (buffer : FixedArrayTable (R+L) Bool) :
    (run (fun _ => 1) A R L T S hT hS buffer).work≤(R+L)*(10+64*A)+128*A+2 := by
  have hr := GeneralPaperNativeFairIndex.arithmetic_work A buffer 0 R (by omega) R le_rfl
  have hs := GeneralPaperNativeFairIndex.arithmetic_work A buffer R L le_rfl L le_rfl
  simp only [run,GeneralPaperNaturalPrimitivePrice.binary]
  nlinarith only [hr,hs]

end Blotto.GeneralPaperNativeDyadicBlocks
