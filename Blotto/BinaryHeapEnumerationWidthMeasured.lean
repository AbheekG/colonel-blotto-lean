import Blotto.BinaryHeapEnumerationMeasured

/-! Recover the enumeration width from the retained bits. A source type index
can otherwise cause a logical tree/store to be rebuilt merely to pass its
natural width to the measured trace wrapper. The equality transport is erased;
the complete value/trace/work record is unchanged. -/
namespace Blotto.BinaryHeapEnumerationWidthMeasured
open BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
set_option autoImplicit false

def allBits (bits : List Bool) :=
  BinaryHeapEnumerationMeasured.all (⟨bits,rfl⟩ : FixedBinaryWord bits.length)

def allFromBits {w : ℕ} (cap : FixedBinaryWord w) :
    (List (Address w cap) × Trace) × ℕ := by
  rcases cap with ⟨bits,size⟩
  subst w
  exact allBits bits

theorem allFromBits_eq {w : ℕ} (cap : FixedBinaryWord w) :
    allFromBits cap = BinaryHeapEnumerationMeasured.all cap := by
  cases cap with
  | mk bits size => subst w; rfl

theorem allFromBits_erases {w : ℕ} (cap : FixedBinaryWord w) :
    (allFromBits cap).1 = BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace cap := by
  rw [allFromBits_eq,BinaryHeapEnumerationMeasured.all_erases]

theorem allFromBits_work {w : ℕ} (cap : FixedBinaryWord w) :
    (allFromBits cap).2 = (BinaryPRGHeapAddressEnumeration.allWithWork cap).2 := by
  rw [allFromBits_eq,BinaryHeapEnumerationMeasured.all_work]

end Blotto.BinaryHeapEnumerationWidthMeasured
