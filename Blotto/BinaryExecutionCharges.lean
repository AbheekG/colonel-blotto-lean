import Blotto.BinaryWordWidthCore

/-! Separate returned charges retain the preceding scopes of primitive,
coin/source emission, persistent-write emission and native materialization/
wrapper emission. Outer wrappers add only their own actual emitter charge.
These named source units do not price complete native scalar/record/GC work. -/
namespace Blotto.BinaryExecutionCharges
set_option autoImplicit false

structure Charges where
  primitive : ℕ
  coinSource : ℕ
  write : ℕ
  native : ℕ
  wrappers : ℕ

def total (charges : Charges) : ℕ :=
  charges.primitive+charges.coinSource+charges.write+charges.native+charges.wrappers

def addWrapper (charges : Charges) (emission : ℕ) : Charges :=
  {charges with wrappers := charges.wrappers+emission}

theorem total_addWrapper (charges : Charges) (emission : ℕ) :
    total (addWrapper charges emission) = total charges+emission := by
  simp only [total,addWrapper]
  omega

theorem fields_le_total (charges : Charges) :
    charges.primitive ≤ total charges ∧ charges.coinSource ≤ total charges ∧
      charges.write ≤ total charges ∧ charges.native ≤ total charges ∧ charges.wrappers ≤ total charges := by
  simp only [total]
  omega

end Blotto.BinaryExecutionCharges
