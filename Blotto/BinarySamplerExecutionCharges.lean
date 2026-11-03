import Blotto.BinaryExecutionCharges

/-! The complete sampler keeps the preceding five execution fields intact and
adds actual seed-store emission as a separate charge. Source work stays in the
preceding measured record. These counters do not price full native machines. -/
namespace Blotto.BinarySamplerExecutionCharges
set_option autoImplicit false

structure Charges where
  execution : BinaryExecutionCharges.Charges
  seedEmission : ℕ

def zero : Charges := ⟨⟨0,0,0,0,0⟩,0⟩

def total (charges : Charges) : ℕ := BinaryExecutionCharges.total charges.execution+charges.seedEmission

def ofExecution (execution : BinaryExecutionCharges.Charges) (seedEmission : ℕ) : Charges :=
  ⟨execution,seedEmission⟩

def addWrapper (charges : Charges) (emission : ℕ) : Charges :=
  ⟨BinaryExecutionCharges.addWrapper charges.execution emission,charges.seedEmission⟩

def add (first second : Charges) : Charges :=
  ⟨⟨first.execution.primitive+second.execution.primitive,
    first.execution.coinSource+second.execution.coinSource,
    first.execution.write+second.execution.write,
    first.execution.native+second.execution.native,
    first.execution.wrappers+second.execution.wrappers⟩,first.seedEmission+second.seedEmission⟩

theorem total_zero : total zero = 0 := rfl

theorem total_ofExecution (execution : BinaryExecutionCharges.Charges) (seedEmission : ℕ) :
    total (ofExecution execution seedEmission) = BinaryExecutionCharges.total execution+seedEmission := rfl

theorem total_addWrapper (charges : Charges) (emission : ℕ) : total (addWrapper charges emission) = total charges+emission := by
  simp only [total,addWrapper,BinaryExecutionCharges.total_addWrapper]
  omega

theorem total_add (first second : Charges) : total (add first second) = total first+total second := by
  simp only [total,add,BinaryExecutionCharges.total]
  omega

theorem fields_le_total (charges : Charges) :
    charges.execution.primitive ≤ total charges ∧ charges.execution.coinSource ≤ total charges ∧
      charges.execution.write ≤ total charges ∧ charges.execution.native ≤ total charges ∧
      charges.execution.wrappers ≤ total charges ∧ charges.seedEmission ≤ total charges := by
  have h := BinaryExecutionCharges.fields_le_total charges.execution
  unfold total
  omega

end Blotto.BinarySamplerExecutionCharges
