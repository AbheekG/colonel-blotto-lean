import Blotto.BinarySamplerExecutionCharges

/-! Fresh generation adds a distinct actual trace-emission price. The complete
preceding sampler ledger is retained, including seed-store emission. -/
namespace Blotto.BinaryGenerationExecutionCharges
set_option autoImplicit false

structure Charges where
  sampler : BinarySamplerExecutionCharges.Charges
  generationEmission : ℕ

def zero : Charges := ⟨BinarySamplerExecutionCharges.zero,0⟩

def total (charges : Charges) : ℕ := BinarySamplerExecutionCharges.total charges.sampler+charges.generationEmission

def ofSampler (sampler : BinarySamplerExecutionCharges.Charges) (generationEmission : ℕ) : Charges :=
  ⟨sampler,generationEmission⟩

def addWrapper (charges : Charges) (emission : ℕ) : Charges :=
  ⟨BinarySamplerExecutionCharges.addWrapper charges.sampler emission,charges.generationEmission⟩

def add (first second : Charges) : Charges :=
  ⟨BinarySamplerExecutionCharges.add first.sampler second.sampler,first.generationEmission+second.generationEmission⟩

theorem total_zero : total zero = 0 := rfl

theorem total_ofSampler (sampler : BinarySamplerExecutionCharges.Charges) (generationEmission : ℕ) :
    total (ofSampler sampler generationEmission) = BinarySamplerExecutionCharges.total sampler+generationEmission := rfl

theorem total_addWrapper (charges : Charges) (emission : ℕ) :
    total (addWrapper charges emission) = total charges+emission := by
  simp only [total,addWrapper,BinarySamplerExecutionCharges.total_addWrapper]
  omega

theorem total_add (first second : Charges) : total (add first second) = total first+total second := by
  simp only [total,add,BinarySamplerExecutionCharges.total_add]
  omega

theorem fields_le_total (charges : Charges) :
    charges.sampler.execution.primitive ≤ total charges ∧ charges.sampler.execution.coinSource ≤ total charges ∧
      charges.sampler.execution.write ≤ total charges ∧ charges.sampler.execution.native ≤ total charges ∧
      charges.sampler.execution.wrappers ≤ total charges ∧ charges.sampler.seedEmission ≤ total charges ∧
      charges.generationEmission ≤ total charges := by
  have h := BinarySamplerExecutionCharges.fields_le_total charges.sampler
  unfold total
  omega

end Blotto.BinaryGenerationExecutionCharges
