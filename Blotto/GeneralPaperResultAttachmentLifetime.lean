import Blotto.GeneralPaperSelectedOuterInputLifetime

/-! Complete final work/result attachment. Both root/work records and
every saved partial price are retained; the memory and root are shared
exactly with the already constructed sampler. -/
namespace Blotto.GeneralPaperResultAttachmentLifetime
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEncodedScalarStorage
open GeneralPaperPayloadInstallationLifetime (cap)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
set_option autoImplicit false
set_option maxHeartbeats 800000

def controls (S A prefixWork : ℕ) (output : Installed A) : List ℕ :=
  [S,A,prefixWork,output.work,prefixWork + output.work,(GeneralPaperSamplerRecordInstallation.attach S A prefixWork output).work]

def window (S A prefixWork : ℕ) (output : Installed A) : ℕ :=
  2 * A + fields S (controls S A prefixWork output) + 128 * S

theorem window_bound (model : RationalCostModel) (S A prefixWork P : ℕ) (output : Installed A)
    (hWork : (GeneralPaperSamplerRecordInstallation.attach S A prefixWork output).work ≤ P) :
    window S A prefixWork output ≤ unit model S A P := by
  have hWhole := hWork
  change prefixWork + output.work + 64 * (S + A + 1) ≤ P at hWork
  have hFields := fields_bound S (natBits (cap S A P)) (controls S A prefixWork output) (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 6 * (natBits (cap S A P) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A P
  unfold window
  omega

theorem shared_memory_and_root (S A prefixWork : ℕ) (output : Installed A) :
    (GeneralPaperSamplerRecordInstallation.attach S A prefixWork output).memory = output.memory ∧
      (GeneralPaperSamplerRecordInstallation.attach S A prefixWork output).root = output.root := ⟨rfl,rfl⟩

end Blotto.GeneralPaperResultAttachmentLifetime
