import Blotto.GeneralPaperStoredStreamWork

/-! Count access is bounded from the actual expanded-header contract.
The pointer width is fixed by initialized memory, and successful positive
prefix headers give the same address-only price in any enclosing memory. -/
namespace Blotto.GeneralPaperStoredCountReadWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperReferenceRegionSlots (Header)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperUnifiedFieldValue
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def bound (model : RationalCostModel) (A : ℕ) : ℕ :=
  GeneralPaperStoredReferenceReadWork.readBound model A A + 65 * A + 64

theorem pointer (model : RationalCostModel) (A : ℕ) (installed : Installed A) (directory : Directory A)
    (hContract : Contract model A installed directory) (header : Header A) (hHeader : header ∈ directory.headers)
    (hf : header.fixed ≠ 0) :
    (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) header.region.reference 0 0).1 =
      some (⟨A,FixedBinaryWord.ofNat A header.targets.length⟩ : GeneralPaperMixedReferenceMemory.Word) := by
  have hIndex : 0 < (GeneralPaperHeaderCountExpansion.expanded header).targets.length := by
    rw [GeneralPaperHeaderCountExpansion.length header hf]
    omega
  have hLookup := GeneralPaperHeaderCountExpansion.count_lookup header hf
  rw [List.getElem?_eq_getElem hIndex] at hLookup
  have h := hContract.1.1 (GeneralPaperHeaderCountExpansion.expanded header)
    (GeneralPaperHeaderCountDirectory.header_member directory header hHeader) ⟨0,hIndex⟩
  rw [Option.some.inj hLookup] at h
  have hFixed : (GeneralPaperHeaderCountExpansion.expanded header).fixed = 0 := by
    simp only [GeneralPaperHeaderCountExpansion.expanded,hf,ite_false]
  rwa [GeneralPaperHeaderCountExpansion.region,hFixed] at h

theorem work (model : RationalCostModel) (A : ℕ) (installed : Installed A) (directory : Directory A)
    (hContract : Contract model A installed directory) (header : Header A) (hHeader : header ∈ directory.headers)
    (hf : header.fixed ≠ 0) :
    (GeneralPaperHeaderCountReadback.count model A installed header.region.reference).2 ≤ bound model A := by
  have h := GeneralPaperStoredReferenceReadWork.read_work model A A 0 0 _ header.region.reference _ (by decide) (Nat.two_pow_pos A)
    (pointer model A installed directory hContract header hHeader hf)
  rw [(hContract.2.2 header hHeader hf).2]
  exact Nat.add_le_add_right (Nat.add_le_add_right h (65 * A)) 64

end Blotto.GeneralPaperStoredCountReadWork
