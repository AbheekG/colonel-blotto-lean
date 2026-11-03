import Blotto.GeneralPaperHeaderCountDirectory

/-! Expanded-header readback implies every old data-slot/scalar readback.
Actual count reads use only installed memory and the loaded root. Native
owner capacity supplies the erased representability proof. -/
namespace Blotto.GeneralPaperHeaderCountReadback
open GeneralPaperFieldDirectory GeneralPaperReferenceRegionSlots
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedFieldValue
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

theorem read_shift (model : RationalCostModel) (A : ℕ) (memory : GeneralPaperPayloadMemory.Memory Word)
    (root : FixedBinaryWord A) (fixed index : ℕ) :
    (GeneralPaperMixedReferenceRegionProgram.read model A memory root 0 (fixed + index)).1 =
      (GeneralPaperMixedReferenceRegionProgram.read model A memory root fixed index).1 := by
  simp only [GeneralPaperMixedReferenceRegionProgram.read_data,Nat.zero_add,Nat.one_mul,Nat.add_zero]

theorem compatible (model : RationalCostModel) (A : ℕ) (installed : Installed A) (directory : Directory A)
    (hRead : Readback model A installed (GeneralPaperHeaderCountDirectory.expanded directory)) : Readback model A installed directory := by
  refine ⟨?_,hRead.2⟩
  intro header hh index
  have hMember := GeneralPaperHeaderCountDirectory.header_member directory header hh
  by_cases hf : header.fixed = 0
  · rw [GeneralPaperHeaderCountExpansion.zero_fixed header hf] at hMember
    exact hRead.1 header hMember index
  · have hIndex : header.fixed + index.val < (GeneralPaperHeaderCountExpansion.expanded header).targets.length := by
      rw [GeneralPaperHeaderCountExpansion.length header hf]
      omega
    have hLookup := GeneralPaperHeaderCountExpansion.target_lookup header hf index
    rw [List.getElem?_eq_getElem hIndex] at hLookup
    have h := hRead.1 (GeneralPaperHeaderCountExpansion.expanded header) hMember ⟨header.fixed + index.val,hIndex⟩
    rw [Option.some.inj hLookup] at h
    have hFixed : (GeneralPaperHeaderCountExpansion.expanded header).fixed = 0 := by
      simp only [GeneralPaperHeaderCountExpansion.expanded,hf,ite_false]
    rw [GeneralPaperHeaderCountExpansion.region,hFixed,read_shift] at h
    exact h

def count (model : RationalCostModel) (A : ℕ) (installed : Installed A) (root : FixedBinaryWord A) : Option ℕ × ℕ :=
  GeneralPaperRulerFieldCursor.read model A ⟨installed.memory,root,0⟩

theorem count_source (model : RationalCostModel) (A : ℕ) (installed : Installed A) (directory : Directory A)
    (hRead : Readback model A installed (GeneralPaperHeaderCountDirectory.expanded directory))
    (header : Header A) (hHeader : header ∈ directory.headers) (hf : header.fixed ≠ 0) (hFits : header.targets.length < 2 ^ A) :
    (count model A installed header.region.reference).1 = some header.targets.length ∧
      (count model A installed header.region.reference).2 =
        (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) header.region.reference 0 0).2 + 65 * A + 64 := by
  have hIndex : 0 < (GeneralPaperHeaderCountExpansion.expanded header).targets.length := by
    rw [GeneralPaperHeaderCountExpansion.length header hf]
    omega
  have hLookup := GeneralPaperHeaderCountExpansion.count_lookup header hf
  rw [List.getElem?_eq_getElem hIndex] at hLookup
  have h := hRead.1 (GeneralPaperHeaderCountExpansion.expanded header)
    (GeneralPaperHeaderCountDirectory.header_member directory header hHeader) ⟨0,hIndex⟩
  rw [Option.some.inj hLookup] at h
  have hFixed : (GeneralPaperHeaderCountExpansion.expanded header).fixed = 0 := by
    simp only [GeneralPaperHeaderCountExpansion.expanded,hf,ite_false]
  rw [GeneralPaperHeaderCountExpansion.region,hFixed] at h
  simp only [count,GeneralPaperRulerFieldCursor.read,h,Option.map_some,Option.elim_some,
    FixedBinaryWord.value_ofNat A header.targets.length hFits]
  constructor
  · exact True.intro
  · ring

theorem restrict (model : RationalCostModel) (A : ℕ) (installed : Installed A) (full part : Directory A)
    (hRead : Readback model A installed full) (hHeaders : ∀ header ∈ part.headers,header ∈ full.headers)
    (hCells : ∀ cell ∈ part.cells,cell ∈ full.cells) : Readback model A installed part := by
  exact ⟨fun header hh index => hRead.1 header (hHeaders header hh) index,
    fun cell hc => hRead.2 cell (hCells cell hc)⟩

end Blotto.GeneralPaperHeaderCountReadback
