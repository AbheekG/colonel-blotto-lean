import Blotto.GeneralPaperLastRegionSelection

/-! Actual outer-record headers and its sole address-control scalar are
installed from extracted regions. Record reads follow stored raw targets;
address recovery follows record -> control header -> scalar payload. No
control value or decoded target is supplied to the reader. -/
namespace Blotto.GeneralPaperEqualOuterFieldProgram
open GeneralPaperEqualOuterFieldLayout GeneralPaperReferenceRegionSlots
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

structure Installed (A : ℕ) where
  references : GeneralPaperPayloadMemory.Memory Word
  naturals : GeneralPaperPayloadMemory.Memory ℕ
  root : FixedBinaryWord A
  work : ℕ

def install (model : RationalCostModel) (S A : ℕ) (fields : Fields A) (branch tag : FixedBinaryWord A) : Installed A :=
  let references := GeneralPaperMixedReferenceRegionProgram.prepare model S A A [] (headers fields branch tag)
    (GeneralPaperPayloadMemory.empty Word)
  let scalar := GeneralPaperPayloadMemory.install S A GeneralPaperEncodedScalarStorage.natBits (GeneralPaperPayloadMemory.empty ℕ)
    [(fields.value.reference,A)]
  ⟨references.memory,scalar.1,fields.record.reference,references.work + scalar.2 + 128 * (S + A + 1)⟩

def read_field (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ) : Option Word × ℕ :=
  GeneralPaperMixedReferenceRegionProgram.read model A installed.references installed.root 0 index

def read_address (model : RationalCostModel) (A : ℕ) (installed : Installed A) : Option ℕ × ℕ :=
  let control := read_field model A installed 1
  match control.1 with
  | none => (none,control.2 + 64 * A + 64)
  | some ⟨B,root⟩ =>
    let pointer := GeneralPaperMixedReferenceRegionProgram.read model B installed.references root 32 0
    match pointer.1 with
    | none => (none,control.2 + pointer.2 + 64 * (A + B + 1))
    | some ⟨C,value⟩ =>
      let scalar := GeneralPaperPayloadMemory.read C GeneralPaperEncodedScalarStorage.natBits installed.naturals value
      (scalar.1,control.2 + pointer.2 + scalar.2 + 64 * (A + B + C + 1))

theorem field_read (model : RationalCostModel) (S A start : ℕ) (branch tag : FixedBinaryWord A)
    (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A)
    (j : Fin 3) :
    (read_field model A (install model S A (canonical A start) branch tag) j.val).1 =
      some (⟨A,([branch,(canonical A start).control.reference,tag][j.val]'(by exact j.isLt))⟩ : Word) := by
  let hs := headers (canonical A start) branch tag
  have hFrom : GeneralPaperReferenceLayoutInstallation.FromLayout model S A start
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A) hs := selected_owners model S A start branch tag
  have hValid := valid A start branch tag
  let header : Header A := ⟨(canonical A start).record,0,[branch,(canonical A start).control.reference,tag]⟩
  have hHeader : header ∈ hs := List.mem_cons_of_mem _ (List.mem_cons_self ..)
  exact GeneralPaperMixedReferenceRegionProgram.outside_read model S A A [] hs (GeneralPaperPayloadMemory.empty Word) hA hValid
    (GeneralPaperReferenceLayoutInstallation.capacities model S A start _ hs hFrom hCap)
    (GeneralPaperReferenceLayoutInstallation.roots model S A start _ hs hFrom hCap)
    (GeneralPaperReferenceLayoutInstallation.owners model S A start _ hs hFrom) header hHeader j

theorem control_read (model : RationalCostModel) (S A start : ℕ) (branch tag : FixedBinaryWord A)
    (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    (GeneralPaperMixedReferenceRegionProgram.read model A (install model S A (canonical A start) branch tag).references
      (canonical A start).control.reference 32 0).1 = some (⟨A,(canonical A start).value.reference⟩ : Word) := by
  let hs := headers (canonical A start) branch tag
  have hFrom : GeneralPaperReferenceLayoutInstallation.FromLayout model S A start
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A) hs := selected_owners model S A start branch tag
  let header : Header A := ⟨(canonical A start).control,32,[(canonical A start).value.reference]⟩
  exact GeneralPaperMixedReferenceRegionProgram.outside_read model S A A [] hs (GeneralPaperPayloadMemory.empty Word) hA
    (valid A start branch tag)
    (GeneralPaperReferenceLayoutInstallation.capacities model S A start _ hs hFrom hCap)
    (GeneralPaperReferenceLayoutInstallation.roots model S A start _ hs hFrom hCap)
    (GeneralPaperReferenceLayoutInstallation.owners model S A start _ hs hFrom) header (List.mem_cons_self ..) ⟨0,by change 0 < 1; omega⟩

theorem scalar_read (model : RationalCostModel) (S A : ℕ) (fields : Fields A) (branch tag : FixedBinaryWord A) :
    (GeneralPaperPayloadMemory.read A GeneralPaperEncodedScalarStorage.natBits (install model S A fields branch tag).naturals
      fields.value.reference).1 = some A := by
  exact GeneralPaperPayloadMemory.installed S A GeneralPaperEncodedScalarStorage.natBits (GeneralPaperPayloadMemory.empty ℕ)
    [(fields.value.reference,A)] (by simp only [List.map_cons,List.map_nil,List.nodup_cons,List.not_mem_nil,List.nodup_nil,
      not_false_eq_true,and_self]) (fields.value.reference,A) (List.mem_cons_self ..)

theorem address_read (model : RationalCostModel) (S A start : ℕ) (branch tag : FixedBinaryWord A)
    (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    (read_address model A (install model S A (canonical A start) branch tag)).1 = some A := by
  have hr := field_read model S A start branch tag hA hCap ⟨1,by decide⟩
  have hc := control_read model S A start branch tag hA hCap
  have hs := scalar_read model S A (canonical A start) branch tag
  simp only [read_address,hr,List.getElem_cons_succ,List.getElem_cons_zero,hc]
  exact hs

theorem address_read_work (model : RationalCostModel) (S A start : ℕ) (branch tag : FixedBinaryWord A)
    (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    (read_address model A (install model S A (canonical A start) branch tag)).2 =
      (read_field model A (install model S A (canonical A start) branch tag) 1).2 +
      (GeneralPaperMixedReferenceRegionProgram.read model A (install model S A (canonical A start) branch tag).references
        (canonical A start).control.reference 32 0).2 +
      GeneralPaperEncodedScalarStorage.natBits A + 64 * A + 64 + 64 * (3 * A + 1) := by
  have hr := field_read model S A start branch tag hA hCap ⟨1,by decide⟩
  have hc := control_read model S A start branch tag hA hCap
  have hs := scalar_read model S A (canonical A start) branch tag
  change (install model S A (canonical A start) branch tag).naturals (canonical A start).value.reference.value = some A at hs
  simp only [read_address,hr,List.getElem_cons_succ,List.getElem_cons_zero,hc]
  dsimp only [GeneralPaperPayloadMemory.read]
  rw [hs]
  simp only [Option.elim_some]
  ring

end Blotto.GeneralPaperEqualOuterFieldProgram
