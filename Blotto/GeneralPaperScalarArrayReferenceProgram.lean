import Blotto.GeneralPaperScalarArrayLayout

/-! A scalar array is installed from its executed payload regions. The
header contains those actual raw roots, and payload cells contain the source
scalars at those roots. The reader follows a computed header slot and then
reads the addressed payload; no decoded source value is given to the reader.
Plan/region lists are temporary construction data, not returned fields. -/
namespace Blotto.GeneralPaperScalarArrayReferenceProgram
open GeneralPaperSequentialLayout
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

structure Prepared (A : ℕ) (α : Type*) where
  references : GeneralPaperRawReferenceMemory.Memory A
  payloads : GeneralPaperPayloadMemory.Memory α
  work : ℕ

def entries {α : Type*} (A : ℕ) (regions : List (Region A)) (values : List α) :
    List (GeneralPaperPayloadMemory.Entry A α) :=
  (regions.map Region.reference).zip values

def install {α : Type*} {n : ℕ} (model : RationalCostModel) (S A base : ℕ) (encode : α → ℕ)
    (source : FixedArrayTable n α) (regions : List (Region A)) : Prepared A α :=
  let targets := regions.map Region.reference
  let body := GeneralPaperPayloadMemory.install S A encode (GeneralPaperPayloadMemory.empty α)
    (entries A regions source.data.toList)
  let header := GeneralPaperReferenceHeaderProgram.prepare model S A base 64 1 0 targets
    (GeneralPaperRawReferenceMemory.empty A)
  ⟨header.memory,body.1,body.2 + header.work + regions.length * (128 * (S + A + 1)) + 64 * (S + A + 1)⟩

def prepare {α : Type*} {n : ℕ} (model : RationalCostModel) (S A base : ℕ)
    (measure : α → GeneralPaperMeasuredBlockPlan.Plan) (encode : α → ℕ) (source : FixedArrayTable n α) : Prepared A α :=
  let planned := GeneralPaperScalarArrayLayout.plan model S A measure source
  let laid := GeneralPaperMeasuredBlockLayout.run model S A base planned
  let actual := install model S A base encode source laid.1.tail
  ⟨actual.references,actual.payloads,laid.2.2 + actual.work + 64 * (S + A + 1)⟩

def read {α : Type*} (model : RationalCostModel) (A : ℕ) (encode : α → ℕ) (prepared : Prepared A α)
    (root : FixedBinaryWord A) (index : ℕ) : Option α × ℕ :=
  let target := GeneralPaperReferenceHeaderProgram.read model A prepared.references root.value 64 1 index 0
  match target.1 with
  | none => (none,target.2 + 64 * A + 64)
  | some pointer =>
    let actual := GeneralPaperPayloadMemory.read A encode prepared.payloads pointer
    (actual.1,target.2 + actual.2 + 64 * A + 64)

theorem read_work_of_some {α : Type*} (model : RationalCostModel) (A : ℕ) (encode : α → ℕ)
    (prepared : Prepared A α) (root : FixedBinaryWord A) (index : ℕ) (value : α)
    (hRead : (read model A encode prepared root index).1 = some value) :
    (read model A encode prepared root index).2 =
      (GeneralPaperReferenceHeaderProgram.read model A prepared.references root.value 64 1 index 0).2 +
        encode value + 128 * A + 128 := by
  cases hTarget : (GeneralPaperReferenceHeaderProgram.read model A prepared.references root.value 64 1 index 0).1 with
  | none => simp only [read,hTarget] at hRead; cases hRead
  | some pointer =>
    have hPayload : prepared.payloads pointer.value = some value := by
      simpa only [read,hTarget,GeneralPaperPayloadMemory.read] using hRead
    simp only [read,hTarget,GeneralPaperPayloadMemory.read,hPayload,Option.elim_some]
    ring

theorem entry_keys {α : Type*} {n : ℕ} (A : ℕ) (source : FixedArrayTable n α) (regions : List (Region A))
    (hLength : regions.length = n) :
    ((entries A regions source.data.toList).map (fun e => e.1.value)) = regions.map (fun r => r.reference.value) := by
  have hLen : (regions.map Region.reference).length ≤ source.data.toList.length := by
    simp only [List.length_map,Array.length_toList,source.size,hLength]
    exact le_refl _
  have h := congrArg (List.map FixedBinaryWord.value) (List.map_fst_zip hLen)
  simpa only [entries,List.map_map,Function.comp_def] using h

theorem entry_at {α : Type*} {n : ℕ} (A : ℕ) (source : FixedArrayTable n α) (regions : List (Region A))
    (hLength : regions.length = n) (j : Fin n) :
    ((regions[j.val]'(by rw [hLength]; exact j.isLt)).reference,source.read j) ∈ entries A regions source.data.toList := by
  have hj : j.val < (entries A regions source.data.toList).length := by
    simp only [entries,List.length_zip,List.length_map,Array.length_toList,source.size,hLength,Nat.min_self]
    exact j.isLt
  have hMem := List.getElem_mem hj
  simpa only [entries,List.getElem_zip,List.getElem_map,Array.getElem_toList,FixedArrayTable.read] using hMem

theorem install_read {α : Type*} {n : ℕ} (model : RationalCostModel) (S A base : ℕ) (encode : α → ℕ)
    (source : FixedArrayTable n α) (regions : List (Region A)) (hLength : regions.length = n)
    (hKeys : (regions.map (fun r => r.reference.value)).Nodup) (hA : 0 < A)
    (hCap : base + A * (64 + n) < 2 ^ A) (j : Fin n) :
    (read model A encode (install model S A base encode source regions) (FixedBinaryWord.ofNat A base) j.val).1 =
      some (source.read j) := by
  have hBase : base < 2 ^ A := by omega
  have hTargets : (regions.map Region.reference).length = n := by simp only [List.length_map,hLength]
  have hHeader := GeneralPaperReferenceHeaderProgram.read_prepared model S A base 64 1 0
    (regions.map Region.reference) (GeneralPaperRawReferenceMemory.empty A) hA (by decide)
    (by simpa only [hTargets,one_mul] using hCap) ⟨j.val,by rw [hTargets]; exact j.isLt⟩
  have hEntries : ((entries A regions source.data.toList).map (fun e => e.1.value)).Nodup := by
    rw [entry_keys A source regions hLength]
    exact hKeys
  have hPayload := GeneralPaperPayloadMemory.installed S A encode (GeneralPaperPayloadMemory.empty α)
    (entries A regions source.data.toList) hEntries _ (entry_at A source regions hLength j)
  simp only [List.getElem_map] at hHeader
  unfold read
  simp only [FixedBinaryWord.value_ofNat A base hBase,install,hHeader]
  exact hPayload

theorem prepared_read {α : Type*} {n : ℕ} (model : RationalCostModel) (S A base : ℕ)
    (measure : α → GeneralPaperMeasuredBlockPlan.Plan) (encode : α → ℕ) (source : FixedArrayTable n α)
    (hMeasure : ∀ x,(measure x).sizes = [encode x]) (hPositive : ∀ x,0 < encode x) (hA : 0 < A)
    (hCap : base + (GeneralPaperScalarArrayLayout.plan model S A measure source).sizes.sum < 2 ^ A) (j : Fin n) :
    (read model A encode (prepare model S A base measure encode source) (FixedBinaryWord.ofNat A base) j.val).1 =
      some (source.read j) := by
  have hLength := GeneralPaperScalarArrayLayout.payload_count model S A base measure encode source hMeasure
  have hKeys := GeneralPaperScalarArrayLayout.payload_keys model S A base measure encode source hMeasure hPositive hCap
  have hHeader := GeneralPaperMeasuredHeaderInstallation.array_cap model S A base measure source hCap
  exact install_read model S A base encode source _ hLength hKeys hA hHeader j

end Blotto.GeneralPaperScalarArrayReferenceProgram
