import Blotto.GeneralPaperPartitionPrice

/-! The source catalogue's actual projected-successor list. One backwards
reference loop converts the retained array to a list, then one priced map
projects the sign and increments each code. No alphabet enumeration occurs.
-/
namespace Blotto.GeneralPaperCataloguePointExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def project (primitive : ℕ → ℕ) (W U code : ℕ) : ℕ × ℕ :=
  let test := GeneralPaperIntegerWordPrice.compare primitive code U
  if code<U then (code,test+32*W)
  else (code-U,test+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) code U+32*W)

def successor (primitive : ℕ → ℕ) (W U code : ℕ) : ℕ × ℕ :=
  let found := project primitive W U code
  (found.1+1,found.2+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) found.1 1+32*W)

def run {n : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ) : List ℕ × ℕ :=
  let values := StoredArrayReferenceList.list summary.data
  let mapped := GeneralPaperPricedListMap.run W (successor primitive W U) values
  (mapped.1,StoredArrayReferenceList.work index (if bits then arrayWord W (n+2) else W) summary.data.size+mapped.2+64*W)

theorem project_data (primitive : ℕ → ℕ) (W U code : ℕ) :
    (project primitive W U code).1=GeneralPaperSignedUpdatePlan.project U code := by
  unfold project GeneralPaperSignedUpdatePlan.project
  split <;> rfl

theorem successor_data (primitive : ℕ → ℕ) (W U code : ℕ) :
    (successor primitive W U code).1=GeneralPaperSignedUpdatePlan.project U code+1 := by
  change (project primitive W U code).1+1=_
  rw [project_data]

theorem data {n : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ) :
    (run bits index primitive W U summary).1=GeneralPaperTailCataloguePartition.points U summary := by
  unfold run GeneralPaperTailCataloguePartition.points
  dsimp only
  simp only [GeneralPaperPricedListMap.data,StoredArrayReferenceList.list_data,successor_data]

theorem length {n : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ) :
    (run bits index primitive W U summary).1.length=n := by
  rw [data]
  exact GeneralPaperTailCataloguePartition.points_length U summary

theorem member_code {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (hCodes : ∀ r,summary.read r<2*U)
    (code : ℕ) (hCode : code∈summary.data.toList) : code<2*U := by
  obtain ⟨i,hi,hRead⟩ := List.getElem_of_mem hCode
  have hiN : i<n := by simpa only [Array.length_toList,summary.size] using hi
  have h : summary.read ⟨i,hiN⟩=code := by
    simpa only [FixedArrayTable.read,Array.getElem_toList] using hRead
  rw [←h]
  exact hCodes ⟨i,hiN⟩

theorem point_bound {n : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ)
    (hCodes : ∀ r,summary.read r<2*U) (point : ℕ) (hPoint : point∈(run bits index primitive W U summary).1) : point≤U := by
  rw [data,GeneralPaperTailCataloguePartition.points] at hPoint
  obtain ⟨code,hCode,rfl⟩ := List.mem_map.mp hPoint
  have h := GeneralPaperUnsignedPartition.project_bound U code (member_code U summary hCodes code hCode)
  omega

end Blotto.GeneralPaperCataloguePointExecution
