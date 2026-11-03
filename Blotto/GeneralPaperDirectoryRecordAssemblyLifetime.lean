import Blotto.GeneralPaperRootWordsLifetime

/-! Shared ownership arithmetic for actual front/trailing record assembly.
Their header-list orders have identical footprints, while the executing
constructors keep their original orders. Child body, target construction,
new header, root read and complete parent price fields coexist. -/
namespace Blotto.GeneralPaperDirectoryRecordAssemblyLifetime
open GeneralPaperFieldDirectory (Directory Body)
open GeneralPaperSequentialLayout (Region)
open GeneralPaperReferenceRegionSlots (Header)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def header {A : ℕ} (region : Region A) (fixed : ℕ) (body : Body A) : Header A :=
  ⟨region,fixed,body.roots.map Region.reference⟩

def front {A : ℕ} (region : Region A) (fixed : ℕ) (body : Body A) : Directory A :=
  ⟨region,header region fixed body :: body.headers,body.cells⟩

def trailing {A : ℕ} (region : Region A) (fixed : ℕ) (body : Body A) : Directory A :=
  ⟨region,body.headers ++ [header region fixed body],body.cells⟩

theorem front_owner (S A fixed : ℕ) (region : Region A) (body : Body A) :
    GeneralPaperFieldDirectoryStorage.directoryFoot S (front region fixed body) ≤
      GeneralPaperDirectoryPrependLifetime.bodyFoot S body + GeneralPaperFieldDirectoryStorage.headerFoot S (header region fixed body) +
      GeneralPaperMeasuredLayoutStorage.regionFoot S region + 2 * S := by
  simp only [front,GeneralPaperFieldDirectoryStorage.directoryFoot,GeneralPaperDirectoryPrependLifetime.bodyFoot,
    GeneralPaperMeasuredLayoutStorage.regionsFoot,listFootprint,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
  omega

theorem trailing_same_foot (S A fixed : ℕ) (region : Region A) (body : Body A) :
    GeneralPaperFieldDirectoryStorage.directoryFoot S (trailing region fixed body) =
      GeneralPaperFieldDirectoryStorage.directoryFoot S (front region fixed body) := by
  simp only [front,trailing,GeneralPaperFieldDirectoryStorage.directoryFoot,listFootprint,List.map_append,List.sum_append,
    List.length_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul]
  omega

def controls (S A : ℕ) (region : Region A) (body : Body A) (childWork totalWork : ℕ) : List ℕ :=
  [S,A,childWork,(GeneralPaperNestedArrayFieldCursor.rootWords S A body.roots).2,
    childWork + (GeneralPaperNestedArrayFieldCursor.rootWords S A body.roots).2,GeneralPaperLastRegionSelection.price S A region,
    childWork + (GeneralPaperNestedArrayFieldCursor.rootWords S A body.roots).2 + GeneralPaperLastRegionSelection.price S A region,totalWork]

def window (S A fixed : ℕ) (region : Region A) (body : Body A) (childSpace childWork totalWork : ℕ) : ℕ :=
  childSpace + GeneralPaperRootWordsLifetime.window S A body.roots +
    GeneralPaperFieldDirectoryStorage.directoryFoot S (front region fixed body) +
    GeneralPaperMeasuredLayoutStorage.regionFoot S region + GeneralPaperLastRegionSelection.price S A region +
    fields S (controls S A region body childWork totalWork) + 128 * S

theorem window_bound (model : RationalCostModel) (S A Q B N Cs fixed : ℕ) (region : Region A) (body : Body A)
    (childSpace childWork totalWork : ℕ) (hA : 0 < A) (hRootCap : ∀ root ∈ body.roots,root.stop < 2 ^ A)
    (hRegionCap : region.stop < 2 ^ A) (hHeader : A * (fixed + body.roots.length) ≤ region.length) (hCount : body.roots.length = N)
    (hChild : childSpace ≤ (B + N + 1) * Cs * unit model S A Q)
    (hBody : GeneralPaperDirectoryPrependLifetime.bodyFoot S body ≤ (B + N + 1) * unit model S A Q)
    (hTotal : totalWork ≤ Q)
    (hPrices : childWork + (GeneralPaperNestedArrayFieldCursor.rootWords S A body.roots).2 + GeneralPaperLastRegionSelection.price S A region ≤ totalWork) :
    window S A fixed region body childSpace childWork totalWork ≤ (B + N + 1) * (Cs + 12) * unit model S A Q := by
  have hRoots := GeneralPaperRootWordsLifetime.window_bound model S A Q body.roots hA hRootCap (by omega)
  rw [hCount] at hRoots
  have hValid : GeneralPaperReferenceRegionSlots.Valid (header region fixed body) := by
    simpa only [GeneralPaperReferenceRegionSlots.Valid,header,List.length_map] using hHeader
  have hHead := GeneralPaperFieldDirectoryStorage.header_bound S A (header region fixed body) hA hValid hRegionCap
  change GeneralPaperFieldDirectoryStorage.headerFoot S _ ≤ ((body.roots.map Region.reference).length + 1) * 384 * (S + A + 1) at hHead
  rw [List.length_map,hCount] at hHead
  have hRegion := GeneralPaperMeasuredLayoutStorage.region_bound S A region hA hRegionCap
  have hRead := GeneralPaperDirectoryCopyWork.region_work model S A region hA hRegionCap
  have hFields := fields_bound S (natBits (cap S A Q)) (controls S A region body childWork totalWork) (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 8 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hHeaderPay := Nat.mul_le_mul_left (N + 1) (show 384 * (S + A + 1) ≤ unit model S A Q by omega)
  have hOwner := front_owner S A fixed region body
  have hParent : 2 * GeneralPaperMeasuredLayoutStorage.regionFoot S region + GeneralPaperLastRegionSelection.price S A region +
      fields S (controls S A region body childWork totalWork) + 130 * S ≤ unit model S A Q := by
    unfold GeneralPaperMeasuredLayoutStorage.regionBound at hRegion
    omega
  have hN := Nat.mul_le_mul_right (unit model S A Q) (show N + 1 ≤ B + N + 1 by omega)
  have hBase := Nat.mul_le_mul_right (unit model S A Q) (show 1 ≤ B + N + 1 by omega)
  unfold window
  nlinarith only [hChild,hBody,hRoots,hHead,hHeaderPay,hOwner,hParent,hN,hBase]

end Blotto.GeneralPaperDirectoryRecordAssemblyLifetime
