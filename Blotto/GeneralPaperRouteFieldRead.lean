import Blotto.GeneralPaperRecordScalarRead

/-! Route decoding reads the stored presence bit before choosing the actual
coefficient slot. No source route or decoded pointer is a reader input.
Output construction prices include the copied label and rational word. -/
namespace Blotto.GeneralPaperRouteFieldRead
open GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def read (model : RationalCostModel) (A : ℕ) (installed : Installed A) : Option (Option ℕ × ℚ) × ℕ :=
  let flag := GeneralPaperRecordScalarRead.read model A installed 0
  match flag.1 with
  | some (.bit false) =>
    let coefficient := GeneralPaperRecordScalarRead.read model A installed 1
    match coefficient.1 with
    | some (.rational value) => (some (none,value),flag.2 + coefficient.2 + rationalWordWidth value + 128 * A + 128)
    | _ => (none,flag.2 + coefficient.2 + 128 * A + 128)
  | some (.bit true) =>
    let label := GeneralPaperRecordScalarRead.read model A installed 1
    let coefficient := GeneralPaperRecordScalarRead.read model A installed 2
    match label.1,coefficient.1 with
    | some (.natural group),some (.rational value) =>
      (some (some group,value),flag.2 + label.2 + coefficient.2 + GeneralPaperEncodedScalarStorage.natBits group + rationalWordWidth value + 192 * A + 192)
    | _,_ => (none,flag.2 + label.2 + coefficient.2 + 192 * A + 192)
  | _ => (none,flag.2 + 64 * A + 64)

theorem absent (model : RationalCostModel) (A : ℕ) (installed : Installed A) (value : ℚ)
    (hFlag : (GeneralPaperRecordScalarRead.read model A installed 0).1 = some (.bit false))
    (hCoefficient : (GeneralPaperRecordScalarRead.read model A installed 1).1 = some (.rational value)) :
    (read model A installed).1 = some (none,value) ∧ (read model A installed).2 =
      (GeneralPaperRecordScalarRead.read model A installed 0).2 + (GeneralPaperRecordScalarRead.read model A installed 1).2 +
      rationalWordWidth value + 128 * A + 128 := by
  simp only [read,hFlag,hCoefficient,and_self]

theorem present (model : RationalCostModel) (A : ℕ) (installed : Installed A) (group : ℕ) (value : ℚ)
    (hFlag : (GeneralPaperRecordScalarRead.read model A installed 0).1 = some (.bit true))
    (hLabel : (GeneralPaperRecordScalarRead.read model A installed 1).1 = some (.natural group))
    (hCoefficient : (GeneralPaperRecordScalarRead.read model A installed 2).1 = some (.rational value)) :
    (read model A installed).1 = some (some group,value) ∧ (read model A installed).2 =
      (GeneralPaperRecordScalarRead.read model A installed 0).2 + (GeneralPaperRecordScalarRead.read model A installed 1).2 +
      (GeneralPaperRecordScalarRead.read model A installed 2).2 + GeneralPaperEncodedScalarStorage.natBits group +
      rationalWordWidth value + 192 * A + 192 := by
  simp only [read,hFlag,hLabel,hCoefficient,and_self]

theorem source_of_fields {m : ℕ} (model : RationalCostModel) (A : ℕ) (installed : Installed A) (route : GroupRoute m)
    (hFields : ∀ index : Fin (GeneralPaperRouteFieldCursor.values route).length,
      (GeneralPaperRecordScalarRead.read model A installed index.val).1 = some ((GeneralPaperRouteFieldCursor.values route)[index.val])) :
    (read model A installed).1 = some (route.1.map Fin.val,route.2) := by
  rcases route with ⟨label,coefficient⟩
  cases label with
  | none =>
    have hFlag := hFields ⟨0,by simp only [GeneralPaperRouteFieldCursor.values,List.length_cons,List.length_nil]; omega⟩
    have hCoefficient := hFields ⟨1,by simp only [GeneralPaperRouteFieldCursor.values,List.length_cons,List.length_nil]; omega⟩
    exact (absent model A _ coefficient hFlag hCoefficient).1
  | some group =>
    have hFlag := hFields ⟨0,by simp only [GeneralPaperRouteFieldCursor.values,List.length_cons,List.length_nil]; omega⟩
    have hLabel := hFields ⟨1,by simp only [GeneralPaperRouteFieldCursor.values,List.length_cons,List.length_nil]; omega⟩
    have hCoefficient := hFields ⟨2,by simp only [GeneralPaperRouteFieldCursor.values,List.length_cons,List.length_nil]; omega⟩
    exact (present model A _ group.val coefficient hFlag hLabel hCoefficient).1

theorem source {m : ℕ} (model : RationalCostModel) (S A start : ℕ) (route : GroupRoute m) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredLeafPlans.route model S A route).sizes.sum < 2 ^ A) :
    (read model A (GeneralPaperUnifiedDirectoryInstallation.install model S A
      (GeneralPaperRouteFieldCursor.expected model S A route start))).1 = some (route.1.map Fin.val,route.2) :=
  source_of_fields model A _ route (fun index => (GeneralPaperRecordScalarRead.route_field model S A start route hA hCap index).1)

end Blotto.GeneralPaperRouteFieldRead
