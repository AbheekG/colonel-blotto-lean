import Blotto.GeneralPaperStoredRouteArraySource

/-! One coordinate uses the actually decoded route and the indexed group
array produced by the stored postselection computation. Full group payload,
index/control, multiplication and result prices are retained. -/
namespace Blotto.GeneralPaperStoredRouteCoordinate
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

def value {m : ℕ} (groups : FixedArrayTable m ℚ) (route : GroupRoute m) : ℚ :=
  match route.1 with
  | none => 0
  | some label => route.2 * groups.read label

def read (model : RationalCostModel) (A : ℕ) (installed : Installed A) (groups : Array ℚ) (index : ℕ) : Option ℚ × ℕ :=
  let route := GeneralPaperRouteArrayRead.read model A installed index
  match route.1 with
  | none => (none,route.2 + 64 * (A + 1))
  | some (none,_) => (some 0,route.2 + rationalWordWidth (0 : ℚ) + 64 * (A + 1))
  | some (some label,coefficient) =>
    let group := groups.getD label 0
    let copied := rationalWordWidth group + GeneralPaperEncodedScalarStorage.natBits label + binaryWordWidth groups.size + 64 * (A + 1)
    let product := GeneralPaperRationalScalarStep.run model A .mul coefficient group
    (some product.1,route.2 + copied + product.2 + 128 * (A + 1))

def price {m : ℕ} (model : RationalCostModel) (A : ℕ) (installed : Installed A) (groups : FixedArrayTable m ℚ)
    (index : ℕ) (route : GroupRoute m) : ℕ :=
  let baseWork := (GeneralPaperRouteArrayRead.read model A installed index).2
  match route.1 with
  | none => baseWork + rationalWordWidth (0 : ℚ) + 64 * (A + 1)
  | some label => baseWork +
      (rationalWordWidth (groups.read label) + GeneralPaperEncodedScalarStorage.natBits label + binaryWordWidth groups.data.size + 64 * (A + 1)) +
      (GeneralPaperRationalScalarStep.run model A .mul route.2 (groups.read label)).2 + 128 * (A + 1)

theorem source {m : ℕ} (model : RationalCostModel) (A : ℕ) (installed : Installed A) (groups : FixedArrayTable m ℚ)
    (index : ℕ) (route : GroupRoute m)
    (hRoute : (GeneralPaperRouteArrayRead.read model A installed index).1 = some (route.1.map Fin.val,route.2)) :
    (read model A installed groups.data index).1 = some (value groups route) ∧
      (read model A installed groups.data index).2 = price model A installed groups index route := by
  rcases route with ⟨label,coefficient⟩
  cases label with
  | none => simp only [Option.map_none,read,hRoute,value,price,and_self]
  | some group =>
    have hg : group.val < groups.data.size := by rw [groups.size]; exact group.isLt
    have hGet : groups.data.getD group.val 0 = groups.read group := by simp [Array.getD,hg,FixedArrayTable.read]
    simp only [Option.map_some,read,hRoute,hGet,value,price,GeneralPaperRationalScalarStep.data,
      GeneralPaperRationalScalarStep.Op.apply,and_self]

end Blotto.GeneralPaperStoredRouteCoordinate
