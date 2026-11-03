import Blotto.GeneralPaperSelectedCursorInputLifetime

/-! Complete three-region outer-field extraction. Original region list,
copied field records, all descriptor/copy/read scratch and saved prices are
bounded by metadata alone. The actual field return is unchanged. -/
namespace Blotto.GeneralPaperOuterFieldCursorLifetime
open GeneralPaperEqualOuterFieldLayout (Fields canonical extract)
open GeneralPaperMeasuredLayoutStorage (regionFoot regionsFoot regionBound)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperPayloadInstallationLifetime (cap)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def fieldsFoot {A : ℕ} (S : ℕ) (fields : Fields A) : ℕ :=
  regionFoot S fields.control + regionFoot S fields.value + regionFoot S fields.record + 64 * S

def window (model : RationalCostModel) (S A start : ℕ) : ℕ :=
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredSelectedPlan.header model S A)).1
  regionsFoot S regions + 2 * fieldsFoot S (canonical A start) + (extract S A regions).2 +
    fields S [S,A,(extract S A regions).2] + 128 * S

theorem window_bound (model : RationalCostModel) (S A start Q : ℕ) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A)
    (hWork : (extract S A (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A)).1).2 ≤ Q) :
    window model S A start ≤ 4 * unit model S A Q := by
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredSelectedPlan.header model S A)).1
  let price := (extract S A regions).2
  change price ≤ Q at hWork
  have hRange := GeneralPaperMeasuredBlockLayout.range model S A start (GeneralPaperEqualMeasuredSelectedPlan.header model S A)
  have hRegions : regions = [(canonical A start).control,(canonical A start).value,(canonical A start).record] :=
    GeneralPaperEqualOuterFieldLayout.regions model S A start
  have hRegion : ∀ r ∈ regions,regionFoot S r ≤ regionBound S A :=
    fun r hr => GeneralPaperMeasuredLayoutStorage.region_bound S A r hA ((hRange r hr).2.trans_lt hCap)
  rw [hRegions] at hRegion
  have hControl := hRegion (canonical A start).control (List.mem_cons_self ..)
  have hValue := hRegion (canonical A start).value (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hRecord := hRegion (canonical A start).record (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hPrice := GeneralPaperTwoPoolPreparationWork.extract_work model S A start hA hCap
  change price ≤ 4 * GeneralPaperMeasuredPlanWorkAlgebra.unit model S A at hPrice
  have hFields := fields_bound S (natBits (cap S A Q)) [S,A,price] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  change regionsFoot S regions + 2 * fieldsFoot S (canonical A start) + price + fields S [S,A,price] + 128 * S ≤ _
  rw [hRegions]
  simp only [regionsFoot,listFootprint,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  unfold fieldsFoot regionBound at *
  omega

def profile (model : RationalCostModel) (S A : ℕ) : ℕ :=
  4 * unit model S A (4 * GeneralPaperMeasuredPlanWorkAlgebra.unit model S A)

theorem constructed (model : RationalCostModel) (S A start : ℕ) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    (extract S A (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A)).1).1 = some (canonical A start) ∧
      window model S A start ≤ profile model S A :=
  ⟨GeneralPaperEqualOuterFieldLayout.extracted model S A start,
    window_bound model S A start _ hA hCap (GeneralPaperTwoPoolPreparationWork.extract_work model S A start hA hCap)⟩

theorem profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L) :
    Polylog (fun x => profile model (S x) (A x)) L := by
  have hOld := GeneralPaperMeasuredPlanWorkRates.unit_rate model hFast S A L hL hS hA
  have hPrice : Polylog (fun x => 4 * GeneralPaperMeasuredPlanWorkAlgebra.unit model (S x) (A x)) L := by fun_prop
  have hSmall := small_of_polylog hL hPrice
  have hUnit := GeneralPaperMeasuredPlanLifetimeRates.unit_rate model hFast S A _ L hL hS hA hSmall
  unfold profile
  fun_prop

end Blotto.GeneralPaperOuterFieldCursorLifetime
