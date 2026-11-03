import Blotto.GeneralPaperRationalCodeRows

/-! A whole law on finitely many distinct feasible rational rows is an
actual candidate-code comparator. All original real probabilities and all
joint row dependence are preserved exactly by the decoded physical law.
-/
namespace Blotto.GeneralPaperFiniteRationalLaw
open MeasureTheory
open scoped BigOperators Classical
open GeneralPaperCodeAlphabet GeneralPaperRationalCodeRows
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

theorem realization {m N : ℕ} (a : Alphabet) (B : ℚ) (law : Mixed m) (r : Fin N → Fin m → ℚ)
    (hUnit : ∀ l j, 0≤r l j ∧ r l j≤1) (hDen : ∀ l j, (r l j).den≤a.D)
    (hBudget : ∀ l, ∑ j, r l j≤B)
    (hInjective : Function.Injective (fun l => (fun j => (r l j:ℝ))))
    (hSupport : ∀ᵐ row ∂(law:Measure (Allocation m)), row∈Set.range (fun l => (fun j => (r l j:ℝ)))) (qbar : ℕ) :
    ∃ X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false B,
      GeneralPaperCodeMixturePhysical.physicalLaw X qbar=law := by
  choose code selected hDecode hValue hClosed using (fun l j => field_exists a (r l j) (hUnit l j) (hDen l j))
  let point := fun l (j : Fin m) => (r l j:ℝ)
  let X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false B := {
    law := {
      labels := N
      weight := GeneralPaperFiniteAtomicLaw.weight law point
      rows := fun l j => ⟨code l j,by
        rw [← a.dyadic]
        exact valid_in_alphabet a false _ (GeneralPaperCodeDecodeSound.decode_valid a false _ _ (hDecode l j))⟩
      nonnegative := GeneralPaperFiniteAtomicLaw.weight_nonnegative law point
      total := GeneralPaperFiniteAtomicLaw.weight_total law point hInjective hSupport }
    choices := fun l => FixedArrayTable.ofFn (selected l)
    decoded := fun l j => by rw [FixedArrayTable.read_ofFn]; exact hDecode l j
    budget := fun l => by
      simpa only [FixedArrayTable.read_ofFn] using row_tag_budget B (r l) (selected l) (hValue l) (hClosed l) (hBudget l) }
  have hAllocation (l : Fin N) : GeneralPaperCodeMixturePhysical.allocation X qbar l=point l := by
    funext j
    change (((FixedArrayTable.ofFn (selected l)).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C):ℝ)=(r l j:ℝ)
    rw [FixedArrayTable.read_ofFn,physical_value _ _ (hValue l j) (hClosed l j)]
  refine ⟨X,?_⟩
  change probabilityMixture (GeneralPaperFiniteAtomicLaw.weight law point)
    (fun l => PureBoundaryEquilibria.pointLaw (GeneralPaperCodeMixturePhysical.allocation X qbar l))
    (GeneralPaperFiniteAtomicLaw.weight_nonnegative law point) (GeneralPaperFiniteAtomicLaw.weight_total law point hInjective hSupport)=law
  have hLaws : (fun l => PureBoundaryEquilibria.pointLaw (GeneralPaperCodeMixturePhysical.allocation X qbar l))=
      fun l => PureBoundaryEquilibria.pointLaw (point l) := funext (fun l => congrArg PureBoundaryEquilibria.pointLaw (hAllocation l))
  rw [hLaws]
  exact GeneralPaperFiniteAtomicLaw.realization law point hInjective hSupport

end Blotto.GeneralPaperFiniteRationalLaw
