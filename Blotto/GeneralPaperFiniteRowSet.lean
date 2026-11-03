import Blotto.GeneralPaperFiniteRationalLaw

/-! Distinct finite feasible rational rows can be indexed without changing
their whole law. Filtering discards only infeasible zero-mass points, using
the original law's hard feasible support. Runtime enumeration is not claimed.
-/
namespace Blotto.GeneralPaperFiniteRowSet
open MeasureTheory
open scoped BigOperators Classical
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def enumerate {α : Type*} (s : Finset α) (i : Fin (Fintype.card ↥s)) : α := ((Fintype.equivFin ↥s).symm i).val

theorem enumerate_mem {α : Type*} (s : Finset α) (i : Fin (Fintype.card ↥s)) : enumerate s i∈s :=
  ((Fintype.equivFin ↥s).symm i).property

theorem enumerate_injective {α : Type*} (s : Finset α) : Function.Injective (enumerate s) :=
  Subtype.val_injective.comp (Fintype.equivFin ↥s).symm.injective

theorem enumerate_covers {α : Type*} (s : Finset α) (x : α) (hx : x∈s) : ∃ i, enumerate s i=x := by
  refine ⟨(Fintype.equivFin ↥s) ⟨x,hx⟩,?_⟩
  simp only [enumerate,Equiv.symm_apply_apply]

theorem realization {m : ℕ} (a : Alphabet) (B : ℚ) (hOne : B≤1) (law : Mixed m)
    (s : Finset (Fin m → ℚ)) (hLaw : Supported (B:ℝ) law)
    (hSupport : ∀ᵐ row ∂(law:Measure (Allocation m)), ∃ r∈s, row=(fun j => (r j:ℝ)))
    (hDen : ∀ r∈s, ∀ j, (r j).den≤a.D) (qbar : ℕ) :
    ∃ X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false B,
      GeneralPaperCodeMixturePhysical.physicalLaw X qbar=law := by
  let t := s.filter (fun r => Blotto.Feasible (B:ℝ) (fun j => (r j:ℝ)))
  let r := enumerate t
  have hMem (i : Fin (Fintype.card ↥t)) : r i∈s := (Finset.mem_filter.mp (enumerate_mem t i)).1
  have hFeasible (i : Fin (Fintype.card ↥t)) : Blotto.Feasible (B:ℝ) (fun j => (r i j:ℝ)) :=
    (Finset.mem_filter.mp (enumerate_mem t i)).2
  have hUnit (i : Fin (Fintype.card ↥t)) (j : Fin m) : 0≤r i j ∧ r i j≤1 := by
    have hLower := (hFeasible i).1 j
    have hUpper := (PureBoundaryEquilibria.feasible_coordinate_le (hFeasible i) j).trans
      (show (B:ℝ)≤1 by exact_mod_cast hOne)
    dsimp only at hLower hUpper
    exact ⟨by exact_mod_cast hLower,by exact_mod_cast hUpper⟩
  have hBudget (i : Fin (Fintype.card ↥t)) : ∑ j, r i j≤B := by
    have hb := (hFeasible i).2
    change (∑ j, (r i j:ℝ))≤(B:ℝ) at hb
    exact_mod_cast hb
  have hInjective : Function.Injective (fun i => (fun j => (r i j:ℝ))) := by
    intro i j he
    apply enumerate_injective t
    funext field
    have hf := congrFun he field
    dsimp only at hf
    change r i field=r j field
    exact_mod_cast hf
  have hSupport' : ∀ᵐ row ∂(law:Measure (Allocation m)), row∈Set.range (fun i => (fun j => (r i j:ℝ))) := by
    filter_upwards [hSupport,hLaw] with row hr hf
    obtain ⟨q,hq,he⟩ := hr
    have ht : q∈t := Finset.mem_filter.mpr ⟨hq,by rw [← he]; exact hf⟩
    obtain ⟨i,hi⟩ := enumerate_covers t q ht
    refine ⟨i,?_⟩
    change (fun j => (enumerate t i j:ℝ))=row
    rw [hi]
    exact he.symm
  exact GeneralPaperFiniteRationalLaw.realization a B law r hUnit (fun i j => hDen (r i) (hMem i) j)
    hBudget hInjective hSupport' qbar

end Blotto.GeneralPaperFiniteRowSet
