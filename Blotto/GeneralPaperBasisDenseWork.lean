import Blotto.GeneralPaperBasisPreparationWork

/-! Dense original-row materialization with the zero array's index
primitive charged at unit price. The same dense coefficients/RHS fields
and retained native annotation are returned; the separate execution ledger
includes the exact constructor correction before the sparse scatter.
-/
namespace Blotto.GeneralPaperBasisDenseWork
open RationalOrderCell GeneralPaperBasisDenseRow GeneralPaperAffineConstraintRows
set_option autoImplicit false

def run {m K : ℕ} (r : Row (Variable m K)) : Dense (m*(K-1)) × ℕ :=
  let dense := build r
  (dense,dense.work+8*(m*(K-1))+2)

theorem data {m K : ℕ} (r : Row (Variable m K)) : (run r).1=build r := rfl

theorem zero_index_correction (d : ℕ) :
    (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun _ : Fin d => ((0:ℤ),2))).2=
      (GeneralPaperBasisCoefficientScatter.zeroRun d).2+8*d+2 := GeneralPaperUnitArrayReprice.work _ _

theorem work {m K : ℕ} (r : Row (Variable m K)) :
    (run r).2≤128*(m*(K-1)+1)+24*r.terms.length+16 := by
  have hh := build_work r
  change (build r).work+8*(m*(K-1))+2≤_
  omega

end Blotto.GeneralPaperBasisDenseWork
