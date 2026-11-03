import Blotto.GeneralPaperUnitArrayReprice

/-! Native integer matrix/vector products with unit-price index primitives
in their indexed constructors. Each literal dot product is evaluated once.
-/
namespace Blotto.GeneralPaperBasisProductsWork
open GeneralPaperBasisStoredProducts
set_option autoImplicit false
set_option maxHeartbeats 4500000

def mulVecRun {n : ℕ} (A : IntMatrix n) (u : Vector n) : Vector n × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun j =>
    let dot := GeneralPaperBasisIntegerDot.run (fun k => (A.read j).read k) u.read
    (dot.value,dot.work+4))

theorem mulVec_data {n : ℕ} (A : IntMatrix n) (u : Vector n) :
    (mulVecRun A u).1=(GeneralPaperBasisStoredProducts.mulVecRun A u).1 := by
  simp only [mulVecRun,GeneralPaperBasisStoredProducts.mulVecRun,PaperIndexedArrayConstruction.run_data]

theorem mulVec_work {n : ℕ} (A : IntMatrix n) (u : Vector n) : (mulVecRun A u).2≤256*(n+1)^2 := by
  have hh := GeneralPaperUnitArrayReprice.work 1 (fun j : Fin n =>
    ((GeneralPaperBasisIntegerDot.run (fun k => (A.read j).read k) u.read).value,
      (GeneralPaperBasisIntegerDot.run (fun k => (A.read j).read k) u.read).work+4))
  change (mulVecRun A u).2=(GeneralPaperBasisStoredProducts.mulVecRun A u).2+8*n+2 at hh
  have ho := GeneralPaperBasisStoredProducts.mulVec_work A u
  nlinarith only [hh,ho]

def rowRun {n : ℕ} (v : Vector n) (A : IntMatrix n) : Vector n × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun k =>
    let dot := GeneralPaperBasisIntegerDot.run v.read (fun j => (A.read j).read k)
    (dot.value,dot.work+4))

theorem row_data {n : ℕ} (v : Vector n) (A : IntMatrix n) :
    (rowRun v A).1=(GeneralPaperBasisStoredProducts.rowRun v A).1 := by
  simp only [rowRun,GeneralPaperBasisStoredProducts.rowRun,PaperIndexedArrayConstruction.run_data]

theorem row_work {n : ℕ} (v : Vector n) (A : IntMatrix n) : (rowRun v A).2≤256*(n+1)^2 := by
  have hh := GeneralPaperUnitArrayReprice.work 1 (fun k : Fin n =>
    ((GeneralPaperBasisIntegerDot.run v.read (fun j => (A.read j).read k)).value,
      (GeneralPaperBasisIntegerDot.run v.read (fun j => (A.read j).read k)).work+4))
  change (rowRun v A).2=(GeneralPaperBasisStoredProducts.rowRun v A).2+8*n+2 at hh
  have ho := GeneralPaperBasisStoredProducts.row_work v A
  nlinarith only [hh,ho]

end Blotto.GeneralPaperBasisProductsWork
