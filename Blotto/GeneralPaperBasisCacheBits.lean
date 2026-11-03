import Blotto.GeneralPaperBasisCacheBitFacts

/-! Complete native cached determinant/adjugate update with actual bit
prices. Every raw product/Schur/entry operand is charged, exact divisions
follow from validity, and no determinant or inverse is recomputed.
-/
namespace Blotto.GeneralPaperBasisCacheBits
open GeneralPaperBasisStoredProducts GeneralPaperBasisStoredCorrect GeneralPaperIntegerPrimitivePrice
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def run {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (D : ℤ) (A : IntMatrix n) (u v : Vector n) (a : ℤ) : GeneralPaperBasisStoredStep.Result n :=
  let au := GeneralPaperBasisProductBits.mulVecRun primitive W A u
  let va := GeneralPaperBasisProductBits.rowRun primitive W v A
  let dot := GeneralPaperIntegerDotPrice.run primitive W v.read au.1.read
  let product := a*D
  let Dnext := product-dot.value
  let matrix := GeneralPaperBasisUpdateBits.run primitive W D Dnext A au.1 va.1
  ⟨Dnext,matrix.1,au.2+va.2+dot.work+matrix.2+32*W+
    binary primitive (fun x y => x*y) a D+binary primitive (fun x y => x-y) product dot.value⟩

theorem determinant_data {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (D : ℤ) (A : IntMatrix n) (u v : Vector n) (a : ℤ) :
    (run primitive W D A u v a).determinant=(GeneralPaperBasisStoredStep.run D A u v a).determinant := by
  simp only [run,GeneralPaperBasisStoredStep.run,GeneralPaperIntegerDotPrice.data,GeneralPaperBasisProductBits.mulVec_data]

theorem adjugate_data {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (D : ℤ) (A : IntMatrix n) (u v : Vector n) (a : ℤ) :
    (run primitive W D A u v a).adjugate=(GeneralPaperBasisStoredStep.run D A u v a).adjugate := by
  simp only [run,GeneralPaperBasisStoredStep.run,GeneralPaperIntegerDotPrice.data,GeneralPaperBasisProductBits.mulVec_data,
    GeneralPaperBasisProductBits.row_data,GeneralPaperBasisUpdateBits.data]

theorem work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W H B : ℕ)
    (hW : 1≤W) (hN : binaryWordWidth (n+2)≤W) (D : ℤ) (A : IntMatrix n) (base : Matrix (Fin n) (Fin n) ℤ)
    (u v : Vector n) (a : ℤ) (hValid : Valid D A base) (hNonzero : D≠0)
    (hNewNonzero : (GeneralPaperBasisStoredStep.run D A u v a).determinant≠0)
    (hD : D.natAbs≤H) (hA : ∀ i k,((A.read i).read k).natAbs≤H)
    (hu : ∀ i,(u.read i).natAbs≤B) (hv : ∀ i,(v.read i).natAbs≤B) (ha : a.natAbs≤B) :
    (run primitive W D A u v a).work≤4096*(n+2)^2*(W+primitive (GeneralPaperBasisCacheBitFacts.width n H B)) := by
  let U := n*H*B
  let V := n*B*H
  let L := GeneralPaperBasisUpdateOperandSize.nextBound n H B
  let Q := primitive (GeneralPaperBasisCacheBitFacts.width n H B)
  let au := GeneralPaperBasisProductBits.mulVecRun primitive W A u
  let va := GeneralPaperBasisProductBits.rowRun primitive W v A
  let dot := GeneralPaperIntegerDotPrice.run primitive W v.read au.1.read
  let Dnext := a*D-dot.value
  let C := B+H+L+1
  have hAU (i) : (au.1.read i).natAbs≤U := by rw [GeneralPaperBasisProductBits.mulVec_data]; exact GeneralPaperStoredProductSize.mulVec A u H B hA hu i
  have hVA (i) : (va.1.read i).natAbs≤V := by rw [GeneralPaperBasisProductBits.row_data]; exact GeneralPaperStoredProductSize.row v A B H hv hA i
  have hNext : Dnext.natAbs≤L := by
    change (run primitive W D A u v a).determinant.natAbs≤L
    rw [determinant_data]
    exact GeneralPaperBasisUpdateOperandSize.determinant D A u v a H B hD hA hu hv ha
  have hExact (i k) : D∣Dnext*(A.read i).read k+au.1.read i*va.1.read k := by
    change D∣(run primitive W D A u v a).determinant*(A.read i).read k+au.1.read i*va.1.read k
    rw [determinant_data,GeneralPaperBasisProductBits.mulVec_data,GeneralPaperBasisProductBits.row_data]
    exact GeneralPaperBasisCacheBitFacts.exact_numerators D A base u v a hValid hNonzero hNewNonzero i k
  have hDot : dot.value.natAbs≤n*B*U := by
    change (GeneralPaperIntegerDotPrice.run primitive W v.read au.1.read).value.natAbs≤_
    rw [GeneralPaperIntegerDotPrice.data]
    exact GeneralPaperIntegerDotSize.run_bound v.read au.1.read B U hv hAU
  have hProduct : (a*D).natAbs≤B*H := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul ha hD
  have hProdL : B*H≤L := Nat.le_add_right _ _
  have hDotL : n*B*U≤L := Nat.le_add_left _ _
  have hBC : B≤C := by dsimp only [C]; omega
  have hHC : H≤C := by dsimp only [C]; omega
  have hLC : L≤C := by dsimp only [C]; omega
  have hMul := binary_le primitive hMono (fun x y => x*y) a D C (ha.trans hBC) (hD.trans hHC) ((hProduct.trans hProdL).trans hLC)
  have hSub := binary_le primitive hMono (fun x y => x-y) (a*D) dot.value C
    ((hProduct.trans hProdL).trans hLC) ((hDot.trans hDotL).trans hLC) (hNext.trans hLC)
  have hw := GeneralPaperBasisCacheBitFacts.component_widths n H B
  have hN' : binaryWordWidth (n+1)≤W := (binaryWordWidth_mono (by omega : n+1≤n+2)).trans hN
  have hAu := (GeneralPaperBasisProductBits.mulVec_work primitive hMono W H B hW hN' A u hA hu).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hMono hw.1) W))
  have hVa := (GeneralPaperBasisProductBits.row_work primitive hMono W B H hW hN' v A hv hA).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hMono hw.2.1) W))
  have hDotWork := (GeneralPaperIntegerDotPrice.work primitive hMono W B U v.read au.1.read hv hAU).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hMono hw.2.2.1) W))
  have hMatrix := (GeneralPaperBasisUpdateBits.work primitive hMono W H U V L hW hN D Dnext A au.1 va.1
    hD hNext hA hAU hVA hExact).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hMono hw.2.2.2.1) W))
  have hDelta := hMono hw.2.2.2.2
  change au.2≤512*(n+1)^2*(W+Q) at hAu
  change va.2≤512*(n+1)^2*(W+Q) at hVa
  change dot.work≤128*(n+1)*(W+Q) at hDotWork
  change _≤512*(n+2)^2*(W+Q) at hMatrix
  change primitive (1+binaryWordWidth C)≤Q at hDelta
  change au.2+va.2+dot.work+(GeneralPaperBasisUpdateBits.run primitive W D Dnext A au.1 va.1).2+32*W+
    binary primitive (fun x y => x*y) a D+binary primitive (fun x y => x-y) (a*D) dot.value≤4096*(n+2)^2*(W+Q)
  nlinarith only [hAu,hVa,hDotWork,hMatrix,hMul,hSub,hDelta,Nat.zero_le (n*W),Nat.zero_le (n*Q)]

end Blotto.GeneralPaperBasisCacheBits
