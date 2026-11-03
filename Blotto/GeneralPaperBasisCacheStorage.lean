import Blotto.GeneralPaperBasisUpdateStorage

/-! Complete literal native bordered cache update. The old matrix and
input/product vectors are retained once alongside the two materializers,
Schur dot/scalars, new matrix construction and returned cache. Primitive
scratch prices are local; total work only bounds encoded native fields. -/
namespace Blotto.GeneralPaperBasisCacheStorage
open GeneralPaperBasisStoredProducts GeneralPaperBasisStoredCorrect GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def matrixFootprint {n : ℕ} (W : ℕ) (A : IntMatrix n) : ℕ := arrayFootprint W (arrayFootprint W integerBits) A
def matrixProfile (W n R : ℕ) : ℕ := arrayProfile W n (arrayProfile W n R)
def price (model : RationalCostModel) (W n R : ℕ) : ℕ := 4096*(n+2)^2*(W+model.rat R)
def metadataCap (model : RationalCostModel) (W n R : ℕ) : ℕ := n+2+3*price model W n R
def controls (n W au va dot matrix mul sub total : ℕ) : List ℕ :=
  [n,au,va,dot,matrix,32*W,mul,sub,au+va,au+va+dot,au+va+dot+matrix,
    au+va+dot+matrix+32*W,au+va+dot+matrix+32*W+mul,total]

def window {n : ℕ} (model : RationalCostModel) (W copied outerCopied innerCopied : ℕ)
    (D : ℤ) (A : IntMatrix n) (u v : Vector n) (a : ℤ) : ℕ :=
  let au := GeneralPaperBasisProductBits.mulVecRun model.rat W A u
  let va := GeneralPaperBasisProductBits.rowRun model.rat W v A
  let dot := GeneralPaperIntegerDotPrice.run model.rat W v.read au.1.read
  let product := a*D
  let Dnext := product-dot.value
  let matrix := GeneralPaperBasisUpdateBits.run model.rat W D Dnext A au.1 va.1
  let mul := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x*y) a D
  let sub := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x-y) product dot.value
  let result := GeneralPaperBasisCacheBits.run model.rat W D A u v a
  matrixFootprint W A+arrayFootprint W integerBits u+arrayFootprint W integerBits v+
    arrayFootprint W integerBits au.1+arrayFootprint W integerBits va.1+matrixFootprint W result.adjugate+
    GeneralPaperBasisProductStorage.window model W copied (fun i k => (A.read i).read k) (fun _ => u.read)+
    GeneralPaperBasisProductStorage.window model W copied (fun _ => v.read) (fun k i => (A.read i).read k)+
    GeneralPaperIntegerDotStorage.window model W copied v.read au.1.read+
    GeneralPaperBasisUpdateStorage.window model W outerCopied innerCopied D Dnext A au.1 va.1+
    listFootprint W integerBits [D,a,product,dot.value,Dnext]+mul+sub+
    fields W (controls n W au.2 va.2 dot.work matrix.2 mul sub result.work)+256*W

def profile (model : RationalCostModel) (W n R : ℕ) : ℕ :=
  matrixProfile W n R+4*arrayProfile W n R+matrixProfile W (n+1) R+
    2*GeneralPaperBasisProductStorage.profile model W n R+GeneralPaperIntegerDotStorage.profile model W n R+
    GeneralPaperBasisUpdateStorage.profile model W n R+5*(R+2*W)+32*W+4*model.rat R+
    14*(natBits (metadataCap model W n R)+W)+288*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W copied outerCopied innerCopied H B R : ℕ)
    (hW : 1≤W) (hIndex : binaryWordWidth (n+2)≤W) (D : ℤ) (A : IntMatrix n)
    (base : Matrix (Fin n) (Fin n) ℤ) (u v : Vector n) (a : ℤ)
    (hValid : Valid D A base) (hNonzero : D≠0)
    (hNewNonzero : (GeneralPaperBasisStoredStep.run D A u v a).determinant≠0)
    (hD : D.natAbs≤H) (hA : ∀ i k,((A.read i).read k).natAbs≤H)
    (hu : ∀ i,(u.read i).natAbs≤B) (hv : ∀ i,(v.read i).natAbs≤B) (ha : a.natAbs≤B)
    (hR : GeneralPaperBasisCacheBitFacts.width n H B≤R) :
    window model W copied outerCopied innerCopied D A u v a≤profile model W n R := by
  let U := n*H*B
  let V := n*B*H
  let L := GeneralPaperBasisUpdateOperandSize.nextBound n H B
  let C := B+H+L+1
  let au := GeneralPaperBasisProductBits.mulVecRun model.rat W A u
  let va := GeneralPaperBasisProductBits.rowRun model.rat W v A
  let dot := GeneralPaperIntegerDotPrice.run model.rat W v.read au.1.read
  let Dnext := a*D-dot.value
  let matrix := GeneralPaperBasisUpdateBits.run model.rat W D Dnext A au.1 va.1
  let mul := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x*y) a D
  let sub := GeneralPaperIntegerPrimitivePrice.binary model.rat (fun x y => x-y) (a*D) dot.value
  let result := GeneralPaperBasisCacheBits.run model.rat W D A u v a
  have hAU (i) : (au.1.read i).natAbs≤U := by
    rw [GeneralPaperBasisProductBits.mulVec_data]; exact GeneralPaperStoredProductSize.mulVec A u H B hA hu i
  have hVA (i) : (va.1.read i).natAbs≤V := by
    rw [GeneralPaperBasisProductBits.row_data]; exact GeneralPaperStoredProductSize.row v A B H hv hA i
  have hNext : Dnext.natAbs≤L := by
    change result.determinant.natAbs≤L
    rw [GeneralPaperBasisCacheBits.determinant_data]
    exact GeneralPaperBasisUpdateOperandSize.determinant D A u v a H B hD hA hu hv ha
  have hExact (i k) : D∣Dnext*(A.read i).read k+au.1.read i*va.1.read k := by
    change D∣result.determinant*(A.read i).read k+au.1.read i*va.1.read k
    rw [GeneralPaperBasisCacheBits.determinant_data,GeneralPaperBasisProductBits.mulVec_data,GeneralPaperBasisProductBits.row_data]
    exact GeneralPaperBasisCacheBitFacts.exact_numerators D A base u v a hValid hNonzero hNewNonzero i k
  have hDot : dot.value.natAbs≤n*B*U := by
    rw [GeneralPaperIntegerDotPrice.data]; exact GeneralPaperIntegerDotSize.run_bound v.read au.1.read B U hv hAU
  have hProduct : (a*D).natAbs≤B*H := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul ha hD
  have hProdL : B*H≤L := Nat.le_add_right _ _
  have hDotL : n*B*U≤L := Nat.le_add_left _ _
  have hBC : B≤C := by dsimp only [C]; omega
  have hHC : H≤C := by dsimp only [C]; omega
  have hLC : L≤C := by dsimp only [C]; omega
  have hw := GeneralPaperBasisCacheBitFacts.component_widths n H B
  have wAU := hw.1.trans hR
  have wVA := hw.2.1.trans hR
  have wDot := hw.2.2.1.trans hR
  have wEntry := hw.2.2.2.1.trans hR
  have wDelta := hw.2.2.2.2.trans hR
  have word (z : ℤ) (hz : z.natAbs≤C) : integerBits z≤R :=
    (Nat.add_le_add_left (binaryWordWidth_mono hz) 1).trans wDelta
  have hMul := (GeneralPaperIntegerPrimitivePrice.binary_le model.rat model.monotone (fun x y => x*y) a D C
    (ha.trans hBC) (hD.trans hHC) ((hProduct.trans hProdL).trans hLC)).trans (Nat.mul_le_mul_left 2 (model.monotone wDelta))
  have hSub := (GeneralPaperIntegerPrimitivePrice.binary_le model.rat model.monotone (fun x y => x-y) (a*D) dot.value C
    ((hProduct.trans hProdL).trans hLC) ((hDot.trans hDotL).trans hLC) (hNext.trans hLC)).trans (Nat.mul_le_mul_left 2 (model.monotone wDelta))
  change mul≤2*model.rat R at hMul
  change sub≤2*model.rat R at hSub
  have hJ : binaryWordWidth (n+1)≤W := (binaryWordWidth_mono (show n+1≤n+2 by omega)).trans hIndex
  have hAu := GeneralPaperBasisProductStorage.bounded model W copied H B R
    (fun i k => (A.read i).read k) (fun _ => u.read) hA (fun _ => hu) wAU hW hJ
  have hVa := GeneralPaperBasisProductStorage.bounded model W copied B H R
    (fun _ => v.read) (fun k i => (A.read i).read k) (fun _ => hv) (fun k i => hA i k) wVA hW hJ
  have hDotWindow := GeneralPaperIntegerDotStorage.bounded model W copied B U R v.read au.1.read hv hAU wDot
  have hMatrix := GeneralPaperBasisUpdateStorage.bounded model W outerCopied innerCopied H U V L R D Dnext A au.1 va.1
    hD hNext hA hAU hVA hExact wEntry hW hIndex
  have hOld := GeneralPaperEncodedBasisStorage.array_bound W (arrayProfile W n R) (arrayFootprint W integerBits) A (by
    intro i; exact GeneralPaperEncodedBasisStorage.array_bound W R integerBits (A.read i) (fun k => word _ ((hA i k).trans hHC)))
  have hU := GeneralPaperEncodedBasisStorage.array_bound W R integerBits u (fun i => word _ ((hu i).trans hBC))
  have hV := GeneralPaperEncodedBasisStorage.array_bound W R integerBits v (fun i => word _ ((hv i).trans hBC))
  have hAUOwner := GeneralPaperEncodedBasisStorage.array_bound W R integerBits au.1 (by
    intro i
    dsimp only [au]
    rw [GeneralPaperBasisProductBits.mulVecRun,GeneralPaperBasisProductBits.materialize,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact GeneralPaperBasisProductStorage.result_word model W H B R _ _ (hA i) hu wAU)
  have hVAOwner := GeneralPaperEncodedBasisStorage.array_bound W R integerBits va.1 (by
    intro k
    dsimp only [va]
    rw [GeneralPaperBasisProductBits.rowRun,GeneralPaperBasisProductBits.materialize,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact GeneralPaperBasisProductStorage.result_word model W B H R _ _ hv (fun i => hA i k) wVA)
  have hNew := GeneralPaperEncodedBasisStorage.array_bound W (arrayProfile W (n+1) R) (arrayFootprint W integerBits) matrix.1 (by
    intro j
    dsimp only [matrix]
    rw [GeneralPaperBasisUpdateBits.run,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact GeneralPaperBasisUpdateStorage.row_payload model W H U V L R D Dnext A au.1 va.1 hD hNext hA hAU hVA hExact wEntry j)
  have hScalars := list_bound W R integerBits [D,a,a*D,dot.value,Dnext] (by
    intro z hz; apply word
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl
    · exact hD.trans hHC
    · exact ha.trans hBC
    · exact (hProduct.trans hProdL).trans hLC
    · exact (hDot.trans hDotL).trans hLC
    · exact hNext.trans hLC)
  change listFootprint W integerBits _≤5*(R+2*W)+32*W at hScalars
  have hWork := (GeneralPaperBasisCacheBits.work model.rat model.monotone W H B hW hIndex D A base u v a
    hValid hNonzero hNewNonzero hD hA hu hv ha).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hR) W))
  change result.work≤price model W n R at hWork
  have hShape : result.work=au.2+va.2+dot.work+matrix.2+32*W+mul+sub := rfl
  have hf := fields_bound W (natBits (metadataCap model W n R)) (controls n W au.2 va.2 dot.work matrix.2 mul sub result.work) (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold metadataCap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤14*(natBits (metadataCap model W n R)+W)+32*W at hf
  change matrixFootprint W A≤matrixProfile W n R at hOld
  change matrixFootprint W result.adjugate≤matrixProfile W (n+1) R at hNew
  unfold window profile
  dsimp only
  dsimp only [au,va,dot,Dnext,matrix,mul,sub,result] at hOld hU hV hAUOwner hVAOwner hNew hAu hVa hDotWindow hMatrix hScalars hMul hSub hf
  omega

end Blotto.GeneralPaperBasisCacheStorage
