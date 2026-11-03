import Blotto.GeneralPaperIntegerDotPrice

/-! Actual integer matrix/vector products with bit-sensitive dots and
linear indexed reference construction. Every dot and stored result executes
once. Native global reference/control capacities remain separate obligations.
-/
namespace Blotto.GeneralPaperBasisProductBits
open GeneralPaperBasisStoredProducts
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6000000

def materialize {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (f g : Fin n → Fin n → ℤ) : Vector n × ℕ :=
  PaperIndexedArrayConstruction.run (fun w => w) W (fun i =>
    let dot := GeneralPaperIntegerDotPrice.run primitive W (f i) (g i)
    (dot.value,dot.work+4*W))

theorem materialize_data {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (f g : Fin n → Fin n → ℤ) :
    (materialize primitive W f g).1=FixedArrayTable.ofFn (fun i => (GeneralPaperBasisIntegerDot.run (f i) (g i)).value) := by
  simp only [materialize,PaperIndexedArrayConstruction.run_data,GeneralPaperIntegerDotPrice.data]

theorem materialize_work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W X Y : ℕ)
    (hW : 1≤W) (hN : binaryWordWidth (n+1)≤W) (f g : Fin n → Fin n → ℤ)
    (hf : ∀ i j,(f i j).natAbs≤X) (hg : ∀ i j,(g i j).natAbs≤Y) :
    (materialize primitive W f g).2≤512*(n+1)^2*(W+primitive (1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap n X Y))) := by
  let P := primitive (1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap n X Y))
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    Nat.add_le_add_right (GeneralPaperIntegerDotPrice.work primitive hMono W X Y (f i) (g i) (hf i) (hg i)) (4*W))
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fun i : Fin n => ((GeneralPaperIntegerDotPrice.run primitive W (f i) (g i)).value,
      (GeneralPaperIntegerDotPrice.run primitive W (f i) (g i)).work+4*W))
  change (materialize primitive W f g).2≤_ at hh
  have hO : 6*W+10*1*binaryWordWidth (n+1)+28≤44*W := by omega
  have ho := Nat.mul_le_mul_left (n+1) hO
  change _≤n*(128*(n+1)*(W+P)+4*W) at hs
  change _≤512*(n+1)^2*(W+P)
  nlinarith only [hs,hh,ho,Nat.zero_le (n*W),Nat.zero_le (n*P)]

def mulVecRun {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (A : IntMatrix n) (u : Vector n) : Vector n × ℕ :=
  materialize primitive W (fun j k => (A.read j).read k) (fun _ => u.read)

theorem mulVec_data {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (A : IntMatrix n) (u : Vector n) :
    (mulVecRun primitive W A u).1=(GeneralPaperBasisStoredProducts.mulVecRun A u).1 := by
  simp only [mulVecRun,materialize_data,GeneralPaperBasisStoredProducts.mulVecRun,PaperIndexedArrayConstruction.run_data]

theorem mulVec_work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W H U : ℕ)
    (hW : 1≤W) (hN : binaryWordWidth (n+1)≤W) (A : IntMatrix n) (u : Vector n)
    (hA : ∀ j k,((A.read j).read k).natAbs≤H) (hu : ∀ j,(u.read j).natAbs≤U) :
    (mulVecRun primitive W A u).2≤512*(n+1)^2*(W+primitive (1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap n H U))) :=
  materialize_work primitive hMono W H U hW hN _ _ hA (fun _ j => hu j)

def rowRun {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (v : Vector n) (A : IntMatrix n) : Vector n × ℕ :=
  materialize primitive W (fun _ => v.read) (fun k j => (A.read j).read k)

theorem row_data {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (v : Vector n) (A : IntMatrix n) :
    (rowRun primitive W v A).1=(GeneralPaperBasisStoredProducts.rowRun v A).1 := by
  simp only [rowRun,materialize_data,GeneralPaperBasisStoredProducts.rowRun,PaperIndexedArrayConstruction.run_data]

theorem row_work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W V H : ℕ)
    (hW : 1≤W) (hN : binaryWordWidth (n+1)≤W) (v : Vector n) (A : IntMatrix n)
    (hv : ∀ j,(v.read j).natAbs≤V) (hA : ∀ j k,((A.read j).read k).natAbs≤H) :
    (rowRun primitive W v A).2≤512*(n+1)^2*(W+primitive (1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap n V H))) :=
  materialize_work primitive hMono W V H hW hN _ _ (fun _ j => hv j) (fun k j => hA j k)

end Blotto.GeneralPaperBasisProductBits
