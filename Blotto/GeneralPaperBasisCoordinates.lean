import Blotto.GeneralPaperBasisUpdateLedger

/-! Explicit row-major indexing of the d=m(K-1) original variable anchors.
The executed index uses only multiplication and addition. Its inverse is
used in the erased surjectivity proof, not in coordinate reads or writes.
-/
namespace Blotto.GeneralPaperBasisCoordinates
open RationalOrderCell
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

def index {m K : ℕ} (v : Variable m K) : Fin (m*(K-1)) :=
  ⟨v.1.val*(K-1)+v.2.val,by
    have hField := Nat.mul_le_mul_right (K-1) (Nat.succ_le_of_lt v.1.isLt)
    have hLabel := v.2.isLt
    nlinarith⟩

theorem index_injective (m K : ℕ) : Function.Injective (@index m K) := by
  intro a b he
  have hv := congrArg Fin.val he
  change a.1.val*(K-1)+a.2.val=b.1.val*(K-1)+b.2.val at hv
  have hMod := congrArg (fun t => t%(K-1)) hv
  have hModA : (a.1.val*(K-1)+a.2.val)%(K-1)=a.2.val := by
    rw [Nat.add_mod,Nat.mul_mod_left]
    simp only [Nat.zero_add,Nat.mod_eq_of_lt a.2.isLt]
  have hModB : (b.1.val*(K-1)+b.2.val)%(K-1)=b.2.val := by
    rw [Nat.add_mod,Nat.mul_mod_left]
    simp only [Nat.zero_add,Nat.mod_eq_of_lt b.2.isLt]
  rw [hModA,hModB] at hMod
  have hProduct : a.1.val*(K-1)=b.1.val*(K-1) := by omega
  have hp : 0<K-1 := by have hh := a.2.isLt; omega
  have hField := Nat.eq_of_mul_eq_mul_right hp hProduct
  exact Prod.ext (Fin.ext hField) (Fin.ext hMod)

theorem index_surjective (m K : ℕ) : Function.Surjective (@index m K) := by
  intro i
  have hn : 0<K-1 := by
    by_contra h
    have hz : K-1=0 := by omega
    have hd : m*(K-1)=0 := by rw [hz,Nat.mul_zero]
    have hi : i.val<0 := i.isLt.trans_eq hd
    exact Nat.not_lt_zero _ hi
  let field : Fin m := ⟨i.val/(K-1),(Nat.div_lt_iff_lt_mul hn).mpr i.isLt⟩
  let label : Fin (K-1) := ⟨i.val%(K-1),Nat.mod_lt _ hn⟩
  refine ⟨(field,label),Fin.ext ?_⟩
  change i.val/(K-1)*(K-1)+i.val%(K-1)=i.val
  have hh := Nat.mod_add_div i.val (K-1)
  nlinarith only [hh]

noncomputable def equivalence (m K : ℕ) : Variable m K ≃ Fin (m*(K-1)) :=
  Equiv.ofBijective index ⟨index_injective m K,index_surjective m K⟩

theorem sum_index {m K : ℕ} (f : Fin (m*(K-1)) → ℝ) :
    (∑ v : Variable m K,f (index v))=∑ i,f i := by
  exact Fintype.sum_equiv (equivalence m K) _ _ (fun _ => rfl)

end Blotto.GeneralPaperBasisCoordinates
