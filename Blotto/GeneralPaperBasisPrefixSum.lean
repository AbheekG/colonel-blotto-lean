import Blotto.GeneralPaperBasisDenseRow

/-! Exact initial-coordinate sum decomposition. The executable embedding
is the original index value; no coordinate inverse or integer quotient
occurs in point/direction evaluation.
-/
namespace Blotto.GeneralPaperBasisPrefixSum
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

def embed {j d : ℕ} (h : j≤d) (i : Fin j) : Fin d := ⟨i.val,i.isLt.trans_le h⟩

theorem prefix_sum {j d : ℕ} (h : j≤d) (f : Fin d → ℝ) :
    (∑ k : Fin d,if k.val<j then f k else 0)=∑ i : Fin j,f (embed h i) := by
  rw [←Finset.sum_filter]
  refine Finset.sum_bij (fun k hk => (⟨k.val,(Finset.mem_filter.mp hk).2⟩ : Fin j)) ?_ ?_ ?_ ?_
  · intro k _
    exact Finset.mem_univ _
  · intro a _ b _ he
    exact Fin.ext (congrArg (fun q : Fin j => q.val) he)
  · intro i _
    refine ⟨embed h i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.isLt⟩,?_⟩
    apply Fin.ext
    rfl
  · intro k _
    congr 1

theorem split_sum {j d : ℕ} (h : j≤d) (f : Fin d → ℝ) :
    (∑ k : Fin d,f k)=(∑ i : Fin j,f (embed h i))+(∑ k : Fin d,if j≤k.val then f k else 0) := by
  rw [←prefix_sum h,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.val<j
  · have hn : ¬j≤k.val := by omega
    simp only [hk,hn,ite_true,ite_false,add_zero]
  · have hj : j≤k.val := by omega
    simp only [hk,hj,ite_true,ite_false,zero_add]

end Blotto.GeneralPaperBasisPrefixSum
