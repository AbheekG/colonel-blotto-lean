import Blotto.GeneralPaperCircleCell

/-! Exact finite-cell conservation: a cyclic shift permutes the cells,
and each representative bin occupies exactly W cells. These finite sums
are erased proof observers, not an executed enumeration of R*W cells. -/
namespace Blotto.GeneralPaperCircleFiniteSums
open GeneralPaperCircleCell
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem rotation (D : ℕ) (hD : 0<D) (shift : ℕ) (f : Fin D → ℝ) :
    (∑ i:Fin D,f (cell D hD shift i.val))=∑ i:Fin D,f i := by
  let : NeZero D := ⟨hD.ne'⟩
  let a : Fin D := ⟨shift%D,Nat.mod_lt _ hD⟩
  have he : ∀ i:Fin D,(Equiv.addLeft a) i=cell D hD shift i.val := by
    intro i
    apply Fin.ext
    change (shift%D+i.val)%D=(shift+i.val)%D
    exact Nat.mod_add_mod _ _ _
  have h := Equiv.sum_comp (Equiv.addLeft a) f
  simpa only [he] using h

theorem bin_product (R W : ℕ) (hW : 0<W) (i : Fin R) (j : Fin W) :
    bin R W hW (finProdFinEquiv (i,j))=i := by
  apply Fin.ext
  change (j.val+W*i.val)/W=i.val
  rw [Nat.add_mul_div_left _ _ hW,Nat.div_eq_of_lt j.isLt,Nat.zero_add]

theorem bins (R W : ℕ) (hW : 0<W) (x : Fin R → ℝ) :
    (∑ i:Fin (R*W),x (bin R W hW i))=(W:ℝ)*∑ a:Fin R,x a := by
  rw [←Equiv.sum_comp (finProdFinEquiv : Fin R × Fin W ≃ Fin (R*W))]
  rw [Fintype.sum_prod_type]
  simp only [bin_product,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [Finset.mul_sum]

theorem rotated_bins (R W : ℕ) (hR : 0<R) (hW : 0<W) (shift : ℕ) (x : Fin R → ℝ) :
    (∑ i:Fin (R*W),x (bin R W hW (cell (R*W) (Nat.mul_pos hR hW) shift i.val)))=
      (W:ℝ)*∑ a:Fin R,x a := by
  exact (rotation (R*W) (Nat.mul_pos hR hW) shift (fun i => x (bin R W hW i))).trans (bins R W hW x)

theorem cell_prefix (D : ℕ) (hD : 0<D) (shift p r : ℕ) :
    cell D hD (cell D hD shift p).val r=cell D hD shift (p+r) := by
  apply Fin.ext
  change ((shift+p)%D+r)%D=(shift+(p+r))%D
  rw [Nat.mod_add_mod,Nat.add_assoc]

end Blotto.GeneralPaperCircleFiniteSums
