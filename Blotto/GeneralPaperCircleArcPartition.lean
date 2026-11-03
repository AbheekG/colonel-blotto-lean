import Blotto.GeneralPaperCircleFiniteSums

/-! Prefixes of original arc lengths partition the finite circle exactly.
Zero lengths are allowed in these identities. The sums and prefix observer
here are mathematical analysis, not an executed cell enumeration. -/
namespace Blotto.GeneralPaperCircleArcPartition
open GeneralPaperCircleCell GeneralPaperCircleFiniteSums
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

noncomputable def before {g : ℕ} (lengths : Fin g → ℕ) : ℕ → ℕ
  | 0 => 0
  | c+1 => before lengths c+if h:c<g then lengths ⟨c,h⟩ else 0

theorem before_step {g : ℕ} (lengths : Fin g → ℕ) (c : ℕ) (hc : c<g) :
    before lengths (c+1)=before lengths c+lengths ⟨c,hc⟩ := by
  rw [before,dite_eq_left hc]

theorem before_sum {g : ℕ} (lengths : Fin g → ℕ) (c : ℕ) (hc : c≤g) :
    before lengths c=∑ i:Fin c,lengths ⟨i.val,by omega⟩ := by
  induction c with
  | zero => simp only [before,Finset.univ_eq_empty,Finset.sum_empty]
  | succ c ih =>
    rw [before_step lengths c (by omega),ih (by omega),Fin.sum_univ_castSucc]
    rfl

theorem before_total {g : ℕ} (lengths : Fin g → ℕ) : before lengths g=∑ i,lengths i := before_sum lengths g le_rfl

theorem partition_prefix {g : ℕ} (lengths : Fin g → ℕ) (shift : ℕ) (f : ℕ → ℝ) (c : ℕ) (hc : c≤g) :
    (∑ j:Fin c,∑ r:Fin (lengths ⟨j.val,by omega⟩),f (shift+before lengths j.val+r.val))=
      ∑ t∈Finset.range (before lengths c),f (shift+t) := by
  induction c with
  | zero => simp only [before,Finset.univ_eq_empty,Finset.sum_empty,Finset.range_zero]
  | succ c ih =>
    rw [Fin.sum_univ_castSucc,before_step lengths c (by omega)]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [ih (by omega),Fin.sum_univ_eq_sum_range (fun r => f (shift+before lengths c+r)) (lengths ⟨c,by omega⟩),
      Finset.sum_range_add]
    simp only [Nat.add_assoc]

theorem partition {g : ℕ} (lengths : Fin g → ℕ) (shift : ℕ) (f : ℕ → ℝ) :
    (∑ j,∑ r:Fin (lengths j),f (shift+before lengths j.val+r.val))=
      ∑ t∈Finset.range (∑ j,lengths j),f (shift+t) := by
  have h := partition_prefix lengths shift f g le_rfl
  rw [before_total] at h
  exact h

theorem partition_cells {g : ℕ} (lengths : Fin g → ℕ) (D : ℕ) (hD : 0<D)
    (hs : ∑ j,lengths j=D) (shift : ℕ) (f : Fin D → ℝ) :
    (∑ j,∑ r:Fin (lengths j),f (cell D hD shift (before lengths j.val+r.val)))=
      ∑ t:Fin D,f (cell D hD shift t.val) := by
  have h := partition lengths shift (fun t => f ⟨t%D,Nat.mod_lt _ hD⟩)
  rw [hs] at h
  calc
    _ = ∑ t∈Finset.range D,f (cell D hD shift t) := by
      simpa only [cell,Nat.add_assoc] using h
    _ = _ := (Fin.sum_univ_eq_sum_range (fun t => f (cell D hD shift t)) D).symm

theorem arc_total {g : ℕ} (lengths : Fin g → ℕ) (R W : ℕ) (hR : 0<R) (hW : 0<W)
    (hs : ∑ j,lengths j=R*W) (shift : ℕ) (x : Fin R → ℝ) (hx : Monotone x) :
    (∑ j,(lengths j:ℝ)*x (choice R W hR hW (cell (R*W) (Nat.mul_pos hR hW) shift (before lengths j.val)) (lengths j)))≤
      (W:ℝ)*∑ a:Fin R,x a := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun j _ =>
    arc_sum R W hR hW x hx (cell (R*W) (Nat.mul_pos hR hW) shift (before lengths j.val)) (lengths j))
  simp_rw [cell_prefix] at h
  rw [partition_cells lengths (R*W) (Nat.mul_pos hR hW) hs shift (fun c => x (bin R W hW c)),
    rotated_bins R W hR hW shift x] at h
  exact h

end Blotto.GeneralPaperCircleArcPartition
