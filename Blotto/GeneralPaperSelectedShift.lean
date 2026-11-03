import Blotto.GeneralPaperNativeCircleSourcePair

/-! Exact midpoint-cell shifts from the paper. Labels are retained even
when their cells coincide. Divisions here specify erased mathematical
semantics; the priced native arithmetic implementation remains separate. -/
namespace Blotto.GeneralPaperSelectedShift
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable def selected (D S : ℕ) (hD : 0<D) (hS : 0<S) (l : Fin S) : Fin D :=
  ⟨((2*l.val+1)*D)/(2*S),by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0<2*S)).mpr
    have hl := l.isLt
    nlinarith only [hl,hD]⟩

theorem selected_prefix (D S : ℕ) (hD : 0<D) (hS : 0<S) (l : Fin S) (A : ℕ) :
    (selected D S hD hS l).val<A ↔ (2*l.val+1)*D<2*S*A := by
  unfold selected
  dsimp only
  rw [Nat.div_lt_iff_lt_mul (by omega : 0<2*S)]
  rw [Nat.mul_comm A (2*S)]

noncomputable def center (D S : ℕ) (hD : 0<D) (hS : 0<S) (l : Fin S) : ℝ :=
  ((selected D S hD hS l).val+1/2:ℝ)/D

theorem center_interior (D S : ℕ) (hD : 0<D) (hS : 0<S) (l : Fin S) :
    ((selected D S hD hS l).val:ℝ)/D<center D S hD hS l ∧
      center D S hD hS l<((selected D S hD hS l).val+1:ℝ)/D := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  unfold center
  constructor <;> apply (div_lt_div_iff_of_pos_right hd).mpr <;> linarith

theorem center_bounds (D S : ℕ) (hD : 0<D) (hS : 0<S) (l : Fin S) :
    0<center D S hD hS l ∧ center D S hD hS l<1 := by
  have hi := center_interior D S hD hS l
  have hn : ((selected D S hD hS l).val:ℝ)+1≤D := by exact_mod_cast (selected D S hD hS l).isLt
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  constructor
  · exact (div_nonneg (Nat.cast_nonneg _) hd.le).trans_lt hi.1
  · exact hi.2.trans_le ((div_le_one hd).mpr hn)

end Blotto.GeneralPaperSelectedShift
