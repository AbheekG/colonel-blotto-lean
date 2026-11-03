import Blotto.PlayerSpecificSweepExecution

/-! State/field copies and primitive sweep operations have bounded source
words at actual input heights. Every control/list-length word is included. -/
namespace Blotto.PlayerSpecificSweepTraceFits
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalSweepHeights
open PlayerSpecificSweep PlayerSpecificRationalTrace PlayerSpecificSweepExecution
set_option autoImplicit false
set_option maxHeartbeats 2000000

def width (T N : ℕ) : ℕ := 128*(T+N+1)

theorem copy_state_fits (s : State ℚ) (T W : ℕ) (hs : StateHeight s T) (hW : 1+2*T≤W) (hcontrol : 6≤W) :
    Fits W (copyState s) := by
  have hp : HasHeight [s.coefficients.A1,s.coefficients.A2,s.coefficients.B1,s.coefficients.B2,s.prefixMax] T :=
    cons_height hs.1 (cons_height hs.2.1 (cons_height hs.2.2.1
      (cons_height hs.2.2.2.1 (cons_height hs.2.2.2.2 (nil_height _)))))
  exact copyRow_fits W _ (fun q hq => (rationalWordWidth_of_height (hp q hq)).trans hW) hcontrol

theorem copy_fields_fits (fields : List (ℚ×ℚ)) (T W : ℕ) (hf : FieldsHeight fields T)
    (hW : 1+2*T≤W) (hcontrol : fields.length+1≤W) (hpair : 3≤W) : Fits W (copyFields fields) := by
  rw [copyFields,fits_append]
  constructor
  · intro e he
    have heq:=List.mem_singleton.mp he
    subst e
    exact (PlayerSpecificRationalTrace.control_width _).trans hcontrol
  · intro e he
    obtain ⟨x,hx,hevent⟩:=List.mem_flatMap.mp he
    have hh:=hf x hx
    have hrow : HasHeight [x.1,x.2] T := cons_height hh.1 (cons_height hh.2 (nil_height _))
    exact copyRow_fits W _ (fun q hq => (rationalWordWidth_of_height (hrow q hq)).trans hW) hpair e hevent

theorem initial_height (fields : List (ℚ×ℚ)) (N H : ℕ) (hf : FieldsHeight fields H)
    (hn : fields.length≤N) (hH : 1≤H) : StateHeight (PlayerSpecificSweepExecution.initial fields).1 (initialBound N H) := by
  rw [initial_value]
  apply state_mono _ _ _ (PlayerSpecificRationalSweepHeights.initial_height fields H hf hH)
  unfold initialBound
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hn 1)) 1

theorem initial_width (N H : ℕ) : H≤ initialBound N H ∧ 3*H≤ initialBound N H ∧
    4*initialBound N H+3≤width (initialBound N H) N ∧ N+1≤width (initialBound N H) N := by
  have hm:=Nat.mul_le_mul_left (3*H+1) (show 1≤N+1 by omega)
  unfold initialBound width at *
  omega

end Blotto.PlayerSpecificSweepTraceFits
