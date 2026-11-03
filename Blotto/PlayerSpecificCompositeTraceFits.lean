import Blotto.PlayerSpecificReadOnlyTraceFits

/-! Actual operand/control width bounds for dense multiplication and
differentiation, including recursively shifted and copied intermediates. -/
namespace Blotto.PlayerSpecificCompositeTraceFits
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificDenseTraceFits
set_option autoImplicit false
set_option maxHeartbeats 6000000

def height (H N : ℕ) : ℕ := (2*H+2)*(N+1)
def width (H N : ℕ) : ℕ := 4*height H N+2*N+16

theorem height_ge (H N : ℕ) : 2*H+1≤height H N := by
  have h := Nat.mul_le_mul_left (2*H+2) (show 1≤N+1 by omega)
  unfold height
  omega

theorem multiply_value_height (p q : Data) (H N : ℕ) (hp : HasHeight p H) (hq : HasHeight q H) (hlen : p.length≤N) :
    HasHeight (PlayerSpecificDenseExecution.multiply p q).1 (height H N) := by
  rw [PlayerSpecificDenseExecution.multiply_value]
  apply mono (multiply_height hp hq)
  exact Nat.mul_le_mul (by omega) (Nat.add_le_add_right hlen 1)

theorem derivative_value_height (p : Data) (H N : ℕ) (hp : HasHeight p H) (hlen : p.length≤N) :
    HasHeight (PlayerSpecificDenseExecution.derivative p).1 (height H N) := by
  rw [PlayerSpecificDenseExecution.derivative_value]
  apply mono (derivative_height hp)
  exact Nat.mul_le_mul (by omega) (Nat.add_le_add_right hlen 1)

theorem multiply_fits (p q : Data) (H N : ℕ) (hp : HasHeight p H) (hq : HasHeight q H)
    (hpl : p.length≤N) (hql : q.length≤N) : Fits (width H N) (PlayerSpecificDenseExecution.multiply p q).2 := by
  have hG := height_ge H N
  have hGP : 1≤height H N := by omega
  have hW : 1+2*height H N≤width H N := by unfold width; omega
  have hN : 2*N+2+1≤width H N := by unfold width; omega
  induction p with
  | nil =>
    have hcopy := copyRow_fits (width H N) q
      (fun r hr => (rationalWordWidth_of_height (hq r hr)).trans (by unfold width; omega)) (by unfold width; omega)
    have hc : Fits (width H N) [.control 0] := by
      intro e he
      have he' := List.mem_singleton.mp he
      subst e
      exact (control_width 0).trans (by unfold width; omega)
    apply finish_fits [] _ (width H N) (height H N) (2*N+2) (nil_height _) (by simp only [List.length_nil]; omega) hW hN
    exact (fits_append _ _ _).mpr ⟨hcopy,hc⟩
  | cons a p ih =>
    have hpt := tail_height hp
    have hptl : p.length≤N := by simp only [List.length_cons] at hpl; omega
    have ht := ih hpt hptl
    have hs := fits_mono (PlayerSpecificDenseTraceFits.scale_fits a q H N (head_height hp) hq hql)
      (show PlayerSpecificDenseTraceFits.width H N≤width H N by unfold PlayerSpecificDenseTraceFits.width width; omega)
    have htail := multiply_value_height p q H N hpt hq hptl
    have htaillen : (PlayerSpecificDenseExecution.multiply p q).1.length≤2*N := by
      rw [PlayerSpecificDenseExecution.multiply_value]
      exact (PlayerSpecificDensePolynomial.multiply_length p q).trans (by omega)
    have hshift := fits_mono (PlayerSpecificReadOnlyTraceFits.shift_fits (PlayerSpecificDenseExecution.multiply p q).1
      (height H N) (2*N) htail hGP htaillen)
      (show PlayerSpecificReadOnlyTraceFits.width (height H N) (2*N)≤width H N by
        unfold PlayerSpecificReadOnlyTraceFits.width width; omega)
    have hscaled : HasHeight (PlayerSpecificDenseExecution.scale a q).1 (height H N) := by
      rw [PlayerSpecificDenseExecution.scale_value]
      exact mono (scale_height (head_height hp) hq) (by omega)
    have hscaledlen : (PlayerSpecificDenseExecution.scale a q).1.length≤2*N+2 := by
      rw [PlayerSpecificDenseExecution.scale_value,PlayerSpecificDensePolynomial.scale_length]
      omega
    have hshifted : HasHeight (PlayerSpecificDenseExecution.shift (PlayerSpecificDenseExecution.multiply p q).1).1 (height H N) := by
      rw [PlayerSpecificDenseExecution.shift_value]
      exact shift_height htail hGP
    have hshiftlen : (PlayerSpecificDenseExecution.shift (PlayerSpecificDenseExecution.multiply p q).1).1.length≤2*N+2 := by
      rw [PlayerSpecificDenseExecution.shift_value]
      change (PlayerSpecificDenseExecution.multiply p q).1.length+1≤_
      omega
    have ha := fits_mono (add_fits _ _ (height H N) (2*N+2) hscaled hshifted hscaledlen hshiftlen)
      (show PlayerSpecificDenseTraceFits.width (height H N) (2*N+2)≤width H N by unfold PlayerSpecificDenseTraceFits.width width; omega)
    have hc := controls_fits (width H N) [p.length+1] (by
      intro n hn
      have he := List.mem_singleton.mp hn
      subst n
      unfold width; omega)
    have hout := multiply_value_height (a::p) q H N hp hq hpl
    have holen : (PlayerSpecificDenseExecution.multiply (a::p) q).1.length≤2*N+2 := by
      rw [PlayerSpecificDenseExecution.multiply_value]
      exact (PlayerSpecificDensePolynomial.multiply_length (a::p) q).trans (by omega)
    apply finish_fits _ _ (width H N) (height H N) (2*N+2) hout holen hW hN
    simpa only [fits_append,List.map_cons,List.map_nil] using
      And.intro (And.intro (And.intro (And.intro hc hs) ht) hshift) ha

theorem derivative_fits (p : Data) (H N : ℕ) (hp : HasHeight p H) (hpl : p.length≤N) :
    Fits (width H N) (PlayerSpecificDenseExecution.derivative p).2 := by
  have hG := height_ge H N
  have hGP : 1≤height H N := by omega
  have hW : 1+2*height H N≤width H N := by unfold width; omega
  have hN : 2*N+2+1≤width H N := by unfold width; omega
  induction p with
  | nil =>
    apply finish_fits [] _ (width H N) (height H N) (2*N+2) (nil_height _) (by simp only [List.length_nil]; omega) hW hN
    exact controls_fits _ [0] (by intro n hn; have he:=List.mem_singleton.mp hn; subst n; unfold width; omega)
  | cons a p ih =>
    have hpt := tail_height hp
    have hptl : p.length≤N := by simp only [List.length_cons] at hpl; omega
    have ht := ih hpt hptl
    have htail := derivative_value_height p H N hpt hptl
    have htaillen : (PlayerSpecificDenseExecution.derivative p).1.length≤N := by
      rw [PlayerSpecificDenseExecution.derivative_value]
      exact (PlayerSpecificDensePolynomial.derivative_length p).trans hptl
    have hshift := fits_mono (PlayerSpecificReadOnlyTraceFits.shift_fits (PlayerSpecificDenseExecution.derivative p).1
      (height H N) N htail hGP htaillen)
      (show PlayerSpecificReadOnlyTraceFits.width (height H N) N≤width H N by unfold PlayerSpecificReadOnlyTraceFits.width width; omega)
    have hshifted : HasHeight (PlayerSpecificDenseExecution.shift (PlayerSpecificDenseExecution.derivative p).1).1 (height H N) := by
      rw [PlayerSpecificDenseExecution.shift_value]
      exact shift_height htail hGP
    have hshiftlen : (PlayerSpecificDenseExecution.shift (PlayerSpecificDenseExecution.derivative p).1).1.length≤2*N+2 := by
      rw [PlayerSpecificDenseExecution.shift_value]
      change (PlayerSpecificDenseExecution.derivative p).1.length+1≤_
      omega
    have ha := fits_mono (add_fits p _ (height H N) (2*N+2) (mono hpt (by omega)) hshifted (by omega) hshiftlen)
      (show PlayerSpecificDenseTraceFits.width (height H N) (2*N+2)≤width H N by unfold PlayerSpecificDenseTraceFits.width width; omega)
    have hc : Fits (width H N) [.copy a,.control (p.length+1)] := by
      intro e he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl | rfl
      · exact (rationalWordWidth_of_height (head_height hp)).trans (by unfold width; omega)
      · exact (control_width _).trans (by unfold width; omega)
    have hout := derivative_value_height (a::p) H N hp hpl
    have holen : (PlayerSpecificDenseExecution.derivative (a::p)).1.length≤2*N+2 := by
      rw [PlayerSpecificDenseExecution.derivative_value]
      exact (PlayerSpecificDensePolynomial.derivative_length (a::p)).trans (by omega)
    apply finish_fits _ _ (width H N) (height H N) (2*N+2) hout holen hW hN
    simpa only [fits_append] using And.intro (And.intro (And.intro hc ht) hshift) ha

end Blotto.PlayerSpecificCompositeTraceFits
