import Blotto.PlayerSpecificDenseTraceFits

/-! Trimming and dyadic-zero padding retain coefficient heights. Subtraction
uses the exact negation bound through its executed scale(-1) stage. -/
namespace Blotto.PlayerSpecificReadOnlyTraceFits
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificDenseTraceFits
set_option autoImplicit false
set_option maxHeartbeats 5000000

def width (H N : ℕ) : ℕ := 2*H+N+8

theorem shift_fits (p : Data) (H N : ℕ) (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤N) :
    Fits (width H N) (PlayerSpecificDenseExecution.shift p).2 := by
  have hW : 1+2*H≤width H N := by unfold width; omega
  have hN : N+2≤width H N := by unfold width; omega
  have hcopy := copyRow_fits (width H N) p
    (fun q hq => (rationalWordWidth_of_height (hp q hq)).trans hW) (by omega)
  have hpre : Fits (width H N) [.control p.length,.copy 0] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact (control_width p.length).trans (by omega)
    · exact (rationalWordWidth_of_height zero_height).trans (by unfold width; omega)
  apply finish_fits (0::p) _ (width H N) H (N+1) (cons_height (zero_height.mono hH) hp)
    (by simp only [List.length_cons]; omega) hW hN
  exact (fits_append _ _ _).mpr ⟨hcopy,hpre⟩

theorem trim_fits (p : Data) (H N : ℕ) (hp : HasHeight p H) (hlen : p.length≤N) :
    Fits (width H N) (PlayerSpecificDenseExecution.trim p).2 := by
  have hW : 1+2*H≤width H N := by unfold width; omega
  have hN : N+1≤width H N := by unfold width; omega
  induction p with
  | nil =>
    apply finish_fits [] _ (width H N) H N (nil_height _) (by simp only [List.length_nil]; omega) hW hN
    exact controls_fits _ [0] (by intro n hn; have he:=List.mem_singleton.mp hn; subst n; omega)
  | cons a p ih =>
    have ht := ih (tail_height hp) (by simp only [List.length_cons] at hlen; omega)
    have hz := equalZero_fits (width H N) a ((rationalWordWidth_of_height (head_height hp)).trans hW)
      ((rationalWordWidth_of_height zero_height).trans (by unfold width; omega)) (by unfold width; omega)
    have htail : (PlayerSpecificDenseExecution.trim p).1.length≤N := by
      rw [PlayerSpecificDenseExecution.trim_value]
      exact (PlayerSpecificDensePolynomial.trim_length p).trans (by simp only [List.length_cons] at hlen; omega)
    have hc := controls_fits (width H N) [(PlayerSpecificDenseExecution.trim p).1.length,1] (by
      intro n hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl | rfl <;> unfold width <;> omega)
    have hv : HasHeight (PlayerSpecificDenseExecution.trim (a::p)).1 H := by
      rw [PlayerSpecificDenseExecution.trim_value]
      exact trim_height hp
    have hl : (PlayerSpecificDenseExecution.trim (a::p)).1.length≤N := by
      rw [PlayerSpecificDenseExecution.trim_value]
      exact (PlayerSpecificDensePolynomial.trim_length (a::p)).trans hlen
    apply finish_fits _ _ (width H N) H N hv hl hW hN
    simpa only [fits_append,List.map_cons,List.map_nil] using And.intro (And.intro ht hz) hc

theorem subtract_fits (p q : Data) (H N : ℕ) (hp : HasHeight p H) (hq : HasHeight q H)
    (hH : 1≤H) (hpl : p.length≤N) (hql : q.length≤N) :
    Fits (PlayerSpecificDenseTraceFits.width H N) (PlayerSpecificDenseExecution.subtract p q).2 := by
  have hminus : RationalHeight (-1:ℚ) H := one_height.neg.mono hH
  have hs := scale_fits (-1) q H N hminus hq hql
  have hneg : HasHeight (PlayerSpecificDenseExecution.scale (-1) q).1 H := by
    rw [PlayerSpecificDenseExecution.scale_value]
    exact negative_height hq
  have hnl : (PlayerSpecificDenseExecution.scale (-1) q).1.length≤N := by
    rw [PlayerSpecificDenseExecution.scale_value,PlayerSpecificDensePolynomial.scale_length]
    exact hql
  have ha := add_fits p (PlayerSpecificDenseExecution.scale (-1) q).1 H N hp hneg hpl hnl
  have hv : HasHeight (PlayerSpecificDenseExecution.subtract p q).1 (H+H+1) := by
    rw [PlayerSpecificDenseExecution.subtract_value]
    exact subtract_height hp hq
  have hl : (PlayerSpecificDenseExecution.subtract p q).1.length≤N := by
    rw [PlayerSpecificDenseExecution.subtract_value,PlayerSpecificDensePolynomial.subtract,
      PlayerSpecificDensePolynomial.add_length,PlayerSpecificDensePolynomial.scale_length]
    exact max_le hpl hql
  apply finish_fits _ _ (PlayerSpecificDenseTraceFits.width H N) (H+H+1) N hv hl
    (by unfold PlayerSpecificDenseTraceFits.width; omega) (by unfold PlayerSpecificDenseTraceFits.width; omega)
  exact (fits_append _ _ _).mpr ⟨hs,ha⟩

end Blotto.PlayerSpecificReadOnlyTraceFits
