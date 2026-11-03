import Blotto.PlayerSpecificCompositeTraceLength

/-! Actual scalar/copy/control widths for traced dense addition and scaling.
All intermediate bounds follow from the numerical input heights and lengths. -/
namespace Blotto.PlayerSpecificDenseTraceFits
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

def width (H N : ℕ) : ℕ := 4*H+N+8

theorem width_pos (H N : ℕ) : 1≤width H N := by unfold width; omega

theorem finish_fits (row : Data) (pre : Trace) (W H N : ℕ) (hrow : HasHeight row H) (hlen : row.length≤N)
    (hW : 1+2*H≤W) (hN : N+1≤W) (hpre : Fits W pre) :
    Fits W (PlayerSpecificDenseExecution.finish row pre).2 := by
  apply (fits_append W pre (copyRow row)).mpr
  exact ⟨hpre,copyRow_fits W row (fun q hq => (rationalWordWidth_of_height (hrow q hq)).trans hW)
    ((Nat.add_le_add_right hlen 1).trans hN)⟩

theorem controls_fits (W : ℕ) (words : List ℕ) (h : ∀ n∈words,n+1≤W) : Fits W (words.map Event.control) := by
  intro e he
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp he
  exact (control_width n).trans (h n hn)

theorem add_fits (p q : Data) (H N : ℕ) (hp : HasHeight p H) (hq : HasHeight q H)
    (hpl : p.length≤N) (hql : q.length≤N) : Fits (width H N) (PlayerSpecificDenseExecution.add p q).2 := by
  have hW : 1+2*(H+H+1)≤width H N := by unfold width; omega
  have hN : N+1≤width H N := by unfold width; omega
  induction p generalizing q with
  | nil =>
    apply finish_fits q _ (width H N) (H+H+1) N (mono hq (by omega)) hql hW hN
    have hc := controls_fits (width H N) [0,q.length] (by
      intro n hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl | rfl <;> unfold width <;> omega)
    exact hc
  | cons a p ih =>
    cases q with
    | nil =>
      apply finish_fits (a::p) _ (width H N) (H+H+1) N (mono hp (by omega)) hpl hW hN
      exact controls_fits _ [(a::p).length,0] (by
        intro n hn
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
        rcases hn with rfl | rfl <;> unfold width <;> omega)
    | cons b q =>
      have ht := ih q (tail_height hp) (tail_height hq)
        (by simp only [List.length_cons] at hpl; omega) (by simp only [List.length_cons] at hql; omega)
      have hs := fits_mono (scalar_fits_height .add a b H (head_height hp) (head_height hq))
        (show 4*H+3≤width H N by unfold width; omega)
      have hc := controls_fits (width H N) [p.length+1,q.length+1] (by
        intro n hn
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
        rcases hn with rfl | rfl <;> simp only [List.length_cons] at hpl hql <;> unfold width <;> omega)
      have hv : HasHeight (PlayerSpecificDenseExecution.add (a::p) (b::q)).1 (H+H+1) := by
        rw [PlayerSpecificDenseExecution.add_value]
        exact add_height hp hq
      have hl : (PlayerSpecificDenseExecution.add (a::p) (b::q)).1.length≤N := by
        rw [PlayerSpecificDenseExecution.add_value,PlayerSpecificDensePolynomial.add_length]
        exact max_le hpl hql
      apply finish_fits _ _ (width H N) _ N hv hl hW hN
      simpa only [fits_append,List.map_cons,List.map_nil] using And.intro (And.intro hc hs) ht

theorem scale_fits (a : ℚ) (p : Data) (H N : ℕ) (ha : RationalHeight a H) (hp : HasHeight p H)
    (hlen : p.length≤N) : Fits (width H N) (PlayerSpecificDenseExecution.scale a p).2 := by
  have hW : 1+2*(H+H)≤width H N := by unfold width; omega
  have hN : N+1≤width H N := by unfold width; omega
  induction p with
  | nil =>
    apply finish_fits [] _ (width H N) (H+H) N (nil_height _) (by simp only [List.length_nil]; omega) hW hN
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact (rationalWordWidth_of_height ha).trans (by unfold width; omega)
    · exact width_pos H N
  | cons b p ih =>
    have ht := ih (tail_height hp) (by simp only [List.length_cons] at hlen; omega)
    have hs := fits_mono (scalar_fits_height .multiply a b H ha (head_height hp))
      (show 4*H+3≤width H N by unfold width; omega)
    have hc := controls_fits (width H N) [p.length+1] (by
      intro n hn
      have he := List.mem_singleton.mp hn
      subst n
      simp only [List.length_cons] at hlen
      unfold width; omega)
    have hv : HasHeight (PlayerSpecificDenseExecution.scale a (b::p)).1 (H+H) := by
      rw [PlayerSpecificDenseExecution.scale_value]
      exact scale_height ha hp
    have hl : (PlayerSpecificDenseExecution.scale a (b::p)).1.length≤N := by
      rw [PlayerSpecificDenseExecution.scale_value,PlayerSpecificDensePolynomial.scale_length]
      exact hlen
    apply finish_fits _ _ (width H N) _ N hv hl hW hN
    simpa only [fits_append,List.map_cons,List.map_nil] using And.intro (And.intro hc hs) ht

end Blotto.PlayerSpecificDenseTraceFits
