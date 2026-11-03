import Blotto.PlayerSpecificMonomialExecution

/-! Actual leading-term construction includes coefficient scanning, degree
control, zero padding and source copies, with input-derived prices. -/
namespace Blotto.PlayerSpecificTermExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 4000000

def run (p q : Data) : Data×Trace :=
  let leading := PlayerSpecificLeadingExecution.readLast p
  let exponent := p.length-q.length
  let result := PlayerSpecificMonomialExecution.run exponent leading.1
  (result.1,copyRow q++[.control p.length,.control q.length,.control exponent]++leading.2++result.2)

theorem value (p q : Data) : (run p q).1=PlayerSpecificPolynomialCancellation.term p q := by
  simp only [run,PlayerSpecificMonomialExecution.value,PlayerSpecificLeadingExecution.readLast_value,
    PlayerSpecificPolynomialCancellation.term]

theorem height (p q : Data) (H : ℕ) (hp : HasHeight p H) (hH : 1≤H) : HasHeight (run p q).1 H := by
  rw [value]
  exact PlayerSpecificCancellationHeights.term_height p q H hp hH

theorem length (p q : Data) : (run p q).1.length=p.length-q.length+1 := by
  rw [value,PlayerSpecificPolynomialCancellation.term,PlayerSpecificCancellationHeights.monomial_length]

theorem length_le (p q : Data) (hp : p≠[]) (hq : q≠[]) : (run p q).1.length≤p.length := by
  rw [value]
  exact PlayerSpecificCancellationHeights.term_length p q hp hq

theorem trace_length (p q : Data) (N : ℕ) (hp : p.length≤N) (hq : q.length≤N) :
    (run p q).2.length≤100*(N+1)^2 := by
  have hr := PlayerSpecificLeadingExecution.readLast_trace_length p
  have hm := PlayerSpecificMonomialExecution.trace_length (p.length-q.length) (PlayerSpecificLeadingExecution.readLast p).1
  have he : p.length-q.length≤N := (Nat.sub_le _ _).trans hp
  have hs := Nat.pow_le_pow_left (Nat.add_le_add_right he 6) 2
  simp only [run,List.length_append,copyRow_length,List.length_cons,List.length_nil]
  nlinarith

def width (H N : ℕ) : ℕ := 2*H+2*N+32

theorem fits (p q : Data) (H N : ℕ) (hp : HasHeight p H) (hq : HasHeight q H)
    (hH : 1≤H) (hpl : p.length≤N) (hql : q.length≤N) : Fits (width H N) (run p q).2 := by
  have hcopy := copyRow_fits (width H N) q
    (fun a ha => (rationalWordWidth_of_height (hq a ha)).trans (by unfold width; omega)) (by unfold width; omega)
  have hc := PlayerSpecificDenseTraceFits.controls_fits (width H N) [p.length,q.length,p.length-q.length] (by
    intro n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl <;> unfold width <;> omega)
  have hr := fits_mono (PlayerSpecificLeadingExecution.readLast_fits p H N hp hH hpl)
    (show PlayerSpecificLeadingExecution.width H N≤width H N by unfold PlayerSpecificLeadingExecution.width width; omega)
  have hm := fits_mono (PlayerSpecificMonomialExecution.fits (p.length-q.length) (PlayerSpecificLeadingExecution.readLast p).1 H N
    (PlayerSpecificLeadingExecution.readLast_height p H hp hH) hH ((Nat.sub_le _ _).trans hpl))
    (show PlayerSpecificMonomialExecution.width H N≤width H N by unfold PlayerSpecificMonomialExecution.width width; omega)
  simpa only [run,fits_append,List.map_cons,List.map_nil] using And.intro (And.intro (And.intro hcopy hc) hr) hm

theorem cost (model : RationalCostModel) (p q : Data) (H N : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hH : 1≤H) (hpl : p.length≤N) (hql : q.length≤N) :
    price model (run p q).2≤300*(N+1)^2*model.rat (width H N) := by
  have h := price_bound model (width H N) (by unfold width; omega) _ (fits p q H N hp hq hH hpl hql)
  have hl := trace_length p q N hpl hql
  have hm := Nat.mul_le_mul_right (3*model.rat (width H N)) hl
  nlinarith

end Blotto.PlayerSpecificTermExecution
