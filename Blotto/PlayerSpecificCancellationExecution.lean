import Blotto.PlayerSpecificTermExecution

/-! Executed leading cancellation returns the cached term and normalized
remainder together. Both refine the existing numerical definitions; the
cached term can be reused by the later quotient update. -/
namespace Blotto.PlayerSpecificCancellationExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 4000000

def run (p q : Data) : (Data×Data)×Trace :=
  let term := PlayerSpecificTermExecution.run p q
  let product := PlayerSpecificDenseExecution.multiply q term.1
  let difference := PlayerSpecificDenseExecution.subtract p product.1
  let normalized := PlayerSpecificDenseExecution.trim difference.1
  ((term.1,normalized.1),term.2++product.2++difference.2++normalized.2++[.control p.length,.control q.length])

theorem value (p q : Data) : (run p q).1=
    (PlayerSpecificPolynomialCancellation.term p q,PlayerSpecificPolynomialCancellation.remainder p q) := by
  simp only [run,PlayerSpecificTermExecution.value,PlayerSpecificDenseExecution.multiply_value,
    PlayerSpecificDenseExecution.subtract_value,PlayerSpecificDenseExecution.trim_value,PlayerSpecificPolynomialCancellation.remainder]

theorem term_value (p q : Data) : (run p q).1.1=PlayerSpecificPolynomialCancellation.term p q := congrArg Prod.fst (value p q)
theorem remainder_value (p q : Data) : (run p q).1.2=PlayerSpecificPolynomialCancellation.remainder p q := congrArg Prod.snd (value p q)

theorem term_height (p q : Data) (H : ℕ) (hp : HasHeight p H) (hH : 1≤H) : HasHeight (run p q).1.1 H := by
  rw [term_value]
  exact PlayerSpecificCancellationHeights.term_height p q H hp hH

theorem remainder_height (p q : Data) (H : ℕ) (hp : HasHeight p H) (hq : HasHeight q H)
    (hH : 1≤H) (hql : q.length≤4) : HasHeight (run p q).1.2 (11*H+6) := by
  rw [remainder_value]
  have h := PlayerSpecificCancellationHeights.remainder_height p q H H 4 hp hq hH hql
  have he : H+(H+H+1)*(4+1)+1=11*H+6 := by ring
  simpa only [he] using h

theorem remainder_normalized (p q : Data) : Normalized (run p q).1.2 := by
  rw [remainder_value]
  exact trim_normalized _

theorem term_length (p q : Data) (hp : p≠[]) (hq : q≠[]) : (run p q).1.1.length≤p.length := by
  rw [term_value]
  exact PlayerSpecificCancellationHeights.term_length p q hp hq

theorem drops_length (p q : Data) (hp : Normalized p) (hq : Normalized q)
    (hp0 : p≠[]) (hm : (semantics q).Monic) (hlen : q.length≤p.length) :
    (run p q).1.2.length<p.length := by
  rw [remainder_value]
  exact PlayerSpecificPolynomialCancellation.drops_length p q hp hq hp0 hm hlen

end Blotto.PlayerSpecificCancellationExecution
