import Blotto.PlayerSpecificSignPreparation

/-! One word envelope for every actual integer control operand/result.
Its size is linear in the measured endpoint/element/certificate widths. -/
namespace Blotto.PlayerSpecificSignControlBudget
open PlayerSpecificSignDepthHeights PlayerSpecificIsolationDepthHeight
set_option autoImplicit false
set_option maxHeartbeats 3000000

def size (E A B : ℕ) : ℕ := E+A+B+100
def word (E A B : ℕ) : ℕ := 1024*size E A B
def atoms (E A B na nb : ℕ) : List ℕ :=
  let M:=2^E
  let U:=1+M
  let pa:=U^na
  let pb:=U^nb
  let coefficient:=na*2^A
  let product:=coefficient*pa
  let L:=1+product
  let gap:=2^B*pb
  let eightM:=8*M
  let scaled:=eightM*L
  let operand:=scaled*gap
  [0,1,2,8,E,A,B,na,nb,M,U,2^A,2^B,pa,pb,coefficient,product,L,gap,eightM,scaled,operand,binaryWordWidth operand]

theorem size_large (E A B : ℕ) : 100≤size E A B := by unfold size; omega

theorem fits (E A B na nb : ℕ) (hna : na≤3) (hnb : nb≤17) :
    ∀ n∈atoms E A B na nb,1+binaryWordWidth n≤word E A B := by
  have hT:=size_large E A B
  have hE : E≤size E A B := by unfold size; omega
  have hA : A≤size E A B := by unfold size; omega
  have hB : B≤size E A B := by unfold size; omega
  have hM : binaryWordWidth (2^E)=E+1 := two_power_width E
  have hEA : binaryWordWidth (2^A)=A+1 := two_power_width A
  have hEB : binaryWordWidth (2^B)=B+1 := two_power_width B
  have hU : binaryWordWidth (1+2^E)≤E+2 := by
    have h:=increment_width (2^E)
    rw [hM] at h
    simpa only [Nat.add_comm 1] using h
  have hpa : binaryWordWidth ((1+2^E)^na)≤3*E+7 := by
    have h:=power_width (1+2^E) na
    have hm:=Nat.mul_le_mul_left na hU
    have hc:=Nat.mul_le_mul_right (E+2) hna
    omega
  have hpb : binaryWordWidth ((1+2^E)^nb)≤17*E+35 := by
    have h:=power_width (1+2^E) nb
    have hm:=Nat.mul_le_mul_left nb hU
    have hc:=Nat.mul_le_mul_right (E+2) hnb
    omega
  have hnaW : binaryWordWidth na≤2 := (binaryWordWidth_mono hna).trans_eq (by decide)
  have hnbW : binaryWordWidth nb≤5 := (binaryWordWidth_mono hnb).trans_eq (by decide)
  have hc : binaryWordWidth (na*2^A)≤A+3 := by have h:=binaryWordWidth_mul na (2^A); omega
  have hp : binaryWordWidth (na*2^A*(1+2^E)^na)≤A+3*E+10 := by
    have h:=binaryWordWidth_mul (na*2^A) ((1+2^E)^na)
    omega
  have hL : binaryWordWidth (1+na*2^A*(1+2^E)^na)≤A+3*E+11 := by
    have h:=increment_width (na*2^A*(1+2^E)^na)
    rw [Nat.add_comm (na*2^A*(1+2^E)^na) 1] at h
    omega
  have hgap : binaryWordWidth (2^B*(1+2^E)^nb)≤B+17*E+36 := by
    have h:=binaryWordWidth_mul (2^B) ((1+2^E)^nb)
    omega
  have h8 : binaryWordWidth 8=4 := by decide
  have h8M : binaryWordWidth (8*2^E)≤E+5 := by have h:=binaryWordWidth_mul 8 (2^E); omega
  have hscaled : binaryWordWidth (8*2^E*(1+na*2^A*(1+2^E)^na))≤A+4*E+16 := by
    have h:=binaryWordWidth_mul (8*2^E) (1+na*2^A*(1+2^E)^na)
    omega
  have hout : binaryWordWidth (8*2^E*(1+na*2^A*(1+2^E)^na)*(2^B*(1+2^E)^nb))≤A+B+21*E+52 := by
    have h:=binaryWordWidth_mul (8*2^E*(1+na*2^A*(1+2^E)^na)) (2^B*(1+2^E)^nb)
    omega
  have hdepth:=PlayerSpecificRationalTrace.control_width
    (binaryWordWidth (8*2^E*(1+na*2^A*(1+2^E)^na)*(2^B*(1+2^E)^nb)))
  have hEW:=PlayerSpecificRationalTrace.control_width E
  have hAW:=PlayerSpecificRationalTrace.control_width A
  have hBW:=PlayerSpecificRationalTrace.control_width B
  have h0 : binaryWordWidth 0=1 := by decide
  have h1 : binaryWordWidth 1=1 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  intro n hn
  simp only [atoms,List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold word size at * <;> omega

theorem dyadic_power_width (E A B exponent : ℕ) (he : exponent≤size E A B) :
    PlayerSpecificNaturalExecution.powerWidth 2 exponent≤word E A B := by
  have ht:=size_large E A B
  have h2 : binaryWordWidth 2=2 := by decide
  unfold PlayerSpecificNaturalExecution.powerWidth word
  rw [h2]
  omega

theorem interval_power_width (E A B exponent : ℕ) (he : exponent≤17) :
    PlayerSpecificNaturalExecution.powerWidth (1+2^E) exponent≤word E A B := by
  have ht:=size_large E A B
  have hU : binaryWordWidth (1+2^E)≤E+2 := by
    have h:=increment_width (2^E)
    rw [two_power_width] at h
    simpa only [Nat.add_comm 1] using h
  have hm:=Nat.mul_le_mul (Nat.add_le_add_right he 1) (Nat.add_le_add_right hU 1)
  unfold PlayerSpecificNaturalExecution.powerWidth word size
  omega

end Blotto.PlayerSpecificSignControlBudget
