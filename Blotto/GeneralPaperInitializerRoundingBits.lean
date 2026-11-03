import Blotto.GeneralPaperPreparedBasisBits

/-! Downward rounding retains the quotient it computes. Both arithmetic
and bit programs execute the bounded quotient once and return the same
native rounded anchor. The retained quotient is EXACTLY its N-lattice
numerator; no second floor or rational numerator extraction is executed.
-/
namespace Blotto.GeneralPaperInitializerRoundingBits
open GeneralPaperRationalPrimitivePrice
set_option autoImplicit false
set_option maxHeartbeats 6000000

def unit (N depth : ℕ) (u : ℚ) : (ℕ × ℚ) × ℕ :=
  let result := GeneralPaperBoundedQuotient.run (u*(N:ℚ)) 1 depth
  ((result.quotient,(result.quotient:ℚ)/N),result.work+32)

def run (model : RationalCostModel) (W N depth : ℕ) (u : ℚ) : (ℕ × ℚ) × ℕ :=
  let scaled := u*(N:ℚ)
  let result := GeneralPaperBoundedQuotient.runWithBits model W scaled 1 depth
  let q := result.1.quotient
  ((q,(q:ℚ)/N),result.2+binary model.rat (fun a b => a*b) u (N:ℚ)+
    model.rat (rationalWordWidth (N:ℚ))+model.rat (rationalWordWidth (q:ℚ))+
    binary model.rat (fun a b => a/b) (q:ℚ) (N:ℚ)+48*W)

theorem data (model : RationalCostModel) (W N depth : ℕ) (u : ℚ) : (run model W N depth u).1=(unit N depth u).1 := by
  simp only [run,unit,GeneralPaperBoundedQuotient.run_data]

theorem value_data (model : RationalCostModel) (W N depth : ℕ) (u : ℚ) :
    (run model W N depth u).1.2=(GeneralPaperInitializerRounding.run N depth u).value := by
  rw [data]
  rfl

theorem unit_work (N depth : ℕ) (u : ℚ) : (unit N depth u).2=12*depth+34 := by
  simp only [unit,GeneralPaperBoundedQuotient.run_work]

theorem quotient_shape (x a : ℚ) (depth : ℕ) : (GeneralPaperBoundedQuotient.run x a depth).quotient<2^depth := by
  induction depth generalizing a with
  | zero => simp only [GeneralPaperBoundedQuotient.run,pow_zero]; decide
  | succ depth ih =>
    have hh := ih (2*a)
    rw [GeneralPaperBoundedQuotient.run]
    split <;> simp only [pow_succ] <;> omega

theorem raw_quotient_words (x a : ℚ) (depth W : ℕ) (hW : depth+2≤W) :
    binaryWordWidth (2*(GeneralPaperBoundedQuotient.run x (2*a) depth).quotient)≤W ∧
    binaryWordWidth (2*(GeneralPaperBoundedQuotient.run x (2*a) depth).quotient+1)≤W := by
  have hh := quotient_shape x (2*a) depth
  have h1 : 2*(GeneralPaperBoundedQuotient.run x (2*a) depth).quotient<2^(depth+1) := by rw [pow_succ]; omega
  have h2 : 2*(GeneralPaperBoundedQuotient.run x (2*a) depth).quotient+1<2^(depth+1) := by rw [pow_succ]; omega
  exact ⟨(binaryWordWidth_le_of_lt_pow (by omega : 0<depth+1) h1).trans (by omega),
    (binaryWordWidth_le_of_lt_pow (by omega : 0<depth+1) h2).trans (by omega)⟩

theorem quotient_le (N depth : ℕ) (hN : 0<N) (hCap : N<2^depth) (u : ℚ) (hu : 0≤u ∧ u≤1) :
    (unit N depth u).1.1≤N := by
  have hs := GeneralPaperBoundedQuotient.run_spec (u*(N:ℚ)) 1 (by norm_num) depth
    (mul_nonneg hu.1 (show (0:ℚ)≤N by exact_mod_cast hN.le)) (by
      have hc : (N:ℚ)<(2:ℚ)^depth := by exact_mod_cast hCap
      have hn : (0:ℚ)≤N := by positivity
      nlinarith only [hu.2,hc,hn])
  have hb : ((unit N depth u).1.1:ℚ)≤N := by
    change ((GeneralPaperBoundedQuotient.run (u*(N:ℚ)) 1 depth).quotient:ℚ)≤N
    have hn : (0:ℚ)≤N := by positivity
    nlinarith only [hs.1,hs.2.1,hu.2,hn]
  exact_mod_cast hb

theorem numerator_data (model : RationalCostModel) (W N depth : ℕ) (hN : 0<N) (u : ℚ) :
    ((run model W N depth u).1.1:ℤ)=latticeNumerator N (GeneralPaperInitializerRounding.run N depth u).value := by
  have he := latticeNumerator_cast_eq_mul (GeneralPaperInitializerRounding.lattice N depth hN u)
  have hn : (N:ℚ)≠0 := by exact_mod_cast hN.ne'
  rw [data]
  have hx : (((unit N depth u).1.1:ℤ):ℚ)=
      ((latticeNumerator N (GeneralPaperInitializerRounding.run N depth u).value:ℤ):ℚ) := by
    rw [he]
    change ((GeneralPaperBoundedQuotient.run (u*(N:ℚ)) 1 depth).quotient:ℚ)=
      ((GeneralPaperBoundedQuotient.run (u*(N:ℚ)) 1 depth).quotient:ℚ)/(N:ℚ)*(N:ℚ)
    rw [div_mul_cancel₀ _ hn]
  exact_mod_cast hx

def width (A N depth : ℕ) : ℕ := 1+2*(A+3*binaryWordWidth N+2*depth+8)

theorem work (model : RationalCostModel) (W N depth A : ℕ) (hN : 0<N) (hCap : N<2^depth)
    (u : ℚ) (hu : 0≤u ∧ u≤1) (hHeight : RationalHeight u A) :
    (run model W N depth u).2≤256*(depth+1)*(W+model.rat (width A N depth)) := by
  let B := binaryWordWidth N
  let L := width A N depth
  let P := model.rat L
  have hn := GeneralPaperBasisDivideBits.nat_height N
  have hs := hHeight.mul hn
  have hOne : RationalHeight (1:ℚ) 1 := by norm_num [RationalHeight]
  have hScaled : u*(N:ℚ)<(1:ℚ)*(2:ℚ)^depth := by
    have hc : (N:ℚ)<(2:ℚ)^depth := by exact_mod_cast hCap
    have hn0 : (0:ℚ)≤N := by positivity
    nlinarith only [hu.2,hc,hn0]
  have hq := GeneralPaperBoundedQuotient.run_bit_work model W (u*(N:ℚ)) 1 (by norm_num) depth (A+B) 1
    (mul_nonneg hu.1 (Nat.cast_nonneg N)) hScaled hs hOne
  have hNat := GeneralPaperBasisDivideBits.nat_height (unit N depth u).1.1
  have hNat' : RationalHeight ((unit N depth u).1.1:ℚ) B := hNat.mono (binaryWordWidth_mono (quotient_le N depth hN hCap u hu))
  have hOut := hNat'.div hn
  have wu : rationalWordWidth u≤L := (rationalWordWidth_of_height hHeight).trans (by dsimp only [L,width]; omega)
  have wn : rationalWordWidth (N:ℚ)≤L := (rationalWordWidth_of_height hn).trans (by dsimp only [L,width]; omega)
  have ws : rationalWordWidth (u*(N:ℚ))≤L := (rationalWordWidth_of_height hs).trans (by dsimp only [L,B,width]; omega)
  have wq : rationalWordWidth ((unit N depth u).1.1:ℚ)≤L := (rationalWordWidth_of_height hNat').trans (by dsimp only [L,B,width]; omega)
  have wo : rationalWordWidth (((unit N depth u).1.1:ℚ)/(N:ℚ))≤L := (rationalWordWidth_of_height hOut).trans (by dsimp only [L,B,width]; omega)
  have pm := binary_le model.rat model.monotone (fun a b => a*b) u (N:ℚ) L wu wn ws
  have pd := binary_le model.rat model.monotone (fun a b => a/b) ((unit N depth u).1.1:ℚ) (N:ℚ) L wq wn wo
  have pn := model.monotone wn
  have pq := model.monotone wq
  have hBudget : 1+2*GeneralPaperBoundedQuotient.heightBudget (A+B) 1 depth≤L := by
    dsimp only [L,B,width,GeneralPaperBoundedQuotient.heightBudget]
    omega
  have hp := model.monotone hBudget
  have hq' : (GeneralPaperBoundedQuotient.runWithBits model W (u*(N:ℚ)) 1 depth).2≤(depth+1)*(64*W+6*P) := by
    apply hq.trans
    unfold GeneralPaperBoundedQuotient.bitProfile
    exact Nat.mul_le_mul_left (depth+1) (by dsimp only [P]; omega)
  dsimp only [run]
  simp only [GeneralPaperBoundedQuotient.run_data]
  change (GeneralPaperBoundedQuotient.runWithBits model W (u*(N:ℚ)) 1 depth).2+
    binary model.rat (fun a b => a*b) u (N:ℚ)+model.rat (rationalWordWidth (N:ℚ))+
    model.rat (rationalWordWidth ((unit N depth u).1.1:ℚ))+
    binary model.rat (fun a b => a/b) ((unit N depth u).1.1:ℚ) (N:ℚ)+48*W≤_
  change _≤256*(depth+1)*(W+P)
  nlinarith only [hq',pm,pd,pn,pq,Nat.zero_le (depth*W),Nat.zero_le (depth*P)]

end Blotto.GeneralPaperInitializerRoundingBits
