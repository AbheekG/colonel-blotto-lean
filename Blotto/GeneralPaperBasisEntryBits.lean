import Blotto.GeneralPaperBasisProductBits

/-! Native bordered adjugate entry with actual integer multiplication,
addition, negation and exact-division operand/result prices. The numerator
is bounded before division; negative nonzero determinants are allowed.
-/
namespace Blotto.GeneralPaperBasisEntryBits
open GeneralPaperBasisStoredProducts GeneralPaperIntegerPrimitivePrice
set_option autoImplicit false
set_option maxHeartbeats 6000000

def cap (H U V L : ℕ) : ℕ := 2*((H+1)*(U+1)*(V+1)*(L+1))

theorem cap_bounds (H U V L : ℕ) :
    H≤cap H U V L ∧ U≤cap H U V L ∧ V≤cap H U V L ∧ L≤cap H U V L ∧ L*H+U*V≤cap H U V L := by
  let B := (H+1)*(U+1)*(V+1)*(L+1)
  have bound (a b c d : ℕ) (ha : a≤H+1) (hb : b≤U+1) (hc : c≤V+1) (hd : d≤L+1) : a*b*c*d≤B :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc) hd
  have hH : H≤B := by simpa only [Nat.mul_one] using bound H 1 1 1 (Nat.le_succ H) (by omega) (by omega) (by omega)
  have hU : U≤B := by simpa only [Nat.one_mul,Nat.mul_one] using bound 1 U 1 1 (by omega) (Nat.le_succ U) (by omega) (by omega)
  have hV : V≤B := by simpa only [Nat.one_mul,Nat.mul_one] using bound 1 1 V 1 (by omega) (by omega) (Nat.le_succ V) (by omega)
  have hL : L≤B := by simpa only [Nat.one_mul] using bound 1 1 1 L (by omega) (by omega) (by omega) (Nat.le_succ L)
  have hLH : L*H≤B := by simpa only [Nat.mul_one,Nat.mul_comm] using bound H 1 1 L (Nat.le_succ H) (by omega) (by omega) (Nat.le_succ L)
  have hUV : U*V≤B := by simpa only [Nat.one_mul,Nat.mul_one] using bound 1 U V 1 (by omega) (Nat.le_succ U) (Nat.le_succ V) (by omega)
  change H≤2*B ∧ U≤2*B ∧ V≤2*B ∧ L≤2*B ∧ L*H+U*V≤2*B
  omega

theorem cap_width (H U V L : ℕ) : binaryWordWidth (cap H U V L)≤
    2+binaryWordWidth (H+1)+binaryWordWidth (U+1)+binaryWordWidth (V+1)+binaryWordWidth (L+1) := by
  have h0 := binaryWordWidth_mul 2 ((H+1)*(U+1)*(V+1)*(L+1))
  have h1 := binaryWordWidth_mul ((H+1)*(U+1)*(V+1)) (L+1)
  have h2 := binaryWordWidth_mul ((H+1)*(U+1)) (V+1)
  have h3 := binaryWordWidth_mul (H+1) (U+1)
  have ht : binaryWordWidth 2=2 := by decide
  unfold cap
  omega

def run {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j k : Fin (n+1)) : ℤ × ℕ :=
  match GeneralPaperBasisAppendIndex.decode n j,GeneralPaperBasisAppendIndex.decode n k with
  | none,none => (D,16*W+primitive (word D))
  | some i,none => (-(au.read i),16*W+unary primitive (fun a => -a) (au.read i))
  | none,some l => (-(va.read l),16*W+unary primitive (fun a => -a) (va.read l))
  | some i,some l =>
    let p := Dnext*(A.read i).read l
    let q := au.read i*va.read l
    let numerator := p+q
    (numerator/D,32*W+binary primitive (fun a b => a*b) Dnext ((A.read i).read l)+
      binary primitive (fun a b => a*b) (au.read i) (va.read l)+
      binary primitive (fun a b => a+b) p q+binary primitive (fun a b => a/b) numerator D)

theorem data {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j k : Fin (n+1)) :
    (run primitive W D Dnext A au va j k).1=GeneralPaperBasisStoredUpdate.entry D Dnext A au va j k := by
  unfold run GeneralPaperBasisStoredUpdate.entry
  cases GeneralPaperBasisAppendIndex.decode n j <;> cases GeneralPaperBasisAppendIndex.decode n k <;> rfl

theorem work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W H U V L : ℕ)
    (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n)
    (hD : D.natAbs≤H) (hNext : Dnext.natAbs≤L) (hA : ∀ i k,((A.read i).read k).natAbs≤H)
    (hU : ∀ i,(au.read i).natAbs≤U) (hV : ∀ i,(va.read i).natAbs≤V)
    (hExact : ∀ i k,D∣Dnext*(A.read i).read k+au.read i*va.read k) (j k : Fin (n+1)) :
    (run primitive W D Dnext A au va j k).2≤32*W+8*primitive (1+binaryWordWidth (cap H U V L)) := by
  let M := cap H U V L
  change (run primitive W D Dnext A au va j k).2≤32*W+8*primitive (1+binaryWordWidth M)
  have hc := cap_bounds H U V L
  have hMD := hD.trans hc.1
  have hMN := hNext.trans hc.2.2.2.1
  have hMA (i k) := (hA i k).trans hc.1
  have hMU (i) := (hU i).trans hc.2.1
  have hMV (i) := (hV i).trans hc.2.2.1
  unfold run
  cases hj : GeneralPaperBasisAppendIndex.decode n j with
  | none =>
    cases hk : GeneralPaperBasisAppendIndex.decode n k with
    | none =>
      dsimp only
      have hh := hMono (word_bound D M hMD)
      omega
    | some l =>
      dsimp only
      have hh := unary_le primitive hMono (fun a => -a) (va.read l) M (hMV l)
        (by simpa only [Int.natAbs_neg] using hMV l)
      omega
  | some i =>
    cases hk : GeneralPaperBasisAppendIndex.decode n k with
    | none =>
      dsimp only
      have hh := unary_le primitive hMono (fun a => -a) (au.read i) M (hMU i)
        (by simpa only [Int.natAbs_neg] using hMU i)
      omega
    | some l =>
      have hp : (Dnext*(A.read i).read l).natAbs≤L*H := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul hNext (hA i l)
      have hq : (au.read i*va.read l).natAbs≤U*V := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul (hU i) (hV l)
      have hpM : (Dnext*(A.read i).read l).natAbs≤M := hp.trans ((Nat.le_add_right _ _).trans hc.2.2.2.2)
      have hqM : (au.read i*va.read l).natAbs≤M := hq.trans ((Nat.le_add_left _ _).trans hc.2.2.2.2)
      have hs : (Dnext*(A.read i).read l+au.read i*va.read l).natAbs≤M :=
        ((Int.natAbs_add_le _ _).trans (Nat.add_le_add hp hq)).trans hc.2.2.2.2
      have hd := GeneralPaperBasisUpdateOperandSize.exact_quotient _ D (hExact i l) M hs
      have hP := binary_le primitive hMono (fun a b => a*b) Dnext ((A.read i).read l) M hMN (hMA i l) hpM
      have hQ := binary_le primitive hMono (fun a b => a*b) (au.read i) (va.read l) M (hMU i) (hMV l) hqM
      have hS := binary_le primitive hMono (fun a b => a+b) _ _ M hpM hqM hs
      have hDiv := binary_le primitive hMono (fun a b => a/b) _ D M hs hMD hd
      dsimp only
      omega

end Blotto.GeneralPaperBasisEntryBits
