import Blotto.GeneralPaperBasisUpdateBits

/-! A valid native determinant/adjugate cache derives every exact division
of its next bordered update, including negative determinants. Uniform cache
word envelopes below combine the raw product, dot, determinant and entry
sizes; no short-final-result or division/cancellation oracle is supplied.
-/
namespace Blotto.GeneralPaperBasisCacheBitFacts
open GeneralPaperBasisStoredProducts GeneralPaperBasisStoredCorrect
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem exact_numerators {n : ℕ} (D : ℤ) (A : IntMatrix n) (M : Matrix (Fin n) (Fin n) ℤ)
    (u v : Vector n) (a : ℤ) (hValid : Valid D A M) (hD : D≠0)
    (hNext : (GeneralPaperBasisStoredStep.run D A u v a).determinant≠0) (i k : Fin n) :
    D∣(GeneralPaperBasisStoredStep.run D A u v a).determinant*(A.read i).read k+
      (GeneralPaperBasisStoredProducts.mulVecRun A u).1.read i*(GeneralPaperBasisStoredProducts.rowRun v A).1.read k := by
  have hd : (GeneralPaperBasisStoredStep.run D A u v a).determinant=
      GeneralPaperBasisAdjugateBlock.determinantUpdate M.det M.adjugate u.read v.read a := by
    rw [GeneralPaperBasisStoredStep.determinant_data,hValid.1,hValid.2]
  have hDet : M.det≠0 := by rw [←hValid.1]; exact hD
  have hNew : GeneralPaperBasisAdjugateBlock.determinantUpdate M.det M.adjugate u.read v.read a≠0 := by rw [←hd]; exact hNext
  have he := GeneralPaperBasisIntegerUpdate.exact_numerator M u.read v.read a hDet hNew i k
  rw [GeneralPaperBasisStoredStep.determinant_data,GeneralPaperBasisStoredProducts.mulVec_data,GeneralPaperBasisStoredProducts.row_data]
  change D∣GeneralPaperBasisAdjugateBlock.determinantUpdate D (observe A) u.read v.read a*(observe A i k)+
    (observe A).mulVec u.read i*GeneralPaperBasisAdjugateBlock.rowProduct v.read (observe A) k
  rw [hValid.1,hValid.2,he]
  exact dvd_mul_left _ _

def width (n H B : ℕ) : ℕ :=
  1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap n H B)+
    binaryWordWidth (GeneralPaperIntegerDotPrice.cap n B H)+
    binaryWordWidth (GeneralPaperIntegerDotPrice.cap n B (n*H*B))+
    binaryWordWidth (GeneralPaperBasisEntryBits.cap H (n*H*B) (n*B*H) (GeneralPaperBasisUpdateOperandSize.nextBound n H B))+
    binaryWordWidth (B+H+GeneralPaperBasisUpdateOperandSize.nextBound n H B+1)

theorem component_widths (n H B : ℕ) :
    1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap n H B)≤width n H B ∧
    1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap n B H)≤width n H B ∧
    1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap n B (n*H*B))≤width n H B ∧
    1+binaryWordWidth (GeneralPaperBasisEntryBits.cap H (n*H*B) (n*B*H) (GeneralPaperBasisUpdateOperandSize.nextBound n H B))≤width n H B ∧
    1+binaryWordWidth (B+H+GeneralPaperBasisUpdateOperandSize.nextBound n H B+1)≤width n H B := by
  unfold width
  omega

theorem width_bound (n H B : ℕ) : width n H B≤
    64*(binaryWordWidth (n+1)+binaryWordWidth (H+1)+binaryWordWidth (B+1)+1) := by
  let R := GeneralPaperIntegerDotPrice.cap n H B
  let U := n*H*B
  let V := n*B*H
  let L := GeneralPaperBasisUpdateOperandSize.nextBound n H B
  let F := binaryWordWidth (n+1)+binaryWordWidth (H+1)+binaryWordWidth (B+1)
  have hR := GeneralPaperIntegerDotPrice.cap_bounds n H B
  have hU : U≤R := hR.2.2
  have hV : V≤R := by simpa only [U,V,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hU
  have hNB : n*B≤R := by
    have hh := Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_succ n) (show 1≤H+1 by omega)) (Nat.le_succ B)
    simpa only [R,GeneralPaperIntegerDotPrice.cap,Nat.mul_one] using hh
  have hBH : B*H≤R := by
    have hh := Nat.mul_le_mul (Nat.mul_le_mul (show 1≤n+1 by omega) (Nat.le_succ H)) (Nat.le_succ B)
    simpa only [R,GeneralPaperIntegerDotPrice.cap,Nat.one_mul,Nat.mul_one,Nat.succ_eq_add_one,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hh
  have hL : L≤R+R*R := Nat.add_le_add hBH (Nat.mul_le_mul hNB hU)
  have wR : binaryWordWidth R≤F := GeneralPaperIntegerDotPrice.cap_width n H B
  have wU := (binaryWordWidth_mono hU).trans wR
  have wV := (binaryWordWidth_mono hV).trans wR
  have wL : binaryWordWidth L≤3*F+1 := by
    have hm := binaryWordWidth_mono hL
    have ha := GeneralPaperRayOperandWidthEnvelope.word_add R (R*R)
    have hp := binaryWordWidth_mul R R
    omega
  have wUp : binaryWordWidth (U+1)≤F+2 := by
    have hh := GeneralPaperRayOperandWidthEnvelope.word_add U 1
    have hw : binaryWordWidth 1=1 := by decide
    omega
  have wVp : binaryWordWidth (V+1)≤F+2 := by
    have hh := GeneralPaperRayOperandWidthEnvelope.word_add V 1
    have hw : binaryWordWidth 1=1 := by decide
    omega
  have wLp : binaryWordWidth (L+1)≤3*F+3 := by
    have hh := GeneralPaperRayOperandWidthEnvelope.word_add L 1
    have hw : binaryWordWidth 1=1 := by decide
    omega
  have wDelta : binaryWordWidth (B+H+L+1)≤binaryWordWidth (B+1)+binaryWordWidth (H+1)+3*F+5 := by
    have hB := binaryWordWidth_mono (Nat.le_succ B)
    have hH := binaryWordWidth_mono (Nat.le_succ H)
    change binaryWordWidth B≤binaryWordWidth (B+1) at hB
    change binaryWordWidth H≤binaryWordWidth (H+1) at hH
    have h1 := GeneralPaperRayOperandWidthEnvelope.word_add B H
    have h2 := GeneralPaperRayOperandWidthEnvelope.word_add (B+H) L
    have h3 := GeneralPaperRayOperandWidthEnvelope.word_add (B+H+L) 1
    have hw : binaryWordWidth 1=1 := by decide
    omega
  have w1 := GeneralPaperIntegerDotPrice.cap_width n H B
  have w2 := GeneralPaperIntegerDotPrice.cap_width n B H
  have w3 := GeneralPaperIntegerDotPrice.cap_width n B U
  have w4 := GeneralPaperBasisEntryBits.cap_width H U V L
  change 1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap n H B)+binaryWordWidth (GeneralPaperIntegerDotPrice.cap n B H)+
    binaryWordWidth (GeneralPaperIntegerDotPrice.cap n B U)+binaryWordWidth (GeneralPaperBasisEntryBits.cap H U V L)+
    binaryWordWidth (B+H+L+1)≤64*(F+1)
  dsimp only [F] at wR wU wV wL wUp wVp wLp wDelta ⊢
  omega

end Blotto.GeneralPaperBasisCacheBitFacts
