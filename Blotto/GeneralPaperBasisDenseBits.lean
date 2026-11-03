import Blotto.GeneralPaperBasisCoordinateBits

/-! Complete sparse-to-dense original row: actual packed-coordinate
arithmetic, zero initialization and additive scatter with prefix bounds.
The native annotation is constructed arithmetically, avoiding a second
native scatter execution; all retained row fields agree exactly.
-/
namespace Blotto.GeneralPaperBasisDenseBits
open RationalOrderCell GeneralPaperBasisDenseRow GeneralPaperBasisCoordinates GeneralPaperAffineConstraintRows
open GeneralPaperBasisStoredProducts
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 7000000

theorem old_overhead (count k : ℕ) : PaperIndexedArrayConstruction.overhead (fun _ => 0) 1 count k=16+34*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change PaperIndexedArrayConstruction.overhead (fun _ => 0) 1 count k+34=16+34*(k+1)
    rw [ih]
    omega

theorem old_zero_work (d : ℕ) : (GeneralPaperBasisCoefficientScatter.zeroRun d).2=36*d+16 := by
  rw [GeneralPaperBasisCoefficientScatter.zeroRun,PaperIndexedArrayConstruction.run_work,old_overhead]
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id]
  omega

theorem native_annotation {m K : ℕ} (r : Row (Variable m K)) : (build r).work=36*(m*(K-1))+24*r.terms.length+30 := by
  simp only [build,GeneralPaperBasisCoefficientScatter.run,GeneralPaperBasisCoefficientScatter.loop_work,
    List.length_map,Nat.zero_add,old_zero_work]
  omega

def run {m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (r : Row (Variable m K)) : Dense (m*(K-1)) × ℕ :=
  let terms := GeneralPaperBasisCoordinateBits.run primitive W r.terms
  let result := GeneralPaperBasisScatterBits.run primitive W terms.1
  (⟨result.vector,r.constant,r.slope,36*(m*(K-1))+24*r.terms.length+30⟩,
    terms.2+result.work+(16*r.terms.length+48)*W)

theorem data {m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (r : Row (Variable m K)) : (run primitive W r).1=build r := by
  have hCoeff : (GeneralPaperBasisScatterBits.run primitive W (GeneralPaperBasisCoordinateBits.run primitive W r.terms).1).vector=(build r).coefficients := by
    rw [GeneralPaperBasisCoordinateBits.data,GeneralPaperBasisScatterBits.data]
    rfl
  change Dense.mk _ r.constant r.slope (36*(m*(K-1))+24*r.terms.length+30)=build r
  rw [hCoeff,←native_annotation r]
  rfl

theorem work {m K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W : ℕ)
    (hW : 1≤W) (hD : binaryWordWidth (m*(K-1)+1)≤W) (r : Row (Variable m K))
    (hTerms : ∀ t∈r.terms,t.2.natAbs≤1) :
    (run primitive W r).2≤1024*(m*(K-1)+r.terms.length+1)*
      (W+primitive (1+binaryWordWidth (m*(K-1)+1))+primitive (1+binaryWordWidth r.terms.length)) := by
  let d := m*(K-1)
  let n := r.terms.length
  let Pi := primitive (1+binaryWordWidth (d+1))
  let Ps := primitive (1+binaryWordWidth n)
  let terms := GeneralPaperBasisCoordinateBits.run primitive W r.terms
  let result := GeneralPaperBasisScatterBits.run primitive W terms.1
  have hLen : terms.1.length=n := by rw [GeneralPaperBasisCoordinateBits.data,List.length_map]
  have hUnit : ∀ t∈terms.1,t.2.natAbs≤1 := by
    rw [GeneralPaperBasisCoordinateBits.data]
    intro t ht
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    exact hTerms u hu
  have hm := GeneralPaperBasisCoordinateBits.work primitive hMono W r.terms
  have hs := GeneralPaperBasisScatterBits.work primitive hMono W hW hD terms.1 hUnit
  rw [hLen] at hs
  change terms.2≤n*(40*W+6*Pi)+2*W at hm
  change result.work≤256*(d+n+1)*(W+Ps) at hs
  change terms.2+result.work+(16*n+48)*W≤1024*(d+n+1)*(W+Pi+Ps)
  nlinarith only [hm,hs,Nat.zero_le (d*W),Nat.zero_le (n*W),Nat.zero_le (d*Pi),Nat.zero_le (n*Pi),
    Nat.zero_le (d*Ps),Nat.zero_le (n*Ps),Nat.zero_le Pi,Nat.zero_le Ps]

end Blotto.GeneralPaperBasisDenseBits
