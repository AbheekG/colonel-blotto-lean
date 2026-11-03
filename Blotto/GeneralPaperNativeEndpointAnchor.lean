import Blotto.GeneralPaperNativeUnitSourceJoin

/-! Read the modified defender's actual zero tag or stored packed rational
point. Positive-label offsets are constructed by arithmetic. Every reached
test, subtraction, product, addition and reference write is priced. -/
namespace Blotto.GeneralPaperNativeEndpointAnchor
open GeneralPaperSourceEndpointBranch
set_option autoImplicit false
set_option maxHeartbeats 2400000

def run {m K : ℕ} (price : ℕ → ℕ) (A : ℕ) (choice : Choice (m*(K-1))) (j : Fin m) (l : Fin K) : ℚ×ℕ :=
  match choice with
  | .zero => (0,32*A)
  | .endpoint _ point =>
    let test := GeneralPaperIntegerWordPrice.compare price l.val 0
    if h:l.val=0 then (0,test+64*A) else
      let stride := K-1
      let label := l.val-1
      let product := j.val*stride
      let offset := product+label
      let v : RationalOrderCell.Variable m K := (j,⟨label,by have hl:=l.isLt;omega⟩)
      (point.read ⟨offset,(GeneralPaperBasisCoordinates.index v).isLt⟩,test+
        GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) K 1+
        GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) l.val 1+
        GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) j.val stride+
        GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) product label+128*A)

theorem data {T m K : ℕ} (price : ℕ → ℕ) (A : ℕ) (labels : Fin T → Fin m → Fin K)
    (choice : Choice (m*(K-1))) (j : Fin m) (l : Fin K) :
    (run price A choice j l).1=(GeneralPaperEndpointDictionary.dictionary ⟨labels,choice⟩).anchor j l := by
  cases choice with
  | zero => exact (GeneralPaperEndpointDictionary.zero_anchors labels j l).symm
  | endpoint gamma point =>
    by_cases hl:l.val=0
    · simp only [run,GeneralPaperEndpointDictionary.dictionary,GeneralPaperEndpointDictionary.anchor,dite_eq_left hl]
    · simp only [run,GeneralPaperEndpointDictionary.dictionary,GeneralPaperEndpointDictionary.anchor,dite_eq_right hl]
      rfl

def width (m K : ℕ) : ℕ := 1+binaryWordWidth (m*K+K+m+2)

theorem work {m K : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (A : ℕ)
    (choice : Choice (m*(K-1))) (j : Fin m) (l : Fin K) :
    (run price A choice j l).2≤9*price (width m K)+128*A := by
  let M := m*K+K+m+2
  have hK : K≤M := by dsimp only [M];omega
  have hj : j.val≤M := by dsimp only [M];have h:=j.isLt;omega
  have hl : l.val≤M := by dsimp only [M];have h:=l.isLt;omega
  have hOne : 1≤M := by dsimp only [M];omega
  have ht := GeneralPaperIntegerWordPrice.compare_le price hMono l.val 0 (width m K)
    (Nat.add_le_add_left (binaryWordWidth_mono hl) 1)
    (Nat.add_le_add_left (binaryWordWidth_mono (Nat.zero_le M)) 1)
  cases choice with
  | zero => simp only [run];omega
  | endpoint gamma point =>
    simp only [run]
    split
    · dsimp only
      omega
    · rename_i hPositive
      let v : RationalOrderCell.Variable m K := (j,⟨l.val-1,by have h:=l.isLt;omega⟩)
      have hStride : K-1≤M := by omega
      have hProduct : j.val*(K-1)≤M :=
        (Nat.mul_le_mul j.isLt.le (Nat.sub_le K 1)).trans (by dsimp only [M];omega)
      have hOffset : j.val*(K-1)+(l.val-1)≤M := by
        have h := (GeneralPaperBasisCoordinates.index v).isLt
        change j.val*(K-1)+(l.val-1)<m*(K-1) at h
        have hd := Nat.mul_le_mul_left m (Nat.sub_le K 1)
        dsimp only [M]
        omega
      have hs := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a-b) K 1 M hK hOne (by omega)
      have hl' := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a-b) l.val 1 M hl hOne (by omega)
      have hm := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a*b) j.val (K-1) M hj hStride hProduct
      have ha := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) (j.val*(K-1)) (l.val-1) M
        hProduct (by omega) hOffset
      change _≤9*price (1+binaryWordWidth M)+128*A
      change _≤price (1+binaryWordWidth M) at ht
      dsimp only
      omega

end Blotto.GeneralPaperNativeEndpointAnchor
