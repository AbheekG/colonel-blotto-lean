import Blotto.GeneralPaperStaticEnumerationPrice

/-! Actual static sparse-row data and family-sensitive prices. Box/order
rows pay one/two terms; only retained budget rows pay up to m terms. Their
literal constructors and original unit RHS/constants are included.
-/
namespace Blotto.GeneralPaperStaticRowPrice
open RationalOrderCell GeneralPaperStaticRayRows GeneralPaperRayUniformSize GeneralPaperRayRationalBound
set_option autoImplicit false
set_option maxHeartbeats 6000000

def support {T m K : ℕ} : StaticIndex T m K → ℕ
  | .inl _ => 1
  | .inr (.inl _) => 2
  | .inr (.inr _) => m

theorem row_length {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (i : StaticIndex T m K) :
    (row labels i).terms.length≤support i := by
  rcases i with ⟨v,b⟩|⟨j,l⟩|i
  · cases b <;> simp only [row,GeneralPaperAffineConstraintRows.constraints,embed,Bool.false_eq_true,ite_false,ite_true,support,List.length_cons,List.length_nil] <;> omega
  · exact rawRow_order_length (fun _ => 0) j (GeneralPaperAffineConstraintRows.orderLeft l) (GeneralPaperAffineConstraintRows.orderRight l)
  · exact rawRow_sum_length (fun _ => 0) (labels i) 0

theorem unit_terms {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (i : StaticIndex T m K) :
    ∀ t∈(row labels i).terms,t.2.natAbs≤1 := by
  intro t ht
  have hu := GeneralPaperAffineConstraintRows.unit_terms labels (fun _ _ => 0) 0 (embed i) t ht
  rcases hu with he|he <;> simp only [he,Int.natAbs_one,Int.natAbs_neg,le_refl]

theorem constant_unit {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (i : StaticIndex T m K) :
    (row labels i).constant.natAbs≤1 :=
  (GeneralPaperAffineConstraintRows.rhs_unit labels (fun _ _ => 0) 0 (embed i)).1

theorem support_bound {T m K : ℕ} (hm : 0<m) (i : StaticIndex T m K) : support i≤m+1 := by
  rcases i with v|v|i <;> dsimp only [support] <;> omega

def evaluate {T m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (x w : Variable m K → ℚ) (i : StaticIndex T m K) : GeneralPaperRayAffine.Affine × ℕ :=
  let residual := GeneralPaperSparseResidualPrice.evaluate primitive W (row labels i) x w
  (residual.1,residual.2+GeneralPaperStaticRayScan.generation i*W)

theorem data {T m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (x w : Variable m K → ℚ) (i : StaticIndex T m K) :
    (evaluate primitive W labels x w i).1=(GeneralPaperStaticRayScan.evaluate labels x w i).1 := by
  simp only [evaluate,GeneralPaperSparseResidualPrice.data,GeneralPaperStaticRayScan.evaluate]

def charge {T m K : ℕ} (W P : ℕ) : StaticIndex T m K → ℕ
  | .inl _ => 146*W+18*P
  | .inr (.inl _) => 210*W+27*P
  | .inr (.inr _) => (64*m+114)*W+(9*m+9)*P

theorem charge_eq {T m K : ℕ} (W P : ℕ) (i : StaticIndex T m K) :
    support i*(48*W+9*P)+(GeneralPaperStaticRayScan.generation i+82)*W+9*P=charge W P i := by
  rcases i with v|v|i <;> dsimp only [support,GeneralPaperStaticRayScan.generation,charge] <;> ring

theorem charge_sum (T m K W P : ℕ) :
    ((enumerate T m K).map (charge W P)).sum=
      (m*(K-1))*(502*W+63*P)+T*((64*m+114)*W+(9*m+9)*P) := by
  have hb (vs : List (Variable m K)) :
      (vs.flatMap (fun _ => [146*W+18*P,146*W+18*P])).sum=(292*W+36*P)*vs.length := by
    induction vs with
    | nil => simp only [List.flatMap_nil,List.sum_nil,List.length_nil,Nat.mul_zero]
    | cons v rest ih =>
      simp only [List.flatMap_cons,List.sum_append,List.sum_cons,List.sum_nil,List.length_cons,ih]
      ring
  simp [enumerate,boxes,orders,budgets,charge,List.map_flatMap,Function.comp_def,hb,variableList_length]
  ring

theorem work {T m K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E X V P : ℕ) (hm : 0<m) (hD : 0<D) (hE : 0<E) (labels : Fin T → Fin m → Fin K)
    (x w : Variable m K → ℚ) (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j))
    (i : StaticIndex T m K) :
    (evaluate primitive W labels x w i).2+56*W+6*primitive (1+2*width D E m X V P)≤
      charge W (primitive (1+2*width D E m X V P)) i := by
  let A := interceptCap m X P
  let B := slopeCap m V
  let R := width D E m X V P
  let Q := primitive (1+2*R)
  have hs := scale_caps m X V P 1 (show 1≤m by omega)
  simp only [Nat.one_mul] at hs
  have hA : 1≤A := Nat.mul_pos (by omega) (by omega)
  have hLen := (row_length labels i).trans (support_bound hm i)
  have hMassX : (row labels i).terms.length*X+1≤A := by
    have hh := Nat.mul_le_mul_right X hLen
    dsimp only [A,interceptCap]
    nlinarith only [hh,Nat.zero_le ((m+1)*P)]
  have hMassV : (row labels i).terms.length*V≤B := by
    have hh := Nat.mul_le_mul_right V hLen
    dsimp only [B,slopeCap]
    nlinarith only [hh]
  have hRoot := GeneralPaperRayAffineBound.rootWidth_mono D E A B (A+A) (B+B) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have he := GeneralPaperSparseResidualPrice.work primitive hMono W D E X V A B R hD hE hA hs.1 hs.2
    hRoot (row labels i) x w hx hw (unit_terms labels i) (constant_unit labels i) hMassX hMassV
  have hTerms := Nat.mul_le_mul_right (48*W+9*Q) (row_length labels i)
  change (GeneralPaperSparseResidualPrice.evaluate primitive W (row labels i) x w).2+
    GeneralPaperStaticRayScan.generation i*W+56*W+6*Q≤charge W Q i
  rw [←charge_eq]
  nlinarith only [he,hTerms]

theorem bounded {T m K : ℕ} (primitive : ℕ → ℕ) (W D E X V P : ℕ) (hm : 0<m)
    (labels : Fin T → Fin m → Fin K) (x w : Variable m K → ℚ)
    (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j)) (i : StaticIndex T m K) :
    GeneralPaperRayAffineBound.Bounded D E (interceptCap m X P) (slopeCap m V) (evaluate primitive W labels x w i).1 := by
  rw [data]
  have hh := GeneralPaperRaySparseSize.static_bound hm D E X V P labels (fun _ _ => 0) 0 i 0 x w hx hw
    ((Bounded.zero D).mono (Nat.zero_le P))
  apply GeneralPaperRayAffineBound.mono hh
  · unfold interceptCap
    nlinarith
  · unfold slopeCap
    nlinarith

end Blotto.GeneralPaperStaticRowPrice
