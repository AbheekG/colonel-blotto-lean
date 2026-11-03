import Blotto.GeneralPaperFixedTupleDecodePrice

/-! The native processed-table invariant supplies the fixed-scan operand
caps and the exact predecessor length of its returned entry. No witness,
cost or label-shape oracle is supplied.
-/
namespace Blotto.GeneralPaperNativeFixedScanPrice
open GeneralPaperRayAffineScoreStep GeneralPaperRayAffineDPSize GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem work {S K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (table : Table S K) (hp : TableBounded D E X V n table) (h : ℕ) (beta : ℚ)
    (hb : GeneralPaperRayRationalBound.Bounded D P beta) (sample : ℚ)
    (ht : RationalHeight sample (2*width D E m X V P+3)) :
    (GeneralPaperFixedViolationPrice.run primitive W table h beta sample).work≤
      GeneralPaperFixedViolationPrice.profile S W (primitive (6*width D E m X V P+9)) := by
  have hTable := GeneralPaperNativeAffinePrices.table_cap D E m X V P n hn table hp
  have hP : P≤ interceptCap m X P := by
    unfold interceptCap
    nlinarith only [Nat.zero_le ((m+1)*X),Nat.zero_le (m*P)]
  have hConst : GeneralPaperRayAffineBound.Bounded D E (interceptCap m X P) (slopeCap m V)
      (GeneralPaperRayBudgetCrossings.constant beta) :=
    ⟨hb.mono hP,(GeneralPaperRayRationalBound.Bounded.zero E).mono (Nat.zero_le _)⟩
  have hR := GeneralPaperRayAffineBound.rootWidth_mono D E (interceptCap m X P) (slopeCap m V)
    (interceptCap m X P+interceptCap m X P) (slopeCap m V+slopeCap m V)
    (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hBeta := (GeneralPaperAffineValuePrice.coefficients hD hE _ hConst).1.mono hR
  have hh := GeneralPaperFixedViolationPrice.work primitive hMono W D E (interceptCap m X P) (slopeCap m V)
    (width D E m X V P) (2*width D E m X V P+3) hD hE hR table hTable h beta sample hBeta ht
  have he : 1+2*(width D E m X V P+(2*width D E m X V P+3)+1)=6*width D E m X V P+9 := by ring
  rw [he] at hh
  exact hh

theorem selected_length {S K : ℕ} (primitive : ℕ → ℕ) (W D E X V n : ℕ)
    (table : Table S K) (hp : TableBounded D E X V n table) (h : ℕ) (beta sample : ℚ)
    (entry : GeneralPaperRayFixedViolation.Entry S K)
    (he : (GeneralPaperFixedViolationPrice.run primitive W table h beta sample).value=some entry) :
    entry.2.labels.length=n := by
  rw [GeneralPaperFixedViolationPrice.data] at he
  have hv := GeneralPaperRayFixedViolation.scan_valid table h beta sample (List.finRange (S+1)) entry he
  exact (hp entry.1 entry.2 hv.2.1).2

end Blotto.GeneralPaperNativeFixedScanPrice
