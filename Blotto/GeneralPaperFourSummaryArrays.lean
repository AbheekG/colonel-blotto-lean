import Blotto.GeneralPaperSummaryFamilyPrice

/-! Four complete native summary families are retained together. The signed
height is formed once and priced. The epoch-cache equality identifies the
next consumer; optimizer/catalogue/field-plan preparation is not priced by
this summary-only bound and remains a subsequent required join.
-/
namespace Blotto.GeneralPaperFourSummaryArrays
open GeneralPaperCodeAlphabet GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperCatalogueTreeCache
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

structure Arrays (m k : ℕ) where
  p : FixedArrayTable m (Summary k)
  q : FixedArrayTable m (Summary k)
  lambda : FixedArrayTable m (Summary k)
  mu : FixedArrayTable m (Summary k)

def specification {m k : ℕ} (powers : GeneralPaperPreparedPowers.Prepared) (digits : ℕ) (a : Alphabet) (trees : Trees m a.lambda) : Arrays m k :=
  ⟨summaries powers digits k trees.p,summaries powers digits k trees.q,
    summaries powers digits k trees.lambda,summaries powers digits k trees.mu⟩

def run (bits : Bool) (index primitive : ℕ → ℕ) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) : Arrays m k × ℕ :=
  let signedHeight := a.lambda+1
  let p := GeneralPaperSummaryFamilyPrice.run bits index primitive W m a.lambda k Qv c hc digits a.lambda trees.p
  let q := GeneralPaperSummaryFamilyPrice.run bits index primitive W m a.lambda k Qv c hc digits a.lambda trees.q
  let lambda := GeneralPaperSummaryFamilyPrice.run bits index primitive W m a.lambda k Qv c hc digits signedHeight trees.lambda
  let mu := GeneralPaperSummaryFamilyPrice.run bits index primitive W m a.lambda k Qv c hc digits signedHeight trees.mu
  (⟨p.1,q.1,lambda.1,mu.1⟩,p.2+q.2+lambda.2+mu.2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) a.lambda 1+128*W)

def profile (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  2*GeneralPaperSummaryFamilyPrice.profile primitive W m lambda k Qv lambda+
  2*GeneralPaperSummaryFamilyPrice.profile primitive W m lambda k Qv (lambda+1)+
  2*primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+128*W

def arithmeticProfile (m lambda k Qv : ℕ) : ℕ :=
  2*GeneralPaperSummaryFamilyPrice.arithmeticProfile m lambda k Qv lambda+
  2*GeneralPaperSummaryFamilyPrice.arithmeticProfile m lambda k Qv (lambda+1)+130

theorem data (bits : Bool) (index primitive : ℕ → ℕ) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees) :
    (run bits index primitive W m k Qv a c hc digits trees).1=specification c.powers digits a trees := by
  have hp := GeneralPaperSummaryFamilyPrice.data bits index primitive W m a.lambda k Qv c hc digits a.lambda trees.p
    (by omega) (hValid .p) (hPaths .p)
  have hq := GeneralPaperSummaryFamilyPrice.data bits index primitive W m a.lambda k Qv c hc digits a.lambda trees.q
    (by omega) (hValid .q) (hPaths .q)
  have hl := GeneralPaperSummaryFamilyPrice.data bits index primitive W m a.lambda k Qv c hc digits (a.lambda+1) trees.lambda
    (Nat.le_refl _) (hValid .lambda) (hPaths .lambda)
  have hm := GeneralPaperSummaryFamilyPrice.data bits index primitive W m a.lambda k Qv c hc digits (a.lambda+1) trees.mu
    (Nat.le_refl _) (hValid .mu) (hPaths .mu)
  unfold run specification
  dsimp only
  rw [hp,hq,hl,hm]

theorem bit_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (hDigits : digits=GeneralPaperQuantileComparison.width a.lambda k)
    (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees) :
    (run true (fun w => w) primitive W m k Qv a c hc digits trees).2≤profile primitive W m a.lambda k Qv := by
  have hp := GeneralPaperSummaryFamilyPrice.bit_work primitive hMono W m a.lambda k Qv c hc digits a.lambda hDigits trees.p
    (by omega) (hValid .p) (hPaths .p)
  have hq := GeneralPaperSummaryFamilyPrice.bit_work primitive hMono W m a.lambda k Qv c hc digits a.lambda hDigits trees.q
    (by omega) (hValid .q) (hPaths .q)
  have hl := GeneralPaperSummaryFamilyPrice.bit_work primitive hMono W m a.lambda k Qv c hc digits (a.lambda+1) hDigits trees.lambda
    (Nat.le_refl _) (hValid .lambda) (hPaths .lambda)
  have hm := GeneralPaperSummaryFamilyPrice.bit_work primitive hMono W m a.lambda k Qv c hc digits (a.lambda+1) hDigits trees.mu
    (Nat.le_refl _) (hValid .mu) (hPaths .mu)
  have hWord := GeneralPaperQuantileDescentControls.height_word m a.lambda k Qv
  have hHeight := (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b) a.lambda 1 (a.lambda+2)
    (by omega) (by omega) (by omega)).trans (Nat.mul_le_mul_left 2 (hMono hWord))
  unfold run profile
  dsimp only
  omega

theorem arithmetic_work (m k Qv : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (hDigits : digits=GeneralPaperQuantileComparison.width a.lambda k) (trees : Trees m a.lambda) :
    (run false (fun _ => 1) (fun _ => 1) 1 m k Qv a c hc digits trees).2≤arithmeticProfile m a.lambda k Qv := by
  have hp := GeneralPaperSummaryFamilyPrice.arithmetic_work m a.lambda k Qv c hc digits a.lambda hDigits trees.p
  have hq := GeneralPaperSummaryFamilyPrice.arithmetic_work m a.lambda k Qv c hc digits a.lambda hDigits trees.q
  have hl := GeneralPaperSummaryFamilyPrice.arithmetic_work m a.lambda k Qv c hc digits (a.lambda+1) hDigits trees.lambda
  have hm := GeneralPaperSummaryFamilyPrice.arithmetic_work m a.lambda k Qv c hc digits (a.lambda+1) hDigits trees.mu
  change (GeneralPaperSummaryFamilyPrice.run false (fun _ => 1) (fun _ => 1) 1 m a.lambda k Qv c hc digits a.lambda trees.p).2+
    (GeneralPaperSummaryFamilyPrice.run false (fun _ => 1) (fun _ => 1) 1 m a.lambda k Qv c hc digits a.lambda trees.q).2+
    (GeneralPaperSummaryFamilyPrice.run false (fun _ => 1) (fun _ => 1) 1 m a.lambda k Qv c hc digits (a.lambda+1) trees.lambda).2+
    (GeneralPaperSummaryFamilyPrice.run false (fun _ => 1) (fun _ => 1) 1 m a.lambda k Qv c hc digits (a.lambda+1) trees.mu).2+2+128≤_
  unfold arithmeticProfile
  omega

theorem epoch_cache_data (bits : Bool) (index primitive : ℕ → ℕ) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees) :
    let arrays := (run bits index primitive W m k Qv a c hc digits trees).1
    GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu=
      GeneralPaperCatalogueTreeCache.prepare c.powers digits a k trees := by
  dsimp only
  rw [data bits index primitive W m k Qv a c hc digits trees hValid hPaths]
  rfl

theorem same_data (primitive : ℕ → ℕ) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees) :
    (run true (fun w => w) primitive W m k Qv a c hc digits trees).1=
      (run false (fun _ => 1) (fun _ => 1) 1 m k Qv a c hc digits trees).1 := by
  rw [data true (fun w => w) primitive W m k Qv a c hc digits trees hValid hPaths,
    data false (fun _ => 1) (fun _ => 1) 1 m k Qv a c hc digits trees hValid hPaths]

end Blotto.GeneralPaperFourSummaryArrays
