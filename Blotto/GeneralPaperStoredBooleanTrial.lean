import Blotto.GeneralPaperStoredFreshRead

/-! One trial loads its fresh-bit count and denominator, performs Boolean
borrow and reads stored categorical rows only when accepted. All source
cache arguments below occur in erased refinement hypotheses. -/
namespace Blotto.GeneralPaperStoredBooleanTrial
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

def run {S : Type*} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (next : S → Bool × S) (state : S) : GeneralPaperEqualBooleanTrial.Result ℕ S :=
  let fresh := GeneralPaperStoredFreshRead.read model A installed next state
  match fresh.bits with
  | none => ⟨none,fresh.state,fresh.reads,fresh.work + 64 * (A + 1)⟩
  | some bits =>
    let denominator := GeneralPaperStoredBooleanCacheRead.denominator model A installed
    match denominator.1 with
    | none => ⟨none,fresh.state,fresh.reads,fresh.work + denominator.2 + 64 * (A + 1)⟩
    | some ⟨_,word⟩ =>
      let compared := GeneralPaperBooleanBorrow.loop bits word.bits false []
      if compared.borrow then
        let selected := GeneralPaperStoredBooleanCacheRead.categorical model A installed bits
        ⟨selected.1,fresh.state,fresh.reads,fresh.work + denominator.2 + compared.work + selected.2 + 128 * (A + 1)⟩
      else ⟨none,fresh.state,fresh.reads,fresh.work + denominator.2 + compared.work + 64 * (A + 1)⟩

def price {S : Type*} {w : ℕ} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (next : S → Bool × S) (state : S) (word denominator : FixedBinaryWord w) : ℕ :=
  let compared := GeneralPaperBooleanBorrow.subtract word denominator
  (GeneralPaperStoredFreshRead.read model A installed next state).work +
    (GeneralPaperStoredBooleanCacheRead.denominator model A installed).2 + compared.2.2 +
    if compared.2.1 then (GeneralPaperStoredBooleanCacheRead.categorical model A installed word.bits).2 + 128 * (A + 1)
    else 64 * (A + 1)

theorem source {S : Type*} {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {prepared : GeneralPaperEqualPreparedCache.Prepared G l} (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (cache : GeneralPaperEqualBooleanCache.Cache prepared) (next : S → Bool × S) (state : S)
    (hCount : (GeneralPaperStoredRulerRead.read model A installed).1 = some prepared.rangeBits)
    (hDenominator : (GeneralPaperStoredBooleanCacheRead.denominator model A installed).1 =
      some (⟨prepared.rangeBits + 1,cache.denominator⟩ : Word))
    (hCategorical : ∀ word : FixedBinaryWord (prepared.rangeBits + 1),
      (GeneralPaperStoredBooleanCacheRead.categorical model A installed word.bits).1 =
        (GeneralPaperBooleanCategoricalSelect.run cache.rows word).1.map Fin.val) :
    (run model A installed next state).output = (GeneralPaperEqualBooleanTrial.run cache next state).output.map Fin.val ∧
      (run model A installed next state).state = (GeneralPaperEqualBooleanTrial.run cache next state).state ∧
      (run model A installed next state).reads = (GeneralPaperEqualBooleanTrial.run cache next state).reads ∧
      (run model A installed next state).work = price model A installed next state
        (GeneralPaperEqualBooleanTrial.readWord cache next state).1.1 cache.denominator := by
  obtain ⟨hv,hs,hr,_⟩ := GeneralPaperStoredFreshRead.source model A installed cache next state hCount
  have hrOld := (GeneralPaperEqualBooleanTrial.readWord_counts cache next state).1
  have hb : (GeneralPaperBooleanBorrow.loop (GeneralPaperEqualBooleanTrial.readWord cache next state).1.1.bits cache.denominator.bits false []).borrow =
      (GeneralPaperBooleanBorrow.subtract (GeneralPaperEqualBooleanTrial.readWord cache next state).1.1 cache.denominator).2.1 := rfl
  have hw : (GeneralPaperBooleanBorrow.loop (GeneralPaperEqualBooleanTrial.readWord cache next state).1.1.bits cache.denominator.bits false []).work =
      (GeneralPaperBooleanBorrow.subtract (GeneralPaperEqualBooleanTrial.readWord cache next state).1.1 cache.denominator).2.2 := rfl
  have hc := hCategorical (GeneralPaperEqualBooleanTrial.readWord cache next state).1.1
  simp only [run,hv,hDenominator,hb,hw,GeneralPaperEqualBooleanTrial.run,price]
  by_cases h : (GeneralPaperBooleanBorrow.subtract (GeneralPaperEqualBooleanTrial.readWord cache next state).1.1 cache.denominator).2.1 = true
  · simp only [h,ite_true,hc,hs,hr,hrOld,Nat.add_assoc,and_self]
  · have hf := Bool.eq_false_of_not_eq_true h
    simp only [hf,Bool.false_eq_true,ite_false,Option.map_none,hs,hr,hrOld,Nat.add_assoc,and_self]

end Blotto.GeneralPaperStoredBooleanTrial
