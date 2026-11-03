import Blotto.GeneralPaperRayOperandStorageHeight

/-! The native budget predicate joins every complete-query phase with its
short budget/probe rationals, returned whole witness, comparison scratch,
Boolean result and encoded native parent/return counters. The uniform H is
erased analysis and is derived from actual source probes by the caller. -/
namespace Blotto.GeneralPaperRayPredicateStorage
open RationalOrderCell GeneralPaperExactScoreDP GeneralPaperRayRationalBound
open GeneralPaperEncodedScalarStorage GeneralPaperScoreSelectionStorage
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192

def comparisonPrice {K : ℕ} (model : RationalCostModel) (beta : ℚ) : Option (GeneralPaperMinimum.Selection K) → ℕ
  | none => 0
  | some c => model.rat (RationalExpression.pairWidth beta c.cost)

def minimumPrice (model : RationalCostModel) (W m K S H : ℕ) : ℕ :=
  GeneralPaperRayMinimumBits.profile m K S W (model.rat H)

def price (model : RationalCostModel) (W m K S H : ℕ) : ℕ := minimumPrice model W m K S H+8*W+model.rat (1+2*H)
def metadataCap (model : RationalCostModel) (W m K S H : ℕ) : ℕ := m+K+S+1+price model W m K S H

theorem minimum_bounded {m K : ℕ} (model : RationalCostModel) (W D E X V S h : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a)) (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a))
    (t : ℚ) (ht : 0≤t ∧ t≤1) :
    GeneralPaperScoreSelectionStorage.Bounded m (GeneralPaperCommonLatticeDPBits.width (D*t.den) (X+V+1) m)
      (GeneralPaperRayMinimumBits.run model W matrix x w t S h).1 := by
  let inputs := (GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t).1
  have hFields := GeneralPaperRayFieldsBits.fields_bounded model W D E X V hED matrix x w hx hw t ht
  have hLen := (GeneralPaperRayQueryStorage.fields_length model W matrix x w t).le
  change GeneralPaperScoreSelectionStorage.Bounded m _ (GeneralPaperCommonLatticeMinimumBits.run model W S h inputs).1
  rw [GeneralPaperCommonLatticeMinimumBits.data]
  apply scan_bounded
  intro s _
  apply GeneralPaperHighMinimumStorage.candidate_bounded
  exact lattice_run_bounded (D*t.den) (X+V+1) m S (Nat.mul_pos hD t.den_pos) inputs hFields hLen

def window {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (S h : ℕ) (beta t : ℚ)
    (phase : GeneralPaperRayQueryStorage.Phase model W matrix x w t S) : ℕ :=
  let minimum := GeneralPaperRayMinimumBits.run model W matrix x w t S h
  let accepted := GeneralPaperRayPredicateBits.compareRun model W beta minimum.1
  let result := GeneralPaperRayPredicateBits.run model W matrix x w S h beta t
  GeneralPaperRayQueryStorage.window model W matrix x w t S h phase+rationalWordWidth beta+rationalWordWidth t+
    optionFootprint W minimum.1+comparisonPrice model beta minimum.1+
    fields W [S,h,minimum.2,accepted.2,result.2,minimum.2+accepted.2,comparisonPrice model beta minimum.1,8*W,
      if result.1=true then 1 else 0]+256*W

def profile (model : RationalCostModel) (W m K S H : ℕ) : ℕ :=
  GeneralPaperRayQueryStorageEnvelope.profile model W m K S H+2*(1+2*H)+optionProfile W K m H+model.rat (1+2*H)+
    9*(natBits (metadataCap model W m K S H)+W)+32*W+256*W

theorem bounded {m K : ℕ} (model : RationalCostModel) (W D E X V P s S h H : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (hs : ∀ j l,((matrix.read j).read l).1≤S)
    (x w : Variable m K → ℚ) (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a))
    (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a)) (beta : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta)
    (t : ℚ) (ht : 0≤t ∧ t≤1) (hT : RationalHeight t s)
    (hCommon : GeneralPaperCommonLatticeDPBits.width (D*t.den) (X+V+1) m≤H)
    (hCompare : GeneralPaperRayUniformSize.width D E m X V P+s≤H) (hh : h≤S)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) (hIndex : binaryWordWidth (S+2)≤W)
    (phase : GeneralPaperRayQueryStorage.Phase model W matrix x w t S) :
    window model W matrix x w S h beta t phase≤profile model W m K S H := by
  let minimum := GeneralPaperRayMinimumBits.run model W matrix x w t S h
  let accepted := GeneralPaperRayPredicateBits.compareRun model W beta minimum.1
  let result := GeneralPaperRayPredicateBits.run model W matrix x w S h beta t
  have hQuery := (GeneralPaperRayQueryStorage.all_phases model W S h D E X V hD hED matrix hs x w hx hw t ht hh hW hK hM hIndex phase).trans
    (GeneralPaperRayQueryStorageEnvelope.dominates model W m K S _ _ H hCommon)
  have hOutput := GeneralPaperScoreSelectionStorage.bounded_mono
    (minimum_bounded model W D E X V S h hD hED matrix x w hx hw t ht) le_rfl hCommon
  have hOutputBits := option_bound W m H minimum.1 hOutput
  have hBeta := rationalWordWidth_of_height ((GeneralPaperRayOperandStorageHeight.budget (E:=E) (m:=m) (X:=X) (V:=V) hD hb).mono
    ((Nat.le_add_right _ s).trans hCompare))
  have hProbe := rationalWordWidth_of_height (hT.mono (show s≤H by omega))
  have hComparison : comparisonPrice model beta minimum.1≤model.rat (1+2*H) := by
    cases hr : minimum.1 with
    | none => change 0≤_; omega
    | some c =>
      have hc : (GeneralPaperRayQueryWork.minimumRun matrix x w t S h).1=some c :=
        (GeneralPaperRayMinimumBits.data model W matrix x w t S h).symm.trans hr
      have ho := GeneralPaperRayComparisonOperandSize.predicate hD hED matrix x w hx hw beta hb t ht hT S h c hc
      have hCost := rationalWordWidth_of_height (ho.2.mono hCompare)
      change model.rat (RationalExpression.pairWidth beta c.cost)≤_
      apply model.monotone
      exact max_le hBeta hCost
  have hMinWork := (GeneralPaperRayMinimumBits.work model W D E X V hD hED matrix x w hx hw t ht S h hW hK hM hIndex).trans
    (GeneralPaperRayMinimumBits.profile_mono m K S W (model.monotone hCommon))
  change minimum.2≤minimumPrice model W m K S H at hMinWork
  have hAccepted : accepted.2=8*W+comparisonPrice model beta minimum.1 := by
    dsimp only [accepted]
    cases minimum.1 <;> rfl
  have hResult : result.2=minimum.2+accepted.2 := rfl
  have hBool : (if result.1=true then 1 else 0)≤1 := by split_ifs <;> omega
  have hf := fields_bound W (natBits (metadataCap model W m K S H))
    [S,h,minimum.2,accepted.2,result.2,minimum.2+accepted.2,comparisonPrice model beta minimum.1,8*W,
      if result.1=true then 1 else 0] (by
      intro n hn
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap price; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤9*(natBits (metadataCap model W m K S H)+W)+32*W at hf
  change GeneralPaperRayQueryStorage.window model W matrix x w t S h phase+rationalWordWidth beta+rationalWordWidth t+
    optionFootprint W minimum.1+comparisonPrice model beta minimum.1+
    fields W [S,h,minimum.2,accepted.2,result.2,minimum.2+accepted.2,comparisonPrice model beta minimum.1,8*W,
      if result.1=true then 1 else 0]+256*W≤_
  unfold profile
  omega

end Blotto.GeneralPaperRayPredicateStorage
