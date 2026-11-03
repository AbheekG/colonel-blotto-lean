import Blotto.GeneralPaperScoreArgumentStorage
import Blotto.GeneralPaperScoreMatrixConstructionStorage

/-! Complete native score-entry arithmetic storage. Literal argument
operands, bit quotient descent/unwind and work counters, returned quotient
record, stored score/anchor pair and both wrapper-work counters are joined.
All bounds precede any matrix/DP/endpoint acceptance assumption. -/
namespace Blotto.GeneralPaperScoreEntryStorage
open GeneralPaperBoundedQuotient GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

def metadataCap (model : RationalCostModel) (W depth S K V A : ℕ) : ℕ :=
  depth+S+K+1+GeneralPaperScoreMatrixBits.scoreProfile model W V depth K+
    GeneralPaperScoreMatrixBits.entryProfile model W V A depth K

def window {T m K : ℕ} (model : RationalCostModel) (W depth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) (j : Fin m) (l : Fin K) : ℕ :=
  let argument := GeneralPaperScoreArgumentBits.argumentRun model W v S j l
  let quotient := runWithBits model W argument.1 1 depth
  let score := GeneralPaperScoreMatrixBits.scoreRun model W depth v S j l
  let entry := GeneralPaperScoreMatrixBits.entryRun model W depth dict v S j l
  GeneralPaperScoreArgumentStorage.window model W v S j l+GeneralPaperBitQuotientStorage.peak model W argument.1 1 depth+
    GeneralPaperQuotientConstructionStorage.record W quotient.1+
    GeneralPaperEncodedScoreMatrixStorage.entryFootprint W entry.1+
    fields W [depth,S,K,score.1,score.2,entry.2]+256*W

def profile (model : RationalCostModel) (W m K S V A depth : ℕ) : ℕ :=
  let X := GeneralPaperScoreArgumentBits.height V depth K
  GeneralPaperScoreArgumentStorage.profile model W m K S V depth+GeneralPaperBitQuotientStorage.profile model W X 1 depth+
    (4*(1+2*heightBudget X 1 depth)+128*W)+GeneralPaperEncodedScoreMatrixStorage.entryProfile W S A+
    6*(natBits (metadataCap model W depth S K V A)+W)+32*W+256*W

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W depth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (S V A : ℕ)
    (hK : 0<K) (hCap : S<2^depth) (j : Fin m) (hv : RationalHeight (v.weight j) V)
    (l : Fin K) (ha : RationalHeight (dict.anchor j l) A) :
    window model W depth dict v S j l≤profile model W m K S V A depth := by
  have hArgument := GeneralPaperScoreArgumentStorage.bounded model W v S depth V hCap j hv l
  have hBounds := GeneralPaperScoreMatrixWork.argument_bounds v S hK j l
  have hRange : 0≤(GeneralPaperScoreArgumentBits.argumentRun model W v S j l).1 ∧
      (GeneralPaperScoreArgumentBits.argumentRun model W v S j l).1<(1:ℚ)*(2:ℚ)^depth := by
    rw [GeneralPaperScoreArgumentBits.argument_data]
    refine ⟨hBounds.1,?_⟩
    have hc : (S:ℚ)<(2:ℚ)^depth := by exact_mod_cast hCap
    simpa only [one_mul] using hBounds.2.trans_lt hc
  have hX := (GeneralPaperScoreArgumentBits.operands_height v S depth V hCap j hv l).2.2.2.2.2.2
  rw [GeneralPaperScoreArgumentBits.value_eq_argument] at hX
  have hXActual : RationalHeight (GeneralPaperScoreArgumentBits.argumentRun model W v S j l).1
      (GeneralPaperScoreArgumentBits.height V depth K) := by
    rw [GeneralPaperScoreArgumentBits.argument_data]
    exact hX
  have hOne : RationalHeight (1:ℚ) 1 := by norm_num [RationalHeight]
  have hQuotient := GeneralPaperBitQuotientStorage.bounded model W
    (GeneralPaperScoreArgumentBits.argumentRun model W v S j l).1 1 (by norm_num) depth _ 1 hRange.1 hRange.2 hXActual hOne
  have hRecord := GeneralPaperBitQuotientStorage.returned_record model W
    (GeneralPaperScoreArgumentBits.argumentRun model W v S j l).1 1 (by norm_num) depth _ 1 hRange.1 hRange.2 hXActual hOne
  have hEntry := GeneralPaperScoreMatrixConstructionStorage.entry_return model W depth S A dict v hK hCap j l ha
  have hScore : (GeneralPaperScoreMatrixBits.scoreRun model W depth v S j l).1≤S := by
    rw [GeneralPaperScoreMatrixBits.score_data model W depth v S hK hCap]
    exact GeneralPaperEncodedScoreMatrixStorage.score_bound v S hK j l
  have hScoreWork := GeneralPaperScoreMatrixBits.score_work model W depth v S V hK hCap j hv l
  have hEntryWork := GeneralPaperScoreMatrixBits.entry_work model W depth dict v S V A hK hCap j hv l ha
  have hf := fields_bound W (natBits (metadataCap model W depth S K V A))
    [depth,S,K,(GeneralPaperScoreMatrixBits.scoreRun model W depth v S j l).1,
      (GeneralPaperScoreMatrixBits.scoreRun model W depth v S j l).2,
      (GeneralPaperScoreMatrixBits.entryRun model W depth dict v S j l).2] (by
      intro n hn
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change fields W _≤6*(natBits (metadataCap model W depth S K V A)+W)+32*W at hf
  have hAll := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    hArgument hQuotient) hRecord) hEntry) hf) (256*W)
  exact hAll.trans_eq (by unfold profile; ring)

@[fun_prop]
theorem scaling (model : RationalCostModel) (m K S V A depth : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => profile model W m K S V A depth) := by
  unfold profile metadataCap GeneralPaperEncodedScoreMatrixStorage.entryProfile
    GeneralPaperScoreMatrixBits.entryProfile GeneralPaperScoreMatrixBits.scoreProfile
    GeneralPaperScoreArgumentBits.argumentProfile bitProfile
  dsimp only
  fun_prop

end Blotto.GeneralPaperScoreEntryStorage
