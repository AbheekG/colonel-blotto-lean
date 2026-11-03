import Blotto.GeneralPaperNativeSelectorPreparationPrice

/-! Full native selector prices, including conditional row conversion,
literal budget construction, descriptor transport and the strict zero
fallback. Returned tuple lengths supply every conversion cap. -/
namespace Blotto.GeneralPaperNativeSelectorPrice
open GeneralPaperNativeSelectorExecution GeneralPaperResponseTag
open GeneralPaperUnsignedCellConstancy (Prefix)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000

def profile (model : RationalCostModel) (W m lambda k Qv K J height leaves budgetWord : ℕ) : ℕ :=
  GeneralPaperNativeSelectorPreparationPrice.profile model W m lambda k Qv K height leaves+
    GeneralPaperOrderedRootPrice.profile model W m lambda k Qv K J (lambda+1) height budgetWord+
    GeneralPaperRowTrimPrice.profile W m leaves+256*W

def arithmeticProfile (m k K J depth height leaves : ℕ) : ℕ :=
  GeneralPaperNativeSelectorPreparationPrice.arithmeticProfile m k K height leaves+
    GeneralPaperOrderedRootPrice.arithmeticProfile K J depth height+(64*leaves+108*m+173)+256

theorem work {m k : ℕ} (model : RationalCostModel) (W Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ)
    (hp : prepared=GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows) (hWeights : ∑ j,weights.read j=Qv)
    (hGood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m ready.alphabet.lambda k Qv (prefixes.read j)) :
    (run true (fun x => x) model.rat W prepared T ready weights prefixes B).2≤
      profile model W m ready.alphabet.lambda k Qv ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        prepared.grid.size prepared.parameters.height prepared.parameters.leafCount (rationalWordWidth B) := by
  let tree := prepareTree true (fun x => x) model.rat W prepared T ready weights prefixes
  let root := GeneralPaperOrderedRootExecution.run true (fun x => x) model.rat W prepared.grid tree.1 (budget B)
  have hSpan := (GeneralPaperNativeSelectorPreparationPrice.span m ready.alphabet.lambda k Qv prepared hp).1
  have ht := GeneralPaperNativeSelectorPreparationPrice.work model W ready.alphabet.lambda Qv T prepared hp ready weights prefixes hT hWeights hGood
  have hTree := prepareTree_data true (fun x => x) model.rat W prepared T ready weights prefixes hSpan
  have hr := Nat.le_of_add_le_add_right (GeneralPaperOrderedRootPrice.native_work model W Qv T prepared ready weights prefixes B hp hT hWeights hGood).1
  rw [←hTree] at hr
  have hf : (finish (fun x => x) (GeneralPaperRowTrimPrice.word W m prepared.parameters.leafCount) m root.1).2≤
      GeneralPaperRowTrimPrice.profile W m prepared.parameters.leafCount := by
    cases hRoot : root.1 with
    | none => exact Nat.zero_le _
    | some result =>
      have hLen := GeneralPaperRootReturnedRows.length true (fun x => x) model.rat W prepared.grid tree.1 (budget B) result hRoot
      exact GeneralPaperRowTrimPrice.work W m prepared.parameters.leafCount result.2 (by rw [hLen,←hSpan])
  change tree.2+root.2+(finish (fun x => x) (GeneralPaperRowTrimPrice.word W m prepared.parameters.leafCount) m root.1).2+256*W≤_
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add ht hr) hf) _

theorem arithmetic_work {m k : ℕ} (model : RationalCostModel) (Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ)
    (hp : prepared=GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv) :
    (run false (fun _ => 1) model.rat 1 prepared T ready weights prefixes B).2≤
      arithmeticProfile m k ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        prepared.grid.size prepared.grid.depth prepared.parameters.height prepared.parameters.leafCount := by
  let tree := prepareTree false (fun _ => 1) model.rat 1 prepared T ready weights prefixes
  let root := GeneralPaperOrderedRootExecution.run false (fun _ => 1) (fun _ => 1) 1 prepared.grid tree.1 (budget B)
  have hSpan := (GeneralPaperNativeSelectorPreparationPrice.span m ready.alphabet.lambda k Qv prepared hp).1
  have ht := GeneralPaperNativeSelectorPreparationPrice.arithmetic_work model ready.alphabet.lambda Qv T prepared hp ready weights prefixes
  have hr := GeneralPaperOrderedRootPrice.arithmetic_work prepared.grid tree.1 (budget B)
  have hf : (finish (fun _ => 1) 1 m root.1).2≤64*prepared.parameters.leafCount+108*m+173 := by
    cases hRoot : root.1 with
    | none => exact Nat.zero_le _
    | some result =>
      have hLen := GeneralPaperRootReturnedRows.length false (fun _ => 1) (fun _ => 1) 1 prepared.grid tree.1 (budget B) result hRoot
      exact GeneralPaperRowTrimPrice.arithmetic_work m prepared.parameters.leafCount result.2 (by rw [hLen,←hSpan])
  change tree.2+root.2+(finish (fun _ => 1) 1 m root.1).2+256≤_
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add ht hr) hf) _

def pickProfile (model : RationalCostModel) (W m lambda k Qv K J height leaves budgetWord : ℕ) : ℕ :=
  profile model W m lambda k Qv K J height leaves budgetWord+GeneralPaperZeroRowPrice.profile W m+128*W

def pickArithmeticProfile (m k K J depth height leaves : ℕ) : ℕ :=
  arithmeticProfile m k K J depth height leaves+(108*m+108)+128

theorem native_work {m k : ℕ} (model : RationalCostModel) (W Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ)
    (hp : prepared=GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows) (hWeights : ∑ j,weights.read j=Qv)
    (hGood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m ready.alphabet.lambda k Qv (prefixes.read j)) :
    (pick true (fun x => x) model.rat W prepared T ready weights prefixes B).2≤
      pickProfile model W m ready.alphabet.lambda k Qv ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        prepared.grid.size prepared.parameters.height prepared.parameters.leafCount (rationalWordWidth B) ∧
    (pick false (fun _ => 1) model.rat 1 prepared T ready weights prefixes B).2≤
      pickArithmeticProfile m k ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        prepared.grid.size prepared.grid.depth prepared.parameters.height prepared.parameters.leafCount := by
  have hb := work model W Qv T prepared ready weights prefixes B hp hT hWeights hGood
  have ha := arithmetic_work model Qv T prepared ready weights prefixes B hp
  have hz := GeneralPaperZeroRowPrice.work W m k
  have hza := GeneralPaperZeroRowPrice.arithmetic_work m k
  exact ⟨Nat.add_le_add_right (Nat.add_le_add hb hz) _,Nat.add_le_add_right (Nat.add_le_add ha hza) _⟩

end Blotto.GeneralPaperNativeSelectorPrice
