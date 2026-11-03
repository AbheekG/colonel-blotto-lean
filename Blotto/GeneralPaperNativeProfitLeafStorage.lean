import Blotto.GeneralPaperNativeProfitScalarStorage
import Blotto.GeneralPaperProfitFieldConstructionStorage

/-! One active native option callback joins its signed-tail children,
coefficient and integer temporaries, borrowed tag/full returned option,
annotation addition and primitive scratch. The source-derived Ready object
supplies all mesh/tag/code caps, including zero weights. -/
namespace Blotto.GeneralPaperNativeProfitLeafStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def elementWindow {m k : ℕ} (model : RationalCostModel) (W : ℕ)
    (r : GeneralPaperCatalogueOptimizer.Ready m k) (weight : ℕ) (prefixes : Prefix k) (j : Fin m)
    (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) : ℕ :=
  let T := (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows
  let plan := r.cached.read j
  let queried := GeneralPaperMeshPairExecution.tails true model.rat W plan.mesh prefixes plan.tails i
  let found := GeneralPaperNativeProfitLeafExecution.element true model.rat W (2*T*weight) prefixes plan i
  GeneralPaperNativeProfitScalarStorage.coefficientWindow model W T weight+
    GeneralPaperMeshPairStorage.tailsWindow model W plan.mesh prefixes plan.tails i+
    GeneralPaperNativeProfitScalarStorage.profitWindow model W (2*T*weight) plan.mesh queried.1.positive queried.1.negative+
    GeneralPaperEncodedProfitField.optionBits W found.1+
    fields W [queried.1.work,24,queried.1.work+24]+
    fields W [m,j.val,(GeneralPaperSourceParameters.prepare k).summarySize+2,i.val]+found.2+256*W

def elementProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  GeneralPaperNativeProfitScalarStorage.coefficientProfile model W m lambda k Qv+
    GeneralPaperMeshPairStorage.tailsProfile model W m lambda k Qv K+
    GeneralPaperNativeProfitScalarStorage.profitProfile model W m lambda k Qv+
    GeneralPaperProfitFieldConstructionStorage.optionCap W m lambda k Qv+
    (3*(H+W)+32*W)+(4*(natBits (m+1)+natBits (K+1)+W)+32*W)+
    GeneralPaperNativeProfitLeafPrice.elementProfile model.rat W m lambda k Qv+256*W

theorem element_bounded {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ)
    (r : GeneralPaperCatalogueOptimizer.Ready m k) (weight : ℕ) (prefixes : Prefix k) (j : Fin m)
    (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (hw : weight≤Qv) (hg : GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv prefixes) :
    elementWindow model W r weight prefixes j i≤elementProfile model W m r.alphabet.lambda k Qv := by
  let T := (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  let plan := r.cached.read j
  let queried := GeneralPaperMeshPairExecution.tails true model.rat W plan.mesh prefixes plan.tails i
  let found := GeneralPaperNativeProfitLeafExecution.element true model.rat W (2*T*weight) prefixes plan i
  have hm := GeneralPaperActualNativeProfitFields.meshes r j
  have hc := GeneralPaperNativeProfitScalarStorage.coefficient_bounded model W m r.alphabet.lambda k Qv T weight rfl hw
  have ht := GeneralPaperMeshPairStorage.tails_bounded model W m r.alphabet.lambda Qv plan.mesh prefixes plan.tails i hm hg
  have hpos := GeneralPaperMeshCountBounds.cached_interval_bound true model.rat W m r.alphabet.lambda Qv plan.mesh prefixes plan.tails.positive
    i.castSucc (Fin.last K) hm hg
  have hneg := GeneralPaperMeshCountBounds.cached_interval_bound true model.rat W m r.alphabet.lambda Qv plan.mesh prefixes plan.tails.negative
    i.castSucc (Fin.last K) hm hg
  have hp := GeneralPaperNativeProfitScalarStorage.profit_bounded model W m r.alphabet.lambda k Qv T plan.mesh weight
    queried.1.positive queried.1.negative rfl hm hw hpos hneg
  have hr := GeneralPaperProfitFieldConstructionStorage.element_bound true model.rat W W Qv r weight prefixes j hw hg i
  have hwork : queried.1.work=24*(30+k)+124 := by
    rw [GeneralPaperMeshPairExecution.tails_data true model.rat W plan.mesh prefixes plan.tails i hm,GeneralPaperSignedTailPlan.evaluate_work]
  have hf := GeneralPaperMeshPairStorage.metadata_fields W m r.alphabet.lambda k Qv [queried.1.work,24,queried.1.work+24] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    all_goals (unfold GeneralPaperMeshQueryMetadata.cap; omega))
  have hi := fields_bound W (natBits (m+1)+natBits (K+1)) [m,j.val,K,i.val] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    have hmword : natBits m≤natBits (m+1) := Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
    have hjword : natBits j.val≤natBits (m+1) := Nat.add_le_add_left (binaryWordWidth_mono (by have := j.isLt; omega)) 1
    have hKword : natBits K≤natBits (K+1) := Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
    have hiword : natBits i.val≤natBits (K+1) := Nat.add_le_add_left (binaryWordWidth_mono (by have := i.isLt; omega)) 1
    rcases hx with rfl|rfl|rfl|rfl
    all_goals omega)
  have hprice := GeneralPaperNativeProfitLeafPrice.element_bit_work model.rat model.monotone W m r.alphabet.lambda Qv T weight prefixes plan i rfl hw hm hg
  dsimp only [elementWindow,elementProfile]
  dsimp only [plan,T,queried] at hc ht hp hf hprice
  simp only [List.length_cons,List.length_nil] at hf hi
  dsimp only [K] at hi
  omega

end Blotto.GeneralPaperNativeProfitLeafStorage
