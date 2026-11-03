import Blotto.GeneralPaperPhysicalResponseRowsDriver

/-! Instantiate the complete checked source-to-row driver with the actual
prepared caches and derived proxy budgets. These are erased observations
of native executions; the final proxy-once driver and extended storage word
are subsequent joins. -/
namespace Blotto.GeneralPaperPhysicalResponseRowsContract
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperSourceStorageRates GeneralPaperSourceCoreLogBound
open GeneralPaperInitializerPreparedPoint GeneralPaperCatalogueShared GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384

def bitProfile (C d W : ℕ) (x : Input) : ℕ :=
  GeneralPaperPhysicalResponseRowsDriver.bitProfile C d W x.k x.Qv
    (GeneralPaperProxyParameters.prepare x.m x.k).qbar ((alphabet x).lambda+1) (alphabet x)
    (prepare (alphabet x) x.k x.Qv x.weights 0 0)

def arithmeticProfile (x : Input) : ℕ :=
  GeneralPaperPhysicalResponseRowsDriver.arithmeticProfile x.k x.Qv (alphabet x)
    (prepare (alphabet x) x.k x.Qv x.weights 0 0)

theorem bit_soft (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Soft GeneralPaperSharpSourceBitRate.sourceRate (fun x => bitProfile C d (W x) x) := by
  have hSource := GeneralPaperPhysicalResponseSourceRates.bit_soft C d W hW
  have hRows := rate_mono (GeneralPaperSourceRowsRates.bitCertificate C d W hW).bound
    (fun x => Nat.le_add_right (monomial 1 3 2 x) (monomial 1 2 4 x))
  have hTail : Polylog (fun x => 96*arrayWord (W x)
      (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs) := by
    have hw := of_tight hW
    unfold arrayWord
    fun_prop
  have ht := poly_at_rate hTail (fun x =>
    (monomial_positive 1 3 2 x).trans (Nat.le_add_right _ (monomial 1 2 4 x)))
  exact add_same (add_same hSource hRows) ht

theorem arithmetic_soft : Soft GeneralPaperSharpSourceRealRate.sourceRate arithmeticProfile := by
  have hSource := GeneralPaperPhysicalResponseSourceRates.arithmetic_soft
  have hRows := rate_mono GeneralPaperSourceRowsRates.arithmeticCertificate.bound
    (fun x => Nat.le_add_right (monomial 1 2 2 x) (monomial 1 1 4 x))
  have hTail := poly_at_rate (poly_constant 96) (fun x =>
    (monomial_positive 1 2 2 x).trans (Nat.le_add_right _ (monomial 1 1 4 x)))
  exact add_same (add_same hSource hRows) hTail

theorem paper_real_bound : ∃ A e : ℕ,∀ x,1≤x.m →arithmeticProfile x≤
    A*GeneralPaperSharpSourceRealRate.paperRate x*(coreLog x)^e := by
  rcases remove_unused_height arithmetic_soft (fun _ => rfl) (fun _ => rfl) with ⟨A,e,hA⟩
  refine ⟨8*A,e,?_⟩
  intro x hm
  exact (hA x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A
    (GeneralPaperSharpSourceRealRate.nonempty_rate x hm))).trans_eq (by ring))

theorem paper_bit_bound (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : ∃ A e : ℕ,∀ x,1≤x.m →bitProfile C d (W x) x≤
    A*GeneralPaperSharpSourceBitRate.paperRate x*(logSize x)^e := by
  rcases bit_soft C d W hW with ⟨A,e,hA⟩
  refine ⟨16*A,e,?_⟩
  intro x hm
  exact (hA x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A
    (GeneralPaperSharpSourceBitRate.nonempty_rate x hm))).trans_eq (by ring))

noncomputable def preparedRun (bits : Bool) (actual : RationalCostModel) (W : ℕ) (x : Input) :=
  let Bc := ownBudget x.m x.k (x.b:ℝ) x.reciprocal
  let Br := opposingBudget x.m x.k (x.b:ℝ) x.reciprocal
  let ready := (GeneralPaperPreparedSharedSource.prepare actual x.k x.Qv x.b x.weights Bc Br).1
  let c := ready.2.source
  let hc : c=GeneralPaperMaterializedPowerCache.specification x.m (alphabet x).lambda x.k x.Qv := by
    dsimp only [c,ready]
    rw [GeneralPaperPreparedSharedSource.data]
    rfl
  let hs : ready.1.2=prepare (alphabet x) x.k x.Qv x.weights Bc Br := by
    dsimp only [ready]
    rw [GeneralPaperPreparedSharedSource.data]
    rfl
  GeneralPaperPhysicalResponseRowsDriver.run bits actual W x.k x.Qv
    (GeneralPaperProxyParameters.prepare x.m x.k).qbar (alphabet x) c hc x.weights Bc Br ready.1.2 hs

theorem native_real_profile (actual : RationalCostModel) (x : Input) :
    (preparedRun false actual 1 x).2≤arithmeticProfile x := by
  let Bc := ownBudget x.m x.k (x.b:ℝ) x.reciprocal
  let Br := opposingBudget x.m x.k (x.b:ℝ) x.reciprocal
  let ready := (GeneralPaperPreparedSharedSource.prepare actual x.k x.Qv x.b x.weights Bc Br).1
  let c := ready.2.source
  have hc : c=GeneralPaperMaterializedPowerCache.specification x.m (alphabet x).lambda x.k x.Qv := by
    dsimp only [c,ready]
    rw [GeneralPaperPreparedSharedSource.data]
    rfl
  have hs : ready.1.2=prepare (alphabet x) x.k x.Qv x.weights Bc Br := by
    dsimp only [ready]
    rw [GeneralPaperPreparedSharedSource.data]
    rfl
  have h := GeneralPaperPhysicalResponseRowsDriver.arithmetic_work actual x.k x.Qv
    (GeneralPaperProxyParameters.prepare x.m x.k).qbar (alphabet x) c hc x.weights Bc Br ready.1.2 hs x.weight_sum
  have hp : GeneralPaperPhysicalResponseRowsDriver.arithmeticProfile x.k x.Qv (alphabet x) ready.1.2=arithmeticProfile x := by
    rw [hs]
    rfl
  exact h.trans_eq hp

theorem native_bit_profile {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W : ℕ) (x : Input) : (preparedRun true actual W x).2≤bitProfile C d W x := by
  let Bc := ownBudget x.m x.k (x.b:ℝ) x.reciprocal
  let Br := opposingBudget x.m x.k (x.b:ℝ) x.reciprocal
  let ready := (GeneralPaperPreparedSharedSource.prepare actual x.k x.Qv x.b x.weights Bc Br).1
  let c := ready.2.source
  have hc : c=GeneralPaperMaterializedPowerCache.specification x.m (alphabet x).lambda x.k x.Qv := by
    dsimp only [c,ready]
    rw [GeneralPaperPreparedSharedSource.data]
    rfl
  have hs : ready.1.2=prepare (alphabet x) x.k x.Qv x.weights Bc Br := by
    dsimp only [ready]
    rw [GeneralPaperPreparedSharedSource.data]
    rfl
  have hb : (0:ℝ)<x.b ∧ (x.b:ℝ)<1 := by exact_mod_cast x.hb
  have hbc := (GeneralPaperSourceBudgetWidths.own_word x.m x.k (x.b:ℝ) hb x.reciprocal).trans
    (GeneralPaperSourceBudgetWidths.leaf_word x.m x.k 0)
  have hbr := (GeneralPaperSourceBudgetWidths.opposing_word x.m x.k (x.b:ℝ) hb x.reciprocal).trans
    (GeneralPaperSourceBudgetWidths.leaf_word x.m x.k 0)
  have h := GeneralPaperPhysicalResponseRowsDriver.bit_work hg W x.k x.Qv
    (GeneralPaperProxyParameters.prepare x.m x.k).qbar ((alphabet x).lambda+1) (alphabet x) c hc x.weights Bc Br
    ready.1.2 hs x.weight_sum
    (GeneralPaperSourceBudgetWidths.own_height x.m x.k (x.b:ℝ) hb x.reciprocal)
    (GeneralPaperSourceBudgetWidths.opposing_height x.m x.k (x.b:ℝ) hb x.reciprocal) hbc hbr
  have hp : GeneralPaperPhysicalResponseRowsDriver.bitProfile C d W x.k x.Qv
      (GeneralPaperProxyParameters.prepare x.m x.k).qbar ((alphabet x).lambda+1) (alphabet x) ready.1.2=bitProfile C d W x := by
    rw [hs]
    rfl
  exact h.trans_eq hp

theorem native_paper_time {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W : Input → ℕ) (hW : Tight W) : ∃ Ar er Ab eb : ℕ,∀ x,1≤x.m →
      (preparedRun false actual 1 x).2≤Ar*GeneralPaperSharpSourceRealRate.paperRate x*(coreLog x)^er ∧
      (preparedRun true actual (W x) x).2≤Ab*GeneralPaperSharpSourceBitRate.paperRate x*(logSize x)^eb := by
  rcases paper_real_bound with ⟨Ar,er,hr⟩
  rcases paper_bit_bound C d W hW with ⟨Ab,eb,hb⟩
  exact ⟨Ar,er,Ab,eb,fun x hm => ⟨(native_real_profile actual x).trans (hr x hm),
    (native_bit_profile hg (W x) x).trans (hb x hm)⟩⟩

theorem native_checks (bits : Bool) (actual : RationalCostModel) (W : ℕ) (x : Input)
    (hm : 0<x.m) (hQv : 0<x.Qv) : (preparedRun bits actual W x).1.2=true := by
  let rho := (GeneralPaperProxyClassifier.classify x.m x.k (x.b:ℝ)).choice.proxy.value
  have hb : (0:ℝ)<x.b ∧ (x.b:ℝ)<1 := by exact_mod_cast x.hb
  have hDc : (ownBudget x.m x.k (x.b:ℝ) x.reciprocal).den∣rho.den := by
    cases x.reciprocal <;> simp [ownBudget,rho]
  have hDr : (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal).den∣rho.den := by
    cases x.reciprocal <;> simp [opposingBudget,rho]
  have hBr : 0≤opposingBudget x.m x.k (x.b:ℝ) x.reciprocal := by
    cases x.reciprocal
    · exact (GeneralPaperProxyClassifier.proxy_unit x.m x.k (x.b:ℝ) hb).1.le
    · exact zero_le_one
  exact GeneralPaperPhysicalResponseRowsDriver.checked bits actual W x.k x.Qv rho.den
    (GeneralPaperProxyParameters.prepare x.m x.k).qbar (alphabet x) _ _ x.weights
    (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal)
    _ (by rw [GeneralPaperPreparedSharedSource.data]; rfl) hm hQv x.weight_sum
    (own_positive x.m x.k (x.b:ℝ) hb x.reciprocal).le hBr (Rat.den_pos rho)
    (GeneralPaperProxyClassifier.proxy_reduced_denominator x.m x.k (x.b:ℝ)) hDc hDr

theorem native_initializer_rows (bits : Bool) (actual : RationalCostModel) (W : ℕ) (x : Input) :
    (preparedRun bits actual W x).1.1=GeneralPaperSourceInitializer.sourceRows x.k x.Qv x.weights (x.b:ℝ) x.reciprocal :=
  GeneralPaperPhysicalResponseRowsDriver.rational_data bits actual W x.k x.Qv
    (GeneralPaperProxyParameters.prepare x.m x.k).qbar (alphabet x) _ _ x.weights
    (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal)
    _ (by rw [GeneralPaperPreparedSharedSource.data]; rfl)

theorem native_model_data (actual : RationalCostModel) (W : ℕ) (x : Input) (hm : 0<x.m) (hQv : 0<x.Qv) :
    (preparedRun true actual W x).1=(preparedRun false actual 1 x).1 := by
  apply Prod.ext
  · exact (native_initializer_rows true actual W x).trans (native_initializer_rows false actual 1 x).symm
  · rw [native_checks true actual W x hm hQv,native_checks false actual 1 x hm hQv]

theorem native_hard_budget (bits : Bool) (actual : RationalCostModel) (W : ℕ) (x : Input)
    (hm : 0<x.m) (hQv : 0<x.Qv) (i : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows) :
    Feasible (ownBudget x.m x.k (x.b:ℝ) x.reciprocal:ℝ)
      (fun j => (((preparedRun bits actual W x).1.1.read i).read j:ℝ)) := by
  rw [native_initializer_rows]
  exact GeneralPaperSourceInitializer.source_rows_feasible x.k x.Qv hm hQv x.weights x.weight_sum
    (x.b:ℝ) (by exact_mod_cast x.hb) x.reciprocal i

theorem native_coordinate_height (bits : Bool) (actual : RationalCostModel) (W : ℕ) (x : Input)
    (i : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows) (j : Fin x.m) :
    RationalHeight (((preparedRun bits actual W x).1.1.read i).read j) (binaryWordWidth (alphabet x).C) := by
  rw [native_initializer_rows]
  exact GeneralPaperSourceScoreHeights.rows_height x.k x.Qv x.weights (x.b:ℝ) x.reciprocal i j

end Blotto.GeneralPaperPhysicalResponseRowsContract
