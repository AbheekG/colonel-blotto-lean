import Blotto.GeneralPaperActualProfitGridQueryStorage

/-! Native mesh-query storage joins the bounded-quotient selected stack,
raw/final records, three casts, product, divisor and short native controls.
Cached total words derive all heights; no probability/prefix scan executes. -/
namespace Blotto.GeneralPaperMeshQueryStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem inputs (m lambda k Qv mesh num total : ℕ)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (ht : 0<total) (hn : num≤total)
    (hw : natBits total≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) :
    let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
    let x := (mesh:ℚ)*(num:ℚ)
    (0:ℚ)<(total:ℚ) ∧ 0≤x ∧ x<(total:ℚ)*(2:ℚ)^(30+k) ∧ RationalHeight x (2*H) ∧ RationalHeight (total:ℚ) H := by
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  have hmesh : binaryWordWidth mesh≤H := by
    have h := GeneralPaperMeshQueryEnvelope.mesh_word m lambda k Qv
    rw [←hm] at h
    change 1+binaryWordWidth mesh≤H at h
    omega
  have htotal : binaryWordWidth total≤H := by change 1+binaryWordWidth total≤H at hw; omega
  have hnum := (binaryWordWidth_mono hn).trans htotal
  have hM := (GeneralPaperBasisDivideBits.nat_height mesh).mono hmesh
  have hN := (GeneralPaperBasisDivideBits.nat_height num).mono hnum
  have hT := (GeneralPaperBasisDivideBits.nat_height total).mono htotal
  have hX : RationalHeight ((mesh:ℚ)*num) (2*H) := (hM.mul hN).mono (by omega)
  have hpositive : (0:ℚ)<(total:ℚ) := by exact_mod_cast ht
  have hnum' : (num:ℚ)≤total := by exact_mod_cast hn
  have hmesh' : (mesh:ℚ)<(2:ℚ)^(30+k) := by
    have h := GeneralPaperCDFMesh.selected_depth k
    rw [←hm] at h
    exact_mod_cast h
  have h1 := mul_le_mul_of_nonneg_left hnum' (show (0:ℚ)≤mesh by positivity)
  have h2 := mul_lt_mul_of_pos_left hmesh' hpositive
  exact ⟨hpositive,by positivity,by nlinarith only [h1,h2],hX,hT⟩

theorem record_annotation (W extra : ℕ) (r : GeneralPaperBoundedQuotient.Result) :
    GeneralPaperQuotientConstructionStorage.record W ⟨r.quotient,r.remainder,r.work+extra⟩≤
      GeneralPaperQuotientConstructionStorage.record W r+natBits (r.work+extra) := by
  unfold GeneralPaperQuotientConstructionStorage.record fields
  dsimp only
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega

def recordProfile (W m lambda k Qv : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  4*(1+2*GeneralPaperBoundedQuotient.heightBudget (2*H) H (30+k))+128*W+H

theorem returned (model : RationalCostModel) (W m lambda k Qv mesh num total : ℕ)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (ht : 0<total) (hn : num≤total)
    (hw : natBits total≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) :
    GeneralPaperQuotientConstructionStorage.record W (GeneralPaperMeshQueryExecution.selected model.rat W k mesh num total).1≤
      recordProfile W m lambda k Qv := by
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  have hs := inputs m lambda k Qv mesh num total hm ht hn hw
  have hr := GeneralPaperQuotientConstructionStorage.record_bound W ((mesh:ℚ)*num) total hs.1 (30+k) (2*H) H
    hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  have ha := record_annotation W 16 (GeneralPaperBoundedQuotient.run ((mesh:ℚ)*num) total (30+k))
  have hword := GeneralPaperMeshQueryMetadata.operand_word m lambda k Qv
  have hmeta : natBits ((GeneralPaperBoundedQuotient.run ((mesh:ℚ)*num) total (30+k)).work+16)≤H := by
    rw [GeneralPaperBoundedQuotient.run_work]
    exact (Nat.add_le_add_left (binaryWordWidth_mono (show 12*(30+k)+2+16≤GeneralPaperMeshQueryMetadata.cap k by
      unfold GeneralPaperMeshQueryMetadata.cap; omega)) 1).trans hword
  unfold GeneralPaperMeshQueryExecution.selected GeneralPaperMeshQueryExecution.run
  dsimp only
  rw [GeneralPaperCompleteQuotientPrice.data]
  dsimp only [recordProfile]
  change _≤4*(1+2*GeneralPaperBoundedQuotient.heightBudget (2*H) H (30+k))+128*W+H
  omega

def window (model : RationalCostModel) (W k mesh num total : ℕ) : ℕ :=
  let x := (mesh:ℚ)*(num:ℚ)
  let a : ℚ := total
  GeneralPaperQuotientConstructionStorage.peak model W x a (30+k)+
    GeneralPaperQuotientConstructionStorage.record W (GeneralPaperCompleteQuotientPrice.run model.rat W x a (30+k)).1+
    GeneralPaperQuotientConstructionStorage.record W (GeneralPaperMeshQueryExecution.selected model.rat W k mesh num total).1+
    fields W [mesh,30+k,num,total,k,30]+
    rationalWordWidth (mesh:ℚ)+rationalWordWidth (num:ℚ)+rationalWordWidth a+rationalWordWidth x+
    (GeneralPaperMeshQueryExecution.selected model.rat W k mesh num total).2+256*W

def profile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let d := 30+k
  (d+1)*GeneralPaperQuotientConstructionStorage.frameCap W H d+GeneralPaperQuotientConstructionStorage.localCap model W (2*H) H d+
    (4*(1+2*GeneralPaperBoundedQuotient.heightBudget (2*H) H d)+128*W)+recordProfile W m lambda k Qv+
    (6*(H+W)+32*W)+(10*H+4)+GeneralPaperMeshQueryEnvelope.profile model.rat W m lambda k Qv+256*W

theorem bounded (model : RationalCostModel) (W m lambda k Qv mesh num total : ℕ)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (ht : 0<total) (hn : num≤total)
    (hw : natBits total≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) :
    window model W k mesh num total≤profile model W m lambda k Qv := by
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  have hs := inputs m lambda k Qv mesh num total hm ht hn hw
  have hstack := GeneralPaperQuotientConstructionStorage.bounded model W ((mesh:ℚ)*num) total hs.1 (30+k) (2*H) H
    hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  have hraw := GeneralPaperQuotientConstructionStorage.record_bound W ((mesh:ℚ)*num) total hs.1 (30+k) (2*H) H
    hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  rw [←GeneralPaperCompleteQuotientPrice.data model.rat W ((mesh:ℚ)*num) total (30+k)] at hraw
  have hout := returned model W m lambda k Qv mesh num total hm ht hn hw
  have hmesh := GeneralPaperMeshQueryEnvelope.mesh_word m lambda k Qv
  rw [←hm] at hmesh
  have hnum := (Nat.add_le_add_left (binaryWordWidth_mono hn) 1).trans hw
  have hdepth := GeneralPaperMeshQueryEnvelope.depth_word m lambda k Qv
  have hk := (Nat.add_le_add_left (binaryWordWidth_mono (show k≤30+k by omega)) 1).trans hdepth
  have h30 := (Nat.add_le_add_left (binaryWordWidth_mono (show 30≤30+k by omega)) 1).trans hdepth
  have hfields := fields_bound W H [mesh,30+k,num,total,k,30] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hmesh
    · exact hdepth
    · exact hnum
    · exact hw
    · exact hk
    · exact h30)
  have hhm : RationalHeight (mesh:ℚ) H := (GeneralPaperBasisDivideBits.nat_height mesh).mono (by change 1+binaryWordWidth mesh≤H at hmesh; omega)
  have hhn : RationalHeight (num:ℚ) H := (GeneralPaperBasisDivideBits.nat_height num).mono (by change 1+binaryWordWidth num≤H at hnum; omega)
  have wm := rationalWordWidth_of_height hhm
  have wn := rationalWordWidth_of_height hhn
  have wt := rationalWordWidth_of_height hs.2.2.2.2
  have wx := rationalWordWidth_of_height hs.2.2.2.1
  have hp := GeneralPaperMeshQueryEnvelope.selected_work model.rat model.monotone W m lambda k Qv mesh num total hm ht hn hw
  change fields W [mesh,30+k,num,total,k,30]≤6*(H+W)+32*W at hfields
  dsimp only [window,profile]
  change _≤(30+k+1)*GeneralPaperQuotientConstructionStorage.frameCap W H (30+k)+
    GeneralPaperQuotientConstructionStorage.localCap model W (2*H) H (30+k)+
    (4*(1+2*GeneralPaperBoundedQuotient.heightBudget (2*H) H (30+k))+128*W)+recordProfile W m lambda k Qv+
    (6*(H+W)+32*W)+(10*H+4)+GeneralPaperMeshQueryEnvelope.profile model.rat W m lambda k Qv+256*W
  omega

theorem record_changed (W P : ℕ) (r s : GeneralPaperBoundedQuotient.Result)
    (hq : s.quotient=r.quotient) (hr : s.remainder=r.remainder) (hw : natBits s.work≤P) :
    GeneralPaperQuotientConstructionStorage.record W s≤GeneralPaperQuotientConstructionStorage.record W r+P := by
  unfold GeneralPaperQuotientConstructionStorage.record fields
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  rw [hq,hr]
  omega

theorem work_word (model : RationalCostModel) (W m lambda k Qv mesh num total extra : ℕ)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (he : extra≤64) :
    natBits ((GeneralPaperMeshQueryExecution.selected model.rat W k mesh num total).1.work+extra)≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  rw [GeneralPaperMeshQueryExecution.selected_data model.rat W k mesh num total hm,GeneralPaperCDFMesh.selected_work]
  exact (Nat.add_le_add_left (binaryWordWidth_mono (show 12*(30+k)+18+extra≤GeneralPaperMeshQueryMetadata.cap k by
    unfold GeneralPaperMeshQueryMetadata.cap; omega)) 1).trans (GeneralPaperMeshQueryMetadata.operand_word m lambda k Qv)

end Blotto.GeneralPaperMeshQueryStorage
