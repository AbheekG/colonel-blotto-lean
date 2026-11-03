import Blotto.GeneralPaperStaticScanLoopStorage

/-! Actual static enumeration return and streaming scan execution. Every
blocker index/root, native candidate/pick, one active sparse-row residual,
enumeration/scan/outer return price and partial sum is counted. Enumeration
and sparse-row constructor temporary windows remain separate joins. -/
namespace Blotto.GeneralPaperNativeStaticScanStorage
open RationalOrderCell GeneralPaperStaticRayRows GeneralPaperRayUniformSize GeneralPaperRayRationalBound
open GeneralPaperStaticChoiceStorage GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def indexFoot {T m K : ℕ} (W : ℕ) : StaticIndex T m K → ℕ
  | .inl (v,b) => fields W [v.1.val,v.2.val,if b then 1 else 0]+32*W
  | .inr (.inl v) => fields W [v.1.val,v.2.val]+32*W
  | .inr (.inr i) => fields W [i.val]+32*W

def indexProfile (W T m K : ℕ) : ℕ := 3*(natBits (T+m+K+1)+W)+64*W

theorem index_bound {T m K : ℕ} (W : ℕ) (i : StaticIndex T m K) : indexFoot W i≤ indexProfile W T m K := by
  rcases i with ⟨v,b⟩|v|i
  · have hv := v.1.isLt
    have hl := v.2.isLt
    have h := fields_bound W (natBits (T+m+K+1)) [v.1.val,v.2.val,if b then 1 else 0] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl
      · omega
      · omega
      · split <;> omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (T+m+K+1)+W)+32*W at h
    exact (Nat.add_le_add_right h (32*W)).trans_eq (by unfold indexProfile; ring)
  · have hv := v.1.isLt
    have hl := v.2.isLt
    have h := fields_bound W (natBits (T+m+K+1)) [v.1.val,v.2.val] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl <;> omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits (T+m+K+1)+W)+32*W at h
    change GeneralPaperEncodedScalarStorage.fields W [v.1.val,v.2.val]+32*W≤_
    unfold indexProfile
    omega
  · have hi := i.isLt
    have h := fields_bound W (natBits (T+m+K+1)) [i.val] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_singleton] at ha
      subst a
      omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤1*(natBits (T+m+K+1)+W)+32*W at h
    change GeneralPaperEncodedScalarStorage.fields W [i.val]+32*W≤_
    unfold indexProfile
    omega

def count (T m K : ℕ) : ℕ := 3*(m*(K-1))+T
def rowPrice (model : RationalCostModel) (W m R : ℕ) : ℕ :=
  (64*m+210)*W+(9*m+27)*model.rat (1+2*R)
def enumerationPrice (W T m K : ℕ) : ℕ := 1024*(m*(K-1)+m+T+1)*W

theorem row_work {T m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ) (hm : 0<m) (hD : 0<D) (hE : 0<E)
    (labels : Fin T → Fin m → Fin K) (x w : Variable m K → ℚ)
    (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j)) (i : StaticIndex T m K) :
    (GeneralPaperStaticRowPrice.evaluate model.rat W labels x w i).2≤rowPrice model W m (width D E m X V P) := by
  have h := GeneralPaperStaticRowPrice.work model.rat model.monotone W D E X V P hm hD hE labels x w hx hw i
  rcases i with v|v|i
  all_goals dsimp only [GeneralPaperStaticRowPrice.charge] at h; unfold rowPrice
  all_goals nlinarith only [h,Nat.zero_le (m*W),Nat.zero_le (m*model.rat (1+2*width D E m X V P))]

def scanPrice (model : RationalCostModel) (W T m K R : ℕ) : ℕ :=
  GeneralPaperStaticScanLoopStorage.workCap model W R (count T m K) (rowPrice model W m R)
def metadataCap (model : RationalCostModel) (W T m K R : ℕ) : ℕ :=
  1+enumerationPrice W T m K+2*scanPrice model W T m K R+8*W

def window {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (x w : Variable m K → ℚ) (active : Option (StaticIndex T m K)) : ℕ :=
  let rows := GeneralPaperStaticEnumerationPrice.run W T m K
  let chosen := GeneralPaperStaticMinimumScanPrice.scan model.rat W (GeneralPaperStaticRowPrice.evaluate model.rat W labels x w) rows.1
  let result := GeneralPaperStaticScanPrice.run model.rat W labels x w
  GeneralPaperStaticScanLoopStorage.window model W (indexFoot W) (GeneralPaperStaticRowPrice.evaluate model.rat W labels x w)
      (GeneralPaperStaticRowResidualStorage.window model W labels x w) rows.1 active+
    choiceFoot W (indexFoot W) result.choice+
    fields W [rows.2,chosen.work,result.work,8*W,rows.2+chosen.work,rows.2+chosen.work+8*W]+256*W

def profile (model : RationalCostModel) (W T m K R : ℕ) : ℕ :=
  GeneralPaperStaticScanLoopStorage.profile model W (indexProfile W T m K) R (count T m K) (rowPrice model W m R)
    (GeneralPaperStaticRowResidualStorage.profile model W m K R)+choiceProfile W (indexProfile W T m K) R+
      6*(natBits (metadataCap model W T m K R)+W)+288*W

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ) (hm : 0<m) (hD : 0<D) (hE : 0<E)
    (labels : Fin T → Fin m → Fin K) (x w : Variable m K → ℚ)
    (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j)) (active : Option (StaticIndex T m K)) :
    window model W labels x w active≤profile model W T m K (width D E m X V P) := by
  let A := interceptCap m X P
  let B := slopeCap m V
  let R := width D E m X V P
  let rows := GeneralPaperStaticEnumerationPrice.run W T m K
  let evaluate := GeneralPaperStaticRowPrice.evaluate model.rat W labels x w
  let chosen := GeneralPaperStaticMinimumScanPrice.scan model.rat W evaluate rows.1
  let result := GeneralPaperStaticScanPrice.run model.rat W labels x w
  have hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R :=
    GeneralPaperRayAffineBound.rootWidth_mono D E A B (A+A) (B+B) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hLength : rows.1.length=count T m K := by rw [GeneralPaperStaticEnumerationPrice.data,enumerate_length]; rfl
  have hBound : ∀ j∈rows.1,GeneralPaperRayAffineBound.Bounded D E A B (evaluate j).1 := fun j _ =>
    GeneralPaperStaticRowPrice.bounded model.rat W D E X V P hm labels x w hx hw j
  have hIndex : ∀ j∈rows.1,indexFoot W j≤ indexProfile W T m K := fun j _ => index_bound W j
  have hWork : ∀ j∈rows.1,(evaluate j).2≤rowPrice model W m R := fun j _ => row_work model W D E X V P hm hD hE labels x w hx hw j
  have hScan := GeneralPaperStaticScanLoopStorage.bounded model W D E A B R (indexProfile W T m K) (count T m K) (rowPrice model W m R)
    (GeneralPaperStaticRowResidualStorage.profile model W m K R) hD hE hR (indexFoot W) evaluate rows.1 hLength.le hIndex hBound hWork
    (GeneralPaperStaticRowResidualStorage.window model W labels x w)
    (fun j _ => GeneralPaperStaticRowResidualStorage.bounded model W D E X V P hm hD hE labels x w hx hw j)
    active (by intro j _; rw [GeneralPaperStaticEnumerationPrice.data]; exact enumerate_mem j)
  have hResult := choice_bound W (indexProfile W T m K) R (indexFoot W) chosen.choice
    (GeneralPaperStaticScanLoopStorage.good model W D E A B R _ hD hE hR (indexFoot W) evaluate rows.1 hIndex hBound none (by intro c hc; cases hc) 0)
  have hChosenWork := GeneralPaperStaticMinimumScanPrice.work model.rat model.monotone W D E A B R hD hE hR evaluate rows.1 hBound
  have hSum := GeneralPaperEncodedScalarStorage.sum_bound (fun j => (evaluate j).2+56*W+6*model.rat (1+2*R))
    (rowPrice model W m R+56*W+6*model.rat (1+2*R)) rows.1 (fun j hj => by have h := hWork j hj; omega)
  have hChosen : chosen.work≤scanPrice model W T m K R := by
    rw [hLength] at hSum
    exact hChosenWork.trans (by unfold scanPrice GeneralPaperStaticScanLoopStorage.workCap; omega)
  have hEnumeration := GeneralPaperStaticEnumerationPrice.work W T m K
  change rows.2≤enumerationPrice W T m K at hEnumeration
  have hShape : result.work=rows.2+chosen.work+8*W := rfl
  have hf := fields_bound W (natBits (metadataCap model W T m K R)) [rows.2,chosen.work,result.work,8*W,rows.2+chosen.work,rows.2+chosen.work+8*W] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (metadataCap model W T m K R)+W)+32*W at hf
  change GeneralPaperStaticScanLoopStorage.window model W (indexFoot W) evaluate (GeneralPaperStaticRowResidualStorage.window model W labels x w) rows.1 active+
    choiceFoot W (indexFoot W) result.choice+GeneralPaperEncodedScalarStorage.fields W [rows.2,chosen.work,result.work,8*W,rows.2+chosen.work,rows.2+chosen.work+8*W]+256*W≤_
  change choiceFoot W (indexFoot W) result.choice≤choiceProfile W (indexProfile W T m K) R at hResult
  unfold profile
  dsimp only [R] at hScan hResult hf
  omega

end Blotto.GeneralPaperNativeStaticScanStorage
