import Blotto.GeneralPaperFinalStaticLoopStorage

/-! Complete final static checker: native index enumeration, full index
ownership, Boolean scan frames, one active residual/row constructor and
all outer phase/partial/return fields. Bounds hold before acceptance. -/
namespace Blotto.GeneralPaperFinalStaticStorage
open RationalOrderCell GeneralPaperStaticRayRows GeneralPaperRayUniformSize GeneralPaperRayRationalBound
open GeneralPaperEncodedScalarStorage GeneralPaperNativeStaticScanStorage
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

def scanPrice (model : RationalCostModel) (W T m K R : ℕ) : ℕ :=
  GeneralPaperFinalStaticLoopStorage.workCap model W R (count T m K) (rowPrice model W m R)
def metadataCap (model : RationalCostModel) (W T m K R : ℕ) : ℕ :=
  2+enumerationPrice W T m K+2*scanPrice model W T m K R+8*W
def caller {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K) (x : Variable m K → ℚ) : ℕ :=
  let rows := GeneralPaperStaticEnumerationPrice.run W T m K
  let checked := GeneralPaperFinalStaticBits.loop model.rat W labels x rows.1 true 0
  let result := GeneralPaperFinalStaticBits.run model.rat W labels x
  fields W [rows.2,checked.work,result.work,8*W,rows.2+checked.work,
    GeneralPaperFinalStaticLoopStorage.bit checked.accepted,GeneralPaperFinalStaticLoopStorage.bit result.accepted]+128*W
def callerProfile (model : RationalCostModel) (W T m K R : ℕ) : ℕ := 7*(natBits (metadataCap model W T m K R)+W)+160*W

inductive Phase (T m K : ℕ) where
  | enumeration (copied : ℕ) (field : Option (Fin m)) (label : Option (Fin (K-1)))
      (activeVariable : Option (Variable m K)) (budget : Option (Fin T))
  | scan (copied : ℕ) (active : Option (StaticIndex T m K))
  | returned

def window {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K) (x : Variable m K → ℚ)
    (phase : Phase T m K) : ℕ :=
  let rows := (GeneralPaperStaticEnumerationPrice.run W T m K).1
  caller model W labels x+listFootprint W (indexFoot W) rows+match phase with
  | .enumeration copied field label activeVariable budget => GeneralPaperStaticEnumerationStorage.window W T m K copied field label activeVariable budget
  | .scan copied active =>
    GeneralPaperFinalStaticLoopStorage.window model W labels x rows (GeneralPaperStaticRowResidualStorage.window model W labels x (fun _ => 0)) active+
      GeneralPaperPricedListStreamStorage.activeSpace (GeneralPaperStaticRowConstructionStorage.window W copied labels) active
  | .returned => 0

def profile (model : RationalCostModel) (W T m K R : ℕ) : ℕ :=
  callerProfile model W T m K R+(count T m K)*(indexProfile W T m K+2*W)+32*W+
    GeneralPaperStaticEnumerationStorage.profile W T m K+
    GeneralPaperFinalStaticLoopStorage.profile model W (indexProfile W T m K) R (count T m K) (rowPrice model W m R)
      (GeneralPaperStaticRowResidualStorage.profile model W m K R)+GeneralPaperStaticRowConstructionStorage.profile W m K

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W D X P R : ℕ) (hm : 0<m) (hD : 0<D)
    (labels : Fin T → Fin m → Fin K) (x : Variable m K → ℚ) (hx : ∀ j,Bounded D X (x j))
    (hR : width D 1 m X 0 P≤R) (phase : Phase T m K) : window model W labels x phase≤profile model W T m K R := by
  let R0 := width D 1 m X 0 P
  let A := interceptCap m X P
  let B := slopeCap m 0
  let rows := GeneralPaperStaticEnumerationPrice.run W T m K
  let checked := GeneralPaperFinalStaticBits.loop model.rat W labels x rows.1 true 0
  let result := GeneralPaperFinalStaticBits.run model.rat W labels x
  have hPositive : 1≤R := by
    have hd := binaryWordWidth_pos D
    unfold width GeneralPaperRayAffineBound.rootWidth at hR
    omega
  have hLength : rows.1.length=count T m K := by rw [GeneralPaperStaticEnumerationPrice.data,enumerate_length]; rfl
  have hIndex (j) (_hj : j∈rows.1) : indexFoot W j≤ indexProfile W T m K := index_bound W j
  have hCoefficients (j) (_hj : j∈rows.1) :
      RationalHeight (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).1.intercept R ∧
      RationalHeight (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).1.slope R := by
    have hb := GeneralPaperStaticRowPrice.bounded model.rat W D 1 X 0 P hm labels x (fun _ => 0) hx (fun _ => Bounded.zero 1) j
    have hh := GeneralPaperAffineValuePrice.coefficients hD (by decide : 0<1) _ hb
    have hw : GeneralPaperRayAffineBound.rootWidth D 1 A B≤R0 :=
      GeneralPaperRayAffineBound.rootWidth_mono D 1 A B (A+A) (B+B) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    exact ⟨hh.1.mono (hw.trans hR),hh.2.mono (hw.trans hR)⟩
  have hWork (j) (_hj : j∈rows.1) : (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).2≤rowPrice model W m R := by
    apply (row_work model W D 1 X 0 P hm hD (by decide) labels x (fun _ => 0) hx (fun _ => Bounded.zero 1) j).trans
    unfold rowPrice
    gcongr
    apply model.monotone
    omega
  have hCompare (j) (_hj : j∈rows.1) : GeneralPaperFinalStaticLoopStorage.comparison model
      (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).1≤model.rat (1+2*R) :=
    (GeneralPaperFinalStaticBits.compare_work model.rat model.monotone W D X P hm hD labels x hx j).trans
      (model.monotone (by omega))
  have hSpace (j) (_hj : j∈rows.1) : GeneralPaperStaticRowResidualStorage.window model W labels x (fun _ => 0) j≤
      GeneralPaperStaticRowResidualStorage.profile model W m K R :=
    (GeneralPaperStaticRowResidualStorage.bounded model W D 1 X 0 P hm hD (by decide) labels x (fun _ => 0) hx (fun _ => Bounded.zero 1) j).trans
      (GeneralPaperSourceStaticRowRates.height_mono model W m K 0 R0 R hR)
  have hResident := list_bound W (indexProfile W T m K) (indexFoot W) rows.1 hIndex
  rw [hLength] at hResident
  have hLoop := GeneralPaperFinalStaticBits.loop_work model.rat W labels x rows.1 true 0
  have hSum := sum_bound (fun j => (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).2+
    GeneralPaperFinalStaticLoopStorage.comparison model (GeneralPaperStaticRowPrice.evaluate model.rat W labels x (fun _ => 0) j).1+8*W)
    (rowPrice model W m R+model.rat (1+2*R)+8*W) rows.1 (fun j hj => by have h:=hWork j hj; have hc:=hCompare j hj; omega)
  rw [hLength] at hSum
  have hScan : checked.work≤scanPrice model W T m K R := by
    dsimp only [checked]
    rw [hLoop]
    unfold scanPrice GeneralPaperFinalStaticLoopStorage.workCap GeneralPaperFinalStaticLoopStorage.comparison at *
    omega
  have hEnumeration := GeneralPaperStaticEnumerationPrice.work W T m K
  change rows.2≤enumerationPrice W T m K at hEnumeration
  have hShape : result.work=rows.2+checked.work+8*W := rfl
  have hBool := GeneralPaperFinalStaticLoopStorage.bit_bound checked.accepted
  have hBool' := GeneralPaperFinalStaticLoopStorage.bit_bound result.accepted
  have hf := fields_bound W (natBits (metadataCap model W T m K R))
    [rows.2,checked.work,result.work,8*W,rows.2+checked.work,GeneralPaperFinalStaticLoopStorage.bit checked.accepted,
      GeneralPaperFinalStaticLoopStorage.bit result.accepted] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      unfold metadataCap
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤7*(natBits (metadataCap model W T m K R)+W)+32*W at hf
  have hCaller : caller model W labels x≤callerProfile model W T m K R := by
    change GeneralPaperEncodedScalarStorage.fields W [rows.2,checked.work,result.work,8*W,rows.2+checked.work,
      GeneralPaperFinalStaticLoopStorage.bit checked.accepted,GeneralPaperFinalStaticLoopStorage.bit result.accepted]+128*W≤_
    unfold callerProfile
    omega
  cases phase with
  | enumeration copied field label activeVariable budget =>
    have hEnum := GeneralPaperStaticEnumerationStorage.bounded W T m K copied field label activeVariable budget
    unfold window profile
    dsimp only
    dsimp only [rows] at hResident
    omega
  | scan copied active =>
    have hActive (j) (_hj : active=some j) : j∈rows.1 := by rw [GeneralPaperStaticEnumerationPrice.data]; exact enumerate_mem j
    have hLoopWindow := GeneralPaperFinalStaticLoopStorage.bounded model W (indexProfile W T m K) R (count T m K) (rowPrice model W m R)
      (GeneralPaperStaticRowResidualStorage.profile model W m K R) hPositive labels x rows.1 hLength.le hIndex hCoefficients hWork hCompare
      (GeneralPaperStaticRowResidualStorage.window model W labels x (fun _ => 0)) hSpace active hActive
    have hRowConstructor := GeneralPaperPricedListStreamStorage.active_bound (GeneralPaperStaticRowConstructionStorage.profile W m K)
      (GeneralPaperStaticRowConstructionStorage.window W copied labels) active rows.1
      (fun j _ => GeneralPaperStaticRowConstructionStorage.bounded W copied hm labels j) hActive
    unfold window profile
    dsimp only
    dsimp only [rows] at hResident hLoopWindow hRowConstructor
    omega
  | returned =>
    unfold window profile
    dsimp only
    dsimp only [rows] at hResident
    omega

end Blotto.GeneralPaperFinalStaticStorage
