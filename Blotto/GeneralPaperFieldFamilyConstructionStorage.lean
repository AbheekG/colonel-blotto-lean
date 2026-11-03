import Blotto.GeneralPaperCellPlanConstructionStorage

/-! The native outer eight-plan field family retains all six input
families, reserved old/new field buffers, full returned records and index
frames. Actual input code bounds derive every retained field payload. -/
namespace Blotto.GeneralPaperFieldFamilyConstructionStorage
open GeneralPaperCodeAlphabet GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def ValidInputs {m k : ℕ} (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ)) : Prop :=
  (∀ j i,(arrays.p.read j).read i<8*a.C) ∧ (∀ j i,(arrays.q.read j).read i<8*a.C) ∧
  (∀ j i,(arrays.lambda.read j).read i<2*(8*a.C)) ∧ (∀ j i,(arrays.mu.read j).read i<2*(8*a.C)) ∧
  (∀ j i,(candidate.read j).read i<8*a.C) ∧ (∀ j i,(response.read j).read i<8*a.C)

theorem source_word (a : Alphabet) (x : ℕ) (hx : x≤2*(8*a.C)) : natBits x≤GeneralPaperDecoderControls.operandWidth a.lambda := by
  have h := (Nat.add_le_add_left (binaryWordWidth_mono hx) 1).trans (GeneralPaperCataloguePartitionStorage.source_payload a)
  unfold GeneralPaperDecoderControls.operandWidth
  exact h.trans (by omega)

def row {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ)) (j : Fin m) :=
  GeneralPaperFieldPlanPreparation.run true (fun w => w) model.rat W k (8*a.C)
    (arrays.p.read j) (arrays.q.read j) (arrays.lambda.read j) (arrays.mu.read j) (candidate.read j) (response.read j)

theorem row_returned {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (hv : ValidInputs a arrays candidate response) (j : Fin m) :
    GeneralPaperEncodedFieldPlanStorage.footprint W (row model W a arrays candidate response j).1≤GeneralPaperEncodedFieldPlanStorage.profile W a.lambda k := by
  rcases hv with ⟨hp,hq,hl,hm,hx,hy⟩
  unfold row
  rw [GeneralPaperFieldPlanPreparation.data]
  apply GeneralPaperEncodedFieldPlanStorage.prepared W a
  · intro i; exact source_word a _ ((hp j i).le.trans (by omega))
  · intro i; exact source_word a _ ((hq j i).le.trans (by omega))
  · intro i; exact source_word a _ (hl j i).le
  · intro i; exact source_word a _ (hm j i).le
  · intro i; exact source_word a _ ((hx j i).le.trans (by omega))
  · intro i; exact source_word a _ ((hy j i).le.trans (by omega))

def filledPrefix {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (count : ℕ) (hc : count≤m) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W m (GeneralPaperEncodedFieldPlanStorage.footprint W)
    (PaperIndexedArrayConstruction.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (GeneralPaperFieldPlanFamily.element true (fun w => w) model.rat W k (8*a.C)
        arrays.p arrays.q arrays.lambda arrays.mu candidate response) count hc).1

theorem prefix_bound {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (hv : ValidInputs a arrays candidate response) (count : ℕ) (hc : count≤m) :
    filledPrefix model W a arrays candidate response count hc≤m*(GeneralPaperEncodedFieldPlanStorage.profile W a.lambda k+W)+64*W :=
  GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m)
    W (GeneralPaperEncodedFieldPlanStorage.profile W a.lambda k) (GeneralPaperEncodedFieldPlanStorage.footprint W)
    (GeneralPaperFieldPlanFamily.element true (fun w => w) model.rat W k (8*a.C)
      arrays.p arrays.q arrays.lambda arrays.mu candidate response) (row_returned model W a arrays candidate response hv) count hc

theorem family_returned {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (hv : ValidInputs a arrays candidate response) :
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedFieldPlanStorage.footprint W)
      (GeneralPaperFieldPlanFamily.run true (fun w => w) model.rat W k (8*a.C)
        arrays.p arrays.q arrays.lambda arrays.mu candidate response).1≤m*(GeneralPaperEncodedFieldPlanStorage.profile W a.lambda k+W)+32*W := by
  apply GeneralPaperEncodedFixedVector.bounded W (GeneralPaperEncodedFieldPlanStorage.profile W a.lambda k)
  intro j
  rw [GeneralPaperFieldPlanFamily.data,FixedArrayTable.read_ofFn]
  have h := row_returned model W a arrays candidate response hv j
  unfold row at h
  rw [GeneralPaperFieldPlanPreparation.data] at h
  exact h

theorem array_family {m n : ℕ} (W : ℕ) (a : Alphabet) (values : FixedArrayTable m (FixedArrayTable n ℕ))
    (hv : ∀ j i,(values.read j).read i≤2*(8*a.C)) :
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) values≤
      m*(n*(GeneralPaperDecoderControls.operandWidth a.lambda+W)+33*W)+32*W := by
  have h := GeneralPaperEncodedFixedVector.bounded W _ (GeneralPaperEncodedNatArray.footprint W) values
    (fun j => GeneralPaperEncodedNatArray.bounded W (GeneralPaperDecoderControls.operandWidth a.lambda) (values.read j)
      (fun i => source_word a _ (hv j i)))
  exact h.trans_eq (by ring)

def window {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (count : ℕ) (hc : count≤m) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) arrays.p+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) arrays.q+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) arrays.lambda+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) arrays.mu+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) candidate+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) response+
    2*filledPrefix model W a arrays candidate response count hc+GeneralPaperGridArrayConstructionStorage.frames W m+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedFieldPlanStorage.footprint W)
      (GeneralPaperFieldPlanFamily.run true (fun w => w) model.rat W k (8*a.C)
        arrays.p arrays.q arrays.lambda arrays.mu candidate response).1+
    fields W [k,8*a.C,m,(GeneralPaperSourceParameters.prepare k).summarySize+2,(GeneralPaperSourceParameters.prepare k).summarySize+2]+
    (GeneralPaperFieldPlanFamily.run true (fun w => w) model.rat W k (8*a.C)
      arrays.p arrays.q arrays.lambda arrays.mu candidate response).2+256*W

def profile (model : RationalCostModel) (W m k : ℕ) (a : Alphabet) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let K := s+2
  let L := GeneralPaperDecoderControls.operandWidth a.lambda
  4*(m*(s*(L+W)+33*W)+32*W)+2*(m*(K*(L+W)+33*W)+32*W)+
    2*(m*(GeneralPaperEncodedFieldPlanStorage.profile W a.lambda k+W)+64*W)+GeneralPaperGridArrayConstructionStorage.frames W m+
    (m*(GeneralPaperEncodedFieldPlanStorage.profile W a.lambda k+W)+32*W)+fields W [k,8*a.C,m,K,K]+
    GeneralPaperFieldPlanFamily.profile model.rat W m K K k (8*a.C)+256*W

theorem bounded {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (hv : ValidInputs a arrays candidate response) (count : ℕ) (hc : count≤m) :
    window model W a arrays candidate response count hc≤profile model W m k a := by
  rcases hv with ⟨hp,hq,hl,hm,hx,hy⟩
  have bp := array_family W a arrays.p (fun j i => (hp j i).le.trans (by omega))
  have bq := array_family W a arrays.q (fun j i => (hq j i).le.trans (by omega))
  have bl := array_family W a arrays.lambda (fun j i => (hl j i).le)
  have bm := array_family W a arrays.mu (fun j i => (hm j i).le)
  have bx := array_family W a candidate (fun j i => (hx j i).le.trans (by omega))
  have by' := array_family W a response (fun j i => (hy j i).le.trans (by omega))
  have hprefix := prefix_bound model W a arrays candidate response ⟨hp,hq,hl,hm,hx,hy⟩ count hc
  have hret := family_returned model W a arrays candidate response ⟨hp,hq,hl,hm,hx,hy⟩
  have hprice := GeneralPaperFieldPlanFamily.bit_work model.rat model.monotone W k (8*a.C)
    arrays.p arrays.q arrays.lambda arrays.mu candidate response hp hq hl hm hx hy
  dsimp only [window,profile]
  omega

def rowWindow {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ)) (j : Fin m) : ℕ :=
  GeneralPaperEncodedFieldPlanStorage.footprint W (row model W a arrays candidate response j).1+
    (row model W a arrays candidate response j).2+
    fields W [k,8*a.C,(GeneralPaperSourceParameters.prepare k).summarySize+2,(GeneralPaperSourceParameters.prepare k).summarySize+2]+256*W

def rowProfile (model : RationalCostModel) (W k : ℕ) (a : Alphabet) : ℕ :=
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  GeneralPaperEncodedFieldPlanStorage.profile W a.lambda k+GeneralPaperFieldPlanPreparation.profile model.rat W K K k (8*a.C)+
    fields W [k,8*a.C,K,K]+256*W

theorem row_bounded {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (candidate response : FixedArrayTable m (FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ))
    (hv : ValidInputs a arrays candidate response) (j : Fin m) : rowWindow model W a arrays candidate response j≤rowProfile model W k a := by
  have hr := row_returned model W a arrays candidate response hv j
  rcases hv with ⟨hp,hq,hl,hm,hx,hy⟩
  have hs := GeneralPaperFieldPlanPreparation.bit_work model.rat model.monotone W k (8*a.C)
    (arrays.p.read j) (arrays.q.read j) (arrays.lambda.read j) (arrays.mu.read j) (candidate.read j) (response.read j)
    (hp j) (hq j) (hl j) (hm j) (hx j) (hy j)
  change (row model W a arrays candidate response j).2≤_ at hs
  dsimp only [rowWindow,rowProfile]
  omega

end Blotto.GeneralPaperFieldFamilyConstructionStorage
