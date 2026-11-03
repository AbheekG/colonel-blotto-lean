import Blotto.GeneralPaperScoreMatrixEntryStorage
import Blotto.GeneralPaperScoreResidencyRates

/-! Actual physical source-matrix construction, including literal entry
arithmetic and the physical wrapper's native work metadata. Source-returned
dictionary and stored values derive every height; no input-width or source
size oracle is supplied. Column residents and surrounding phases remain
separate joins. -/
namespace Blotto.GeneralPaperSourceMatrixStorage
open GeneralPaperProxyParameters GeneralPaperExactScoreDP GeneralPaperEncodedScalarStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

def physicalPrice (model : RationalCostModel) (W m K V A depth : ℕ) : ℕ :=
  GeneralPaperScoreMatrixBits.matrixProfile model W V A depth m K+
    64*m*K*GeneralPaperSummaryArrayExecution.arrayWord W (m*K+m+K)

def metadataCap (model : RationalCostModel) (W m K S V A depth : ℕ) : ℕ :=
  m+K+S+depth+1+physicalPrice model W m K V A depth

def window {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (outer : ℕ) (ho : outer≤m) (j : Fin m) (inner : ℕ) (hi : inner≤K) (l : Fin K) : ℕ :=
  let v := GeneralPaperRetainedFieldValues.selector values
  GeneralPaperScoreMatrixEntryStorage.window model W depth (GeneralPaperRowQuantizer.dictionary columns) v S outer ho j inner hi l+
    fields W [m,K,S,depth,(GeneralPaperPhysicalScoreMatrix.run true model W depth columns v S).2]+128*W

def profile (model : RationalCostModel) (W m K S V A depth : ℕ) : ℕ :=
  GeneralPaperScoreMatrixEntryStorage.profile model W depth S V A m K+
    5*(natBits (metadataCap model W m K S V A depth)+W)+32*W+128*W

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W depth S V A : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (hK : 0<K) (hCap : S<2^depth)
    (hv : ∀ j,RationalHeight ((GeneralPaperRetainedFieldValues.selector values).weight j) V)
    (ha : ∀ j l,RationalHeight ((columns.read j).anchors.read l) A)
    (hW : 1≤W) (hLabel : binaryWordWidth (K+1)≤W) (hField : binaryWordWidth (m+1)≤W)
    (outer : ℕ) (ho : outer≤m) (j : Fin m) (inner : ℕ) (hi : inner≤K) (l : Fin K) :
    window model W depth S columns values outer ho j inner hi l≤profile model W m K S V A depth := by
  have hMatrix := GeneralPaperScoreMatrixEntryStorage.bounded model W depth (GeneralPaperRowQuantizer.dictionary columns)
    (GeneralPaperRetainedFieldValues.selector values) S V A hK hCap hv ha hW hLabel hField outer ho j inner hi l
  have hWork := GeneralPaperPhysicalScoreMatrix.bit_work model W depth V A columns
    (GeneralPaperRetainedFieldValues.selector values) S hK hCap hv ha hW hLabel hField
  change (GeneralPaperPhysicalScoreMatrix.run true model W depth columns (GeneralPaperRetainedFieldValues.selector values) S).2≤
    physicalPrice model W m K V A depth at hWork
  have hf := fields_bound W (natBits (metadataCap model W m K S V A depth))
    [m,K,S,depth,(GeneralPaperPhysicalScoreMatrix.run true model W depth columns (GeneralPaperRetainedFieldValues.selector values) S).2] (by
      intro n hn
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (metadataCap model W m K S V A depth)+W)+32*W at hf
  have hAll := Nat.add_le_add_right (Nat.add_le_add hMatrix hf) (128*W)
  exact hAll.trans_eq (by unfold profile; ring)

def sourceProfile (model : RationalCostModel) (W m k Qv : ℕ) : ℕ :=
  profile model W m (prepare m k).K (prepare m k).S (binaryWordWidth Qv)
    (GeneralPaperSourceScoreHeights.anchorHeight m k) (GeneralPaperScoreScaleParameters.prepare m k).depth

theorem actual {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
    (hW : 1≤W) (hLabel : binaryWordWidth ((prepare m k).K+1)≤W) (hField : binaryWordWidth (m+1)≤W)
    (outer : ℕ) (ho : outer≤m) (j : Fin m) (inner : ℕ) (hi : inner≤(prepare m k).K) (l : Fin (prepare m k).K) :
    window model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S columns values outer ho j inner hi l≤
      sourceProfile model W m k Qv := by
  apply bounded model W _ _ _ _ columns values (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperScoreScaleParameters.score_cap m k) _
    (GeneralPaperSourceScoreResidents.anchors k Qv hQv weights hp hs b hb reciprocal columns hColumns)
    hW hLabel hField outer ho j inner hi l
  intro t
  rw [hValues]
  exact GeneralPaperSourceScoreHeights.value_height Qv hQv weights hp hs t

end Blotto.GeneralPaperSourceMatrixStorage
