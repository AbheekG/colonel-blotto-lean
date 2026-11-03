import Blotto.GeneralPaperSourceEndpointRefinementRates

/-! Affine expressions, whole predecessor witnesses and retained native
affine fields/tables. Label lists are counted in full even when tails are
shared. Common-lattice bounds derive coefficient heights independently of
sample and refinement history. -/
namespace Blotto.GeneralPaperAffineWitnessStorage
open GeneralPaperEncodedScalarStorage GeneralPaperRayAffine GeneralPaperRayAffineMinimum
open GeneralPaperRayAffineScoreStep GeneralPaperEncodedReferenceVector
set_option autoImplicit false
set_option maxHeartbeats 3000000

def affineFoot (W : ℕ) (f : Affine) : ℕ := rationalWordWidth f.intercept+rationalWordWidth f.slope+32*W
def affineProfile (W R : ℕ) : ℕ := 2*(1+2*R)+32*W

theorem affine_bound (W R : ℕ) (f : Affine) (hi : RationalHeight f.intercept R) (hs : RationalHeight f.slope R) :
    affineFoot W f≤affineProfile W R := by
  have a := rationalWordWidth_of_height hi
  have b := rationalWordWidth_of_height hs
  unfold affineFoot affineProfile
  omega

def optionAffineFoot (W : ℕ) : Option Affine → ℕ
  | none => 1
  | some f => 1+affineFoot W f+8*W
def optionAffineProfile (W R : ℕ) : ℕ := 1+affineProfile W R+8*W

theorem option_affine_bound (W R : ℕ) (a : Option Affine)
    (ha : ∀ f,a=some f → RationalHeight f.intercept R ∧ RationalHeight f.slope R) :
    optionAffineFoot W a≤optionAffineProfile W R := by
  cases a with
  | none => dsimp only [optionAffineFoot,optionAffineProfile]; omega
  | some f =>
    have hf := affine_bound W R f (ha f rfl).1 (ha f rfl).2
    dsimp only [optionAffineFoot,optionAffineProfile]
    omega

def choiceFoot {K : ℕ} (W : ℕ) (c : Choice K) : ℕ :=
  affineFoot W c.expression+listFootprint W GeneralPaperScoreSelectionStorage.labelBits c.labels+32*W
def choiceProfile (W K n R : ℕ) : ℕ := affineProfile W R+n*(1+binaryWordWidth K+2*W)+64*W
def optionChoiceFoot {K : ℕ} (W : ℕ) : Option (Choice K) → ℕ
  | none => 1
  | some c => 1+choiceFoot W c+8*W
def optionChoiceProfile (W K n R : ℕ) : ℕ := 1+choiceProfile W K n R+8*W

theorem choice_bound {K : ℕ} (W n R : ℕ) (c : Choice K) (hn : c.labels.length≤n)
    (hi : RationalHeight c.expression.intercept R) (hs : RationalHeight c.expression.slope R) :
    choiceFoot W c≤choiceProfile W K n R := by
  have hf := affine_bound W R c.expression hi hs
  have hl := (list_bound W (1+binaryWordWidth K) GeneralPaperScoreSelectionStorage.labelBits c.labels
    (fun l _ => GeneralPaperScoreSelectionStorage.label_bound l)).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  unfold choiceFoot choiceProfile
  omega

theorem option_choice_bound {K : ℕ} (W n R : ℕ) (a : Option (Choice K))
    (ha : ∀ c,a=some c → c.labels.length≤n ∧ RationalHeight c.expression.intercept R ∧ RationalHeight c.expression.slope R) :
    optionChoiceFoot W a≤optionChoiceProfile W K n R := by
  cases a with
  | none => dsimp only [optionChoiceFoot,optionChoiceProfile]; omega
  | some c =>
    have hc := choice_bound W n R c (ha c rfl).1 (ha c rfl).2.1 (ha c rfl).2.2
    dsimp only [optionChoiceFoot,optionChoiceProfile]
    omega

def tableFoot {S K : ℕ} (W : ℕ) (table : Table S K) : ℕ := footprint W (optionChoiceFoot W) table.data
def tableProfile (W S K n R : ℕ) : ℕ := (S+1)*(optionChoiceProfile W K n R+W)+64*W

theorem processed_option_bound {K : ℕ} (W D E X V n m P : ℕ) (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (a : Option (Choice K)) (ha : ∀ c,a=some c → GeneralPaperRayAffineDPSize.ChoiceBounded D E X V n c) :
    optionChoiceFoot W a≤optionChoiceProfile W K m (GeneralPaperRayUniformSize.width D E m X V P) := by
  have hCaps := GeneralPaperRayUniformSize.scale_caps m X V P n hn
  let A := GeneralPaperRayUniformSize.interceptCap m X P
  let B := GeneralPaperRayUniformSize.slopeCap m V
  have hWidth : GeneralPaperRayAffineBound.rootWidth D E A B≤GeneralPaperRayUniformSize.width D E m X V P :=
    GeneralPaperRayAffineBound.rootWidth_mono D E A B (A+A) (B+B) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  apply option_choice_bound W m _ a
  intro c hc
  have h := ha c hc
  have hh := GeneralPaperAffineValuePrice.coefficients hD hE c.expression (GeneralPaperRayAffineBound.mono h.1 hCaps.1 hCaps.2)
  exact ⟨h.2.le.trans hn,hh.1.mono hWidth,hh.2.mono hWidth⟩

theorem table_bound {S K : ℕ} (W D E X V n m P : ℕ) (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (table : Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n table) :
    tableFoot W table≤tableProfile W S K m (GeneralPaperRayUniformSize.width D E m X V P) := by
  have hCaps := GeneralPaperNativeAffinePrices.table_cap D E m X V P n hn table hp
  let A := GeneralPaperRayUniformSize.interceptCap m X P
  let B := GeneralPaperRayUniformSize.slopeCap m V
  have hWidth : GeneralPaperRayAffineBound.rootWidth D E A B≤GeneralPaperRayUniformSize.width D E m X V P :=
    GeneralPaperRayAffineBound.rootWidth_mono D E A B (A+A) (B+B) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hb := bounded W (optionChoiceProfile W K m (GeneralPaperRayUniformSize.width D E m X V P)) (optionChoiceFoot W) table.data (by
    intro i
    let s : Fin (S+1) := ⟨i.val,i.isLt.trans_eq table.size⟩
    apply option_choice_bound W m _ (table.read s)
    intro c hc
    have hHeight := GeneralPaperAffineValuePrice.coefficients hD hE c.expression (hCaps s c hc)
    exact ⟨(hp s c hc).2.le.trans hn,hHeight.1.mono hWidth,hHeight.2.mono hWidth⟩)
  simpa only [tableFoot,tableProfile,table.size] using hb

def fieldFoot {K : ℕ} (W : ℕ) (field : Field K) : ℕ := footprint W (fun d => natBits d.1+affineFoot W d.2+32*W) field.data
def fieldProfile (W K S R : ℕ) : ℕ := K*(natBits S+affineProfile W R+33*W)+64*W

theorem field_bound {K : ℕ} (W D E X V m P S : ℕ) (hD : 0<D) (hE : 0<E) (hm : 1≤m)
    (field : Field K) (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field) (hs : ∀ l,(field.read l).1≤S) :
    fieldFoot W field≤fieldProfile W K S (GeneralPaperRayUniformSize.width D E m X V P) := by
  have hCaps := GeneralPaperNativeAffinePrices.field_cap D E m X V P hm field hf
  let A := GeneralPaperRayUniformSize.interceptCap m X P
  let B := GeneralPaperRayUniformSize.slopeCap m V
  have hWidth : GeneralPaperRayAffineBound.rootWidth D E A B≤GeneralPaperRayUniformSize.width D E m X V P :=
    GeneralPaperRayAffineBound.rootWidth_mono D E A B (A+A) (B+B) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hb := bounded W (natBits S+affineProfile W (GeneralPaperRayUniformSize.width D E m X V P)+32*W)
    (fun d => natBits d.1+affineFoot W d.2+32*W) field.data (by
      intro i
      let l : Fin K := ⟨i.val,i.isLt.trans_eq field.size⟩
      have hHeight := GeneralPaperAffineValuePrice.coefficients hD hE (field.read l).2 (hCaps l)
      have hA := affine_bound W _ (field.read l).2 (hHeight.1.mono hWidth) (hHeight.2.mono hWidth)
      have hS := Nat.add_le_add_left (binaryWordWidth_mono (hs l)) 1
      change natBits (field.read l).1+affineFoot W (field.read l).2+32*W≤_
      unfold natBits at *
      omega)
  have he : K*(natBits S+affineProfile W (GeneralPaperRayUniformSize.width D E m X V P)+32*W+W)+64*W=
      fieldProfile W K S (GeneralPaperRayUniformSize.width D E m X V P) := by unfold fieldProfile; ring
  exact (by simpa only [fieldFoot,field.size] using hb : fieldFoot W field≤_).trans_eq he

end Blotto.GeneralPaperAffineWitnessStorage
