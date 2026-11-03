import Blotto.GeneralPaperNativePayloadFillStorage

/-! Literal forward sparse-coordinate packing: K-1, field multiplication
and label addition with actual operands/results, primitive scratch, packed
terms and native map/partial-work fields. All callback windows are retained
conservatively. No inverse, floor, division or dense lookup is executed. -/
namespace Blotto.GeneralPaperBasisCoordinateStorage
open RationalOrderCell GeneralPaperEncodedScalarStorage GeneralPaperStaticRowResidualStorage
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def packedTermFoot {d : ℕ} (W : ℕ) (t : Fin d×ℤ) : ℕ := natBits t.1.val+GeneralPaperEncodedBasisStorage.integerBits t.2+32*W
def packedTermProfile (W d : ℕ) : ℕ := natBits (d+1)+2+32*W

theorem packed_term_bound {d : ℕ} (W : ℕ) (t : Fin d×ℤ) (ht : t.2.natAbs≤1) :
    packedTermFoot W t≤packedTermProfile W d := by
  have hI := Nat.add_le_add_left (binaryWordWidth_mono (show t.1.val≤d+1 by omega)) 1
  have hC := binaryWordWidth_mono ht
  have hOne : binaryWordWidth 1=1 := by decide
  unfold packedTermFoot packedTermProfile GeneralPaperEncodedBasisStorage.integerBits natBits at *
  omega

def scalarPrice (model : RationalCostModel) (W d : ℕ) : ℕ := 24*W+6*model.rat (1+binaryWordWidth (d+1))
def scalarCap (model : RationalCostModel) (W m K : ℕ) : ℕ := m+K+m*(K-1)+1+3*scalarPrice model W (m*(K-1))+24*W
def scalarWindow {m K : ℕ} (model : RationalCostModel) (W : ℕ) (v : Variable m K) : ℕ :=
  let sub := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a-b) K 1
  let mul := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) v.1.val (K-1)
  let add := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (v.1.val*(K-1)) v.2.val
  let result := GeneralPaperBasisCoordinateBits.scalar model.rat W v
  sub+mul+add+fields W [m,K,K-1,v.1.val,v.2.val,v.1.val*(K-1),result.1.val,sub,mul,add,result.2,sub+mul,sub+mul+add,24*W]+256*W
def scalarProfile (model : RationalCostModel) (W m K : ℕ) : ℕ :=
  6*model.rat (1+binaryWordWidth (m*(K-1)+1))+14*(natBits (scalarCap model W m K)+W)+288*W

theorem scalar_bound {m K : ℕ} (model : RationalCostModel) (W : ℕ) (v : Variable m K) :
    scalarWindow model W v≤scalarProfile model W m K := by
  let sub := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a-b) K 1
  let mul := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) v.1.val (K-1)
  let add := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (v.1.val*(K-1)) v.2.val
  let result := GeneralPaperBasisCoordinateBits.scalar model.rat W v
  have hOps := GeneralPaperBasisCoordinateBits.operands v
  have hWork := GeneralPaperBasisCoordinateBits.scalar_work model.rat model.monotone W v
  change result.2≤scalarPrice model W (m*(K-1)) at hWork
  have hShape : result.2=24*W+sub+mul+add := rfl
  have hIndex := result.1.isLt
  have hScratch : sub+mul+add≤6*model.rat (1+binaryWordWidth (m*(K-1)+1)) := by unfold scalarPrice at hWork; omega
  have hf := fields_bound W (natBits (scalarCap model W m K))
    [m,K,K-1,v.1.val,v.2.val,v.1.val*(K-1),result.1.val,sub,mul,add,result.2,sub+mul,sub+mul+add,24*W] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold scalarCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤14*(natBits (scalarCap model W m K)+W)+32*W at hf
  unfold scalarWindow scalarProfile
  dsimp only
  dsimp only [sub,mul,add,result] at hf hScratch
  omega

def callbackPrice (model : RationalCostModel) (W d : ℕ) : ℕ := scalarPrice model W d+8*W
def callbackWindow {m K : ℕ} (model : RationalCostModel) (W : ℕ) (t : Variable m K×ℤ) : ℕ :=
  let packed := GeneralPaperBasisCoordinateBits.scalar model.rat W t.1
  termFoot W t+packedTermFoot W (packed.1,t.2)+scalarWindow model W t.1+
    fields W [packed.2,packed.2+8*W,8*W]+128*W
def callbackProfile (model : RationalCostModel) (W m K : ℕ) : ℕ :=
  termProfile W m K+packedTermProfile W (m*(K-1))+scalarProfile model W m K+
    3*(natBits (scalarCap model W m K)+W)+160*W

theorem callback_bound {m K : ℕ} (model : RationalCostModel) (W : ℕ) (t : Variable m K×ℤ) (ht : t.2.natAbs≤1) :
    callbackWindow model W t≤callbackProfile model W m K := by
  let packed := GeneralPaperBasisCoordinateBits.scalar model.rat W t.1
  have hT := term_bound W t ht
  have hP := packed_term_bound W (packed.1,t.2) ht
  have hScalar := scalar_bound model W t.1
  have hWork := GeneralPaperBasisCoordinateBits.scalar_work model.rat model.monotone W t.1
  change packed.2≤scalarPrice model W (m*(K-1)) at hWork
  have hf := fields_bound W (natBits (scalarCap model W m K)) [packed.2,packed.2+8*W,8*W] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals unfold scalarCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (scalarCap model W m K)+W)+32*W at hf
  unfold callbackWindow callbackProfile
  dsimp only
  dsimp only [packed] at hP hf
  omega

def price (model : RationalCostModel) (W d N : ℕ) : ℕ := N*(40*W+6*model.rat (1+binaryWordWidth (d+1)))+2*W
def metadataCap (model : RationalCostModel) (W m K N : ℕ) : ℕ := m+K+m*(K-1)+N+1+3*price model W (m*(K-1)) N+2*W
def window {m K : ℕ} (model : RationalCostModel) (W : ℕ) (terms : List (Variable m K×ℤ)) : ℕ :=
  let result := GeneralPaperBasisCoordinateBits.run model.rat W terms
  listFootprint W (termFoot W) terms+
    GeneralPaperPricedPayloadStreamStorage.mapWindow W (packedTermFoot W)
      (fun t => let p := GeneralPaperBasisCoordinateBits.scalar model.rat W t.1; ((p.1,t.2),p.2+8*W))
      (fun _ => 0) none terms+(terms.map (callbackWindow model W)).sum+
    fields W [m,K,m*(K-1),terms.length,result.2,2*W]+192*W
def profile (model : RationalCostModel) (W m K N : ℕ) : ℕ :=
  N*(termProfile W m K+2*W)+32*W+
    GeneralPaperPricedPayloadStreamStorage.filterProfile W (packedTermProfile W (m*(K-1))) (callbackPrice model W (m*(K-1))) N 0+
    N*callbackProfile model W m K+6*(natBits (metadataCap model W m K N)+W)+224*W

theorem bounded {m K : ℕ} (model : RationalCostModel) (W N : ℕ) (terms : List (Variable m K×ℤ))
    (hn : terms.length≤N) (hu : ∀ t∈terms,t.2.natAbs≤1) : window model W terms≤profile model W m K N := by
  have hList := (list_bound W (termProfile W m K) (termFoot W) terms (fun t ht => term_bound W t (hu t ht))).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  have hMap := GeneralPaperPricedPayloadStreamStorage.map_bounded W (packedTermProfile W (m*(K-1))) (callbackPrice model W (m*(K-1))) N 0
    (packedTermFoot W) (fun t => let p := GeneralPaperBasisCoordinateBits.scalar model.rat W t.1; ((p.1,t.2),p.2+8*W))
    (fun _ => 0) none terms hn (by
      intro t _
      exact Nat.add_le_add_right (GeneralPaperBasisCoordinateBits.scalar_work model.rat model.monotone W t.1) (8*W))
    (fun t ht => packed_term_bound W _ (hu t ht)) (fun _ _ => le_rfl) (by intro a ha; cases ha)
  have hCallbacks := (sum_bound (callbackWindow model W) (callbackProfile model W m K) terms (fun t ht => callback_bound model W t (hu t ht))).trans
    (Nat.mul_le_mul_right _ hn)
  have hWork := (GeneralPaperBasisCoordinateBits.work model.rat model.monotone W terms).trans
    (show terms.length*(40*W+6*model.rat (1+binaryWordWidth (m*(K-1)+1)))+2*W≤price model W (m*(K-1)) N by unfold price; gcongr)
  have hf := fields_bound W (natBits (metadataCap model W m K N))
    [m,K,m*(K-1),terms.length,(GeneralPaperBasisCoordinateBits.run model.rat W terms).2,2*W] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (metadataCap model W m K N)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only at hMap
  omega

end Blotto.GeneralPaperBasisCoordinateStorage
