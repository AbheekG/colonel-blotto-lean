import Blotto.GeneralPaperSourceBlockerRowConstructionReachedRates

/-! Literal indexed mutable-reference-array fill storage for arbitrary
payloads. Two capacity buffers and the full returned array are retained;
recursive frames retain callback payloads and encoded native prices, with
one active callback window. The caller derives payload/work/scratch caps. -/
namespace Blotto.GeneralPaperNativePayloadFillStorage
open GeneralPaperEncodedScalarStorage PaperIndexedArrayConstruction
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def workCap (W n C : ℕ) : ℕ := n*C+64*(n+1)*W
def metadataCap (W n C : ℕ) : ℕ := n+1+3*workCap W n C+C+64*W

theorem prefix_work {α : Type*} {n : ℕ} (W C : ℕ) (callback : Fin n → α×ℕ)
    (hc : ∀ i,(callback i).2≤C) (hW : 1≤W) (hIndex : binaryWordWidth (n+1)≤W)
    (k : ℕ) (hk : k≤n) : (fill (fun w => w) W callback k hk).2≤workCap W n C := by
  rw [fill_work]
  have hSum := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin k) _ => hc ⟨i.val,by omega⟩)
  change (∑ i : Fin k,(callback ⟨i.val,by omega⟩).2)≤∑ _ : Fin k,C at hSum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hSum
  have hOver := overhead_bound (fun w => w) 1 (fun _ => by omega) W n k hk
  have hStep : 6*W+10*1*binaryWordWidth (n+1)+28≤64*W := by omega
  have hO := hOver.trans (Nat.mul_le_mul_left (k+1) hStep)
  have hC := Nat.mul_le_mul_right C hk
  have hK := Nat.mul_le_mul_right (64*W) (Nat.add_le_add_right hk 1)
  unfold workCap
  nlinarith only [hSum,hO,hC,hK]

def frame {α : Type*} {n : ℕ} (W : ℕ) (encode : α → ℕ) (callback : Fin n → α×ℕ) : (k : ℕ) → k≤n → ℕ
  | 0,hk => fields W [n,0,initialWork (fun w => w) W n,(fill (fun w => w) W callback 0 hk).2]+128*W
  | k+1,hk =>
    let earlier := fill (fun w => w) W callback k (by omega)
    let current := callback ⟨k,by omega⟩
    let step := stepWork (fun w => w) W k
    let result := fill (fun w => w) W callback (k+1) hk
    encode current.1+fields W [n,k,k+1,earlier.2,current.2,step,result.2,earlier.2+current.2,earlier.2+current.2+step]+192*W
def frameProfile (W P n C : ℕ) : ℕ := P+9*(natBits (metadataCap W n C)+W)+224*W

theorem frame_bound {α : Type*} {n : ℕ} (W P C : ℕ) (encode : α → ℕ) (callback : Fin n → α×ℕ)
    (hp : ∀ i,encode (callback i).1≤P) (hc : ∀ i,(callback i).2≤C)
    (hW : 1≤W) (hIndex : binaryWordWidth (n+1)≤W) (k : ℕ) (hk : k≤n) :
    frame W encode callback k hk≤frameProfile W P n C := by
  cases k with
  | zero =>
    have hWork := prefix_work W C callback hc hW hIndex 0 hk
    have hShape : (fill (fun w => w) W callback 0 hk).2=initialWork (fun w => w) W n := rfl
    have hf := fields_bound W (natBits (metadataCap W n C)) [n,0,initialWork (fun w => w) W n,(fill (fun w => w) W callback 0 hk).2] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (metadataCap W n C)+W)+32*W at hf
    dsimp only [frame,frameProfile]
    omega
  | succ k =>
    let earlier := fill (fun w => w) W callback k (by omega)
    let current := callback ⟨k,by omega⟩
    let step := stepWork (fun w => w) W k
    let result := fill (fun w => w) W callback (k+1) hk
    have hEarlier := prefix_work W C callback hc hW hIndex k (by omega)
    have hWork := prefix_work W C callback hc hW hIndex (k+1) hk
    change earlier.2≤workCap W n C at hEarlier
    change result.2≤workCap W n C at hWork
    have hCurrent : current.2≤C := hc _
    have hPayload : encode current.1≤P := hp _
    have hShape : result.2=earlier.2+current.2+step := rfl
    have hf := fields_bound W (natBits (metadataCap W n C))
      [n,k,k+1,earlier.2,current.2,step,result.2,earlier.2+current.2,earlier.2+current.2+step] (by
        intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals unfold metadataCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤9*(natBits (metadataCap W n C)+W)+32*W at hf
    change encode current.1+GeneralPaperEncodedScalarStorage.fields W [n,k,k+1,earlier.2,current.2,step,result.2,earlier.2+current.2,earlier.2+current.2+step]+192*W≤_
    unfold frameProfile
    omega

def frames {α : Type*} {n : ℕ} (W : ℕ) (encode : α → ℕ) (callback : Fin n → α×ℕ) : (k : ℕ) → k≤n → ℕ
  | 0,hk => frame W encode callback 0 hk
  | k+1,hk => frame W encode callback (k+1) hk+frames W encode callback k (by omega)

theorem frames_bound {α : Type*} {n : ℕ} (W P C : ℕ) (encode : α → ℕ) (callback : Fin n → α×ℕ)
    (hp : ∀ i,encode (callback i).1≤P) (hc : ∀ i,(callback i).2≤C)
    (hW : 1≤W) (hIndex : binaryWordWidth (n+1)≤W) (k : ℕ) (hk : k≤n) :
    frames W encode callback k hk≤(k+1)*frameProfile W P n C := by
  induction k with
  | zero => simpa only [frames,Nat.zero_add,Nat.one_mul] using frame_bound W P C encode callback hp hc hW hIndex 0 hk
  | succ k ih =>
    exact (Nat.add_le_add (frame_bound W P C encode callback hp hc hW hIndex (k+1) hk) (ih (by omega))).trans_eq (by ring)

def current {α : Type*} {n : ℕ} (encode : α → ℕ) (callback : Fin n → α×ℕ) (k : ℕ) : ℕ :=
  if h : k<n then encode (callback ⟨k,h⟩).1 else 0
def active {n : ℕ} (space : Fin n → ℕ) (k : ℕ) : ℕ := if h : k<n then space ⟨k,h⟩ else 0

def window {α : Type*} {n : ℕ} (W : ℕ) (encode : α → ℕ) (callback : Fin n → α×ℕ)
    (space : Fin n → ℕ) (k : ℕ) (hk : k≤n) : ℕ :=
  let built :=  fill (fun w => w) W callback k hk
  let result := run (fun w => w) W callback
  2*GeneralPaperEncodedReferenceVector.reservedFootprint W n encode built.1+
    GeneralPaperEncodedBasisStorage.arrayFootprint W encode result.1+frames W encode callback k hk+
    current encode callback k+active space k+fields W [n,k,k+1,built.2,result.2]+192*W
def profile (W P n C Q : ℕ) : ℕ := 2*(n*(P+W)+64*W)+(n*(P+W)+64*W)+
  (n+1)*frameProfile W P n C+P+Q+5*(natBits (metadataCap W n C)+W)+224*W

theorem bounded {α : Type*} {n : ℕ} (W P C Q : ℕ) (encode : α → ℕ) (callback : Fin n → α×ℕ)
    (space : Fin n → ℕ) (hp : ∀ i,encode (callback i).1≤P) (hc : ∀ i,(callback i).2≤C) (hq : ∀ i,space i≤Q)
    (hW : 1≤W) (hIndex : binaryWordWidth (n+1)≤W) (k : ℕ) (hk : k≤n) :
    window W encode callback space k hk≤profile W P n C Q := by
  have hBuffer := GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w) W W P encode callback hp k hk
  have hReturned := GeneralPaperEncodedBasisStorage.array_bound W P encode (run (fun w => w) W callback).1 (by
    intro i; rw [run_data,FixedArrayTable.read_ofFn]; exact hp i)
  have hFrames := (frames_bound W P C encode callback hp hc hW hIndex k hk).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hk 1))
  have hCurrent : current encode callback k≤P := by unfold current; split; exact hp _; omega
  have hActive : active space k≤Q := by unfold active; split; exact hq _; omega
  have hPartial := prefix_work W C callback hc hW hIndex k hk
  have hWork := prefix_work W C callback hc hW hIndex n le_rfl
  change (run (fun w => w) W callback).2≤workCap W n C at hWork
  have hf := fields_bound W (natBits (metadataCap W n C))
    [n,k,k+1,(fill (fun w => w) W callback k hk).2,(run (fun w => w) W callback).2] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (metadataCap W n C)+W)+32*W at hf
  unfold GeneralPaperEncodedBasisStorage.arrayProfile at hReturned
  rw [Nat.add_comm W P] at hReturned
  unfold window profile
  dsimp only
  omega

end Blotto.GeneralPaperNativePayloadFillStorage
