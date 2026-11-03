import Blotto.GeneralPaperSourceBlockDivisionReachedRates

/-! Literal native indexed scatter storage. The initial buffer and its
fill stack, current/returned arrays, two write reservations and recursive
metadata frames coexist. Older table payload histories do not accumulate;
each frame retains references, a callback value/key and encoded prices. -/
namespace Blotto.GeneralPaperNativeIndexedScatterStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperIndexedScatter (fill run)
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

def fillPrice (W m C : ℕ) : ℕ := m*C+96*(m+1)*W
def price (W n m C : ℕ) : ℕ := m*C+192*(n+m+1)*W
def metadataCap (W n m C : ℕ) : ℕ :=
  n+m+1+GeneralPaperNativePayloadFillStorage.workCap W n (32*W)+fillPrice W m C+price W n m C+C+96*W

theorem fill_payload {α : Type*} {n m : ℕ} (W P : ℕ) (encode : α → ℕ)
    (callback : Fin m → (Fin n×α)×ℕ) (hp : ∀ i,encode (callback i).1.2≤P)
    (k : ℕ) (hk : k≤m) (table : FixedArrayTable n α) (ht : ∀ j,encode (table.read j)≤P) :
    ∀ j,encode ((fill (fun w => w) W callback k hk table).1.read j)≤P := by
  induction k with
  | zero => exact ht
  | succ k ih =>
    intro j
    rw [fill]
    dsimp only
    rw [FixedArrayTable.read_write]
    split
    · exact hp _
    · exact ih (by omega) j

theorem fill_work {α : Type*} {n m : ℕ} (W C : ℕ) (callback : Fin m → (Fin n×α)×ℕ)
    (hc : ∀ i,(callback i).2≤C) (hW : 1≤W) (hIndex : binaryWordWidth (n+m+1)≤W)
    (k : ℕ) (hk : k≤m) (table : FixedArrayTable n α) :
    (fill (fun w => w) W callback k hk table).2≤fillPrice W m C :=
  (GeneralPaperIndexedScatter.fill_work (fun w => w) W C hW callback hc
    (fun _i hi => (binaryWordWidth_mono (by omega)).trans hIndex) k hk table).trans
      (by unfold fillPrice; gcongr)

theorem work {α : Type*} {n m : ℕ} (W C : ℕ) (default : α) (callback : Fin m → (Fin n×α)×ℕ)
    (hc : ∀ i,(callback i).2≤C) (hW : 1≤W) (hIndex : binaryWordWidth (n+m+1)≤W) :
    (run (fun w => w) W default callback).2≤price W n m C :=
  GeneralPaperIndexedScatter.work (fun w => w) W C hW default callback hc
    (fun _i hi => (binaryWordWidth_mono (Nat.add_le_add_right hi 1)).trans hIndex)

def frame {α : Type*} {n m : ℕ} (W : ℕ) (encode : α → ℕ) (callback : Fin m → (Fin n×α)×ℕ)
    (table : FixedArrayTable n α) : (k : ℕ) → k≤m → ℕ
  | 0,hk => fields W [m,0,(fill (fun w => w) W callback 0 hk table).2]+128*W
  | k+1,hk =>
    let old := fill (fun w => w) W callback k (by omega) table
    let current := callback ⟨k,by omega⟩
    let step := PaperIndexedArrayConstruction.stepWork (fun w => w) W k
    let result := fill (fun w => w) W callback (k+1) hk table
    encode current.1.2+fields W [m,k+1,current.1.1.val,old.2,current.2,step,result.2,
      old.2+current.2,old.2+current.2+step,32*W]+step+128*W
def frameProfile (W P n m C : ℕ) : ℕ := P+10*(natBits (metadataCap W n m C)+W)+256*W

theorem frame_bound {α : Type*} {n m : ℕ} (W P C : ℕ) (encode : α → ℕ)
    (callback : Fin m → (Fin n×α)×ℕ) (hp : ∀ i,encode (callback i).1.2≤P) (hc : ∀ i,(callback i).2≤C)
    (hW : 1≤W) (hIndex : binaryWordWidth (n+m+1)≤W) (table : FixedArrayTable n α) (k : ℕ) (hk : k≤m) :
    frame W encode callback table k hk≤frameProfile W P n m C := by
  cases k with
  | zero =>
    have hZero : (fill (fun w => w) W callback 0 hk table).2=16*W := rfl
    have hf := fields_bound W (natBits (metadataCap W n m C)) [m,0,(fill (fun w => w) W callback 0 hk table).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
    change fields W _≤3*(natBits (metadataCap W n m C)+W)+32*W at hf
    change fields W [m,0,(fill (fun w => w) W callback 0 hk table).2]+128*W≤_
    unfold frameProfile
    omega
  | succ k =>
    let old := fill (fun w => w) W callback k (by omega) table
    let current := callback ⟨k,by omega⟩
    let step := PaperIndexedArrayConstruction.stepWork (fun w => w) W k
    let result := fill (fun w => w) W callback (k+1) hk table
    have hOld := fill_work W C callback hc hW hIndex k (by omega) table
    have hResult := fill_work W C callback hc hW hIndex (k+1) hk table
    change old.2≤fillPrice W m C at hOld
    change result.2≤fillPrice W m C at hResult
    have hCurrent : current.2≤C := hc _
    have hPayload : encode current.1.2≤P := hp _
    have hShape : result.2=old.2+current.2+step+32*W := rfl
    have hStep : step≤50*W := (GeneralPaperListReferenceConstructionStorage.step_bound W m k (by omega) hW
      ((binaryWordWidth_mono (by omega)).trans hIndex)).trans' (by omega)
    have hKey := current.1.1.isLt.le
    have hf := fields_bound W (natBits (metadataCap W n m C))
      [m,k+1,current.1.1.val,old.2,current.2,step,result.2,old.2+current.2,old.2+current.2+step,32*W] (by
        intro z hz
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals unfold metadataCap; omega)
    change fields W _≤10*(natBits (metadataCap W n m C)+W)+32*W at hf
    change encode current.1.2+fields W [m,k+1,current.1.1.val,old.2,current.2,step,result.2,
      old.2+current.2,old.2+current.2+step,32*W]+step+128*W≤_
    unfold frameProfile
    omega

def frames {α : Type*} {n m : ℕ} (W : ℕ) (encode : α → ℕ) (callback : Fin m → (Fin n×α)×ℕ)
    (table : FixedArrayTable n α) : (k : ℕ) → k≤m → ℕ
  | 0,hk => frame W encode callback table 0 hk
  | k+1,hk => frame W encode callback table (k+1) hk+frames W encode callback table k (by omega)

theorem frames_bound {α : Type*} {n m : ℕ} (W P C : ℕ) (encode : α → ℕ)
    (callback : Fin m → (Fin n×α)×ℕ) (hp : ∀ i,encode (callback i).1.2≤P) (hc : ∀ i,(callback i).2≤C)
    (hW : 1≤W) (hIndex : binaryWordWidth (n+m+1)≤W) (table : FixedArrayTable n α) (k : ℕ) (hk : k≤m) :
    frames W encode callback table k hk≤(k+1)*frameProfile W P n m C := by
  induction k with
  | zero => simpa only [frames,Nat.zero_add,Nat.one_mul] using frame_bound W P C encode callback hp hc hW hIndex table 0 hk
  | succ k ih => exact (Nat.add_le_add (frame_bound W P C encode callback hp hc hW hIndex table (k+1) hk)
      (ih (by omega))).trans_eq (by ring)

def window {α : Type*} {n m : ℕ} (W : ℕ) (encode : α → ℕ) (default : α)
    (callback : Fin m → (Fin n×α)×ℕ) (space : Fin m → ℕ)
    (initialCount : ℕ) (hi : initialCount≤n) (count : ℕ) (hc : count≤m) (active : Option (Fin m)) : ℕ :=
  let initial := PaperIndexedArrayConstruction.run (fun w => w) W (fun _ : Fin n => (default,32*W))
  let built := fill (fun w => w) W callback count hc initial.1
  let result := run (fun w => w) W default callback
  GeneralPaperNativePayloadFillStorage.window W encode (fun _ : Fin n => (default,32*W)) (fun _ => 0) initialCount hi+
    3*arrayFootprint W encode built.1+arrayFootprint W encode result.1+frames W encode callback initial.1 count hc+
    (match active with | none => 0 | some i => natBits (callback i).1.1.val+encode (callback i).1.2+space i)+
    fields W [n,m,initial.2,built.2,result.2,initial.2+built.2,16*W,count]+128*W
def profile (W P n m C Q : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.profile W P n (32*W) 0+4*arrayProfile W n P+
    (m+1)*frameProfile W P n m C+natBits n+P+Q+8*(natBits (metadataCap W n m C)+W)+160*W

theorem profile_mono (W P n m C C' Q Q' : ℕ) (hc : C≤C') (hq : Q≤Q') :
    profile W P n m C Q≤profile W P n m C' Q' := by
  unfold profile frameProfile metadataCap fillPrice price natBits
  gcongr

theorem bounded {α : Type*} {n m : ℕ} (W P C Q : ℕ) (encode : α → ℕ) (default : α)
    (callback : Fin m → (Fin n×α)×ℕ) (space : Fin m → ℕ) (hd : encode default≤P)
    (hp : ∀ i,encode (callback i).1.2≤P) (hc : ∀ i,(callback i).2≤C) (hq : ∀ i,space i≤Q)
    (hW : 1≤W) (hIndex : binaryWordWidth (n+m+1)≤W)
    (initialCount : ℕ) (hi : initialCount≤n) (count : ℕ) (hCount : count≤m) (active : Option (Fin m)) :
    window W encode default callback space initialCount hi count hCount active≤profile W P n m C Q := by
  let initial := PaperIndexedArrayConstruction.run (fun w => w) W (fun _ : Fin n => (default,32*W))
  let built := fill (fun w => w) W callback count hCount initial.1
  let result := run (fun w => w) W default callback
  have hI : binaryWordWidth (n+1)≤W := (binaryWordWidth_mono (by omega)).trans hIndex
  have hInitial := GeneralPaperNativePayloadFillStorage.bounded W P (32*W) 0 encode
    (fun _ : Fin n => (default,32*W)) (fun _ => 0) (fun _ => hd) (fun _ => le_rfl) (fun _ => le_rfl) hW hI initialCount hi
  have hInitialPayload (j : Fin n) : encode (initial.1.read j)≤P := by
    dsimp only [initial]
    rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact hd
  have hBuilt := array_bound W P encode built.1 (fill_payload W P encode callback hp count hCount initial.1 hInitialPayload)
  have hReturned := array_bound W P encode result.1 (fill_payload W P encode callback hp m le_rfl initial.1 hInitialPayload)
  have hFrames := (frames_bound W P C encode callback hp hc hW hIndex initial.1 count hCount).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hCount 1))
  have hActive : (match active with | none => 0 | some i => natBits (callback i).1.1.val+encode (callback i).1.2+space i)≤natBits n+P+Q := by
    cases active with
    | none => exact Nat.zero_le _
    | some i =>
      have hKey := Nat.add_le_add_left (binaryWordWidth_mono (callback i).1.1.isLt.le) 1
      exact Nat.add_le_add (Nat.add_le_add hKey (hp i)) (hq i)
  have hIW := GeneralPaperNativePayloadFillStorage.prefix_work W (32*W) (fun _ : Fin n => (default,32*W)) (fun _ => le_rfl) hW hI n le_rfl
  change initial.2≤GeneralPaperNativePayloadFillStorage.workCap W n (32*W) at hIW
  have hBW := fill_work W C callback hc hW hIndex count hCount initial.1
  change built.2≤fillPrice W m C at hBW
  have hWork := work W C default callback hc hW hIndex
  change result.2≤price W n m C at hWork
  have hf := fields_bound W (natBits (metadataCap W n m C))
    [n,m,initial.2,built.2,result.2,initial.2+built.2,16*W,count] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change fields W _≤8*(natBits (metadataCap W n m C)+W)+32*W at hf
  change GeneralPaperNativePayloadFillStorage.window W encode (fun _ : Fin n => (default,32*W)) (fun _ => 0) initialCount hi+
    3*arrayFootprint W encode built.1+arrayFootprint W encode result.1+frames W encode callback initial.1 count hCount+_+
    fields W [n,m,initial.2,built.2,result.2,initial.2+built.2,16*W,count]+128*W≤_
  unfold profile
  omega

end Blotto.GeneralPaperNativeIndexedScatterStorage
