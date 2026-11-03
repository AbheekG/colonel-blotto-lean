import Blotto.GeneralPaperEqualCopiedPipeline

/-! Literal indexed-fill storage with separate temporary-frame and output
reference widths. Source prices still come from the destination-priced fill.
The exact saved values are unchanged; temporary frame references use S.
Payload sums preserve the additive large-entry bound. -/
namespace Blotto.GeneralPaperDualWidthFillStorage
open GeneralPaperEncodedScalarStorage PaperIndexedArrayConstruction
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem fields_upgrade (S D : ℕ) (xs : List ℕ) : fields S xs ≤ fields D xs + (xs.length + 32) * S := by
  unfold fields
  nlinarith

def frame {α : Type*} {n : ℕ} (S D : ℕ) (encode : α → ℕ) (callback : Fin n → α × ℕ) : (k : ℕ) → k ≤ n → ℕ
  | 0,hk => fields S [n,0,initialWork id D n,(fill id D callback 0 hk).2] + 128 * S
  | k + 1,hk =>
    let earlier := fill id D callback k (by omega)
    let current := callback ⟨k,by omega⟩
    let step := stepWork id D k
    let result := fill id D callback (k + 1) hk
    encode current.1 + fields S [n,k,k+1,earlier.2,current.2,step,result.2,earlier.2+current.2,earlier.2+current.2+step] + 192 * S

theorem frame_upgrade {α : Type*} {n : ℕ} (S D : ℕ) (encode : α → ℕ) (callback : Fin n → α × ℕ)
    (k : ℕ) (hk : k ≤ n) : frame S D encode callback k hk ≤
      GeneralPaperNativePayloadFillStorage.frame D encode callback k hk + 256 * S := by
  cases k with
  | zero =>
    have h := fields_upgrade S D [n,0,initialWork id D n,(fill id D callback 0 hk).2]
    change fields S _ ≤ fields D _ + 36 * S at h
    dsimp only [frame,GeneralPaperNativePayloadFillStorage.frame]
    change fields S [n,0,initialWork id D n,(fill id D callback 0 hk).2] + 128 * S ≤
      fields D [n,0,initialWork id D n,(fill id D callback 0 hk).2] + 128 * D + 256 * S
    omega
  | succ k =>
    let earlier := fill id D callback k (by omega)
    let current := callback ⟨k,by omega⟩
    let step := stepWork id D k
    let result := fill id D callback (k + 1) hk
    have h := fields_upgrade S D
      [n,k,k+1,earlier.2,current.2,step,result.2,earlier.2+current.2,earlier.2+current.2+step]
    change fields S _ ≤ fields D _ + 41 * S at h
    dsimp only [frame,GeneralPaperNativePayloadFillStorage.frame]
    change encode current.1 + fields S [n,k,k+1,earlier.2,current.2,step,result.2,earlier.2+current.2,earlier.2+current.2+step] + 192 * S ≤
      encode current.1 + fields D [n,k,k+1,earlier.2,current.2,step,result.2,earlier.2+current.2,earlier.2+current.2+step] + 192 * D + 256 * S
    omega

def frames {α : Type*} {n : ℕ} (S D : ℕ) (encode : α → ℕ) (callback : Fin n → α × ℕ) : (k : ℕ) → k ≤ n → ℕ
  | 0,hk => frame S D encode callback 0 hk
  | k + 1,hk => frame S D encode callback (k + 1) hk + frames S D encode callback k (by omega)

theorem frames_upgrade {α : Type*} {n : ℕ} (S D : ℕ) (encode : α → ℕ) (callback : Fin n → α × ℕ)
    (k : ℕ) (hk : k ≤ n) : frames S D encode callback k hk ≤
      GeneralPaperNativePayloadFillStorage.frames D encode callback k hk + (k + 1) * (256 * S) := by
  induction k with
  | zero => simpa only [frames,GeneralPaperNativePayloadFillStorage.frames,Nat.zero_add,Nat.one_mul] using
      frame_upgrade S D encode callback 0 hk
  | succ k ih =>
    have hf := frame_upgrade S D encode callback (k + 1) hk
    have hi := ih (by omega)
    dsimp only [frames,GeneralPaperNativePayloadFillStorage.frames]
    nlinarith only [hf,hi]

def window {α : Type*} {n : ℕ} (S D : ℕ) (encode : α → ℕ) (callback : Fin n → α × ℕ)
    (space : Fin n → ℕ) (k : ℕ) (hk : k ≤ n) : ℕ :=
  let built := fill id D callback k hk
  let result := run id D callback
  2 * GeneralPaperEncodedReferenceVector.reservedFootprint D n encode built.1 +
    GeneralPaperEncodedBasisStorage.arrayFootprint D encode result.1 + frames S D encode callback k hk +
    GeneralPaperNativePayloadFillStorage.current encode callback k + GeneralPaperNativePayloadFillStorage.active space k +
    fields S [n,k,k+1,built.2,result.2] + 192 * S

theorem window_upgrade {α : Type*} {n : ℕ} (S D : ℕ) (encode : α → ℕ) (callback : Fin n → α × ℕ)
    (space : Fin n → ℕ) (k : ℕ) (hk : k ≤ n) : window S D encode callback space k hk ≤
      GeneralPaperNativePayloadFillStorage.window D encode callback space k hk + (k + 2) * (256 * S) := by
  have hFrames := frames_upgrade S D encode callback k hk
  have hFields := fields_upgrade S D [n,k,k+1,(fill id D callback k hk).2,(run id D callback).2]
  change fields S _ ≤ fields D _ + 37 * S at hFields
  dsimp only [window,GeneralPaperNativePayloadFillStorage.window]
  change
    2 * GeneralPaperEncodedReferenceVector.reservedFootprint D n encode (fill id D callback k hk).1 +
      GeneralPaperEncodedBasisStorage.arrayFootprint D encode (run id D callback).1 + frames S D encode callback k hk +
      GeneralPaperNativePayloadFillStorage.current encode callback k + GeneralPaperNativePayloadFillStorage.active space k +
      fields S [n,k,k+1,(fill id D callback k hk).2,(run id D callback).2] + 192 * S ≤
    2 * GeneralPaperEncodedReferenceVector.reservedFootprint D n encode (fill id D callback k hk).1 +
      GeneralPaperEncodedBasisStorage.arrayFootprint D encode (run id D callback).1 +
      GeneralPaperNativePayloadFillStorage.frames D encode callback k hk +
      GeneralPaperNativePayloadFillStorage.current encode callback k + GeneralPaperNativePayloadFillStorage.active space k +
      fields D [n,k,k+1,(fill id D callback k hk).2,(run id D callback).2] + 192 * D + (k + 2) * (256 * S)
  nlinarith only [hFrames,hFields]

def profile (S D B P n C Q : ℕ) : ℕ :=
  GeneralPaperAdditivePayloadFillStorage.profile D B P n C Q + (n + 2) * (256 * S)

theorem bounded {α : Type*} {n : ℕ} (S D B P C Q : ℕ) (encode : α → ℕ)
    (callback : Fin n → α × ℕ) (space : Fin n → ℕ)
    (hB : (∑ i : Fin n,encode (callback i).1) ≤ B) (hP : ∀ i,encode (callback i).1 ≤ P)
    (hC : ∀ i,(callback i).2 ≤ C) (hQ : ∀ i,space i ≤ Q)
    (hD : 1 ≤ D) (hIndex : binaryWordWidth (n + 1) ≤ D) (k : ℕ) (hk : k ≤ n) :
    window S D encode callback space k hk ≤ profile S D B P n C Q := by
  have hw := window_upgrade S D encode callback space k hk
  have hb := GeneralPaperAdditivePayloadFillStorage.bounded D B P C Q encode callback space hB hP hC hQ hD hIndex k hk
  have hn := Nat.mul_le_mul_right (256 * S) (by omega : k + 2 ≤ n + 2)
  unfold profile
  omega

end Blotto.GeneralPaperDualWidthFillStorage
