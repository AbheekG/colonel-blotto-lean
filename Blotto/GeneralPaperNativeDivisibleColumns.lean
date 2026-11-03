import Blotto.GeneralPaperNativeDictionaryNormalize

/-! The divisor-sized quantizer constructs B=T/K by adaptive arithmetic
once. Size casts erase and retain the same source/label arrays. No built-in
integer division runs on the real path to obtain the block size. -/
namespace Blotto.GeneralPaperNativeDivisibleColumns
set_option autoImplicit false
set_option maxHeartbeats 3200000

def blocks (price : ℕ → ℕ) (A T K : ℕ) (hK : 0<K) : Fin (T+1)×ℕ :=
  GeneralPaperNativeBlockLabel.run price A hK ⟨T,by nlinarith only [hK]⟩

theorem blocks_data (price : ℕ → ℕ) (A T K : ℕ) (hK : 0<K) : (blocks price A T K hK).1.val=T/K := by
  unfold blocks
  rw [GeneralPaperNativeBlockLabel.data]
  rfl

def castColumns {T U m K : ℕ} (h : T=U) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column U K)) :
    FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K) := h.symm ▸ columns

theorem cast_dictionary {T U m K : ℕ} (h : T=U) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column U K)) :
    GeneralPaperRowQuantizer.dictionary (castColumns h columns)=
      GeneralPaperRowQuantizer.castDictionary h (GeneralPaperRowQuantizer.dictionary columns) := by
  subst U
  rfl

theorem cast_words {T U m : ℕ} (h : T=U) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (H : ℕ)
    (hv : ∀ i j,rationalWordWidth ((rows.read i).read j)≤H) :
    ∀ i j,rationalWordWidth (((GeneralPaperRowQuantizer.castRows h rows).read i).read j)≤H := by
  subst U
  exact hv

def run {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)×ℕ :=
  let divided := blocks price A T K hK
  let B := divided.1.val
  have hs : T=K*B := by dsimp only [B,divided];rw [blocks_data];exact GeneralPaperRowQuantizer.divisor_size hDiv
  have hp : 0<B := by dsimp only [B,divided];rw [blocks_data];exact GeneralPaperRowQuantizer.divisor_block_pos hT hK hDiv
  let result := GeneralPaperNativeQuantizedMatrix.run price index A hK hp (GeneralPaperRowQuantizer.castRows hs rows)
  (castColumns hs result.1,divided.2+result.2+64*A)

theorem data {T m K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) :
    GeneralPaperRowQuantizer.dictionary (run price index A hT hK hDiv rows).1=
      GeneralPaperRowQuantizer.buildDivisible hT hK hDiv rows := by
  let B := (blocks price A T K hK).1.val
  have hs : T=K*B := by dsimp only [B];rw [blocks_data];exact GeneralPaperRowQuantizer.divisor_size hDiv
  have hp : 0<B := by dsimp only [B];rw [blocks_data];exact GeneralPaperRowQuantizer.divisor_block_pos hT hK hDiv
  have hGeneral (C : ℕ) (hc : C=T/K) (he : T=K*C) (hC : 0<C) :
      GeneralPaperRowQuantizer.castDictionary he
        (GeneralPaperRowQuantizer.build hK hC (GeneralPaperRowQuantizer.castRows he rows))=
          GeneralPaperRowQuantizer.buildDivisible hT hK hDiv rows := by
    subst C
    rfl
  change GeneralPaperRowQuantizer.dictionary (castColumns hs
    (GeneralPaperNativeQuantizedMatrix.run price index A hK hp (GeneralPaperRowQuantizer.castRows hs rows)).1)=_
  rw [cast_dictionary,GeneralPaperNativeQuantizedMatrix.dictionary_data]
  exact hGeneral B (blocks_data price A T K hK) hs hp

theorem work {T m K : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A H : ℕ) (hA : 1≤A)
    (hT : 0<T) (hK : 0<K) (hDiv : K∣T) (rows : FixedArrayTable T (FixedArrayTable m ℚ))
    (hv : ∀ i j,rationalWordWidth ((rows.read i).read j)≤H)
    (hIndex : ∀ i≤2*T+K+m,index (binaryWordWidth (i+1))≤A) :
    let B := (blocks price A T K hK).1.val
    (run price index A hT hK hDiv rows).2≤
      512*(binaryWordWidth ((T+1)*K)+1)*(A+price (GeneralPaperNativeBlockLabel.width ((T+1)*K) K))+
      m*(GeneralPaperNativeQuantizedMatrix.fieldProfile K B A (price H)
        (price (GeneralPaperNativeBlockLabel.width (K*B) B)) (price (1+binaryWordWidth (K*B+B+1)))+64*A)+44*(m+1)*A+64*A := by
  let B := (blocks price A T K hK).1.val
  have hs : T=K*B := by dsimp only [B];rw [blocks_data];exact GeneralPaperRowQuantizer.divisor_size hDiv
  have hp : 0<B := by dsimp only [B];rw [blocks_data];exact GeneralPaperRowQuantizer.divisor_block_pos hT hK hDiv
  have hd := GeneralPaperNativeBlockLabel.work (K:=T+1) (B:=K) price hMono A hK ⟨T,by nlinarith only [hK]⟩
  have hm := GeneralPaperNativeQuantizedMatrix.work price index hMono A H hA hK hp (GeneralPaperRowQuantizer.castRows hs rows)
    (cast_words hs rows H hv) (fun i hi => hIndex i (by omega))
  change (blocks price A T K hK).2≤_ at hd
  change (blocks price A T K hK).2+
    (GeneralPaperNativeQuantizedMatrix.run price index A hK hp (GeneralPaperRowQuantizer.castRows hs rows)).2+64*A≤_
  dsimp only [B] at hm
  omega

end Blotto.GeneralPaperNativeDivisibleColumns
