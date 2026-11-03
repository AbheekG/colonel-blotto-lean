import Blotto.GeneralPaperOriginalTupleConstructionStorage

/-! Literal ORIGINAL blocker-row construction, including high-row signed
map, full descriptor/tuple and sparse returned row. All sign callbacks are
conservatively retained, with input/output operands and native metadata.
Original dictionary/basis owners remain in preceding phase contracts. -/
namespace Blotto.GeneralPaperBlockerRowConstructionStorage
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStaticRayRows GeneralPaperRayBlockerRows
open GeneralPaperStaticRowResidualStorage GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem unit_row_bound {m K : ℕ} (W : ℕ) (r : Row (Variable m K)) (hn : r.terms.length≤m+1)
    (hu : ∀ t∈r.terms,t.2.natAbs≤1) (hc : r.constant.natAbs≤1) (hs : r.slope.natAbs≤1) :
    rowFoot W (termFoot W) r≤rowProfile W m K := by
  have hl := (list_bound W (termProfile W m K) (termFoot W) r.terms (fun t ht => term_bound W t (hu t ht))).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  have hC := binaryWordWidth_mono hc
  have hS := binaryWordWidth_mono hs
  have hOne : binaryWordWidth 1=1 := by decide
  unfold rowFoot rowProfile GeneralPaperEncodedBasisStorage.integerBits
  omega

theorem output_bound {T m K : ℕ} (W : ℕ) (hm : 0<m) (labels : Fin T → Fin m → Fin K) (b : Descriptor T m K) :
    rowFoot W (termFoot W) (GeneralPaperBlockerRowPrice.run W labels b).1≤rowProfile W m K := by
  cases b with
  | inl i =>
    rw [GeneralPaperBlockerRowPrice.data]
    exact GeneralPaperStaticRowResidualStorage.row_bound W hm labels i
  | inr tuple =>
    apply unit_row_bound
    · rw [GeneralPaperBlockerRowPrice.data]
      exact GeneralPaperBlockerRowPrice.length hm labels (.inr tuple)
    · intro t ht
      change t∈(GeneralPaperPricedListMap.run W (fun t => ((t.1,-t.2),8*W))
        (GeneralPaperBlockerRowPrice.tupleRun W tuple.read).1).1 at ht
      rw [GeneralPaperPricedListMap.data] at ht
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      simpa only [Int.natAbs_neg] using GeneralPaperOriginalTupleConstructionStorage.terms_unit W tuple.read u hu
    · change (0:ℤ).natAbs≤1; norm_num
    · change (-1:ℤ).natAbs≤1; norm_num

def callbackWindow {m K : ℕ} (W : ℕ) (t : Variable m K×ℤ) : ℕ :=
  termFoot W t+termFoot W (t.1,-t.2)+fields W [8*W]+128*W
def callbackProfile (W m K : ℕ) : ℕ := 2*termProfile W m K+(natBits (8*W)+W)+160*W

theorem callback_bound {m K : ℕ} (W : ℕ) (t : Variable m K×ℤ) (ht : t.2.natAbs≤1) :
    callbackWindow W t≤callbackProfile W m K := by
  have hA := term_bound W t ht
  have hB := term_bound W (t.1,-t.2) (by simpa only [Int.natAbs_neg] using ht)
  have hf := fields_bound W (natBits (8*W)) [8*W] (by intro a ha; simp only [List.mem_singleton] at ha; subst a; exact le_rfl)
  change GeneralPaperEncodedScalarStorage.fields W _≤1*(natBits (8*W)+W)+32*W at hf
  unfold callbackWindow callbackProfile
  omega

def signedWindow {m K : ℕ} (W : ℕ) (labels : Fin m → Fin K) : ℕ :=
  let terms := (GeneralPaperBlockerRowPrice.tupleRun W labels).1
  GeneralPaperPricedPayloadStreamStorage.mapWindow W (termFoot W) (fun t => ((t.1,-t.2),8*W))
    (fun _ => 0) none terms+listFootprint W (termFoot W) terms+(terms.map (callbackWindow W)).sum
def signedProfile (W m K : ℕ) : ℕ :=
  GeneralPaperPricedPayloadStreamStorage.filterProfile W (termProfile W m K) (8*W) m 0+
    GeneralPaperPricedPayloadStreamStorage.listProfile W (termProfile W m K) m+m*callbackProfile W m K

theorem signed_bound {m K : ℕ} (W : ℕ) (labels : Fin m → Fin K) : signedWindow W labels≤signedProfile W m K := by
  let terms := (GeneralPaperBlockerRowPrice.tupleRun W labels).1
  have hLen := GeneralPaperOriginalTupleConstructionStorage.terms_length W labels
  have hUnit := GeneralPaperOriginalTupleConstructionStorage.terms_unit W labels
  have hMap := GeneralPaperPricedPayloadStreamStorage.map_bounded W (termProfile W m K) (8*W) m 0
    (termFoot W) (fun t => ((t.1,-t.2),8*W)) (fun _ => 0) none terms hLen (fun _ _ => le_rfl)
    (fun t ht => term_bound W (t.1,-t.2) (by simpa only [Int.natAbs_neg] using hUnit t ht))
    (fun _ _ => le_rfl) (by intro a ha; cases ha)
  have hList := (list_bound W (termProfile W m K) (termFoot W) terms (fun t ht => term_bound W t (hUnit t ht))).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) _)
  have hCallbacks := (sum_bound (callbackWindow W) (callbackProfile W m K) terms (fun t ht => callback_bound W t (hUnit t ht))).trans
    (Nat.mul_le_mul_right _ hLen)
  unfold signedWindow signedProfile GeneralPaperPricedPayloadStreamStorage.listProfile
  dsimp only
  dsimp only [terms] at hMap hList hCallbacks
  omega

def descriptorProfile (W T m K : ℕ) : ℕ :=
  GeneralPaperNativeStaticScanStorage.indexProfile W T m K+GeneralPaperFixedTupleDecodeStorage.rowProfile W m K+8*W

theorem descriptor_bound {T m K : ℕ} (W : ℕ) (b : Descriptor T m K) :
    GeneralPaperEndpointReturnStorage.descriptorFoot W b≤descriptorProfile W T m K := by
  cases b with
  | inl i =>
    have h := GeneralPaperNativeStaticScanStorage.index_bound W i
    dsimp only [GeneralPaperEndpointReturnStorage.descriptorFoot,descriptorProfile]
    omega
  | inr tuple =>
    have h := GeneralPaperFixedTupleDecodeStorage.row_bound W (some tuple)
    dsimp only [GeneralPaperEndpointReturnStorage.descriptorFoot,descriptorProfile]
    omega

def tupleWork {T m K : ℕ} (W : ℕ) (labels : Fin T → Fin m → Fin K) : Descriptor T m K → ℕ
  | .inl (.inr (.inr i)) => (GeneralPaperBlockerRowPrice.tupleRun W (labels i)).2
  | .inr tuple => (GeneralPaperBlockerRowPrice.tupleRun W tuple.read).2
  | _ => 0
def signedWork {T m K : ℕ} (W : ℕ) : Descriptor T m K → ℕ
  | .inr tuple => (GeneralPaperPricedListMap.run W (fun t => ((t.1,-t.2),8*W)) (GeneralPaperBlockerRowPrice.tupleRun W tuple.read).1).2
  | _ => 0

def branch {T m K : ℕ} (W copied : ℕ) (labels : Fin T → Fin m → Fin K) : Descriptor T m K → ℕ
  | .inl (.inl v) => GeneralPaperStaticRowConstructionStorage.window W copied labels (.inl v)
  | .inl (.inr (.inl v)) => GeneralPaperStaticRowConstructionStorage.window W copied labels (.inr (.inl v))
  | .inl (.inr (.inr i)) => GeneralPaperOriginalTupleConstructionStorage.window W copied (labels i)
  | .inr tuple => GeneralPaperOriginalTupleConstructionStorage.window W copied tuple.read+signedWindow W tuple.read

def controlCap (W T m K : ℕ) : ℕ := T+m+K+1+3*(256*(m+1)*W)+64*W
def window {T m K : ℕ} (W copied : ℕ) (labels : Fin T → Fin m → Fin K) (b : Descriptor T m K) : ℕ :=
  let result := GeneralPaperBlockerRowPrice.run W labels b
  GeneralPaperEndpointReturnStorage.descriptorFoot W b+rowFoot W (termFoot W) result.1+branch W copied labels b+
    fields W [T,m,K,result.2,tupleWork W labels b,signedWork W b,tupleWork W labels b+signedWork W b,
      tupleWork W labels b+signedWork W b+16*W,16*W,32*W,64*W]+256*W
def profile (W T m K : ℕ) : ℕ := descriptorProfile W T m K+rowProfile W m K+
  GeneralPaperStaticRowConstructionStorage.profile W m K+GeneralPaperOriginalTupleConstructionStorage.profile W m K+signedProfile W m K+
    11*(natBits (controlCap W T m K)+W)+288*W

theorem bounded {T m K : ℕ} (W copied : ℕ) (hm : 0<m) (labels : Fin T → Fin m → Fin K) (b : Descriptor T m K) :
    window W copied labels b≤profile W T m K := by
  let result := GeneralPaperBlockerRowPrice.run W labels b
  have hDescriptor := descriptor_bound W b
  have hRow := output_bound W hm labels b
  have hBranch : branch W copied labels b≤GeneralPaperStaticRowConstructionStorage.profile W m K+
      GeneralPaperOriginalTupleConstructionStorage.profile W m K+signedProfile W m K := by
    rcases b with static|tuple
    · rcases static with v|v|i
      · have h := GeneralPaperStaticRowConstructionStorage.bounded W copied hm labels (.inl v)
        dsimp only [branch]; omega
      · have h := GeneralPaperStaticRowConstructionStorage.bounded W copied hm labels (.inr (.inl v))
        dsimp only [branch]; omega
      · have h := GeneralPaperOriginalTupleConstructionStorage.bounded W copied (labels i)
        dsimp only [branch]; omega
    · have h := GeneralPaperOriginalTupleConstructionStorage.bounded W copied tuple.read
      have hs := signed_bound W tuple.read
      dsimp only [branch]; omega
  have hWork := GeneralPaperBlockerRowPrice.work W labels b
  change result.2≤256*(m+1)*W at hWork
  have hSum : tupleWork W labels b+signedWork W b+16*W≤result.2 := by
    rcases b with static|tuple
    · rcases static with ⟨v,b⟩|v|i
      · cases b <;> dsimp only [tupleWork,signedWork,result,GeneralPaperBlockerRowPrice.run] <;> omega
      · dsimp only [tupleWork,signedWork,result,GeneralPaperBlockerRowPrice.run]; omega
      · dsimp only [tupleWork,signedWork,result,GeneralPaperBlockerRowPrice.run]; omega
    · dsimp only [tupleWork,signedWork,result,GeneralPaperBlockerRowPrice.run]; omega
  have hPay : 64*W≤256*(m+1)*W := by nlinarith only [Nat.zero_le (m*W)]
  have hf := fields_bound W (natBits (controlCap W T m K))
    [T,m,K,result.2,tupleWork W labels b,signedWork W b,tupleWork W labels b+signedWork W b,
      tupleWork W labels b+signedWork W b+16*W,16*W,32*W,64*W] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold controlCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤11*(natBits (controlCap W T m K)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [result] at hf
  omega

end Blotto.GeneralPaperBlockerRowConstructionStorage
