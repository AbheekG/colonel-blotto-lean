import Blotto.GeneralPaperStaticEnumerationStorage

/-! Stock source list ofFn/map/flatten construction in the paper reference
model. Owned payloads, copied reference prefixes and constructor control
frames are counted. Flatten conservatively retains complete intermediate
append results; no runtime encoding or input-census pass is executed. -/
namespace Blotto.GeneralPaperStockListPayloadStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

def ofFnWindow {α : Type*} {n : ℕ} (W copied : ℕ) (encode : α → ℕ) (f : Fin n → α) : ℕ :=
  listFootprint W encode (List.ofFn f)+GeneralPaperBorrowedListStorage.footprint W ((List.ofFn f).take copied)+GeneralPaperFinRangeStorage.frames W n

def ofFnProfile (W P n : ℕ) : ℕ := n*(P+2*W)+32*W+(2*n*W+32*W)+(n+1)*(2*(natBits n+W)+160*W)

theorem ofFn_bound {α : Type*} {n : ℕ} (W P copied : ℕ) (encode : α → ℕ) (f : Fin n → α) (hf : ∀ i,encode (f i)≤P) :
    ofFnWindow W copied encode f≤ofFnProfile W P n := by
  have hList := list_bound W P encode (List.ofFn f) (by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact hf i)
  rw [List.length_ofFn] at hList
  have hCopy := GeneralPaperBorrowedListStorage.bounded W n ((List.ofFn f).take copied) (by rw [List.length_take,List.length_ofFn]; exact Nat.min_le_right _ _)
  have hFrames := GeneralPaperFinRangeStorage.frames_bound W n
  unfold ofFnWindow ofFnProfile
  omega

def mapWindow {α β : Type*} (W copied : ℕ) (encode : α → ℕ) (output : β → ℕ) (f : α → β) (xs : List α) : ℕ :=
  listFootprint W encode xs+listFootprint W output (xs.map f)+GeneralPaperBorrowedListStorage.footprint W ((xs.map f).take copied)+GeneralPaperFinRangeStorage.frames W xs.length

def mapProfile (W P Q N : ℕ) : ℕ := N*(P+2*W)+32*W+N*(Q+2*W)+32*W+(2*N*W+32*W)+(N+1)*(2*(natBits N+W)+160*W)

theorem map_bound {α β : Type*} (W P Q N copied : ℕ) (encode : α → ℕ) (output : β → ℕ) (f : α → β) (xs : List α)
    (hn : xs.length≤N) (hx : ∀ a∈xs,encode a≤P) (hf : ∀ a∈xs,output (f a)≤Q) :
    mapWindow W copied encode output f xs≤mapProfile W P Q N := by
  have hX := (list_bound W P encode xs hx).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  have hY := list_bound W Q output (xs.map f) (by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    exact hf a ha)
  rw [List.length_map] at hY
  have hY' := hY.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  have hCopy := GeneralPaperBorrowedListStorage.bounded W N ((xs.map f).take copied) (by
    rw [List.length_take,List.length_map]
    exact (Nat.min_le_right _ _).trans hn)
  have hFrames := (GeneralPaperFinRangeStorage.frames_bound W xs.length).trans (show
      (xs.length+1)*(2*(natBits xs.length+W)+160*W)≤(N+1)*(2*(natBits N+W)+160*W) by
        have hBits := Nat.add_le_add_left (binaryWordWidth_mono hn) 1
        change natBits xs.length≤natBits N at hBits
        gcongr)
  unfold mapWindow mapProfile
  omega

theorem flatten_length {α : Type*} (B : ℕ) (xss : List (List α)) (hb : ∀ xs∈xss,xs.length≤B) :
    xss.flatten.length≤xss.length*B := by
  induction xss with
  | nil => simp only [List.flatten_nil,List.length_nil,Nat.zero_mul,le_refl]
  | cons xs rest ih =>
    have hX := hb xs List.mem_cons_self
    have hRest := ih (fun ys hy => hb ys (List.mem_cons_of_mem _ hy))
    simp only [List.flatten_cons,List.length_append,List.length_cons]
    nlinarith only [hX,hRest]

def flattenFrames {α : Type*} (W copied : ℕ) (encode : α → ℕ) : List (List α) → ℕ
  | [] => fields W [0,0,0,0]+128*W
  | xs::rest =>
    GeneralPaperPayloadAppendStorage.window W copied encode xs rest.flatten+
      fields W [(xs::rest).length,xs.length,rest.flatten.length,(xs::rest).flatten.length]+128*W+
        flattenFrames W copied encode rest

def flattenFrameProfile (W P B N : ℕ) : ℕ :=
  GeneralPaperPayloadAppendStorage.profile W P (N*B)+4*(natBits (N+N*B+B+1)+W)+160*W

theorem flatten_frames {α : Type*} (W P B N copied : ℕ) (encode : α → ℕ) (xss : List (List α)) (hn : xss.length≤N)
    (hb : ∀ xs∈xss,xs.length≤B) (hp : ∀ xs∈xss,∀ a∈xs,encode a≤P) :
    flattenFrames W copied encode xss≤(xss.length+1)*flattenFrameProfile W P B N := by
  induction xss with
  | nil =>
    have hf := fields_bound W (natBits (N+N*B+B+1)) [0,0,0,0] (by intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha; rcases ha with rfl|rfl|rfl|rfl <;> exact Nat.add_le_add_left (binaryWordWidth_mono (Nat.zero_le _)) 1)
    change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (N+N*B+B+1)+W)+32*W at hf
    simp only [flattenFrames,List.length_nil,Nat.zero_add,Nat.one_mul]
    unfold flattenFrameProfile
    omega
  | cons xs rest ih =>
    have hRestLen : rest.length≤N := by simp only [List.length_cons] at hn; omega
    have hRest := ih hRestLen (fun ys hy => hb ys (List.mem_cons_of_mem _ hy)) (fun ys hy => hp ys (List.mem_cons_of_mem _ hy))
    have hLength := (flatten_length B (xs::rest) hb).trans (Nat.mul_le_mul_right B hn)
    have hRestFlat := (flatten_length B rest (fun ys hy => hb ys (List.mem_cons_of_mem _ hy))).trans (Nat.mul_le_mul_right B hRestLen)
    have hHead := hb xs List.mem_cons_self
    have hAppend := GeneralPaperPayloadAppendStorage.bounded W P (N*B) copied encode xs rest.flatten
      (by simpa only [List.flatten_cons,List.length_append] using hLength) (hp xs List.mem_cons_self) (by
        intro a ha
        obtain ⟨ys,hy,ha⟩ := List.mem_flatten.mp ha
        exact hp ys (List.mem_cons_of_mem _ hy) a ha)
    have hf := fields_bound W (natBits (N+N*B+B+1)) [(xs::rest).length,xs.length,rest.flatten.length,(xs::rest).flatten.length] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl <;> omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (N+N*B+B+1)+W)+32*W at hf
    change GeneralPaperPayloadAppendStorage.window W copied encode xs rest.flatten+
      GeneralPaperEncodedScalarStorage.fields W [(xs::rest).length,xs.length,rest.flatten.length,(xs::rest).flatten.length]+128*W+flattenFrames W copied encode rest≤_
    unfold flattenFrameProfile at *
    simp only [List.length_cons] at hf ⊢
    nlinarith only [hRest,hAppend,hf]

def flattenWindow {α : Type*} (W copied : ℕ) (encode : α → ℕ) (xss : List (List α)) : ℕ :=
  listFootprint W (listFootprint W encode) xss+flattenFrames W copied encode xss

def flattenProfile (W P B N : ℕ) : ℕ :=
  N*(B*(P+2*W)+32*W+2*W)+32*W+(N+1)*flattenFrameProfile W P B N

theorem flatten_bound {α : Type*} (W P B N copied : ℕ) (encode : α → ℕ) (xss : List (List α)) (hn : xss.length≤N)
    (hb : ∀ xs∈xss,xs.length≤B) (hp : ∀ xs∈xss,∀ a∈xs,encode a≤P) :
    flattenWindow W copied encode xss≤flattenProfile W P B N := by
  have hList := (list_bound W (B*(P+2*W)+32*W) (listFootprint W encode) xss (fun xs hx =>
    (list_bound W P encode xs (hp xs hx)).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hb xs hx)) _))).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  have hFrames := (flatten_frames W P B N copied encode xss hn hb hp).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hn 1))
  unfold flattenWindow flattenProfile
  omega

end Blotto.GeneralPaperStockListPayloadStorage
