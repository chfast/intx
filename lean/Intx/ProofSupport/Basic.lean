import Mathlib
import Intx.Model.Uint
set_option warningAsError true
/-!
# Proof support: numbers of words, vectors and loops

The number `val` of a list of words, the array operations of the model, and the loop rules for the
`for` loops of the model.
-/

namespace Intx

/-! ## The number of a list of words -/

@[simp] theorem val_nil : val [] = 0 := rfl

@[simp] theorem val_cons (x : Word) (xs : List Word) :
    val (x :: xs) = x.toNat + 2 ^ 64 * val xs := rfl

theorem val_append (xs ys : List Word) :
    val (xs ++ ys) = val xs + 2 ^ (64 * xs.length) * val ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.cons_append, val_cons, val_cons, ih, List.length_cons, Nat.mul_succ, pow_add]
    ring

theorem val_lt (xs : List Word) : val xs < 2 ^ (64 * xs.length) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := x.toNat_lt
    simp only [val_cons, List.length_cons, Nat.mul_succ, pow_add]
    nlinarith

@[simp] theorem val_replicate_zero (n : Nat) : val (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem val_take_add_drop (l : List Word) (k : Nat) :
    val (l.take k) + 2 ^ (64 * k) * val (l.drop k) = val l := by
  by_cases hk : k ≤ l.length
  · have := val_append (l.take k) (l.drop k)
    rw [List.take_append_drop, List.length_take, Nat.min_eq_left hk] at this
    omega
  · rw [List.drop_eq_nil_of_le (by omega), List.take_of_length_le (by omega)]
    simp

theorem val_take (l : List Word) (k : Nat) : val (l.take k) = val l % 2 ^ (64 * k) := by
  have h1 := val_take_add_drop l k
  have h2 := val_lt (l.take k)
  have h3 : (l.take k).length ≤ k := by simp
  have h4 : 2 ^ (64 * (l.take k).length) ≤ 2 ^ (64 * k) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [← h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem val_drop (l : List Word) (k : Nat) : val (l.drop k) = val l / 2 ^ (64 * k) := by
  have h1 := val_take_add_drop l k
  have h2 : val (l.take k) < 2 ^ (64 * k) := by rw [val_take]; exact Nat.mod_lt _ (by positivity)
  rw [← h1, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h2, zero_add]

theorem val_set (l : List Word) (i : Nat) (v : Word) (h : i < l.length) :
    val (l.set i v) + 2 ^ (64 * i) * l[i].toNat = val l + 2 ^ (64 * i) * v.toNat := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp; ring
    | succ i =>
      simp only [List.set_cons_succ, val_cons, List.getElem_cons_succ]
      have := ih i (by simpa using h)
      rw [Nat.mul_succ, pow_add]
      nlinarith

theorem getElem_toNat (l : List Word) (i : Nat) (h : i < l.length) :
    l[i].toNat = val l / 2 ^ (64 * i) % 2 ^ 64 := by
  rw [← val_drop, List.drop_eq_getElem_cons h, val_cons, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (UInt64.toNat_lt _)]

/-- A list of words is the number whose words are its elements. -/
theorem val_eq_of_getElem (l : List Word) (X : Nat)
    (h : ∀ i (hi : i < l.length), l[i].toNat = X / 2 ^ (64 * i) % 2 ^ 64) :
    val l = X % 2 ^ (64 * l.length) := by
  induction l generalizing X with
  | nil => simp [Nat.mod_one]
  | cons x xs ih =>
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.mul_zero, pow_zero, Nat.div_one] at h0
    have ht := ih (X / 2 ^ 64) (fun i hi => by
      have := h (i + 1) (by simpa using hi)
      simp only [List.getElem_cons_succ] at this
      rw [this, Nat.div_div_eq_div_mul, ← pow_add]
      congr 3
      ring)
    simp only [val_cons, ht, h0, List.length_cons]
    rw [Nat.mul_succ, Nat.add_comm (64 * xs.length) 64, pow_add, Nat.mod_mul]

theorem val_ext {xs ys : List Word} (hl : xs.length = ys.length) (h : val xs = val ys) :
    xs = ys := by
  apply List.ext_getElem hl
  intro i h1 h2
  apply UInt64.toNat_inj.mp
  rw [getElem_toNat _ _ h1, getElem_toNat _ _ h2, h]

/-- The words `b` to `b + c` of `X` are the words of `X % 2 ^ a` for `b + c ≤ a`. -/
theorem mod_div_mod_pow (X a b c : Nat) (h : b + c ≤ a) :
    X % 2 ^ a / 2 ^ b % 2 ^ c = X / 2 ^ b % 2 ^ c := by
  conv_rhs => rw [← Nat.mod_add_div X (2 ^ a)]
  have e1 : 2 ^ a = 2 ^ b * (2 ^ c * 2 ^ (a - b - c)) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [e1, Nat.mul_assoc, Nat.add_mul_div_left _ _ (by positivity), Nat.mul_assoc,
    Nat.add_mul_mod_self_left, ← e1]

/-! ## The number of a vector of words -/

theorem val_toList_lt {n : Nat} (v : Vector Word n) : val v.toList < 2 ^ (64 * n) := by
  simpa using val_lt v.toList

theorem getElem_toNat' {n : Nat} (v : Vector Word n) (i : Nat) (h : i < n) :
    v[i].toNat = val v.toList / 2 ^ (64 * i) % 2 ^ 64 := by
  rw [← getElem_toNat v.toList i (by simpa using h), Vector.getElem_toList]

theorem val_toList_eq_of_getElem {n : Nat} (v : Vector Word n) (X : Nat)
    (h : ∀ i (hi : i < n), v[i].toNat = X / 2 ^ (64 * i) % 2 ^ 64) :
    val v.toList = X % 2 ^ (64 * n) := by
  have := val_eq_of_getElem v.toList X (fun i hi => by
    rw [Vector.getElem_toList]; exact h i (by simpa using hi))
  simpa using this

theorem vector_ext_val {n : Nat} {v w : Vector Word n} (h : val v.toList = val w.toList) : v = w :=
  Vector.toList_inj.mp (val_ext (by simp) h)

theorem val_toList_set {n : Nat} (v : Vector Word n) (i : Nat) (x : Word) (h : i < n) :
    val (v.set i x h).toList + 2 ^ (64 * i) * v[i].toNat = val v.toList + 2 ^ (64 * i) * x.toNat := by
  rw [Vector.toList_set, ← Vector.getElem_toList (h := by simpa using h)]
  exact val_set v.toList i x (by simpa using h)

@[simp] theorem val_toList_replicate_zero (n : Nat) : val (Vector.replicate n (0 : Word)).toList = 0 := by
  simp

/-! ## The array operations of the model -/

open Model

@[simp] theorem require_pos {c : Prop} [Decidable c] (h : c) : require c = some ⟨h⟩ := by
  simp [require, h]

@[simp] theorem getElem_span {n : Nat} (a : Vector Word n) (off len : Nat) (h : off + len ≤ n)
    (i : Nat) (hi : i < len) : (span a off len h)[i] = a[off + i] := by
  simp [span]

theorem toList_span {n : Nat} (a : Vector Word n) (off len : Nat) (h : off + len ≤ n) :
    (span a off len h).toList = (a.toList.drop off).take len := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp

theorem val_span {n : Nat} (a : Vector Word n) (off len : Nat) (h : off + len ≤ n) :
    val (span a off len h).toList = val a.toList / 2 ^ (64 * off) % 2 ^ (64 * len) := by
  rw [toList_span, val_take, val_drop]

theorem getElem_setSpan {n m : Nat} (a : Vector Word n) (off : Nat) (w : Vector Word m)
    (h : off + m ≤ n) (i : Nat) (hi : i < n) :
    (setSpan a off w h)[i] = if h' : off ≤ i ∧ i < off + m then w[i - off] else a[i] := by
  simp [setSpan]

theorem toList_setSpan {n m : Nat} (a : Vector Word n) (off : Nat) (w : Vector Word m)
    (h : off + m ≤ n) :
    (setSpan a off w h).toList = a.toList.take off ++ w.toList ++ a.toList.drop (off + m) := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [Vector.getElem_toList, Vector.length_toList] at h1 ⊢
  rw [getElem_setSpan _ _ _ _ _ h1]
  split_ifs with h'
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
    simp [show i - min off n = i - off by omega]
  · by_cases hlt : i < off
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
      simp
    · rw [List.getElem_append_right (by simp; omega)]
      simp [show off + m + (i - (min off n + m)) = i by omega]

theorem val_setSpan {n m : Nat} (a : Vector Word n) (off : Nat) (w : Vector Word m)
    (h : off + m ≤ n) :
    val (setSpan a off w h).toList = val a.toList % 2 ^ (64 * off) + 2 ^ (64 * off) * val w.toList
      + 2 ^ (64 * (off + m)) * (val a.toList / 2 ^ (64 * (off + m))) := by
  rw [toList_setSpan, val_append, val_append, val_take, val_drop]
  simp only [List.length_take, Vector.length_toList, List.length_append, Nat.min_eq_left (by omega : off ≤ n)]

theorem copy_eq_setSpan {m n : Nat} (src : Vector Word m) (dst : Vector Word n) (h : m ≤ n) :
    copy src dst h = setSpan dst 0 src := rfl

@[simp] theorem getElem_resize {m : Nat} (n : Nat) (v : Vector Word m) (i : Nat) (hi : i < n) :
    (resize n v)[i] = if h : i < m then v[i] else 0 := by
  simp [resize]

theorem val_resize {m : Nat} (n : Nat) (v : Vector Word m) :
    val (resize n v).toList = val v.toList % 2 ^ (64 * n) := by
  apply val_toList_eq_of_getElem
  intro i hi
  rw [getElem_resize]
  split_ifs with h
  · exact getElem_toNat' _ _ h
  · have h1 := val_toList_lt v
    have h2 : 2 ^ (64 * m) ≤ 2 ^ (64 * i) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [Nat.div_eq_of_lt (lt_of_lt_of_le h1 h2)]

/-! ## The loop rules -/

/-- The loop rule for `for h : a in l do` in `Id`: an invariant `I k b` after `k` iterations. -/
theorem forIn'_inv_id {α β : Type} (l : List α) (init : β)
    (f : (a : α) → a ∈ l → β → Id (ForInStep β)) (I : Nat → β → Prop) (h0 : I 0 init)
    (hstep : ∀ k b (hk : k < l.length), I k b →
      ∃ b', f l[k] (List.getElem_mem hk) b = .yield b' ∧ I (k + 1) b') :
    I l.length (Id.run (forIn' l init f)) := by
  induction l generalizing init I with
  | nil => simpa using h0
  | cons a as ih =>
    obtain ⟨b', hf, hI⟩ := hstep 0 init (by simp) h0
    rw [List.forIn'_cons]
    simp only [List.getElem_cons_zero] at hf
    simp only [Id.run, hf]
    exact ih (f := fun a' m b => f a' (List.mem_cons_of_mem a m) b) (init := b')
      (I := fun k b => I (k + 1) b) hI
      (fun k b hk hI => hstep (k + 1) b (by simpa using hk) hI)

/-- The loop rule for `for h : i in lo...<hi do` in `Id`, followed by `k`. -/
theorem forIn'_rco_id {β γ : Type} {lo hi : Nat} {init : β}
    {f : (i : Nat) → i ∈ (lo...<hi) → β → Id (ForInStep β)} {k : β → Id γ} {P : γ → Prop}
    (I : Nat → β → Prop) (h0 : I 0 init)
    (hstep : ∀ j b, lo + j < hi → ∀ hm : lo + j ∈ (lo...<hi), I j b →
      ∃ b', f (lo + j) hm b = .yield b' ∧ I (j + 1) b')
    (hk : ∀ b, I (hi - lo) b → P (Id.run (k b))) :
    P (Id.run (forIn' (lo...<hi) init f >>= k)) := by
  rw [Std.Rco.forIn'_eq_forIn'_toList]
  have h := forIn'_inv_id (lo...<hi).toList init
    (fun a ha acc => f a (Std.Rco.mem_toList_iff_mem.mp ha) acc) I h0 (fun j b hj hI => by
      simp only [Nat.length_toList_rco] at hj
      have e : (lo...<hi).toList[j] = lo + j := Nat.getElem_toList_rco _
      simp only [e]
      exact hstep j b (by omega) _ hI)
  simp only [Nat.length_toList_rco] at h
  exact hk _ h

/-- The loop rule for `for h : i in 0...<hi do` in `Id`, followed by `k`. -/
theorem forIn'_rco0_id {β γ : Type} {hi : Nat} {init : β}
    {f : (i : Nat) → i ∈ (0...<hi) → β → Id (ForInStep β)} {k : β → Id γ} {P : γ → Prop}
    (I : Nat → β → Prop) (h0 : I 0 init)
    (hstep : ∀ j b, j < hi → ∀ hm : j ∈ (0...<hi), I j b →
      ∃ b', f j hm b = .yield b' ∧ I (j + 1) b')
    (hk : ∀ b, I hi b → P (Id.run (k b))) :
    P (Id.run (forIn' (0...<hi) init f >>= k)) := by
  rw [Std.Rco.forIn'_eq_forIn'_toList]
  have h := forIn'_inv_id (0...<hi).toList init
    (fun a ha acc => f a (Std.Rco.mem_toList_iff_mem.mp ha) acc) I h0 (fun j b hj hI => by
      simp only [Nat.length_toList_rco] at hj
      have e : (0...<hi).toList[j] = j := by simp
      simp only [e]
      exact hstep j b (by omega) _ hI)
  simp only [Nat.length_toList_rco, Nat.sub_zero] at h
  exact hk _ h

/-- The loop rule for `for h : a in l do` in `Option`. -/
theorem forIn'_inv_opt {α β : Type} (l : List α) (init : β)
    (f : (a : α) → a ∈ l → β → Option (ForInStep β)) (I : Nat → β → Prop) (h0 : I 0 init)
    (hstep : ∀ k b (hk : k < l.length), I k b →
      ∃ b', f l[k] (List.getElem_mem hk) b = some (.yield b') ∧ I (k + 1) b') :
    ∃ b, forIn' l init f = some b ∧ I l.length b := by
  induction l generalizing init I with
  | nil => exact ⟨init, by simp, by simpa using h0⟩
  | cons a as ih =>
    obtain ⟨b', hf, hI⟩ := hstep 0 init (by simp) h0
    rw [List.forIn'_cons]
    simp only [List.getElem_cons_zero] at hf
    obtain ⟨b'', h1, h2⟩ := ih (f := fun a' m b => f a' (List.mem_cons_of_mem a m) b) (init := b')
      (I := fun k b => I (k + 1) b) hI
      (fun k b hk hI => hstep (k + 1) b (by simpa using hk) hI)
    exact ⟨b'', by simp [hf, h1], by simpa using h2⟩

/-- The loop rule for `for h : i in lo...<hi do` in `Option`, followed by `k`. -/
theorem forIn'_rco_opt {β γ : Type} {lo hi : Nat} {init : β}
    {f : (i : Nat) → i ∈ (lo...<hi) → β → Option (ForInStep β)} {k : β → Option γ}
    {P : γ → Prop} (I : Nat → β → Prop) (h0 : I 0 init)
    (hstep : ∀ j b, lo + j < hi → ∀ hm : lo + j ∈ (lo...<hi), I j b →
      ∃ b', f (lo + j) hm b = some (.yield b') ∧ I (j + 1) b')
    (hk : ∀ b, I (hi - lo) b → ∃ v, k b = some v ∧ P v) :
    ∃ v, (forIn' (lo...<hi) init f >>= k) = some v ∧ P v := by
  rw [Std.Rco.forIn'_eq_forIn'_toList]
  obtain ⟨b, hb, hI⟩ := forIn'_inv_opt (lo...<hi).toList init
    (fun a ha acc => f a (Std.Rco.mem_toList_iff_mem.mp ha) acc) I h0 (fun j b hj hI => by
      simp only [Nat.length_toList_rco] at hj
      have e : (lo...<hi).toList[j] = lo + j := Nat.getElem_toList_rco _
      simp only [e]
      exact hstep j b (by omega) _ hI)
  simp only [Nat.length_toList_rco] at hI
  obtain ⟨v, hv, hP⟩ := hk b hI
  exact ⟨v, by simp [hb, hv], hP⟩

/-- The loop rule for `for h : i in 0...<hi do` in `Option`, followed by `k`. -/
theorem forIn'_rco0_opt {β γ : Type} {hi : Nat} {init : β}
    {f : (i : Nat) → i ∈ (0...<hi) → β → Option (ForInStep β)} {k : β → Option γ}
    {P : γ → Prop} (I : Nat → β → Prop) (h0 : I 0 init)
    (hstep : ∀ j b, j < hi → ∀ hm : j ∈ (0...<hi), I j b →
      ∃ b', f j hm b = some (.yield b') ∧ I (j + 1) b')
    (hk : ∀ b, I hi b → ∃ v, k b = some v ∧ P v) :
    ∃ v, (forIn' (0...<hi) init f >>= k) = some v ∧ P v := by
  rw [Std.Rco.forIn'_eq_forIn'_toList]
  obtain ⟨b, hb, hI⟩ := forIn'_inv_opt (0...<hi).toList init
    (fun a ha acc => f a (Std.Rco.mem_toList_iff_mem.mp ha) acc) I h0 (fun j b hj hI => by
      simp only [Nat.length_toList_rco] at hj
      have e : (0...<hi).toList[j] = j := by simp
      simp only [e]
      exact hstep j b (by omega) _ hI)
  simp only [Nat.length_toList_rco, Nat.sub_zero] at hI
  obtain ⟨v, hv, hP⟩ := hk b hI
  exact ⟨v, by simp [hb, hv], hP⟩

end Intx

namespace Intx

/-! ## Rules for `Option` code -/

/-- `X >>= K` returns a value with `R` if `X` returns one with `Q` and `K` maps those to `R`. -/
theorem ex_bind {α β : Type} {X : Option α} {K : α → Option β} (Q : α → Prop) {R : β → Prop}
    (hX : ∃ v, X = some v ∧ Q v) (hK : ∀ v, Q v → ∃ w, K v = some w ∧ R w) :
    ∃ w, X.bind K = some w ∧ R w := by
  obtain ⟨v, hv, hQ⟩ := hX
  obtain ⟨w, hw, hR⟩ := hK v hQ
  exact ⟨w, by simp [hv, hw], hR⟩

/-- `ex_bind` for a loop body that yields. -/
theorem ex_bind_yield {α β : Type} {X : Option α} {K : α → Option (ForInStep β)} (Q : α → Prop)
    {R : β → Prop} (hX : ∃ v, X = some v ∧ Q v)
    (hK : ∀ v, Q v → ∃ w, K v = some (.yield w) ∧ R w) :
    ∃ w, X.bind K = some (.yield w) ∧ R w := by
  obtain ⟨v, hv, hQ⟩ := hX
  obtain ⟨w, hw, hR⟩ := hK v hQ
  exact ⟨w, by simp [hv, hw], hR⟩

/-- The loop rule for `for h : i in lo...<hi do` in `Option`. -/
theorem forIn'_rco_ex {β : Type} {lo hi : Nat} {init : β}
    {f : (i : Nat) → i ∈ (lo...<hi) → β → Option (ForInStep β)} (I : Nat → β → Prop)
    (h0 : I 0 init)
    (hstep : ∀ j b, lo + j < hi → ∀ hm : lo + j ∈ (lo...<hi), I j b →
      ∃ b', f (lo + j) hm b = some (.yield b') ∧ I (j + 1) b') :
    ∃ b, forIn' (lo...<hi) init f = some b ∧ I (hi - lo) b := by
  obtain ⟨v, hv, hP⟩ := forIn'_rco_opt (k := fun b => some b) (P := I (hi - lo)) I h0 hstep
    (fun b hb => ⟨b, rfl, hb⟩)
  exact ⟨v, by simpa using hv, hP⟩

/-- The loop rule for `for h : i in 0...<hi do` in `Option`. -/
theorem forIn'_rco0_ex {β : Type} {hi : Nat} {init : β}
    {f : (i : Nat) → i ∈ (0...<hi) → β → Option (ForInStep β)} (I : Nat → β → Prop)
    (h0 : I 0 init)
    (hstep : ∀ j b, j < hi → ∀ hm : j ∈ (0...<hi), I j b →
      ∃ b', f j hm b = some (.yield b') ∧ I (j + 1) b') :
    ∃ b, forIn' (0...<hi) init f = some b ∧ I hi b := by
  obtain ⟨v, hv, hP⟩ := forIn'_rco0_opt (k := fun b => some b) (P := I hi) I h0 hstep
    (fun b hb => ⟨b, rfl, hb⟩)
  exact ⟨v, by simpa using hv, hP⟩

end Intx

namespace Intx

/-- A weaker postcondition. -/
theorem ex_mono {α : Type} {X : Option α} {Q Q' : α → Prop} (hX : ∃ v, X = some v ∧ Q v)
    (h : ∀ v, Q v → Q' v) : ∃ v, X = some v ∧ Q' v := by
  obtain ⟨v, hv, hQ⟩ := hX
  exact ⟨v, hv, h v hQ⟩

end Intx
