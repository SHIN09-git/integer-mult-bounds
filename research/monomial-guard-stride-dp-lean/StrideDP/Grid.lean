import CountDP.Address

namespace StrideDP
open CountDP
variable {V : Type*} [DecidableEq V]

/-- Product of the radices of axes strictly before the selected axis. -/
def stride (n : V → ℕ) (w : V) : List V → ℕ
  | [] => 0
  | v :: vs => if w = v then 1 else (n v + 1) * stride n w vs

theorem stride_prefix (n : V → ℕ) (v : V) (xs ys : List V) (h : v ∉ xs) :
    stride n v (xs ++ v :: ys) = slots n xs := by
  induction xs with
  | nil => simp [stride, slots]
  | cons x xs ih =>
    have hx : v ≠ x := fun e => h (List.mem_cons.mpr (.inl e))
    have ht : v ∉ xs := fun hm => h (List.mem_cons_of_mem _ hm)
    simp [stride, slots, hx, ih ht]

private theorem addr_congr (n : V → ℕ) (xs : List V) (a b : Multiset V)
    (h : ∀ x ∈ xs, a.count x = b.count x) : address n xs a = address n xs b := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [address, address, h x List.mem_cons_self, ih (fun w hw => h w (List.mem_cons_of_mem _ hw))]

theorem erase_add_stride (xs : List V) (n : V → ℕ) (m : Multiset V) {w : V}
    (hd : xs.Nodup) (hx : w ∈ xs) (hm : w ∈ m) :
    address n xs (m.erase w) + stride n w xs = address n xs m := by
  induction xs with
  | nil => simp at hx
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := List.nodup_cons.mp hd
    by_cases he : w = v
    · subst w
      have ht := addr_congr n vs (m.erase v) m (fun x hx =>
        Multiset.count_erase_of_ne (fun e : x = v => hv (e ▸ hx)) _)
      have hp := Multiset.count_pos.mpr hm
      simp only [address, stride, if_true, Multiset.count_erase_self, ht]
      omega
    · have ht := ih hvs ((List.mem_cons.mp hx).resolve_left he)
      simp only [address, stride, if_neg he, Multiset.count_erase_of_ne (Ne.symm he)]
      rw [Nat.add_assoc, ← Nat.mul_add, ht]

theorem predecessor_address (xs : List V) (n : V → ℕ) (m : Multiset V) {w : V}
    (hd : xs.Nodup) (hx : w ∈ xs) (hm : w ∈ m) :
    address n xs (m.erase w) = address n xs m - stride n w xs := by
  have := erase_add_stride xs n m hd hx hm
  omega

omit [DecidableEq V] in
theorem unpack_support (xs : List V) (n : V → ℕ) (k : ℕ) {w : V}
    (h : w ∈ unpack n xs k) : w ∈ xs := by
  induction xs generalizing k with
  | nil => simp [unpack] at h
  | cons v vs ih =>
    rcases Multiset.mem_add.mp h with h | h
    · exact List.mem_cons.mpr (.inl (Multiset.eq_of_mem_replicate h))
    · exact List.mem_cons_of_mem _ (ih _ h)

theorem unpack_fits (xs : List V) (n : V → ℕ) (hd : xs.Nodup) (k : ℕ) :
    Fits xs n (unpack n xs k) := by
  refine ⟨fun _ h => unpack_support _ _ _ h, ?_⟩
  induction xs generalizing k with
  | nil => simp
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := List.nodup_cons.mp hd
    have hout : v ∉ unpack n vs (k / (n v + 1)) := fun h => hv (unpack_support _ _ _ h)
    intro w hw
    rcases List.mem_cons.mp hw with he | hw
    · subst w
      simpa [unpack, hout] using Nat.le_of_lt_succ (Nat.mod_lt k (Nat.succ_pos (n v)))
    · have hne : w ≠ v := fun e => hv (e ▸ hw)
      simpa [unpack, Multiset.count_replicate, Ne.symm hne] using ih hvs (k / (n v + 1)) w hw

theorem address_unpack (xs : List V) (n : V → ℕ) (hd : xs.Nodup) {k : ℕ}
    (hk : k < slots n xs) : address n xs (unpack n xs k) = k := by
  induction xs generalizing k with
  | nil => simpa [address, slots] using Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk) |>.symm
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := List.nodup_cons.mp hd
    let b := n v + 1
    have hp : 0 < b := Nat.succ_pos _
    have hq : k / b < slots n vs := (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [slots, b, Nat.mul_comm] using hk)
    let tail := unpack n vs (k / b)
    have hout : v ∉ tail := fun h => hv (unpack_support _ _ _ h)
    have ht : address n vs (Multiset.replicate (k % b) v + tail) = address n vs tail := by
      apply addr_congr
      intro w hw
      have hne : w ≠ v := fun e => hv (e ▸ hw)
      simp [Multiset.count_replicate, Ne.symm hne]
    change (Multiset.replicate (k % b) v + tail).count v + b * address n vs (Multiset.replicate (k % b) v + tail) = k
    rw [ht, show address n vs tail = k / b from ih hvs hq]
    simpa [hout] using Nat.mod_add_div k b

end StrideDP
