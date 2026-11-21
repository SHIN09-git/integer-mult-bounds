import AffineGuard.Image

namespace AffineGuard
open Finset Ternary
open OrbitGuard (State Frame Gate)

variable {I D E : Type*} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]

/-- All signed row frames of the labeled affine data. The key type has no parameter index. -/
abbrev Key (I : Type*) := Finset (Data I)

abbrev FrameCode (I : Type*) := Equiv.Perm I × (I → Fˣ)

def decode (c : FrameCode I) : Frame I :=
  ⟨c.1, fun i => (c.2 i : F), fun i => (c.2 i).ne_zero⟩

def encode (q : Frame I) : FrameCode I :=
  (q.perm, fun i => Units.mk0 (q.factor i) (q.nonzero i))

omit [Fintype I] [DecidableEq I] in
theorem decode_encode (q : Frame I) : decode (encode q) = q := by cases q; rfl

def underFrame (q : Frame I) (p : Data I) : Data I :=
  step (.scale q.factor q.nonzero) (step (.permute q.perm) p)

def orbit (p : Data I) : Key I :=
  univ.image fun c : FrameCode I => underFrame (decode c) p

def key (s : State I D) : Key I := orbit (data s)

theorem data_frame (q : Frame I) (s : State I D) :
    data (q.act s) = underFrame q (data s) := by
  change data ((HZ.Operation.scale q.factor q.nonzero).apply ((HZ.Operation.permute q.perm).apply s)) = _
  rw [data_step, data_step]
  rfl

theorem mem_key (s : State I D) (p : Data I) :
    p ∈ key s ↔ ∃ q : Frame I, data (q.act s) = p := by
  simp only [key, orbit, Finset.mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨decode c, data_frame _ _⟩
  · rintro ⟨q, rfl⟩
    exact ⟨encode q, by rw [decode_encode, data_frame]⟩

private theorem mem_key_states (s : State I D) (p : Data I) :
    p ∈ key s ↔ ∃ t : State I D, OrbitGuard.vertex t = OrbitGuard.vertex s ∧ data t = p := by
  rw [mem_key]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.act s, OrbitGuard.vertex_frame q s, rfl⟩
  · rintro ⟨t, h, rfl⟩
    obtain ⟨q, rfl⟩ := (OrbitGuard.vertex_eq_iff_frame s t).mp h.symm
    exact ⟨q, rfl⟩

theorem key_of_vertex {s t : State I D} (h : OrbitGuard.vertex s = OrbitGuard.vertex t) :
    key s = key t := by
  ext p
  rw [mem_key_states, mem_key_states, h]

theorem key_frame (q : Frame I) (s : State I D) : key (q.act s) = key s :=
  key_of_vertex (OrbitGuard.vertex_frame q s)

theorem key_permute (s : State I D) (e : Equiv.Perm I) : key (s.permute e) = key s :=
  key_of_vertex (OrbitGuard.vertex_permute s e)

theorem key_scale (s : State I D) (c : I → F) (hc : ∀ i, c i ≠ 0) :
    key (s.scale c) = key s := key_of_vertex (OrbitGuard.vertex_scale s c hc)

theorem data_mem_key (s : State I D) : data s ∈ key s :=
  (mem_key_states s _).mpr ⟨s, rfl, rfl⟩

theorem key_eq_iff (s : State I D) (t : State I E) :
    key s = key t ↔ ∃ q : Frame I, data (q.act s) = data t := by
  constructor
  · intro h
    exact (mem_key s _).mp (h ▸ data_mem_key t)
  · rintro ⟨q, h⟩
    exact (key_frame q s).symm.trans (congrArg orbit h)

def gateOp (g : Gate I) : HZ.Operation I F := .add g.dst g.src g.coeff g.distinct g.nonzero

theorem gate_key (g : Gate I) (s : State I D) : key (g.act s) = orbit (step (gateOp g) (data s)) :=
  congrArg orbit (data_step (gateOp g) s)

def Edge (x y : Key I) : Prop :=
  ∃ (p : Data I) (g : Gate I), p ∈ x ∧ orbit (step (gateOp g) p) = y

/-- Lift a paid quotient edge from any representative, on that representative's row labels. -/
theorem edge_from (s : State I D) (y : Key I) :
    Edge (key s) y ↔ ∃ g : Gate I, key (g.act s) = y := by
  constructor
  · rintro ⟨p, g, hp, hy⟩
    obtain ⟨q, rfl⟩ := (mem_key s p).mp hp
    have h := (gate_key g (q.act s)).trans hy
    exact ⟨g.transport q, by rw [← key_frame q ((g.transport q).act s), ← g.act_frame]; exact h⟩
  · rintro ⟨g, h⟩
    exact ⟨data s, g, data_mem_key s, (gate_key g s).symm.trans h⟩

/-- Test all proper prefixes in one order against every member of the affine set. -/
def PassIn {m : ℕ} (p : Data I) (e : Fin m ≃ I) : Prop :=
  ∀ k, k < m → ∀ z ∈ p.2, 1 - ∑ i ∈ HZ.prefixSet m k, p.1 (e i) * z (e i) ≠ 0

def WinsData (p : Data I) : Prop := ∃ (m : ℕ) (e : Fin m ≃ I), PassIn p e

omit [DecidableEq I] in
theorem passIn_iff {m : ℕ} (s : State I D) (e : Fin m ≃ I) :
    PassIn (data s) e ↔ HZ.Passes (reindex s e) := by
  constructor
  · intro h k hk a
    rw [HZ.principalMinor_eq]
    exact h k hk _ ((mem_image s _).mpr ⟨a, rfl⟩)
  · intro h k hk z hz
    obtain ⟨a, rfl⟩ := (mem_image s z).mp hz
    simpa only [HZ.principalMinor_eq] using h k hk a

omit [DecidableEq I] in
theorem winsData_iff (s : State I D) : WinsData (data s) ↔ FullGuard s :=
  exists_congr fun _ => exists_congr fun e => passIn_iff s e

omit [Fintype I] [DecidableEq D] in
private theorem prod_frame (q : Frame I) (s : State I D) (a : D → F) (i : I) :
    (q.act s).u i * HZ.familyRow (q.act s) a i = s.u (q.perm i) * HZ.familyRow s a (q.perm i) := by
  have hz := congrFun (family_step (HZ.Operation.scale q.factor q.nonzero) (s.permute q.perm) a) i
  change HZ.familyRow (q.act s) a i = (q.factor i)⁻¹ * HZ.familyRow s a (q.perm i) at hz
  rw [hz]
  change (q.factor i * s.u (q.perm i)) * _ = _
  field_simp [q.nonzero i]

omit [Fintype I] [DecidableEq D] in
private theorem passes_frame_order {m : ℕ} (q : Frame I) (s : State I D) (e : Fin m ≃ I) :
    HZ.Passes (reindex (q.act s) e) ↔ HZ.Passes (reindex s (e.trans q.perm)) := by
  have minor (k : ℕ) (a : D → F) :
      HZ.principalMinor (reindex (q.act s) e) a (HZ.prefixSet m k) =
      HZ.principalMinor (reindex s (e.trans q.perm)) a (HZ.prefixSet m k) := by
    rw [HZ.principalMinor_eq, HZ.principalMinor_eq]
    congr 1
    exact Finset.sum_congr rfl fun i _ => prod_frame q s a (e i)
  exact ⟨fun h k hk a => minor k a ▸ h k hk a, fun h k hk a => (minor k a).symm ▸ h k hk a⟩

omit [Fintype I] [DecidableEq D] in
theorem guard_frame (q : Frame I) (s : State I D) : FullGuard (q.act s) ↔ FullGuard s := by
  constructor
  · rintro ⟨m,e,h⟩
    exact ⟨m,e.trans q.perm,(passes_frame_order q s e).mp h⟩
  · rintro ⟨m,e,h⟩
    refine ⟨m,e.trans q.perm.symm,(passes_frame_order q s _).mpr ?_⟩
    have he : (e.trans q.perm.symm).trans q.perm = e := by ext i; simp
    rwa [he]

theorem guard_key {s : State I D} {t : State I E} (h : key s = key t) : FullGuard s ↔ FullGuard t := by
  obtain ⟨q, hq⟩ := (key_eq_iff s t).mp h
  exact (guard_frame q s).symm.trans (guard_congr hq)

def Winning (x : Key I) : Prop := ∃ p ∈ x, WinsData p

theorem winning_key (s : State I D) : Winning (key s) ↔ FullGuard s := by
  constructor
  · rintro ⟨p,hp,hw⟩
    obtain ⟨q,rfl⟩ := (mem_key s p).mp hp
    exact (guard_frame q s).mp ((winsData_iff _).mp hw)
  · intro h
    exact ⟨_, data_mem_key s, (winsData_iff s).mpr h⟩

end AffineGuard
