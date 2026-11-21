import AffineGuard.FiveShells

/-! The intermediate five-row quotient identifies the three common parameter translations. -/

namespace AffineGuard.Census
open Finset Ternary
open OrbitGuard (Gate vertex)
open OrbitGuard.Examples (five)

/-- Replace the parameter a by a+t in every row, with its slope unchanged. -/
def shift (s : Model) (t : F) : Model :=
  ⟨s.u, s.w, fun i => s.b i + t * s.w i 0⟩

private theorem shift_zero (s : Model) : shift s 0 = s := by
  apply HZ.State.ext
  · rfl
  · rfl
  funext i
  simp [shift]

private theorem shift_add (s : Model) (t u : F) : shift (shift s t) u = shift s (t+u) := by
  apply HZ.State.ext
  · rfl
  · rfl
  funext i
  simp [shift, add_mul, add_assoc]

private theorem shift_frame (q : OrbitGuard.Frame (Fin 5)) (s : Model) (t : F) :
    shift (q.act s) t = q.act (shift s t) := by
  apply HZ.State.ext
  · rfl
  · rfl
  funext i
  simp [shift, OrbitGuard.Frame.act, HZ.State.scale, HZ.State.permute, mul_add, mul_left_comm]

private theorem shift_gate (g : Gate (Fin 5)) (s : Model) (t : F) :
    shift (g.act s) t = g.act (shift s t) := by
  apply HZ.State.ext
  · rfl
  · rfl
  funext i
  by_cases hi : i = g.src
  · subst i
    simp [shift, OrbitGuard.Gate.act, HZ.State.addRow]
    ring
  · simp [shift, OrbitGuard.Gate.act, HZ.State.addRow, hi]

abbrev TranslationVertex := Finset (OrbitGuard.Vertex (Fin 5) (Fin 1))

/-- The orbit of the complete-row vertex under the three common translations. -/
def translationClass (s : Model) : TranslationVertex :=
  (univ : Finset F).image fun t => vertex (shift s t)

private theorem mem_class (s : Model) (v) :
    v ∈ translationClass s ↔ ∃ t, vertex (shift s t) = v := by
  simp [translationClass]

theorem translationClass_of_vertex {s r : Model} (h : vertex s = vertex r) :
    translationClass s = translationClass r := by
  obtain ⟨q,rfl⟩ := (OrbitGuard.vertex_eq_iff_frame s r).mp h
  exact Finset.image_congr fun t _ => by rw [shift_frame, OrbitGuard.vertex_frame]

private theorem class_shift (s : Model) (t : F) : translationClass (shift s t) = translationClass s := by
  ext v
  rw [mem_class, mem_class]
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨t+u, by rw [shift_add]⟩
  · rintro ⟨u,rfl⟩
    exact ⟨u-t, by rw [shift_add, add_sub_cancel]⟩

private theorem class_eq_iff (s r : Model) :
    translationClass s = translationClass r ↔ ∃ t, vertex (shift s t) = vertex r := by
  constructor
  · intro h
    apply (mem_class s _).mp
    rw [h]
    exact (mem_class r _).mpr ⟨0, by rw [shift_zero]⟩
  · rintro ⟨t,h⟩
    exact (class_shift s t).symm.trans (translationClass_of_vertex h)

/-- Precisely a common translation followed by a row permutation and independent row signs. -/
theorem translationClass_iff (s r : Model) :
    translationClass s = translationClass r ↔
      ∃ (t : F) (q : OrbitGuard.Frame (Fin 5)), q.act (shift s t) = r := by
  simp only [class_eq_iff, OrbitGuard.vertex_eq_iff_frame]

private def translationVariants (s : Model) : Finset Code :=
  (univ : Finset F).image fun t => rowKey (shift s t)

private theorem mem_variants (s : Model) (c : Code) :
    c ∈ translationVariants s ↔ ∃ r : Model, translationClass s = translationClass r ∧ rowKey r = c := by
  constructor
  · intro h
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp h
    exact ⟨_,(class_shift s t).symm,rfl⟩
  · rintro ⟨r,h,rfl⟩
    obtain ⟨t,ht⟩ := (class_eq_iff s r).mp h
    exact Finset.mem_image.mpr ⟨t,mem_univ _,(rowKey_iff _ _).mpr ht⟩

private theorem translationVariants_ne (s : Model) : (translationVariants s).Nonempty :=
  ⟨_,(mem_variants s _).mpr ⟨s,rfl,rfl⟩⟩

/-- Lexicographically least complete-row code over the three parameter origins. -/
def translationKey (s : Model) : Code := (translationVariants s).min' (translationVariants_ne s)

private theorem key_mem (s : Model) :
    ∃ r : Model, translationClass s = translationClass r ∧ rowKey r = translationKey s :=
  (mem_variants s _).mp (Finset.min'_mem _ (translationVariants_ne s))

theorem translationKey_iff (s r : Model) :
    translationKey s = translationKey r ↔ translationClass s = translationClass r := by
  constructor
  · intro h
    obtain ⟨a,ha,ea⟩ := key_mem s
    obtain ⟨b,hb,eb⟩ := key_mem r
    exact ha.trans ((translationClass_of_vertex ((rowKey_iff a b).mp (ea.trans (h.trans eb.symm)))).trans hb.symm)
  · intro h
    have hv : translationVariants s = translationVariants r := by ext c; rw [mem_variants,mem_variants,h]
    simp only [translationKey,hv]

private theorem translationKey_read (s : Model) :
    translationKey (readCode (translationKey s)) = translationKey s := by
  obtain ⟨r,hr,he⟩ := key_mem s
  apply (translationKey_iff _ _).mpr
  rw [← he]
  exact (translationClass_of_vertex (vertex_read r)).trans hr.symm

def TranslationEdge (x y : TranslationVertex) : Prop :=
  ∃ (s : Model) (g : Gate (Fin 5)), translationClass s = x ∧ translationClass (g.act s) = y

/-- An edge can be taken from each representative with just one paid addition. -/
theorem translation_edge_from (s : Model) (y : TranslationVertex) :
    TranslationEdge (translationClass s) y ↔ ∃ g : Gate (Fin 5), translationClass (g.act s) = y := by
  constructor
  · rintro ⟨r,g,h,hy⟩
    obtain ⟨t,q,rfl⟩ := (translationClass_iff s r).mp h.symm
    refine ⟨g.transport q, ?_⟩
    rw [g.act_frame] at hy
    have hf := translationClass_of_vertex (OrbitGuard.vertex_frame q ((g.transport q).act (shift s t)))
    rwa [hf, ← shift_gate, class_shift] at hy
  · rintro ⟨g,h⟩
    exact ⟨s,g,rfl,h⟩

inductive TranslationWalk : TranslationVertex → ℕ → TranslationVertex → Prop
  | nil (x) : TranslationWalk x 0 x
  | cons {x y z n} : TranslationEdge x y → TranslationWalk y n z → TranslationWalk x (1+n) z

theorem translation_project_run {s r : Model} {n} (h : HZ.Run s n r) :
    TranslationWalk (translationClass s) n (translationClass r) := by
  induction h with
  | nil => exact .nil _
  | cons s op _ ih =>
    cases op with
    | add i j c hij hc =>
      let g : Gate (Fin 5) := ⟨i,j,c,hij,hc⟩
      exact .cons ((translation_edge_from s _).mpr ⟨g,rfl⟩) ih
    | permute e =>
      simpa [HZ.Operation.cost,HZ.Operation.apply,translationClass_of_vertex (OrbitGuard.vertex_permute s e)] using ih
    | scale c hc =>
      simpa [HZ.Operation.cost,HZ.Operation.apply,translationClass_of_vertex (OrbitGuard.vertex_scale s c hc)] using ih

theorem translation_lift_walk {x y : TranslationVertex} {n} (w : TranslationWalk x n y)
    (s : Model) (hs : translationClass s = x) : ∃ r : Model, HZ.Run s n r ∧ translationClass r = y := by
  induction w generalizing s with
  | nil => exact ⟨s,.nil _,hs⟩
  | cons e _ ih =>
    rw [← hs] at e
    obtain ⟨g,hg⟩ := (translation_edge_from s _).mp e
    obtain ⟨r,hr,hy⟩ := ih (g.act s) hg
    exact ⟨r,(g.run s).trans hr,hy⟩

def translationBall (n : ℕ) : Finset Code :=
  (rowBall n).image fun c => translationKey (readCode c)

theorem translationBall_spec (n : ℕ) (c : Code) :
    c ∈ translationBall n ↔ ∃ s : Model, translationKey s = c ∧
      Within (TranslationWalk (translationClass five)) n (translationClass s) := by
  constructor
  · intro h
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨s,rfl,j,hj,w⟩ := (rowBall_spec _ _).mp hp
    have wp := translation_project_run ((OrbitGuard.walk_iff_run five s j).mp w)
    exact ⟨_,rfl,j,hj,(translationClass_of_vertex (vertex_read s)).symm ▸ wp⟩
  · rintro ⟨s,rfl,j,hj,w⟩
    obtain ⟨r,hr,he⟩ := translation_lift_walk w five rfl
    refine Finset.mem_image.mpr ⟨rowKey r,(rowBall_spec _ _).mpr ⟨r,rfl,j,hj,OrbitGuard.project_run hr⟩,?_⟩
    exact (translationKey_iff _ _).mpr ((translationClass_of_vertex (vertex_read r)).trans he)

def TranslationNearest (x : TranslationVertex) (n : ℕ) (y : TranslationVertex) : Prop :=
  TranslationWalk x n y ∧ ∀ j, TranslationWalk x j y → n ≤ j

theorem translation_shell_card (n : ℕ) :
    {v | TranslationNearest (translationClass five) (n+1) v}.ncard =
      (translationBall (n+1) \ translationBall n).card :=
  count_shell translationClass translationKey translationKey_iff translationKey_read
    (TranslationWalk (translationClass five))
    (fun _ _ w => by obtain ⟨s,_,h⟩ := translation_lift_walk w five rfl; exact ⟨s,h⟩)
    translationBall translationBall_spec n

end AffineGuard.Census
