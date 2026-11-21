import AffineGuard.FiveCertificate
import AffineGuard.FiveTranslation

/-! Kernel-checked numerical witnesses for the three distance-three spheres. -/

namespace AffineGuard.Census
open Finset
open OrbitGuard.Examples (five)

set_option maxRecDepth 8192

set_option maxHeartbeats 4000000 in
private theorem allMoves (i : Fin 47) : MoveCheck rowAt edgesAt i := by
  fin_cases i <;> unfold MoveCheck <;> decide +kernel

set_option maxHeartbeats 4000000 in
private theorem allImages (i : Fin 213) : AffineCheck rowAt affineAt i := by
  fin_cases i <;> unfold AffineCheck <;> decide +kernel

private theorem movesBelow {k : ℕ} (hk : k ≤ 47) (i : Fin k) : MoveCheck rowAt edgesAt i :=
  allMoves ⟨i,lt_of_lt_of_le i.isLt hk⟩

private theorem imagesBelow {k : ℕ} (hk : k ≤ 213) (i : Fin k) : AffineCheck rowAt affineAt i :=
  allImages ⟨i,lt_of_lt_of_le i.isLt hk⟩

private theorem row0 : rowBall 0 = entries rowAt 1 := by decide

private theorem row1 : rowBall 1 = entries rowAt 7 :=
  expand_table rowAt edgesAt parentAt (n := 0) (k := 1) (l := 7) row0 (by decide)
    (movesBelow (by decide)) (by unfold Coverage; decide +kernel)

private theorem row2 : rowBall 2 = entries rowAt 47 :=
  expand_table rowAt edgesAt parentAt (n := 1) (k := 7) (l := 47) row1 (by decide)
    (movesBelow (by decide)) (by unfold Coverage; decide +kernel)

private theorem row3 : rowBall 3 = entries rowAt 213 :=
  expand_table rowAt edgesAt parentAt (n := 2) (k := 47) (l := 213) row2 (by decide)
    allMoves (by unfold Coverage; decide +kernel)

private theorem aff2 : affineBall 2 = entries affineAt 47 :=
  project_table rowAt affineAt (n := 2) (k := 47) row2 (imagesBelow (by decide))

private theorem aff3 : affineBall 3 = entries affineAt 213 :=
  project_table rowAt affineAt (n := 3) (k := 213) row3 allImages

/-- Closed balls through two and three paid steps, before and after the affine quotient. -/
theorem five_ball_counts : (rowBall 2).card = 47 ∧ (rowBall 3).card = 213 ∧
    (affineBall 2).card = 42 ∧ (affineBall 3).card = 122 := by
  rw [row2,row3,aff2,aff3]
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

private theorem row_mono (n : ℕ) : rowBall n ⊆ rowBall (n+1) := by
  rw [rowBall]
  exact Finset.subset_union_left

/-- Counts of the actual graph vertices at minimum paid distance three from the five-row input. -/
theorem five_three_shells :
    {v | OrbitGuard.Nearest (OrbitGuard.vertex five) 3 v}.ncard = 166 ∧
    {v | AffineGuard.Nearest (key five) 3 v}.ncard = 80 := by
  obtain ⟨r2,r3,a2,a3⟩ := five_ball_counts
  constructor
  · rw [row_shell_card 2,Finset.card_sdiff_of_subset (row_mono 2),r2,r3]
  · have ha : affineBall 2 ⊆ affineBall 3 := Finset.image_mono (fun c => affineKey (readCode c)) (row_mono 2)
    rw [affine_shell_card 2,Finset.card_sdiff_of_subset ha,a2,a3]

private def translationAt (i : ℕ) : Code := Table.translations[i]?.getD []

private def TranslationCheck (i : ℕ) : Prop :=
  translationKey (readCode (rowAt i)) = translationAt i

set_option maxHeartbeats 4000000 in
private theorem allTranslations (i : Fin 213) : TranslationCheck i := by
  fin_cases i <;> unfold TranslationCheck <;> decide +kernel

private theorem translation_table {n k : ℕ} (h : rowBall n = entries rowAt k) (hk : k ≤ 213) :
    translationBall n = entries translationAt k :=
  map_entries rowAt translationAt (fun c => translationKey (readCode c)) h
    (fun i => allTranslations ⟨i,lt_of_lt_of_le i.isLt hk⟩)

theorem five_translation_ball_counts :
    (translationBall 2).card = 47 ∧ (translationBall 3).card = 173 := by
  rw [translation_table row2 (by decide),translation_table row3 (by decide)]
  exact ⟨by decide +kernel,by decide +kernel⟩

theorem five_translation_shell :
    {v | TranslationNearest (translationClass five) 3 v}.ncard = 126 := by
  have hm : translationBall 2 ⊆ translationBall 3 :=
    Finset.image_mono (fun c => translationKey (readCode c)) (row_mono 2)
  obtain ⟨h₂,h₃⟩ := five_translation_ball_counts
  rw [translation_shell_card 2,Finset.card_sdiff_of_subset hm,h₂,h₃]

/-- Third spheres from the same input under complete rows, translations, and the full affine image. -/
theorem five_three_shells_all :
    {v | OrbitGuard.Nearest (OrbitGuard.vertex five) 3 v}.ncard = 166 ∧
    {v | TranslationNearest (translationClass five) 3 v}.ncard = 126 ∧
    {v | AffineGuard.Nearest (key five) 3 v}.ncard = 80 :=
  ⟨five_three_shells.1,five_translation_shell,five_three_shells.2⟩

end AffineGuard.Census
