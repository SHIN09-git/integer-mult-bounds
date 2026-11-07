import SmallFields.Formulas
import Mathlib.Data.List.FinRange

namespace SmallFields
open Finset CountDP
variable {I V : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [DecidableEq V]

omit [DecidableEq I] in
/-- Zero rows may be counted in the raw histogram; positive-residue counts agree. -/
theorem input_count (y : I → V) {v : V} (hv : v ≠ 0) :
    (input y).count v = (histogram y univ).count v := by
  have e : input y = (histogram y univ).filter (fun z => z ≠ 0) := by
    unfold input histogram HZ.active
    rw [Finset.filter_val,Multiset.filter_map]
    apply congrArg (Multiset.map y)
    have same (p : I → Prop) (first second : DecidablePred p) (s : Multiset I) :
        @Multiset.filter I p first s = @Multiset.filter I p second s := by rw [Subsingleton.elim first second]
    exact same _ _ _ _
  rw [e,Multiset.count_filter_of_pos (p := fun z : V => z ≠ 0) hv]

theorem blockCount_three (y : I → ZMod 3) (hs : ∑ i, y i = 0) :
    let m := histogram y univ
    HZ.blockCount y = formula3 (m.count 1) (m.count 2) := by
  rw [blockCount_eq_Z y hs,Z_three _ (zero_notMem_input y) ((input_sum y).trans hs)]
  rw [input_count y (by decide : (1 : ZMod 3) ≠ 0),input_count y (by decide : (2 : ZMod 3) ≠ 0)]

theorem blockCount_five (y : I → ZMod 5) (hs : ∑ i, y i = 0) :
    let m := histogram y univ
    HZ.blockCount y = formula5 (m.count 1) (m.count 2) (m.count 3) (m.count 4) := by
  rw [blockCount_eq_Z y hs,Z_five _ (zero_notMem_input y) ((input_sum y).trans hs)]
  rw [input_count y (by decide : (1 : ZMod 5) ≠ 0),input_count y (by decide : (2 : ZMod 5) ≠ 0),
      input_count y (by decide : (3 : ZMod 5) ≠ 0),input_count y (by decide : (4 : ZMod 5) ≠ 0)]

/-- Executable entry points. List positions are the original row identities. -/
def direct3 (xs : List (ZMod 3)) := formula3 (xs.count 1) (xs.count 2)
def direct5 (xs : List (ZMod 5)) := formula5 (xs.count 1) (xs.count 2) (xs.count 3) (xs.count 4)

theorem get_histogram {F : Type*} (xs : List F) :
    histogram xs.get univ = (xs : Multiset F) := by
  rw [← List.toFinset_finRange xs.length,histogram,List.toFinset_val,
      List.dedup_eq_self.mpr (List.nodup_finRange _),Multiset.map_coe,List.finRange_map_get]

theorem direct3_correct (xs : List (ZMod 3)) (hs : xs.sum = 0) : direct3 xs = HZ.blockCount xs.get := by
  have hz := (histogram_sum xs.get univ).symm
  rw [get_histogram] at hz
  have h := blockCount_three xs.get (hz.trans hs)
  simpa only [get_histogram,Multiset.coe_count,direct3] using h.symm

theorem direct5_correct (xs : List (ZMod 5)) (hs : xs.sum = 0) : direct5 xs = HZ.blockCount xs.get := by
  have hz := (histogram_sum xs.get univ).symm
  rw [get_histogram] at hz
  have h := blockCount_five xs.get (hz.trans hs)
  simpa only [get_histogram,Multiset.coe_count,direct5] using h.symm

end SmallFields
