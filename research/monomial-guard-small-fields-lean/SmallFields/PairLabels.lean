import SmallFields.Labels
import SmallFields.Inverse
import Mathlib.Data.Fintype.BigOperators

namespace SmallFields
open Finset
variable {I V : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V]

/-- The two new labels are distinct constructors, even if x = -x. -/
def attachPair (y : I → V) (x : V) : I ⊕ Bool → V :=
  Sum.elim y (fun sign => if sign then x else -x)

theorem input_attachPair (y : I → V) (x : V) (hx : x ≠ 0) :
    input (attachPair y x) = pair x + input y := by
  classical
  rw [input_singletons,input_singletons,Fintype.sum_sum_type,Fintype.sum_bool]
  simp [attachPair,hx,pair,Multiset.add_comm]

theorem blockCount_attachPair (y : I → V) (hs : ∑ i, y i = 0) (x : V) (hx : x ≠ 0) :
    HZ.blockCount (attachPair y x) = HZ.blockCount y+1 := by
  have ht : ∑ i, attachPair y x i = 0 := by
    rw [Fintype.sum_sum_type,Fintype.sum_bool]
    simpa [attachPair] using hs
  rw [blockCount_eq_Z _ ht,blockCount_eq_Z _ hs,input_attachPair _ _ hx]
  exact Z_add_inverse _ ((input_sum y).trans hs) _ hx

end SmallFields
