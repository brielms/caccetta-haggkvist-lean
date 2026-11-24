import checkpoints.shen_extension.BankReachTransfer
import checkpoints.shen_extension.ShellCycleSupply

namespace LeanCH.BR.BankReachTransfer
open Finset BRq2 BRq3 BR45 BRsGen

/-- A marked row inside a prefix with no sink must spend part of its reachable
space inside that prefix. If it also covers an entire shell of another
root, the rest of that root's layers fit into the remaining space. -/
theorem prefix_return_size {D V P u a q j d k} (free : QFree D V q)
    (uv : u∈V) (am : a∈P) (initial : P⊆ball D V u j)
    (internal : ∀v∈P,1≤(outN D P v).card) (time : d+k+1≤q)
    (seen : ball D V u (j+1)\ball D V u j⊆ball D V a d) :
    d+k+1+((ball D V u (j+1+k)).card-(ball D V u j).card)≤(ball D V a (d+k)).card := by
  have pv : P⊆V := fun _ h=>ball_subset (initial h)
  have inner := ball_one_growth (free.mono_set pv) internal am (d+k) time
  have cap := count_with_prefix (j:=j) (k:=k) uv (A:=ball D P a (d+k))
    (fun _ h=>initial (ball_subset h)) (ShellCycleSupply.lift_ball pv) seen
  omega

#print axioms prefix_return_size
end LeanCH.BR.BankReachTransfer
