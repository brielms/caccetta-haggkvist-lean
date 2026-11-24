import checkpoints.shen_extension.WideLayerReturn
import checkpoints.shen_extension.BypassRepair

/-!
# Layer excess around a root

For a root `u` of a `q`-free graph of minimum out-degree `r`, the punctured
`k`-ball `(ball k).erase u` keeps every row's heads except those in the next
layer. If that layer has `c` labels, the punctured ball has minimum out-degree
at least `r - c`, so a lower-degree host bound applies to it
(`punctured_peel`): `q · t < |(ball k).erase u|` whenever `t + c ≤ r` and degree
`t` has no host at cutoff `q`.
-/

namespace LeanCH.BR.LayerExcess
open Finset BRq2 BRq3 BypassRepair

/-- **Punctured peel.** A punctured `k`-ball whose next layer leaves every row at
least `t` heads, with `NoHost q t`, has more than `q · t` labels. -/
theorem punctured_peel {D : CH.Digraph} {V : Finset ℕ} {q r k u t : ℕ}
    (free : QFree D V q) (hu : u ∈ V) (time : k + 1 ≤ q)
    (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (lower : NoHost q t)
    (loss : t + (ball D V u (k + 1) \ ball D V u k).card ≤ r)
    (live : ((ball D V u k).erase u).Nonempty) :
    q * t < ((ball D V u k).erase u).card := by
  by_contra! small
  have rows := minOut_prefix_erase (d := t) free hu time degree loss
  have sub : (ball D V u k).erase u ⊆ V := (erase_subset _ _).trans ball_subset
  exact lower D _ live small (free.mono_set sub) rows

#print axioms punctured_peel
end LeanCH.BR.LayerExcess
