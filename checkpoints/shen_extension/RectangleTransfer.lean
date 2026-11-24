import checkpoints.shen_extension.ContainerTransfer
import checkpoints.shen_extension.FourthStrip

namespace LeanCH.BR.ShenRectangleTransfer
open BRq2 BRq3 BR45 ShenFirstStrip
open DotTwoPassShellTransport (fullColumns full_bank_avoids)
open Classical

/-- For any cutoff and adjacent radii, a hypothetical small next ball forces
a shared container. A and B are the two preceding ball floors, c=B-A, t is
the allowed next-layer width, and H is the complementary ball floor. -/
theorem bank_with_slack {D : CH.Digraph} {V : Finset ℕ} {q s L k r A B c t H e m p u : ℕ}
    (order : ∀ F W, QFree F W q → (∀ v∈W, s≤(outN F W v).card) → W.Nonempty → L≤W.card)
    (hf : QFree D V q) (hm : ∀ v∈V, s≤(outN D V v).card) (hu : u∈V)
    (hA : ∀ v∈V, A≤(ball D V v k).card)
    (hB : B≤(ball D V u (k+1)).card)
    (hH : ∀ v∈V, H≤(ball D V v r).card)
    (hwidth : A+c=B) (ht : t<s) (hcpos : 1≤c)
    (hslope : ∀ x : ℕ, x*(t+2)≤x*c+x*x+p)
    (hbudget : B+c*t+m+p≤L+t+1) (hmpos : 1≤m)
    (horder : V.card+1≤B+H+e)
    (hprefix : k+2≤q) (hpair : (k+1)+r≤q)
    (hbad : (ball D V u (k+2)).card<B+t+1) :
    ∃ C K : Finset ℕ, C⊆V ∧ C⊆K ∧ (∀ h∈C, ball D V h r⊆K) ∧
      (∀ h∈C, (K \ ball D V h r).card≤e) ∧ m≤C.card := by
  let P := (ball D V u (k+1)).card
  let U := (ball D V u (k+1)).erase u
  let S := ball D V u (k+1) \ ball D V u k
  let T := ball D V u (k+2) \ ball D V u (k+1)
  let C := fullColumns D V (k+1) u
  let K := V \ U
  let x := P-B
  have hP : P=B+x := by change B≤P at hB; dsimp [x]; omega
  have hU : U.card+1=P := Finset.card_erase_add_one (self_mem_ball hu)
  have hS : S.card+(ball D V u k).card=P :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hT : T.card+P=(ball D V u (k+2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hc : S.card≤c+x := by have := hA u hu; omega
  have htx : T.card+x≤t := by omega
  have localBudget : U.card+(c+x)*T.card+m≤L+T.card := by
    obtain ⟨z,hz⟩ : ∃ z, T.card+x+z=t := ⟨t-(T.card+x),by omega⟩
    have prod := congrArg (fun a : ℕ => c*a) hz
    have prodXZ := congrArg (fun a : ℕ => a*x) hz
    have cz := Nat.mul_le_mul_right z hcpos
    nlinarith only [hU,hP,hbudget,hz,prod,hslope x,prodXZ,cz,
      Nat.zero_le (z*x)]
  have rect := ShenFourthStrip.same_rectangle hf hm hu (by omega : 1≤s) order hprefix
    (show T.card<s by omega) hc localBudget hmpos
  have hs : S.card=c+x := rect.1
  have hinner : (ball D V u k).card=A := by omega
  have hC : m≤C.card := by
    have heq : C=(ball D V u (k+2) \ ball D V u (k+1)).filter
        (fun h => ∀ v∈ball D V u (k+1) \ ball D V u k, D v h=true) := by
      ext h
      simp only [C,fullColumns,DotTwoPassShellTransport.shell,DotTwoPassShellTransport.layer,
        Nat.add_sub_cancel,Finset.mem_filter]
    rw [heq]; exact rect.2
  have hUV : U⊆V := (Finset.erase_subset _ _).trans ball_subset
  have hCT : C⊆T := Finset.filter_subset _ _
  have hCV : C⊆V := fun _ hh => ball_subset (Finset.mem_sdiff.mp (hCT hh)).1
  have hCK : C⊆K := fun _ hh => Finset.mem_sdiff.mpr ⟨hCV hh,
    fun h => (Finset.mem_sdiff.mp (hCT hh)).2 (Finset.mem_of_mem_erase h)⟩
  have boxes : ∀ h∈C, ball D V h r⊆K := by
    apply full_bank_avoids hf hu hpair
    intro v hv
    have he := Finset.card_erase_add_one (self_mem_ball hu : u∈ball D V u k)
    have := hA v (hUV hv)
    omega
  have hK : K.card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
  refine ⟨C,K,hCV,hCK,boxes,?_,hC⟩
  intro h hh
  have := Finset.card_sdiff_add_card_eq_card (boxes h hh)
  have := hH h (hCV hh)
  omega

/-- Positive outdegree on a compressed bank gives the next radius bound. -/
theorem growth {D : CH.Digraph} {V : Finset ℕ} {q s L k r A B c t H e u : ℕ}
    (order : ∀ F W, QFree F W q → (∀ v∈W, s≤(outN F W v).card) → W.Nonempty → L≤W.card)
    (hf : QFree D V q) (hm : ∀ v∈V, s≤(outN D V v).card) (hu : u∈V)
    (hA : ∀ v∈V, A≤(ball D V v k).card)
    (hB : B≤(ball D V u (k+1)).card)
    (hH : ∀ v∈V, H≤(ball D V v r).card)
    (hwidth : A+c=B) (ht : t<s) (hslope : t+1≤c)
    (hbudget : B+c*t+(e+2)≤L+t+1) (horder : V.card+1≤B+H+e)
    (hprefix : k+2≤q) (hpair : (k+1)+r≤q) (hreturn : r+e+1≤q)
    (hcycle : e*(e+2)≤q) : B+t+1≤(ball D V u (k+2)).card := by
  by_contra! hbad
  obtain ⟨C,K,hCV,hCK,hballs,hmiss,hc⟩ := bank_with_slack (p:=0) (m:=e+2) (e:=e) order hf hm hu hA hB hH
    hwidth ht (by omega) (fun x => by
      nlinarith only [Nat.mul_le_mul_left x hslope,Nat.le_mul_self x])
    hbudget (by omega) horder hprefix hpair hbad
  exact ShenContainerTransfer.container_false hf hCV hCK hballs hmiss hc hreturn hcycle

#print axioms growth
end LeanCH.BR.ShenRectangleTransfer
