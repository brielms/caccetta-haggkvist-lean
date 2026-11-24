import checkpoints.shen_extension.RectangleTransfer

/-! A cutoff-independent obstruction on one minimum-order host. Every floor is
an actual minimum on that host. Different radii may choose different roots. -/
namespace LeanCH.BR.ShenMinimumOrder
open BRq2 BRq3 BR45 ShenFirstStrip
open Classical

structure Source (q s : ℕ) where
  D : CH.Digraph
  V : Finset ℕ
  nonempty : V.Nonempty
  free : QFree D V q
  degree : ∀ v∈V, s≤(outN D V v).card
  least : ∀ F W, QFree F W q → (∀ v∈W, s≤(outN F W v).card) →
    W.Nonempty → V.card≤W.card

theorem exists_source {D : CH.Digraph} {V : Finset ℕ} {q s : ℕ}
    (hf : QFree D V q) (hm : ∀ v∈V, s≤(outN D V v).card) (ne : V.Nonempty) :
    ∃ X : Source q s, X.V.card≤V.card := by
  let Good := fun m => ∃ (F : CH.Digraph) (W : Finset ℕ), W.card=m ∧ W.Nonempty ∧
    QFree F W q ∧ ∀ v∈W, s≤(outN F W v).card
  have hex : ∃ m, Good m := ⟨V.card,D,V,rfl,ne,hf,hm⟩
  obtain ⟨F,W,hW,hne,hfree,hdeg⟩ := Nat.find_spec hex
  have least (E : CH.Digraph) (Y : Finset ℕ) (hE : QFree E Y q)
      (hmin : ∀ v∈Y, s≤(outN E Y v).card) (hY : Y.Nonempty) : W.card≤Y.card := by
    rw [hW]; exact Nat.find_min' hex ⟨E,Y,rfl,hY,hE,hmin⟩
  exact ⟨⟨F,W,hne,hfree,hdeg,least⟩,least D V hf hm ne⟩

noncomputable def Source.floor {q s : ℕ} (X : Source q s) (k : ℕ) : ℕ :=
  (X.V.image (fun v => (ball X.D X.V v k).card)).min' (X.nonempty.image _)

theorem Source.floor_le {q s : ℕ} (X : Source q s) (k : ℕ) {u : ℕ} (hu : u∈X.V) :
    X.floor k≤(ball X.D X.V u k).card :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem _ hu)

theorem Source.attains {q s : ℕ} (X : Source q s) (k : ℕ) :
    ∃ u∈X.V, (ball X.D X.V u k).card=X.floor k :=
  Finset.mem_image.mp (Finset.min'_mem _ _)

theorem Source.floor_mono {q s : ℕ} (X : Source q s) {i j : ℕ} (hij : i≤j) :
    X.floor i≤X.floor j := by
  obtain ⟨u,hu,he⟩ := X.attains j
  rw [← he]
  exact (X.floor_le i hu).trans (Finset.card_le_card (ball_mono_radius hij))

/-- A plateau would leave a smaller punctured ball retaining the full degree. -/
theorem Source.floor_strict {q s : ℕ} (X : Source q s) (hs : 0<s) {k : ℕ} (hk : k+1≤q) :
    X.floor k<X.floor (k+1) := by
  by_contra! hn
  obtain ⟨u,hu,hroot⟩ := X.attains (k+1)
  have sub := ball_mono_radius (D:=X.D) (W:=X.V) (u:=u) (show k≤k+1 by omega)
  have eqB := Finset.eq_of_subset_of_card_le sub ((hroot.le.trans hn).trans (X.floor_le k hu))
  let U := (ball X.D X.V u k).erase u
  have hUV : U⊆X.V := (Finset.erase_subset _ _).trans ball_subset
  have ret := minOut_prefix_erase (d:=s) X.free hu hk X.degree (by rw [← eqB]; simp)
  have ho := X.degree u hu
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (show 0<(outN X.D X.V u).card by omega)
  have hy' := outN_prefix_erase_root X.free hu hk (self_mem_ball hu) hy
  rw [← eqB] at hy'
  have least := X.least X.D U (X.free.mono_set hUV) ret ⟨y,(mem_outN.mp hy').1⟩
  have he := Finset.card_erase_add_one (self_mem_ball hu : u∈ball X.D X.V u k)
  have hcard := Finset.card_le_card (ball_subset (D:=X.D) (W:=X.V) (u:=u) (k:=k))
  change X.V.card≤((ball X.D X.V u k).erase u).card at least
  omega

private theorem slope_cost (c t x : ℕ) :
    x*(t+2)≤x*c+x*x+(t+2-c)^2/4 := by
  by_cases hs : t+2≤c
  · exact (Nat.mul_le_mul_left x hs).trans (by omega)
  let z := t+2-c
  have hz : c+z=t+2 := by dsimp [z]; omega
  have prod := congrArg (fun n : ℕ => x*n) hz
  have sq : 4*(x*z)≤4*(x*x)+z^2 := by
    zify
    nlinarith only [sq_nonneg (2*(x:ℤ)-z)]
  change x*(t+2)≤x*c+x*x+z^2/4
  nlinarith only [prod,(show x*z≤x*x+z^2/4 by omega)]

/-- Here c and t are successive differences of the minimum ball sizes, and
e is the slack in the complementary-pair inequality. The host order cancels
from the concluding inequality. -/
theorem Source.profile_obstruction {q s : ℕ} (X : Source q s) (k r : ℕ)
    (hprefix : k+2≤q) (hpair : k+1+r≤q) :
    let c := X.floor (k+1)-X.floor k
    let t := X.floor (k+2)-X.floor (k+1)
    let e := X.V.card+1-(X.floor (k+1)+X.floor r)
    t<s → r+e+1≤q → e*(e+2)≤q → X.floor r≤(c-1)*t+1+(t+2-c)^2/4 := by
  intro c t e ht hr hcycle
  have h1 := X.floor_mono (show k≤k+1 by omega)
  have h2 := X.floor_mono (show k+1≤k+2 by omega)
  have hc : X.floor k+c=X.floor (k+1) := by dsimp [c]; omega
  have hstrict := X.floor_strict (by omega : 0<s) (show k+1≤q by omega)
  have hnext : X.floor (k+1)+t=X.floor (k+2) := by dsimp [t]; omega
  have hcap := card_ge_of_two_balls X.free hpair
    (fun _ hv => X.floor_le (k+1) hv) (fun _ hv => X.floor_le r hv) X.nonempty
  have he : X.floor (k+1)+X.floor r+e=X.V.card+1 := by dsimp [e]; omega
  by_contra! bad
  obtain ⟨u,hu,hroot⟩ := X.attains (k+2)
  have hprod : (c-1)*t+t=c*t := by
    rw [← Nat.succ_mul,show (c-1).succ=c by omega]
  have hb : X.floor (k+1)+c*t+(e+2)+(t+2-c)^2/4≤X.V.card+t+1 := by omega
  obtain ⟨C,K,hCV,hCK,boxes,miss,hC⟩ := ShenRectangleTransfer.bank_with_slack
    (m:=e+2) (e:=e) (p:=(t+2-c)^2/4) X.least X.free X.degree hu
    (fun _ hv => X.floor_le k hv) (X.floor_le (k+1) hu) (fun _ hv => X.floor_le r hv)
    hc ht (by omega) (slope_cost c t) hb (by omega) he.ge hprefix hpair (by omega)
  exact ShenContainerTransfer.container_false X.free hCV hCK boxes miss hC hr hcycle

#print axioms exists_source
#print axioms Source.floor_strict
#print axioms Source.profile_obstruction
end LeanCH.BR.ShenMinimumOrder
