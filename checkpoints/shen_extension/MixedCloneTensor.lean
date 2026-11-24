import checkpoints.shen_extension.DotFourthPrefixQuadratic_20261118
import checkpoints.shen_extension.ContainerTransfer

namespace LeanCH.BR.ShenMixedClone
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open DotTwoPassShellTransport DotClonePairCompletion
open Classical

/-- One actual completion pays its clone pairs against two different ball
radii. Both floors are imposed on arbitrary completed hosts. -/
theorem mixed_deficiency {q s i j B C : ℕ} (hij : i+j≤q)
    (floor : ∀ F W, QFree F W q → (∀ x∈W,s≤(outN F W x).card) → W.Nonempty →
      ∀ x∈W, B≤(ball F W x i).card ∧ C≤(ball F W x j).card)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hm : ∀ x∈V, 1≤(outN D V x).card) (ne : V.Nonempty) :
    let g := fun v => s-(outN D V v).card
    let K := V.card+∑ v∈V,g v
    (∑ v∈V,g v*(g v+1))+K*(B+C)≤K*(K+1) := by
  obtain ⟨F,W,f,p,hF,hdeg,hK,hne,hp,hedge,hsub,hproj⟩ :=
    exists_deficiency_completion_bundles (d:=s) hf hm
  have h := bundle_pairs_le_incomparable (r:=max i j) hf hp hedge (by omega) hsub hproj
  rw [incomparable_card_rows] at h
  have rows (x) (_ : x∈W) : (W \ (ball F W x (max i j) ∪ reverseBall F W x (max i j))).card≤
      (W \ (ball F W x i ∪ reverseBall F W x j)).card := by
    apply Finset.card_le_card
    intro y hy
    obtain ⟨hyW,hn⟩ := Finset.mem_sdiff.mp hy
    refine Finset.mem_sdiff.mpr ⟨hyW,fun hw => hn ?_⟩
    rcases Finset.mem_union.mp hw with w|w
    · exact Finset.mem_union_left _ (ball_mono_radius (Nat.le_max_left _ _) w)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hyW,ball_mono_radius (Nat.le_max_right _ _) (Finset.mem_filter.mp w).2⟩)
  have hh := h.trans (Finset.sum_le_sum rows)
  have bounds := floor F W hF hdeg (hne ne)
  have h1 := Finset.sum_le_sum (fun x hx => (bounds x hx).1)
  have h2 := Finset.sum_le_sum (fun x hx => (bounds x hx).2)
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at h1 h2
  have cap := tensor_capacity_identity hF hij
  dsimp only
  rw [← hK,Nat.mul_add]
  omega

/-- A concentrated deficit on a small punctured ball forces a large
completion. The holes and all clone pairs refer to this same prefix. -/
theorem prefix_price {q s i j B C L M J k u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hij : i+j≤q)
    (floor : ∀ F W, QFree F W q → (∀ x∈W,s≤(outN F W x).card) → W.Nonempty →
      ∀ x∈W, B≤(ball F W x i).card ∧ C≤(ball F W x j).card)
    (hf : QFree D V q) (hm : ∀ v∈V,s≤(outN D V v).card) (hu : u∈V)
    (hs : 1≤s) (hk : k+2≤q) (ht : (shell D V (k+1) u).card<s)
    (hJ : ((ball D V u (k+1)).erase u).card≤J)
    (hM : (layer D V (k+1) u).card≤M)
    (price : M*L*(L-(B+C)) < (B+C-1-J)^2) :
    L+holes D V (k+1) u ≤ ((ball D V u (k+1)).erase u).card+
      (layer D V (k+1) u).card*(shell D V (k+1) u).card := by
  let U := (ball D V u (k+1)).erase u
  let S := layer D V (k+1) u
  let g := fun v => s-(outN D U v).card
  let G := ∑ v∈U,g v
  let Q := ∑ v∈U,g v*(g v+1)
  let K := U.card+G
  have hUV : U⊆V := (Finset.erase_subset _ _).trans ball_subset
  obtain ⟨hne,hrt,hSU,hz,hbudget⟩ := DotFourthPrefixQuadratic.prefix_gap_budget hf hm hu hs hk ht
  change U.Nonempty at hne
  change ∀ v∈U,1≤(outN D U v).card at hrt
  change S⊆U at hSU
  change ∀ v∈U \ S,g v=0 at hz
  change G+holes D V (k+1) u≤S.card*(shell D V (k+1) u).card at hbudget
  have sg : (∑ v∈S,g v)=G := Finset.sum_subset hSU
    (fun v hv hn => hz v (Finset.mem_sdiff.mpr ⟨hv,hn⟩))
  have sq : (∑ v∈S,g v*(g v+1))=Q := Finset.sum_subset hSU (by
    intro v hv hn; simp [hz v (Finset.mem_sdiff.mpr ⟨hv,hn⟩)])
  have cauchy := gap_cauchy S g
  rw [sg,sq] at cauchy
  have quad := mixed_deficiency hij floor (hf.mono_set hUV) hrt hne
  change Q+K*(B+C)≤K*(K+1) at quad
  have Kpos : 0<K := by dsimp [K]; have := Finset.card_pos.mpr hne; omega
  have floorK : B+C≤K+1 := Nat.le_of_mul_le_mul_left (by omega : K*(B+C)≤K*(K+1)) Kpos
  change U.card≤J at hJ
  change S.card≤M at hM
  have Kdef : K=U.card+G := rfl
  have lower : L≤K := by
    by_contra! bad
    have pos : B+C≤L := by omega
    have prod := Nat.mul_le_mul_left K (show K+1≤(L-(B+C))+(B+C) by omega)
    conv at prod => rhs; rw [Nat.mul_add]
    have hQ : Q≤L*(L-(B+C)) :=
      (show Q≤K*(L-(B+C)) by omega).trans (Nat.mul_le_mul_right _ bad.le)
    have small := Nat.mul_le_mul hM hQ
    have low := Nat.pow_le_pow_left (show B+C-1-J≤G by omega) 2
    rw [← Nat.mul_assoc] at small
    omega
  change L+_≤U.card+S.card*_
  omega

/-- A local paid-prefix version of the full-column growth argument. A
completed prefix may have a stronger lower bound than an arbitrary host. -/
theorem paid_growth {D : CH.Digraph} {V : Finset ℕ} {q L k r A B c t H e u : ℕ}
    (hf : QFree D V q) (hu : u∈V)
    (hA : ∀ v∈V, A≤(ball D V v k).card) (hB : B≤(ball D V u (k+1)).card)
    (hH : ∀ v∈V, H≤(ball D V v r).card)
    (width : A+c=B) (slope : t+1≤c)
    (budget : B+c*t+(e+2)≤L+t+1) (order : V.card+1≤B+H+e)
    (pair : (k+1)+r≤q) (ret : r+e+1≤q) (cycle : e*(e+2)≤q)
    (pay : (ball D V u (k+2)).card<B+t+1 →
      L+holes D V (k+1) u ≤ ((ball D V u (k+1)).erase u).card+
        (layer D V (k+1) u).card*(shell D V (k+1) u).card) :
    B+t+1≤(ball D V u (k+2)).card := by
  by_contra! bad
  let P := (ball D V u (k+1)).card
  let U := (ball D V u (k+1)).erase u
  let S := layer D V (k+1) u
  let T := shell D V (k+1) u
  let C := fullColumns D V (k+1) u
  let K := V \ U
  let x := P-B
  have hp : P=B+x := by change B≤P at hB; dsimp [x]; omega
  have hu' : U.card+1=P := Finset.card_erase_add_one (self_mem_ball hu)
  have hs : S.card+(ball D V u k).card=P := by
    simpa only [S,layer,Nat.add_sub_cancel] using Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=u) (show k≤k+1 by omega))
  have ht : T.card+P=(ball D V u (k+2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hc : S.card≤c+x := by have := hA u hu; omega
  obtain ⟨z,hz⟩ : ∃ z,T.card+x+z=t := ⟨t-(T.card+x),by omega⟩
  have loc : U.card+(c+x)*T.card+(e+2)≤L+T.card := by
    have hsl : x*(t+2)≤x*c+x*x := by
      nlinarith only [Nat.mul_le_mul_left x slope,Nat.le_mul_self x]
    nlinarith only [hu',hp,budget,hz,congrArg (fun n : ℕ => c*n) hz,
      congrArg (fun n : ℕ => n*x) hz,hsl,Nat.mul_le_mul_right z (show 1≤c by omega),
      Nat.zero_le (z*x)]
  have paid := pay bad
  change L+holes D V (k+1) u≤U.card+S.card*T.card at paid
  have eq : S.card=c+x := by
    by_contra h
    have le := Nat.mul_le_mul_right T.card (show S.card+1≤c+x by omega)
    rw [Nat.add_mul,Nat.one_mul] at le
    omega
  have nC : e+2≤C.card := by
    rw [eq] at paid
    have := full_columns_bound (D:=D) (V:=V) (R:=k+1) (u:=u)
    change T.card≤C.card+holes D V (k+1) u at this
    omega
  have hUV : U⊆V := (Finset.erase_subset _ _).trans ball_subset
  have hCT : C⊆T := Finset.filter_subset _ _
  have hCV : C⊆V := hCT.trans (Finset.sdiff_subset.trans ball_subset)
  have boxes : ∀ h∈C, ball D V h r⊆K := by
    apply full_bank_avoids hf hu pair
    intro v hv
    have := Finset.card_erase_add_one (self_mem_ball hu : u∈ball D V u k)
    have := hA v (hUV hv)
    omega
  have hK : K.card+U.card=V.card := Finset.card_sdiff_add_card_eq_card hUV
  apply ShenContainerTransfer.container_false hf hCV
    (fun h hh => boxes h hh (self_mem_ball (hCV hh))) boxes _ nC ret cycle
  intro h hh
  have := Finset.card_sdiff_add_card_eq_card (boxes h hh)
  have := hH h (hCV hh)
  omega

#print axioms mixed_deficiency
#print axioms prefix_price
#print axioms paid_growth
end LeanCH.BR.ShenMixedClone
