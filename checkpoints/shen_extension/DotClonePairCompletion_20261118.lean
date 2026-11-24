import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import checkpoints.shen_extension.DotTwoPassShellTransport_20261117
import Mathlib.Data.Nat.Pairing
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
Independent fourth-strip work: one actual clone completion and its labelled
incomparable-pair carrier. This file does not assume the upper-order closure.
-/
namespace LeanCH.BR.DotClonePairCompletion
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

noncomputable def cloneBundle (f g : ℕ → ℕ) (x : ℕ) : Finset ℕ :=
  insert (Nat.pair (f x) 0)
    ((Finset.range (g x)).image (fun i => Nat.pair x (i+1)))

noncomputable def bundlePairs (f g : ℕ → ℕ) (x : ℕ) : Finset (ℕ × ℕ) :=
  (cloneBundle f g x).offDiag

theorem mem_bundle {f g : ℕ → ℕ} {x z : ℕ} :
    z ∈ cloneBundle f g x ↔
      z=Nat.pair (f x) 0 ∨ ∃ i<g x, z=Nat.pair x (i+1) := by
  simp only [cloneBundle,Finset.mem_insert,Finset.mem_image,Finset.mem_range]
  constructor
  · rintro (h|⟨i,hi,he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i,hi,he.symm⟩
  · rintro (h|⟨i,hi,he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i,hi,he.symm⟩

theorem bundle_card (f g : ℕ → ℕ) (x : ℕ) :
    (cloneBundle f g x).card=g x+1 := by
  have hn : Nat.pair (f x) 0 ∉
      (Finset.range (g x)).image (fun i => Nat.pair x (i+1)) := by
    intro hh
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hh
    have h := (Nat.pair_eq_pair.mp he).2
    omega
  have hinj : Function.Injective (fun i => Nat.pair x (i+1)) := by
    intro i j h
    have hh := (Nat.pair_eq_pair.mp h).2
    omega
  simp only [cloneBundle,Finset.card_insert_of_notMem hn,
    Finset.card_image_of_injective _ hinj,Finset.card_range]

theorem bundle_pairs_card (f g : ℕ → ℕ) (x : ℕ) :
    (bundlePairs f g x).card=g x*(g x+1) := by
  rw [bundlePairs,Finset.offDiag_card,bundle_card]
  have h : g x+1≤(g x+1)*(g x+1) := by nlinarith
  have hh := Nat.sub_add_cancel h
  nlinarith

/-- Distinct bundles may share their chosen base label, but nothing else. -/
theorem bundle_intersection_base {f g : ℕ → ℕ} {x y z : ℕ}
    (hne : x≠y) (hx : z ∈ cloneBundle f g x) (hy : z ∈ cloneBundle f g y) :
    z=Nat.pair (f x) 0 ∧ z=Nat.pair (f y) 0 := by
  rcases mem_bundle.mp hx with hx|⟨i,hi,hx⟩
  · rcases mem_bundle.mp hy with hy|⟨j,hj,hy⟩
    · exact ⟨hx,hy⟩
    · have he := (Nat.pair_eq_pair.mp (hx.symm.trans hy)).2
      omega
  · rcases mem_bundle.mp hy with hy|⟨j,hj,hy⟩
    · have he := (Nat.pair_eq_pair.mp (hx.symm.trans hy)).2
      omega
    · exact (hne (Nat.pair_eq_pair.mp (hx.symm.trans hy)).1).elim

/-- No ordered distinct pair belongs to two different source-row bundles. -/
theorem bundle_pair_owner {f g : ℕ → ℕ} {x y : ℕ} {p : ℕ × ℕ}
    (hx : p ∈ bundlePairs f g x) (hy : p ∈ bundlePairs f g y) : x=y := by
  by_contra hne
  obtain ⟨hx1,hx2,hp⟩ := Finset.mem_offDiag.mp hx
  obtain ⟨hy1,hy2,_⟩ := Finset.mem_offDiag.mp hy
  have he1 := (bundle_intersection_base hne hx1 hy1).1
  have he2 := (bundle_intersection_base hne hx2 hy2).1
  exact hp (he1.trans he2.symm)

/-- The joint carrier map forgets the row tag, and is genuinely injective. -/
theorem bundle_pairs_joint_injective (S : Finset ℕ) (f g : ℕ → ℕ) :
    Set.InjOn (fun z : Σ _ : ℕ, ℕ × ℕ => z.2)
      (S.sigma (bundlePairs f g) : Set (Σ _ : ℕ, ℕ × ℕ)) := by
  rintro ⟨x,p⟩ hx ⟨y,r⟩ hy he
  dsimp only at he
  subst r
  have hxy := bundle_pair_owner (Finset.mem_sigma.mp hx).2 (Finset.mem_sigma.mp hy).2
  change x=y at hxy
  subst y
  rfl

/-- Exact same-length walk transport through one vertex projection. -/
theorem walk_project {D F : CH.Digraph} {V U : Finset ℕ} {p : ℕ → ℕ}
    (hp : ∀ x ∈ U, p x ∈ V)
    (hedge : ∀ x y, F x y=true → D (p x) (p y)=true)
    {x y l : ℕ} (w : Walk F U x y l) : Walk D V (p x) (p y) l := by
  induction w with
  | refl x => exact .refl (p x)
  | step hy hxy _ ih => exact .step (hp _ hy) (hedge _ _ hxy) ih

theorem qfree_project {D F : CH.Digraph} {V U : Finset ℕ} {p : ℕ → ℕ} {q : ℕ}
    (hf : QFree D V q) (hp : ∀ x ∈ U, p x ∈ V)
    (hedge : ∀ x y, F x y=true → D (p x) (p y)=true) :
    QFree F U q := by
  intro x l hl hlq w
  exact hf (p x) l hl hlq (walk_project hp hedge w)

/-- Equal-projection distinct labels are incomparable at EVERY bounded
radius up to q, not only at a source-specific half-radius. -/
theorem equal_projection_incomparable
    {D F : CH.Digraph} {V U : Finset ℕ} {p : ℕ → ℕ} {q r x y : ℕ}
    (hf : QFree D V q) (hp : ∀ z ∈ U, p z ∈ V)
    (hedge : ∀ a b, F a b=true → D (p a) (p b)=true)
    (hr : r≤q) (hne : x≠y) (he : p x=p y) :
    y ∉ ball F U x r ∧ x ∉ ball F U y r := by
  have one {a b : ℕ} (hne : a≠b) (he : p a=p b) :
      b ∉ ball F U a r := by
    intro hb
    obtain ⟨_,l,hl,w⟩ := mem_ball.mp hb
    have hlp : 1≤l := by
      cases l with
      | zero => cases w; exact (hne rfl).elim
      | succ l => omega
    have wp := walk_project hp hedge w
    rw [← he] at wp
    exact hf (p a) l hlp (by omega) wp
  exact ⟨one hne he,one (Ne.symm hne) he.symm⟩

noncomputable def orderedIncomparable (D : CH.Digraph) (V : Finset ℕ) (r : ℕ) :
    Finset (ℕ × ℕ) :=
  V.offDiag.filter (fun z => z.2 ∉ ball D V z.1 r ∧ z.1 ∉ ball D V z.2 r)

/-- Pair injection into the ONE actual completed graph. This is doubled
unordered-pair counting, retaining the labelled ordered carrier explicitly. -/
theorem bundle_pairs_le_incomparable
    {D F : CH.Digraph} {V U S : Finset ℕ} {p f g : ℕ → ℕ} {q r : ℕ}
    (hf : QFree D V q) (hp : ∀ z ∈ U, p z ∈ V)
    (hedge : ∀ a b, F a b=true → D (p a) (p b)=true)
    (hr : r≤q)
    (hBU : ∀ x ∈ S, cloneBundle f g x ⊆ U)
    (hproj : ∀ x ∈ S, ∀ z ∈ cloneBundle f g x, p z=f x) :
    (∑ x ∈ S, g x*(g x+1))≤(orderedIncomparable F U r).card := by
  let A := S.sigma (bundlePairs f g)
  let B := A.image (fun z => z.2)
  have hB : B.card=∑ x ∈ S, g x*(g x+1) := by
    rw [Finset.card_image_iff.mpr (bundle_pairs_joint_injective S f g)]
    simp only [A,Finset.card_sigma,bundle_pairs_card]
  have hsub : B ⊆ orderedIncomparable F U r := by
    intro z hz
    obtain ⟨⟨x,w⟩,hx,he⟩ := Finset.mem_image.mp hz
    dsimp only at he
    subst z
    obtain ⟨hxS,hwp⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hw1,hw2,hwne⟩ := Finset.mem_offDiag.mp hwp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_offDiag.mpr ⟨hBU x hxS hw1,hBU x hxS hw2,hwne⟩,?_⟩
    exact equal_projection_incomparable hf hp hedge hr hwne
      ((hproj x hxS _ hw1).trans (hproj x hxS _ hw2).symm)
  rw [← hB]
  exact Finset.card_le_card hsub

#print axioms bundle_pairs_joint_injective
#print axioms equal_projection_incomparable
#print axioms bundle_pairs_le_incomparable
end LeanCH.BR.DotClonePairCompletion


namespace LeanCH.BR.DotClonePairCompletion
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

theorem incomparable_card_rows (D : CH.Digraph) (V : Finset ℕ) (r : ℕ) :
    (orderedIncomparable D V r).card =
      ∑ x ∈ V, (V \ (ball D V x r ∪ reverseBall D V x r)).card := by
  let M := fun x => V \ (ball D V x r ∪ reverseBall D V x r)
  let A := V.sigma M
  let f : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun z => (z.1,z.2)
  have hinj : Function.Injective f := by
    rintro ⟨x,y⟩ ⟨u,v⟩ he
    have he1 : x=u := congrArg Prod.fst he
    have he2 : y=v := congrArg Prod.snd he
    subst u
    subst v
    rfl
  have heq : orderedIncomparable D V r=A.image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzdiag,hz1,hz2⟩ := Finset.mem_filter.mp hz
      obtain ⟨hx,hy,hne⟩ := Finset.mem_offDiag.mp hzdiag
      refine Finset.mem_image.mpr ⟨⟨z.1,z.2⟩,Finset.mem_sigma.mpr ⟨hx,?_⟩,rfl⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨hy,?_⟩
      rintro hh
      rcases Finset.mem_union.mp hh with hb|hb
      · exact hz1 hb
      · exact hz2 (Finset.mem_filter.mp hb).2
    · intro hz
      obtain ⟨⟨x,y⟩,hxy,he⟩ := Finset.mem_image.mp hz
      change (x,y)=z at he
      subst z
      obtain ⟨hx,hyM⟩ := Finset.mem_sigma.mp hxy
      obtain ⟨hy,hn⟩ := Finset.mem_sdiff.mp hyM
      have hforw : y ∉ ball D V x r := fun hb => hn (Finset.mem_union_left _ hb)
      have hback : x ∉ ball D V y r := fun hb =>
        hn (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy,hb⟩))
      have hne : x≠y := by
        intro hh
        subst y
        exact hforw (self_mem_ball hx)
      exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hx,hy,hne⟩,hforw,hback⟩
  rw [heq,Finset.card_image_of_injective _ hinj]
  exact Finset.card_sigma _ _

/-- Exact reach/incomparability partition for one actual host. -/
theorem incomparable_reach_identity {D : CH.Digraph} {V : Finset ℕ} {q r : ℕ}
    (hf : QFree D V q) (hr : r+r≤q) :
    (orderedIncomparable D V r).card +
      2*(∑ x ∈ V, (ball D V x r).card)=V.card*(V.card+1) := by
  have part (x) (hx : x ∈ V) :
      (V \ (ball D V x r ∪ reverseBall D V x r)).card +
        ((ball D V x r).card+(reverseBall D V x r).card)=V.card+1 := by
    let F := ball D V x r
    let I := reverseBall D V x r
    have hI : I ⊆ (V \ F) ∪ {x} := reverseBall_subset_complement hf hr
    have hmeet : F ∩ I={x} := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyF,hyI⟩ := Finset.mem_inter.mp hy
        rcases Finset.mem_union.mp (hI hyI) with hh|hh
        · exact ((Finset.mem_sdiff.mp hh).2 hyF).elim
        · exact hh
      · intro hy
        obtain rfl := Finset.mem_singleton.mp hy
        exact Finset.mem_inter.mpr ⟨self_mem_ball hx,Finset.mem_filter.mpr
          ⟨hx,self_mem_ball hx⟩⟩
    have hsub : F ∪ I ⊆ V := Finset.union_subset ball_subset (Finset.filter_subset _ _)
    have h1 := Finset.card_sdiff_add_card_eq_card hsub
    have h2 := Finset.card_union_add_card_inter F I
    rw [hmeet,Finset.card_singleton] at h2
    change (V \ (F ∪ I)).card+(F.card+I.card)=V.card+1
    omega
  have hs := Finset.sum_congr (s₁:=V) rfl part
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,
    sum_reverseBall_eq_sum_ball D V r,Finset.sum_const_nat (fun _ _ => rfl)] at hs
  rw [incomparable_card_rows]
  omega

theorem incomparable_universal_bound {D : CH.Digraph} {V : Finset ℕ} {q r B : ℕ}
    (hf : QFree D V q) (hr : r+r≤q)
    (hlow : ∀ x ∈ V, B≤(ball D V x r).card) :
    (orderedIncomparable D V r).card+2*V.card*B≤V.card*(V.card+1) := by
  have he := incomparable_reach_identity hf hr
  have hl := Finset.sum_le_sum hlow
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at hl
  nlinarith

/-- Universal same-completion inequality. The radius floor is required on
this actual completed host and cannot be replaced by a source-capped bound. -/
theorem joint_completion_pair_bound
    {D F : CH.Digraph} {V U S : Finset ℕ} {p f g : ℕ → ℕ} {q r B : ℕ}
    (hf : QFree D V q) (hp : ∀ z ∈ U, p z ∈ V)
    (hedge : ∀ a b, F a b=true → D (p a) (p b)=true)
    (hr : r+r≤q)
    (hBU : ∀ x ∈ S, cloneBundle f g x ⊆ U)
    (hproj : ∀ x ∈ S, ∀ z ∈ cloneBundle f g x, p z=f x)
    (hlow : ∀ z ∈ U, B≤(ball F U z r).card) :
    (∑ x ∈ S, g x*(g x+1))+2*U.card*B≤U.card*(U.card+1) := by
  have hF := qfree_project hf hp hedge
  have hi := bundle_pairs_le_incomparable (r:=r) hf hp hedge (by omega) hBU hproj
  have hc := incomparable_universal_bound hF hr hlow
  omega

#print axioms incomparable_reach_identity
#print axioms incomparable_universal_bound
#print axioms joint_completion_pair_bound
end LeanCH.BR.DotClonePairCompletion


namespace LeanCH.BR.DotClonePairCompletion
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

/-- A full degree completion carrying its actual projection and ALL clone
bundles simultaneously. No bundle or witness is chosen separately later. -/
theorem exists_deficiency_completion_bundles {D : CH.Digraph} {V : Finset ℕ} {q d : ℕ}
    (hf : QFree D V q) (hmin : ∀ v ∈ V, 1≤(outN D V v).card) :
    ∃ (F : CH.Digraph) (U : Finset ℕ) (f p : ℕ → ℕ),
      QFree F U q ∧
      (∀ v ∈ U, d≤(outN F U v).card) ∧
      U.card=V.card+∑ v ∈ V, (d-(outN D V v).card) ∧
      (V.Nonempty → U.Nonempty) ∧
      (∀ z ∈ U, p z ∈ V) ∧
      (∀ a b, F a b=true → D (p a) (p b)=true) ∧
      (∀ x ∈ V, cloneBundle f (fun v => d-(outN D V v).card) x ⊆ U) ∧
      (∀ x ∈ V, ∀ z ∈ cloneBundle f (fun v => d-(outN D V v).card) x, p z=f x) := by
  have hchoose : ∀ v, ∃ w, v ∈ V → w ∈ V ∧ D v w=true := by
    intro v
    by_cases hv : v ∈ V
    · obtain ⟨w,hw⟩ := Finset.card_pos.mp (hmin v hv)
      exact ⟨w,fun _ => mem_outN.mp hw⟩
    · exact ⟨v,fun h => (hv h).elim⟩
  choose f hfspec using hchoose
  let gap := fun v => d-(outN D V v).card
  let S : Finset (Σ _ : ℕ, ℕ) := V.sigma (fun v => Finset.range (gap v+1))
  let enc : (Σ _ : ℕ, ℕ) → ℕ := fun z => Nat.pair z.1 z.2
  let U := S.image enc
  let p : ℕ → ℕ := fun x =>
    if (Nat.unpair x).2=0 then (Nat.unpair x).1 else f (Nat.unpair x).1
  let F : CH.Digraph := fun x y => D (p x) (p y)
  have henc : Function.Injective enc := by
    rintro ⟨v,i⟩ ⟨w,j⟩ he
    have hh := Nat.pair_eq_pair.mp he
    rcases hh with ⟨rfl,rfl⟩
    rfl
  have hmem (v i) (hv : v ∈ V) (hi : i≤gap v) : Nat.pair v i ∈ U := by
    apply Finset.mem_image.mpr
    exact ⟨⟨v,i⟩,Finset.mem_sigma.mpr
      ⟨hv,Finset.mem_range.mpr (by change i<gap v+1; omega)⟩,rfl⟩
  have hp0 (v) : p (Nat.pair v 0)=v := by simp [p]
  have hpi (v i) (hi : i≠0) : p (Nat.pair v i)=f v := by simp [p,hi]
  have hpV : ∀ x ∈ U, p x ∈ V := by
    intro x hx
    obtain ⟨⟨v,i⟩,hvi,rfl⟩ := Finset.mem_image.mp hx
    have hv := (Finset.mem_sigma.mp hvi).1
    change p (Nat.pair v i) ∈ V
    by_cases hi : i=0
    · subst i
      rw [hp0]
      exact hv
    · rw [hpi v i hi]
      exact (hfspec v hv).1
  have hedge : ∀ a b, F a b=true → D (p a) (p b)=true := fun _ _ h => h
  refine ⟨F,U,f,p,qfree_project hf hpV hedge,?_,?_,?_,hpV,hedge,?_,?_⟩
  · intro x hx
    have hv := hpV x hx
    let A := (outN D V (p x)).image (fun w => Nat.pair w 0)
    let B := (Finset.range (gap (p x))).image (fun i => Nat.pair (p x) (i+1))
    have hAc : A.card=(outN D V (p x)).card := by
      apply Finset.card_image_of_injective
      intro a b h
      exact (Nat.pair_eq_pair.mp h).1
    have hBc : B.card=gap (p x) := by
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range _
      · intro i j h
        have := (Nat.pair_eq_pair.mp h).2
        omega
    have hAB : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro y hyA hyB
      obtain ⟨w,_,hw⟩ := Finset.mem_image.mp hyA
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hyB
      have := (Nat.pair_eq_pair.mp (hw.trans hi.symm)).2
      omega
    have hsub : A ∪ B ⊆ outN F U x := by
      intro y hy
      rcases Finset.mem_union.mp hy with hyA|hyB
      · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hyA
        refine mem_outN.mpr ⟨hmem w 0 (outN_subset hw) (by omega),?_⟩
        change D (p x) (p (Nat.pair w 0))=true
        rw [hp0]
        exact (mem_outN.mp hw).2
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hyB
        have hi' := Finset.mem_range.mp hi
        refine mem_outN.mpr ⟨hmem (p x) (i+1) hv (by omega),?_⟩
        change D (p x) (p (Nat.pair (p x) (i+1)))=true
        rw [hpi _ _ (by omega)]
        exact (hfspec (p x) hv).2
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hAB,hAc,hBc] at hc
    dsimp only [gap] at hc
    omega
  · change (S.image enc).card=_
    rw [Finset.card_image_of_injective _ henc]
    change (V.sigma (fun v => Finset.range (gap v+1))).card=_
    rw [Finset.card_sigma]
    simp only [Finset.card_range,Finset.sum_add_distrib,gap]
    rw [Finset.sum_const_nat (fun _ _ => rfl)]
    omega
  · rintro ⟨v,hv⟩
    exact ⟨Nat.pair v 0,hmem v 0 hv (by omega)⟩
  · intro x hx z hz
    rcases mem_bundle.mp hz with he|⟨i,hi,he⟩
    · rw [he]
      exact hmem (f x) 0 (hfspec x hx).1 (by omega)
    · rw [he]
      exact hmem x (i+1) hx (by change i<gap x at hi; omega)
  · intro x hx z hz
    rcases mem_bundle.mp hz with he|⟨i,hi,he⟩
    · rw [he,hp0]
    · rw [he,hpi x (i+1) (by omega)]

/-- A universal radius theorem transfers to a QUADRATIC deficiency bound,
through one explicit completion and the joint clone-pair injection. -/
theorem deficiency_quadratic_bound {q d r B : ℕ}
    (hr : r+r≤q)
    (hball : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ x ∈ U, d≤(outN F U x).card) → U.Nonempty →
      ∀ x ∈ U, B≤(ball F U x r).card)
    {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hmin : ∀ v ∈ V, 1≤(outN D V v).card)
    (hne : V.Nonempty) :
    let g := fun v => d-(outN D V v).card
    let K := V.card+∑ v ∈ V, g v
    (∑ v ∈ V, g v*(g v+1))+2*K*B≤K*(K+1) := by
  obtain ⟨F,U,f,p,hF,hm,hc,hn,hp,hedge,hBU,hproj⟩ :=
    exists_deficiency_completion_bundles hf hmin
  have hlow := hball F U hF hm (hn hne)
  have hbound := joint_completion_pair_bound hf hp hedge hr hBU hproj hlow
  simpa only [hc] using hbound

#print axioms exists_deficiency_completion_bundles
#print axioms deficiency_quadratic_bound
end LeanCH.BR.DotClonePairCompletion


namespace LeanCH.BR.DotClonePairCompletion
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

/-- Cauchy contracts the already-labelled row bundles; zero gaps are allowed. -/
theorem gap_cauchy (S : Finset ℕ) (g : ℕ → ℕ) :
    (∑ x ∈ S, g x)^2+S.card*(∑ x ∈ S,g x) ≤
      S.card*(∑ x ∈ S,g x*(g x+1)) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S g (fun _ => (1:ℕ))
  simp only [mul_one,one_pow,Finset.sum_const_nat] at hc
  have he : (∑ x ∈ S,g x*(g x+1)) =
      (∑ x ∈ S,(g x)^2)+(∑ x ∈ S,g x) := by
    simp only [mul_add,mul_one,pow_two,Finset.sum_add_distrib]
  rw [he]
  nlinarith

/-- Additive form avoids truncated subtraction in the completed-host bound. -/
theorem quadratic_native_form {Q K b : ℕ} (hb : 1≤b)
    (h : Q+2*K*(b-1)≤K*(K+1)) :
    Q+2*K*b≤K*(K+3) := by
  have hb' := Nat.sub_add_cancel hb
  nlinarith

theorem quadratic_case_zero {s D K Q : ℕ}
    (hs : 12≤s) (hD : s*(s-2)≤D)
    (hK : K≤2*s*(s-3)+3)
    (hpair : Q+2*K*(s*(s-3))≤K*(K+3))
    (hcauchy : D^2+s*D≤s*Q) : False := by
  have hmul := Nat.mul_le_mul_left K hK
  have hQ : Q≤6*(2*s*(s-3)+3) := by nlinarith
  obtain ⟨x,hx⟩ : ∃ x,s=x+12 := ⟨s-12,by omega⟩
  subst s
  rw [show x+12-2=x+10 by omega] at hD
  rw [show x+12-3=x+9 by omega] at hQ
  have hD2 := Nat.mul_le_mul hD hD
  have hDs := Nat.mul_le_mul_left (x+12) hD
  have hQs := Nat.mul_le_mul_left (x+12) hQ
  nlinarith [Nat.zero_le (x^2),Nat.zero_le (x^3),Nat.zero_le (x^4)]

theorem quadratic_case_one {s D K Q : ℕ}
    (hs : 11≤s) (hD : s*s≤D+2*s+1)
    (hK : K≤2*s*(s-3)+2)
    (hpair : Q+2*K*(s*(s-3))≤K*(K+3))
    (hcauchy : D^2+(s+1)*D≤(s+1)*Q) : False := by
  have hmul := Nat.mul_le_mul_left K hK
  have hQ : Q≤5*(2*s*(s-3)+2) := by nlinarith
  obtain ⟨x,hx⟩ : ∃ x,s=x+11 := ⟨s-11,by omega⟩
  subst s
  rw [show x+11-3=x+8 by omega] at hQ
  have hD' : x*x+20*x+98≤D := by nlinarith
  have hD2 := Nat.mul_le_mul hD' hD'
  have hDs := Nat.mul_le_mul_left (x+12) hD'
  have hQs := Nat.mul_le_mul_left (x+12) hQ
  nlinarith [Nat.zero_le (x^2),Nat.zero_le (x^3),Nat.zero_le (x^4)]

#print axioms gap_cauchy
#print axioms quadratic_native_form
#print axioms quadratic_case_zero
#print axioms quadratic_case_one
end LeanCH.BR.DotClonePairCompletion
