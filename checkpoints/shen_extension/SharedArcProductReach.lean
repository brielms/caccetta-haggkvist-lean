import checkpoints.shen_extension.SharedArcIntervalPuncture

namespace LeanCH.BR.Closure.SharedArcProductReach
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights SharedArcIntervalPuncture

/-- Every pair of sets larger than k contains a related pair. For a
puncture the relation is reachability in at most q-2 steps. -/
def Meets {α : Type*} (R : α → α → Prop) (k : ℕ) : Prop :=
  ∀S T : Finset α,k<S.card → k<T.card → ∃x∈S,∃y∈T,R x y

/-- A single orbit of qk+1 labels forces a positive forward displacement
of at most (q-2)k between heavy sets, except at an overlapping label
when both sets have exactly k+1 members. -/
theorem orbit_overlap {α : Type*} [Fintype α] [DecidableEq α] {q k : ℕ} (hq : 3≤q) (hk : 0<k)
    (size : Fintype.card α=q*k+1) (f : Equiv.Perm α) (cyclic : ∀x y : α,∃m,(f : α→α)^[m] x=y)
    {S T : Finset α} (hs : k<S.card) (ht : k<T.card)
    (no : ∀x∈S,∀y∈T,∀m,0<m → m≤(q-2)*k → (f : α→α)^[m] x≠y) :
    S.card=k+1 ∧ T.card=k+1 ∧ ∃x∈S,x∈T := by
  classical
  let L := (q-2)*k
  have split : q*k=L+2*k := by dsimp [L]; rw [←Nat.add_mul,show q-2+2=q by omega]
  have lp : 0<L := Nat.mul_pos (by omega) hk
  obtain ⟨s,ss⟩ := card_pos.mp (show 0<S.card by omega)
  obtain ⟨t,tt⟩ := card_pos.mp (show 0<T.card by omega)
  have budget (A : Finset α) {l : ℕ} (an : A.Nonempty)
      (out : ∀y∈T,y∉band (f : α→α) A l) : T.card+(A.card+l) ≤ q*k+1 := by
    have grow := band_growth (subset_univ A) an (fun x _ y _ => cyclic x y)
      (mem_univ t) (out t tt)
    have dis := disjoint_left.mpr out
    have lim := card_le_card (subset_univ (T∪band (f : α→α) A l))
    rw [card_union_of_disjoint dis,card_univ,size] at lim
    omega
  have shifted := budget (S.image f) (l:=L-1) ⟨f s,mem_image_of_mem _ ss⟩ (by
    intro y yt hit
    obtain ⟨v,hv,m,le,eq⟩ := in_band.mp hit
    obtain ⟨x,xs,rfl⟩ := mem_image.mp hv
    exact no x xs y yt (m+1) (by omega) (by change m+1≤L; omega)
      (by rw [Function.iterate_succ_apply]; exact eq))
  rw [card_image_of_injective _ f.injective] at shifted
  refine ⟨by omega,by omega,?_⟩
  by_contra! apart
  have plain := budget S (l:=L) ⟨s,ss⟩ (by
    intro y yt hit
    obtain ⟨x,xs,m,le,eq⟩ := in_band.mp hit
    cases m with
    | zero =>
      have xy : x=y := eq
      exact apart x xs (xy.symm ▸ yt)
    | succ m => exact no x xs y yt (m+1) (by omega) le eq)
  omega

private def fiber {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β]
    (S : Finset (α×β)) (i : α) := univ.filter fun y : β => (i,y)∈S

private theorem project_heavy {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β]
    (S : Finset (α×β)) {k d} (big : k*Fintype.card β+d<S.card) : k<(S.image Prod.fst).card := by
  by_contra! low
  have lim : S⊆(S.image Prod.fst) ×ˢ (univ : Finset β) :=
    fun p hp => mem_product.mpr ⟨mem_image_of_mem _ hp,mem_univ _⟩
  have bound := card_le_card lim
  rw [card_product,card_univ] at bound
  have cap := Nat.mul_le_mul_right (Fintype.card β) low
  omega

private theorem fiber_heavy {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β]
    (S : Finset (α×β)) {k d} (big : k*Fintype.card β+d<S.card)
    (count : (S.image Prod.fst).card=k+1) {i} (hit : i∈S.image Prod.fst) : d<(fiber S i).card := by
  let A := S.image Prod.fst
  have sub : S⊆((A.erase i) ×ˢ (univ : Finset β)) ∪ (({i} : Finset α) ×ˢ fiber S i) := by
    rintro ⟨x,y⟩ xy
    by_cases h : x=i
    · subst x; exact mem_union_right _ (mk_mem_product (mem_singleton_self _) (mem_filter.mpr ⟨mem_univ _,xy⟩))
    · exact mem_union_left _ (mk_mem_product (mem_erase.mpr ⟨h,mem_image_of_mem Prod.fst xy⟩) (mem_univ _))
  have bound := (card_le_card sub).trans (card_union_le ..)
  have rem : (A.erase i).card=k := by rw [card_erase_of_mem hit,count]; simp
  simp only [card_product,rem,card_univ,card_singleton,one_mul] at bound
  omega

/-- An outer interval order preserves the heavy-set reach law of any
inner relation. The output has the same form as the input and can be
used as the next inner factor. -/
theorem lex_step {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {q k d : ℕ} (hq : 3≤q) (hk : 0<k) (size : Fintype.card α=q*k+1)
    (f : Equiv.Perm α) (cyclic : ∀x y : α,∃m,(f : α→α)^[m] x=y)
    {inner : β → β → Prop} (law : Meets inner d) (R : (α×β) → (α×β) → Prop)
    (outerLift : ∀i j : α,∀m,0<m → m≤(q-2)*k → (f : α→α)^[m] i=j →
      ∀x y : β,R (i,x) (j,y))
    (innerLift : ∀i x y,inner x y → R (i,x) (i,y)) : Meets R (k*Fintype.card β+d) := by
  classical
  intro S T hs ht
  by_contra! miss
  have no (i) (si : i∈S.image Prod.fst) (j) (tj : j∈T.image Prod.fst)
      (m) (pos : 0<m) (le : m≤(q-2)*k) (eq : (f : α→α)^[m] i=j) : False := by
    obtain ⟨⟨i,x⟩,hx,rfl⟩ := mem_image.mp si
    obtain ⟨⟨j,y⟩,hy,rfl⟩ := mem_image.mp tj
    exact miss _ hx _ hy (outerLift i j m pos le eq x y)
  obtain ⟨sc,tc,i,si,ti⟩ := orbit_overlap hq hk size f cyclic (project_heavy S hs) (project_heavy T ht) no
  obtain ⟨x,sx,y,ty,edge⟩ := law _ _ (fiber_heavy S hs sc si) (fiber_heavy T ht tc ti)
  exact miss _ (mem_filter.mp sx).2 _ (mem_filter.mp ty).2 (innerLift i x y edge)

#print axioms lex_step

/-- Transport the law across an actual labelling of the puncture. -/
theorem relabel {α β : Type*} [DecidableEq α] [DecidableEq β] {k} {R : α → α → Prop}
    {P : β → β → Prop} (e : α ≃ β) (law : Meets R k)
    (lift : ∀x y,R x y → P (e x) (e y)) : Meets P k := by
  intro S T hs ht
  obtain ⟨x,sx,y,ty,edge⟩ := law (S.image e.symm) (T.image e.symm)
    (by simpa only [card_image_of_injective _ e.symm.injective] using hs)
    (by simpa only [card_image_of_injective _ e.symm.injective] using ht)
  obtain ⟨x,hx,rfl⟩ := mem_image.mp sx
  obtain ⟨y,hy,rfl⟩ := mem_image.mp ty
  exact ⟨x,hx,y,hy,by simpa using lift _ _ edge⟩

theorem interval_base {α : Type*} [Fintype α] [DecidableEq α] {q k : ℕ}
    (hq : 3≤q) (hk : 0<k) (size : Fintype.card α=q*k+1)
    (f : Equiv.Perm α) (cyclic : ∀x y : α,∃m,(f : α→α)^[m] x=y) :
    Meets (fun x y => ∃m≤(q-2)*k,(f : α→α)^[m] x=y) k := by
  intro S T hs ht
  by_contra! miss
  obtain ⟨_,_,i,si,ti⟩ := orbit_overlap hq hk size f cyclic hs ht
    (fun x xs y yt m _ le => miss x xs y yt m le)
  exact miss i si i ti 0 (Nat.zero_le _) rfl

/-- A positive outer displacement can finish at any label in its final
block by subdividing the displacement into at most r genuine arcs. -/
theorem outer_walk {q n k} (X : Model q n) {α β : Type*} (f : α → α)
    (label : α×β → X.V)
    (jump : ∀i x y,∀j,0<j → j≤k → X.D (label (i,x)) (label (f^[j] i,y))=true)
    (i : α) (x y : β) {r m : ℕ} (pos : 0<m) (le : m≤r*k) :
    ∃l≤r,Walk X.D X.V (label (i,x)) (label (f^[m] i,y)) l := by
  induction r generalizing m with
  | zero => simp at le; omega
  | succ r ih =>
    by_cases early : m≤r*k
    · obtain ⟨l,lo,p⟩ := ih pos early; exact ⟨l,by omega,p⟩
    by_cases one : m≤k
    · exact ⟨1,by omega,.step (label _).property (jump i x y m pos one) (.refl _)⟩
    have left : 0<m-k := by omega
    have lim : m-k≤r*k := by rw [Nat.succ_mul] at le; omega
    obtain ⟨l,lo,p⟩ := ih left lim
    have hk : 0<k := by
      by_contra! hz
      have zero : k=0 := by omega
      simp [zero] at le
      omega
    have arc := jump (f^[m-k] i) y y k hk le_rfl
    rw [←Function.iterate_add_apply,show k+(m-k)=m by omega] at arc
    exact ⟨l+1,by omega,p.snoc (label _).property arc⟩

/-- A puncture satisfying the reach law is excluded from the actual least
source even when all arcs incident to the omitted vertex are arbitrary. -/
theorem excludes {q n k} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (a : X.V) (U : Finset X.V) (size : U.card=q*k+1)
    (rows : ∀i : X.V,i≠a → (U.filter (fun j : X.V => X.D i j=true)).card≤k)
    (cols : ∀i : X.V,i≠a → (U.filter (fun j : X.V => X.D j i=true)).card≤k)
    (law : Meets (fun i j : U => j.val.val∈ball X.D X.V i.val.val (q-2)) k) : False := by
  classical
  obtain ⟨hc,ht⟩ := degree_floors X small a U size rows cols
  let C := (univ : Finset U).filter (fun i : U => X.D a i.val=true)
  let T := (univ : Finset U).filter (fun i : U => X.D i.val a=true)
  have count (p : X.V → Bool) :
      ((univ : Finset U).filter (fun i : U => p i.val=true)).card=(U.filter (fun j => p j=true)).card := by
    let S := (univ : Finset U).filter (fun i : U => p i.val=true)
    have eq : S.image Subtype.val=U.filter (fun j => p j=true) := by
      ext j
      constructor
      · intro h; obtain ⟨i,hi,rfl⟩ := mem_image.mp h
        exact mem_filter.mpr ⟨i.property,(mem_filter.mp hi).2⟩
      · intro h; obtain ⟨ju,pj⟩ := mem_filter.mp h
        exact mem_image.mpr ⟨⟨j,ju⟩,mem_filter.mpr ⟨mem_univ _,pj⟩,rfl⟩
    rw [←eq,card_image_of_injective _ Subtype.val_injective]
  obtain ⟨h,head,t,parent,hit⟩ := law C T
    (lt_of_lt_of_eq hc (count (fun j => X.D a j)).symm)
    (lt_of_lt_of_eq ht (count (fun j => X.D j a)).symm)
  exact SharedArcPunctureExpansion.far_parent X hq a h.val t.val (mem_filter.mp head).2 (mem_filter.mp parent).2 hit

#print axioms excludes
#print axioms outer_walk
#print axioms interval_base

/-- A graph-level consumer for a product-labelled puncture. Outer arc
rectangles are actual one-step arcs, and the inner supplier only has to
realize its relation inside each copy within the allowed radius. -/
theorem lex_excludes {q n k d} (X : Model q n) (hq : 3≤q) (small : SmallerSmallRow q X.V.card)
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (hk : 0<k) (outerSize : Fintype.card α=q*k+1) (f : Equiv.Perm α)
    (cyclic : ∀x y : α,∃m,(f : α→α)^[m] x=y) (a : X.V) (U : Finset X.V) (labels : α×β ≃ U)
    (size : U.card=q*(k*Fintype.card β+d)+1)
    (rows : ∀i : X.V,i≠a → (U.filter (fun j : X.V => X.D i j=true)).card≤k*Fintype.card β+d)
    (cols : ∀i : X.V,i≠a → (U.filter (fun j : X.V => X.D j i=true)).card≤k*Fintype.card β+d)
    (jump : ∀i x y,∀j,0<j → j≤k →
      X.D (labels (i,x)).val (labels ((f : α→α)^[j] i,y)).val=true)
    {inner : β → β → Prop} (law : Meets inner d)
    (innerLift : ∀i x y,inner x y →
      (labels (i,y)).val.val∈ball X.D X.V (labels (i,x)).val.val (q-2)) : False := by
  let P := fun i j : U => j.val.val∈ball X.D X.V i.val.val (q-2)
  apply excludes X (by omega) small a U size rows cols
  apply relabel (P:=P) labels (R:=fun x y => P (labels x) (labels y)) _ (fun _ _ h => h)
  apply lex_step hq hk outerSize f cyclic law _ _ innerLift
  intro i j m pos le eq x y
  obtain ⟨l,lo,path⟩ := outer_walk X f (fun v => (labels v).val) jump i x y pos le
  subst j
  exact mem_ball.mpr ⟨(labels _).val.property,l,lo,path⟩

#print axioms lex_excludes
end LeanCH.BR.Closure.SharedArcProductReach
