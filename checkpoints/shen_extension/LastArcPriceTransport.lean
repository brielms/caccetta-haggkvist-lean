import checkpoints.shen_extension.LastArcGatePayment

namespace LeanCH.BR.Closure.LastArcPriceTransport
open Finset BRq2 BRq3 BR45 WeightedSD FiniteCutInverse FirstPacketBarrier MarkedCyclePeeling
open OmittedCycleProgress LastArcGatePayment SharedArcBarrier SharedArcComponentExchange ShortestCycleWeights

/-- Marginals divided by their own strict margins decrease under an inclusion
of graphs on this support. They are row and column sums of the respective inverses. -/
private theorem marginals {q n D G x ρ d w π c} (X : Model q n) (small : SmallerSmallRow q X.V.card)
    (fg : QFree G X.V q) (fd : QFree D X.V q)
    (sub : ∀i∈X.V,∀j∈X.V,G i j=true → D i j=true)
    (old : Flat q G X.V x ρ d) (newer : Flat q D X.V w π c) (z : X.V) :
    w z/(c-1)≤x z/(d-1) ∧ π z/(c-1)≤ρ z/(d-1) := by
  obtain ⟨dh,xp,_,xm,rm,xr,rc⟩ := old
  obtain ⟨ch,wp,_,wm,pm,wr,pc⟩ := newer
  obtain ⟨H,ih⟩ := common_inverse_of_smaller_strict small fg ⟨x,xp,xm,fun i hi=>(xr i hi) ▸ dh⟩
  obtain ⟨K,ik⟩ := common_inverse_of_smaller_strict small fd ⟨w,wp,wm,fun i hi=>(wr i hi) ▸ ch⟩
  have order := graph_inverse_antitone sub ih ik
  have a := graph_inverse_transport ih x ρ xp xm rm d dh xr rc
  have b := graph_inverse_transport ik w π wp wm pm c ch wr pc
  have dc : (0:ℝ)<(d:ℝ)-1 := by exact_mod_cast sub_pos.mpr dh
  have cc : (0:ℝ)<(c:ℝ)-1 := by exact_mod_cast sub_pos.mpr ch
  have scale (g y t : ℝ) (pos : 0<g) (eq : g*t=y) : y/g=t := (div_eq_iff pos.ne').mpr (by linarith only [eq])
  have one : (w z:ℝ)/((c:ℝ)-1)≤(x z:ℝ)/((d:ℝ)-1) := by
    rw [scale _ _ _ cc (b.1 z),scale _ _ _ dc (a.1 z)]
    exact sum_le_sum (fun j _=>order z j)
  have two : (π z:ℝ)/((c:ℝ)-1)≤(ρ z:ℝ)/((d:ℝ)-1) := by
    rw [scale _ _ _ cc (b.2.1 z),scale _ _ _ dc (a.2.1 z)]
    exact sum_le_sum (fun i _=>order i z)
  exact_mod_cast And.intro one two

private theorem subset_path {q n wanted} {X : Model q n} {A P : Stage X}
    (path : Relation.ReflTransGen (Edge X wanted) A P) : A.cycles⊆P.cycles := by
  induction path with
  | refl => exact Subset.rfl
  | tail _ step ih =>
    obtain ⟨M,_,_,sub,_⟩ := step
    exact ih.trans (fun _ h=>sub (mem_insert_of_mem h))

private theorem arcs {D F E i j} (sub : F⊆E) (hit : graph D F i j=true) : graph D E i j=true := by
  obtain ⟨M,h⟩ := active.mp hit
  exact active.mpr ⟨M,mem_col.mpr ⟨sub (mem_col.mp h).1,(mem_col.mp h).2⟩⟩

/-- Both prices on the actual last step are bounded by the same isolated
price at the original attachment, after dividing by the two strict margins.
This includes batched restorations in which the two individual prices differ. -/
theorem compare {q n} (X : Model q n) (small : SmallerSmallRow q X.V.card)
    {wanted} {A P C : Stage X} (path : Relation.ReflTransGen (Edge X wanted) A P) (last : Edge X wanted P C)
    (u v : X.V) (hit : graph X.D C.cycles u v=true)
    {w π c} (isolated : Flat q (insertArc (graph X.D A.cycles) u v) X.V w π c)
    (p₁ : (q:ℚ)*A.π u*w v=c-A.value) (p₂ : (q:ℚ)*π u*A.x v=c-A.value) :
    let scale := (P.value-1)*(C.value-1)
    let cap := (c-A.value)/((A.value-1)*(c-1))
    (q:ℚ)*P.π u*C.x v/scale≤cap ∧ (q:ℚ)*C.π u*P.x v/scale≤cap := by
  intro scale cap
  have ap := subset_path path
  obtain ⟨M,_,_,sub,_⟩ := last
  have pc : P.cycles⊆C.cycles := fun _ h=>sub (mem_insert_of_mem h)
  have inc (i j) (ed : insertArc (graph X.D A.cycles) u v i j=true) : graph X.D C.cycles i j=true := by
    by_cases atUV : i=u.val ∧ j=v.val
    · simpa only [atUV.1,atUV.2] using hit
    · exact arcs (ap.trans pc) (by simpa [insertArc,atUV] using ed)
  have cf := PrivateArcEndpoints.graph_free X C.cycles
  have early := marginals X small (PrivateArcEndpoints.graph_free X A.cycles) (PrivateArcEndpoints.graph_free X P.cycles)
    (fun _ _ _ _ h=>arcs ap h) A.flat P.flat
  have late := marginals X small (qfree_sub inc cf) cf (fun i _ j _=>inc i j) isolated C.flat
  have mix {a b a' b' : ℚ} (ha : 0≤a) (hb : 0≤b) (ac : a≤a') (bc : b≤b') :
      (q:ℚ)*(a*b)≤(q:ℚ)*(a'*b') :=
    mul_le_mul_of_nonneg_left (mul_le_mul ac bc hb (ha.trans ac)) (Nat.cast_nonneg q)
  have first := mix (div_nonneg (P.flat.2.2.1 u u.property).le (sub_pos.mpr P.flat.1).le)
    (div_nonneg (C.flat.2.1 v v.property).le (sub_pos.mpr C.flat.1).le) (early u).2 (late v).1
  have second := mix (div_nonneg (C.flat.2.2.1 u u.property).le (sub_pos.mpr C.flat.1).le)
    (div_nonneg (P.flat.2.1 v v.property).le (sub_pos.mpr P.flat.1).le) (late u).2 (early v).1
  constructor
  · dsimp [scale,cap]
    rw [←p₁]
    convert first using 1 <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
  · dsimp [scale,cap]
    rw [←p₂]
    convert second using 1 <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring

/-- One last edge, one original gate, same identified labels, both last-step
prices, and the original attachment's exchange test, all in the same witness. -/
theorem at_gate {q n F B} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (A : Stage X) (same : graph X.D A.cycles=graph X.D (insert B F))
    {ρ d H} (ap : A.π=ρ) (av : A.value=d)
    (inv : CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    (wanted : Family) (ws : wanted⊆family X) :
    wanted⊆A.cycles ∨ ∃P C : Stage X,Relation.ReflTransGen (Edge X wanted) A P ∧ Edge X wanted P C ∧
      wanted⊆C.cycles ∧ ∃M∈wanted,∃u v : X.V,u.val∈M ∧ v.val∈M ∧
      (u.val,v.val)∈CrossValueOmissions.lost (graph X.D C.cycles) (graph X.D P.cycles) X.V ∧
      X.D u v=true ∧ graph X.D (insert B F) u v=false ∧ Bill X F B A.x ρ d H u v ∧
      ∀w π c,Flat q (insertArc (graph X.D (insert B F)) u v) X.V w π c →
      (q:ℚ)*ρ u*w v=c-d → (q:ℚ)*π u*A.x v=c-d →
      let scale := (P.value-1)*(C.value-1)
      let cap := (c-d)/((d-1)*(c-1))
      (q:ℚ)*P.π u*C.x v/scale≤cap ∧ (q:ℚ)*C.π u*P.x v/scale≤cap := by
  rcases rooted X hq small step least stop A same ap av inv wanted ws with done |
    ⟨P,C,path,last,full,M,mw,u,v,um,vm,hit,uv,off,bill⟩
  · exact Or.inl done
  refine Or.inr ⟨P,C,path,last,full,M,mw,u,v,um,vm,hit,uv,off,bill,?_⟩
  intro w π c isolated p₁ p₂
  rw [←same] at isolated
  rw [←ap,←av] at p₁
  rw [←av] at p₂ ⊢
  exact compare X small path last u v (mem_filter.mp hit).2.1 isolated p₁ p₂

#print axioms at_gate

#print axioms compare
end LeanCH.BR.Closure.LastArcPriceTransport
