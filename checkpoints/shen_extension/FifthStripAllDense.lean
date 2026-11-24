import checkpoints.shen_extension.FifthStripAllTop
import checkpoints.shen_extension.CommonSuccessorTensor

/-!
# Fifth strip, top order, any parity: the dense-table route

At order `qs` with the rigid balls of `top_rigid` and the universal order `qs`
(no host of order `qs - 1`), the common-successor tensor bound of
`ShenCommonSuccessor.dense_table_bound` contradicts the prefix budget once the
decidable arithmetic `DenseOK a g e` holds for some table parameters `g`, `e`.
Generic in `a`; this replaces the old threshold `52 ≤ a` of `mixed_top_false`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.FifthStripAll
open Finset BRq2 BRq3 BR45 ShenFirstStrip

/-- Arithmetic side conditions of the dense table at shift `a`. -/
def DenseOK (a g e : ℕ) : Prop :=
  2*g < a+6 ∧ 2*((a+7)*(a+4))+1+2*g < (a+6)+2*((a+7)*(a+3)+1)+2*(e+1) ∧
    a+3+1+e+1 ≤ 2*a+7 ∧ 3*e ≤ 2*a+7 ∧
    ∀ x ∈ range (a+8), (g+1)*(e+1) + (a+7)*(a+3) + x*(a+6) < (g+1)*x + (2*a+7)*(a+7)

instance (a g e : ℕ) : Decidable (DenseOK a g e) := by unfold DenseOK; infer_instance

theorem top_false_dense {a g e : ℕ} (ha : 2 ≤ a) (L : LedgerFloors a)
    (tc : Top a ((2*a+7)*(a+7)))
    (order : MixedRadiusCompletion.Order (2*a+7) (a+7) ((2*a+7)*(a+7)))
    (ok : DenseOK a g e)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V (2*a+7))
    (hm : ∀ v ∈ V, a+7 ≤ (outN D V v).card) (ne : V.Nonempty)
    (size : V.card = (2*a+7)*(a+7)) : False := by
  obtain ⟨hg, hcut, hret, htri, fin⟩ := ok
  have rig := top_rigid ha L tc hf hm size
  have pair : (a+3)+(a+4) ≤ 2*a+7 := by omega
  have e5 : (2*a+7)*(a+7) = (a+7)*(a+3)+(a+7)*(a+4) := by ring
  have heq : (a+7)*(a+3)+1 + (a+7)*(a+4) = V.card + 1 := by omega
  have hi : ∀ v ∈ V, (a+7)*(a+3)+1 ≤ (ball D V v (a+3)).card := fun v hv => (rig v hv).1.ge
  have hj : ∀ v ∈ V, (a+7)*(a+4) ≤ (ball D V v (a+4)).card := fun v hv => (rig v hv).2.ge
  have total (x) (hx : x ∈ V) (y) (hy : y ∈ V) :
      y ∈ ball D V x (a+4) ∨ x ∈ ball D V y (a+4) := by
    by_cases h : y ∈ ball D V x (a+3)
    · exact Or.inl (ball_mono_radius (by omega) h)
    · have comp := two_balls_boundary_complement hf pair hi hj heq hx
      have back : y ∈ reverseBall D V x (a+4) := by
        rw [comp]; exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hy, h⟩)
      exact Or.inr (Finset.mem_filter.mp back).2
  obtain ⟨u, hu⟩ := ne
  let S := ball D V u (a+3) \ ball D V u (a+2)
  let T := ball D V u (a+4) \ ball D V u (a+3)
  let U := (ball D V u (a+3)).erase u
  let H := ∑ x ∈ S, (T \ outN D T x).card
  have hS : S.card + (ball D V u (a+2)).card = (ball D V u (a+3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hT : T.card + (ball D V u (a+3)).card = (ball D V u (a+4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hU : U.card + 1 = (ball D V u (a+3)).card := Finset.card_erase_add_one (self_mem_ball hu)
  have hR := (rig u hu).1
  have hN := (rig u hu).2
  have e3 : (a+7)*(a+4) = (a+7)*(a+3) + (a+7) := by ring
  have hTc : T.card = a+6 := by omega
  have hin := L.f2 D V hf hm u hu
  have e2 : (a+7)*(a+3) = (a+7)*(a+2) + (a+7) := by ring
  have hSc : S.card ≤ a+7 := by omega
  have retained := minOut_prefix_erase (d := 1) hf hu (by omega : (a+3)+1 ≤ 2*a+7) hm
    (show 1 + T.card ≤ a+7 by omega)
  have budget := PrefixTensor.same_degree_missing_capacity (k := a+2) hf hm hu (by omega)
    (fun F W h m n => order F W h m n) (by omega) retained
  change (2*a+7)*(a+7) + H ≤ U.card + S.card * T.card at budget
  rw [hTc] at budget
  have hSV : S ⊆ V := Finset.sdiff_subset.trans ball_subset
  have hTV : T ⊆ V := Finset.sdiff_subset.trans ball_subset
  have obs := ShenCommonSuccessor.dense_table_bound (r := a+3) (g := g) (e := e)
    hf hSV hTV (by omega) (fun z hz => (rig z (hTV hz)).1.ge)
    (fun x hx => (rig x (hSV hx)).2.le) (fun x hx y hy => total x (hSV hx) y (hSV hy))
    (by omega) (by rw [hTc]; exact hcut) hret htri
  change (g+1)*S.card ≤ (g+1)*(e+1) + H at obs
  have f := fin S.card (mem_range.mpr (by omega))
  have hUc : U.card = (a+7)*(a+3) := by omega
  rw [hUc] at budget
  have comm : S.card * (a+6) = S.card * (a+6) := rfl
  omega

#print axioms top_false_dense
end LeanCH.BR.FifthStripAll
