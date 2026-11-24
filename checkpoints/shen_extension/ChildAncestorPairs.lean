import checkpoints.shen_extension.SharedLayerBarrier
import checkpoints.shen_extension.CHForwardCatalog

namespace LeanCH.BR.ChildAncestorPairs
open Finset BRq2 BRq3 BR45

/-- Reach data for a single ordered pair of roots. The two tested radii,
the two child radii and the length of the ancestral path may all differ. -/
@[aesop safe forward (immediate := [safe,ux,wx,back,forward,reverse,budget,early])
  (rule_sets := [CHGraphFamilies])]
theorem missing_pair {D : CH.Digraph} {V : Finset ℕ} {q u w x z i j a b ℓ : ℕ}
    (safe : QFree D V q) (ux : x∈outN D V u) (wx : x∈outN D V w)
    (back : Walk D V x z ℓ)
    (forward : w∈ball D V u i → w∈ball D V z a)
    (reverse : u∈ball D V w j → u∈ball D V x b)
    (budget : ℓ+a+1≤q) (early : b+1≤q) :
    w∉ball D V u i ∧ u∉ball D V w j := by
  constructor
  · intro hit
    obtain ⟨_,k,fit,road⟩ := mem_ball.mp (forward hit)
    exact safe x _ (by omega) (by omega) ((back.append road).snoc (outN_subset wx) (mem_outN.mp wx).2)
  · intro hit
    obtain ⟨_,k,fit,road⟩ := mem_ball.mp (reverse hit)
    exact safe x _ (by omega) (by omega) (road.snoc (outN_subset ux) (mem_outN.mp ux).2)

/-- Each distinct eligible physical head consumes a distinct missing
partner at this root. A child may have several owners. -/
@[aesop safe forward (immediate := [safe,heads,supply,rows,forward,reverse,paths,budget,early])
  (rule_sets := [CHGraphFamilies])]
theorem missing_partners {D V q u z i j a b h} {S X : Finset ℕ} (child : ℕ→ℕ)
    (safe : QFree D V q) (heads : X⊆outN D V u) (supply : X⊆S.image child)
    (rows : ∀w∈S,child w∈outN D V w)
    (forward : ∀w∈S,child w∈X → w∈ball D V u i → w∈ball D V z a)
    (reverse : ∀w∈S,child w∈X → u∈ball D V w j → u∈ball D V (child w) b)
    (paths : ∀x∈X,z∈ball D V x h) (budget : h+a+1≤q) (early : b+1≤q) :
    X.card≤(S.filter (fun w=>w∉ball D V u i ∧ u∉ball D V w j)).card := by
  classical
  let M := S.filter (fun w=>w∉ball D V u i ∧ u∉ball D V w j)
  have coverage : X⊆M.image child := by
    intro x xm
    obtain ⟨w,ws,rfl⟩ := mem_image.mp (supply xm)
    obtain ⟨_,k,fit,road⟩ := mem_ball.mp (paths _ xm)
    have missed := missing_pair safe (heads xm) (rows w ws) road (forward w ws xm)
      (reverse w ws xm) (by omega) early
    exact mem_image.mpr ⟨w,mem_filter.mpr ⟨ws,missed⟩,rfl⟩
  exact (card_le_card coverage).trans card_image_le

#print axioms missing_pair
#print axioms missing_partners
end LeanCH.BR.ChildAncestorPairs
