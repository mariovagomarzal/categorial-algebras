import CategorialAlgebras.Extended.Functor

/-!
# Products of globular categories

The operations of a globular categorial algebra are globular functors out of finite products
of globular categories (Definition `DGlCatAlg` of the draft). The product of a family of globular
categories has, in each dimension, the product of the sets of cells of that dimension, with
every operation computed componentwise.
-/

universe u v

namespace CategorialAlgebras.Extended

open CategoryStruct

variable {Index : Type} [Preorder Index] {J : Type v} {C : J → TypeFamily.{u} Index}

/-- Let $(C^{j})_{j \in J}$ be a family of globular categorial structures with dimensions in
$I$. Their product has, as $k$-cells, the families $(f_j)_{j \in J}$ with $f_j \in C^{j}_k$;
sources, targets and identities are taken componentwise, and $g \circ^{(i)} f$ is defined
exactly when every $g_j \circ^{(i)} f_j$ is, and then is their family.
-/
instance CategoryStruct.pi [∀ j, CategoryStruct Index (C j)] :
    CategoryStruct Index (fun k => (j : J) → C j k) where
  sc h f j := sc h (f j)
  tg h f j := tg h (f j)
  idm h u j := idm h (u j)
  pcomp h g f := ⟨∀ j, sc h (g j) = tg h (f j), fun hh j => g j ♯[h] f j ← hh j⟩
  pcomp_dom := by
    intro k j' h f g
    exact ⟨fun hh => funext hh, fun hh j => congrFun hh j⟩

section Pi

variable [∀ j, CategoryStruct Index (C j)]

lemma pi_sc_is_tg {k i : Index} {h : i < k} {g f : (j : J) → C j k} :
    sc_is_tg (C := fun k => (j : J) → C j k) h g f ↔ ∀ j, sc_is_tg h (g j) (f j) :=
  ⟨fun hh j => congrFun hh j, fun hh => funext hh⟩

end Pi

/-!
### Product of globular categories

If every $C^{j}$ is a globular category with dimensions in $I$, so is their product, since
every axiom holds componentwise. In particular, finite products of globular $n$-categories are
globular $n$-categories, and the empty product is the final one, with a single cell in each
dimension.
-/

instance PreCategory.pi [∀ j, PreCategory Index (C j)] :
    PreCategory Index (fun k => (j : J) → C j k) where
  sckj_compkj_eq_sckj h :=
    funext fun j => PreCategory.sckj_compkj_eq_sckj (pi_sc_is_tg.mp h j)
  tgkj_compkj_eq_tgkj h :=
    funext fun j => PreCategory.tgkj_compkj_eq_tgkj (pi_sc_is_tg.mp h j)
  sckj_idmkj h u := funext fun j => PreCategory.sckj_idmkj h (u j)
  tgkj_idmkj h u := funext fun j => PreCategory.tgkj_idmkj h (u j)
  compkj_idmkj_sckj_eq_id h f := funext fun j => PreCategory.compkj_idmkj_sckj_eq_id h (f j)
  compkj_tgkj_idmkj_eq_id h f := funext fun j => PreCategory.compkj_tgkj_idmkj_eq_id h (f j)
  assoc h₁ h₂ :=
    funext fun j => PreCategory.assoc (pi_sc_is_tg.mp h₁ j) (pi_sc_is_tg.mp h₂ j)

instance Category.pi [∀ j, Category Index (C j)] :
    Category Index (fun k => (j : J) → C j k) where
  scji_sckj_eq_scki h₁ h₂ f := funext fun j => Category.scji_sckj_eq_scki h₁ h₂ (f j)
  scji_tgkj_eq_scki h₁ h₂ f := funext fun j => Category.scji_tgkj_eq_scki h₁ h₂ (f j)
  tgji_tgkj_eq_tgki h₁ h₂ f := funext fun j => Category.tgji_tgkj_eq_tgki h₁ h₂ (f j)
  tgji_sckj_eq_tgki h₁ h₂ f := funext fun j => Category.tgji_sckj_eq_tgki h₁ h₂ (f j)
  sckj_compki_eq_compji_sckj h :=
    funext fun j => Category.sckj_compki_eq_compji_sckj (pi_sc_is_tg.mp h j)
  tgkj_compki_eq_compji_tgkj h :=
    funext fun j => Category.tgkj_compki_eq_compji_tgkj (pi_sc_is_tg.mp h j)
  idmkj_idmji_eq_idmki h₁ h₂ u := funext fun j => Category.idmkj_idmji_eq_idmki h₁ h₂ (u j)
  idmkj_compji_eq_compki_idmkj h :=
    funext fun j => Category.idmkj_compji_eq_compki_idmkj (pi_sc_is_tg.mp h j)
  interchange := by
    intro _ _ _ _ i_lt_j _ _ _ _ h₁ h₂ h₃ h₄
    exact funext fun x => Category.interchange (i_lt_j := i_lt_j) (pi_sc_is_tg.mp h₁ x)
      (pi_sc_is_tg.mp h₂ x) (pi_sc_is_tg.mp h₃ x) (pi_sc_is_tg.mp h₄ x)

end CategorialAlgebras.Extended
