import CategorialAlgebras.ChangeOfSignature.OmegaCompatibility
import CategorialAlgebras.Omega.Equivalence
import CategorialAlgebras.Preliminaries.Grothendieck

/-!
# Change of signature commutes with graduation and unification in dimension $\omega$

Graduation and unification in dimension $\omega$ are not induced by generalized
hep-derivors; their compatibility with the change of signature is proved from their
explicit descriptions. Graduation of a reduct is the reduct of the graduation: in both, the
cells of sort $(k,s)$ are the $k$-cells of sort $\varphi(s)$ and $\sigma_k$ acts as the term
operation of $c(\sigma)$. Unification of a reduct is the reduct of the unification: both have
the $\omega$-cells of sort $\varphi(s)$ as cells of sort $s$, and the operations are computed on
representatives at a common finite level. These are equalities of functors between the
split indexed categories of reducts.

Transported along the identifications of the induced functors with the reducts, they give
$\mathrm{Gd}^{(\omega)}_{\Sigma}\circ\mathbf{c}^{(\omega)\ast}_{\mathfrak{gd}}\cong
\mathbf{c}^{\mathrm{htg}(\omega)\ast}_{\mathfrak{gd}}\circ\mathrm{Gd}^{(\omega)}_{\Lambda}$ and
$\mathrm{Uf}^{(\omega)}_{\Sigma}\circ\mathbf{c}^{\mathrm{htg}(\omega)\ast}_{\mathfrak{gd}}\cong
\mathbf{c}^{(\omega)\ast}_{\mathfrak{gd}}\circ\mathrm{Uf}^{(\omega)}_{\Lambda}$.
-/

universe u v w

namespace CategorialAlgebras.ChangeOfSignature

open CategoryTheory Omega

variable {S T : Type u} {sig : Signature.{u, v} S} {tau : Signature.{u, v} T}

/-! ## Graduation -/

/-- In the graduation of a homogeneous algebra, term functors act on the underlying cells as
in the original algebra. -/
theorem graduated_termFunctor_val (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ tau)
    {R : Type u} (φ : R → T) (a : List R) {t} (P : Term tau (Word.MappedVariables φ a) t)
    (k : ℕ) (x : Word.Family (fun r => (graduatedAlgebra B).carrier (k, φ r)) a) :
    (((graduatedAlgebra B).termFunctor φ a P).toFun k x).val =
      (B.termFunctor φ a P).toFun (fun j => (x j).val) := by
  induction P with
  | var y =>
    obtain ⟨j, h⟩ := y
    cases h
    rfl
  | app τ t ih =>
    change (B.op τ).toFun _ = (B.op τ).toFun _
    exact congrArg (B.op τ).toFun (funext ih)

/-- The graduation of a reduct is the reduct of the graduation. -/
theorem graduatedAlgebra_reduct (c : Derivor sig tau)
    (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ tau) :
    graduatedAlgebra (homogeneousReduct c B) = heterogeneousReduct c (graduatedAlgebra B) := by
  unfold heterogeneousReduct
  change Heterogeneous.CategorialAlgebra.mk _ _ = Heterogeneous.CategorialAlgebra.mk _ _
  congr 1
  funext a s σ
  apply Heterogeneous.Functor.ext
  funext k x
  apply Subtype.ext
  exact (graduated_termFunctor_val B c.sortMap a (c.image σ) k x).symm

/-- Graduation in dimension $\omega$ commutes strictly with the reduct functors. -/
theorem graduation_reduct (c : Derivor sig tau) :
    homogeneousOmegaReductFunctor.{u, v, w} c ⋙ graduationFunctor sig =
      graduationFunctor tau ⋙ heterogeneousReductFunctor ℕ c :=
  Functor.hext (fun B => graduatedAlgebra_reduct c B.obj) (fun _ _ _ =>
    heterogeneous_hom_heq (graduatedAlgebra_reduct c _) (graduatedAlgebra_reduct c _)
      _ _ HEq.rfl)

/-- Graduation in dimension $\omega$ commutes with change of signature:
$\mathrm{Gd}^{(\omega)}_{\Sigma}\circ\mathbf{c}^{(\omega)\ast}_{\mathfrak{gd}}\cong
\mathbf{c}^{\mathrm{htg}(\omega)\ast}_{\mathfrak{gd}}\circ\mathrm{Gd}^{(\omega)}_{\Lambda}$.

**Formally weaker** than the informal statement. Informally, the two functors are equal; here the
carriers of transformed algebras are subtypes of cells, so the equality becomes a natural
isomorphism that is the identity on elements. -/
noncomputable def omegaGraduationFunctorChange (c : Derivor sig tau) :
    homogeneousOmegaFunctor.{u, v, w} c ⋙ graduationFunctor sig ≅
      graduationFunctor tau ⋙ heterogeneousFunctor ℕ c :=
  Functor.isoWhiskerRight (homogeneousOmegaFunctorReductIso c) _ ≪≫
    eqToIso (graduation_reduct c) ≪≫
    Functor.isoWhiskerLeft _ (heterogeneousFunctorReductIso ℕ c).symm

/-! ## Unification -/

/-- Morphisms of a full subcategory between equal objects are heterogeneously equal when
their underlying morphisms are. -/
theorem fullSubcategory_hom_heq {C : Type*} [Category C] {P : ObjectProperty C}
    {A A' B B' : P.FullSubcategory} (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : HEq f.hom g.hom) : HEq f g := by
  subst hA hB
  cases f
  cases g
  cases h
  rfl

/-- In the unification of a heterogeneous algebra, term functors act on classes represented
at a common level as the term functors of the original algebra at that level. -/
theorem unified_termFunctor_cellIn (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} tau)
    {R : Type u} (φ : R → T) (a : List R) {t} (P : Term tau (Word.MappedVariables φ a) t)
    (n : ℕ) (y : Word.Family (fun r => B.carrier (n, φ r)) a) :
    ((unifiedAlgebra B).termFunctor φ a P).toFun (fun j => cellIn B n _ (y j)) =
      cellIn B n t ((B.termFunctor φ a P).toFun n y) := by
  induction P with
  | var z =>
    obtain ⟨j, h⟩ := z
    cases h
    rfl
  | app τ ts ih =>
    change unifiedBase B τ (fun j => ((unifiedAlgebra B).termFunctor φ a (ts j)).toFun _) = _
    rw [show (fun j => ((unifiedAlgebra B).termFunctor φ a (ts j)).toFun
        (fun j => cellIn B n _ (y j))) =
      (fun j => cellIn B n _ ((B.termFunctor φ a (ts j)).toFun n y)) from funext ih]
    exact unifiedBase_in B τ _

/-- The unification of a reduct is the reduct of the unification. -/
theorem unifiedAlgebra_reduct (c : Derivor sig tau)
    (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} tau) :
    unifiedAlgebra (heterogeneousReduct c B) = homogeneousReduct c (unifiedAlgebra B) := by
  unfold homogeneousReduct
  change Homogeneous.CategorialAlgebra.mk _ _ = Homogeneous.CategorialAlgebra.mk _ _
  congr 1
  funext a s σ
  apply Homogeneous.Functor.ext
  funext x
  obtain ⟨n, -, ys, hy⟩ := cell_cover B (fun j => c.sortMap (a.get j)) x 0
  have hx : (fun j => cellIn B n _ (ys j)) = x := funext hy
  rw [← hx]
  refine (unifiedBase_in (heterogeneousReduct c B) σ ys).trans ?_
  exact (unified_termFunctor_cellIn B c.sortMap a (c.image σ) n ys).symm

/-- Unification in dimension $\omega$ commutes strictly with the reduct functors. -/
theorem unification_reduct (c : Derivor sig tau) :
    heterogeneousReductFunctor.{0, u, u, v, v, w} ℕ c ⋙ unificationFunctor sig =
      unificationFunctor tau ⋙ homogeneousOmegaReductFunctor c := by
  apply Functor.hext
  · intro B
    exact ObjectProperty.FullSubcategory.ext (unifiedAlgebra_reduct c B)
  · intro A B f
    apply fullSubcategory_hom_heq (ObjectProperty.FullSubcategory.ext (unifiedAlgebra_reduct c A))
      (ObjectProperty.FullSubcategory.ext (unifiedAlgebra_reduct c B))
    exact hom_heq (unifiedAlgebra_reduct c A) (unifiedAlgebra_reduct c B) _ _ HEq.rfl

/-- Unification in dimension $\omega$ commutes with change of signature:
$\mathrm{Uf}^{(\omega)}_{\Sigma}\circ\mathbf{c}^{\mathrm{htg}(\omega)\ast}_{\mathfrak{gd}}\cong
\mathbf{c}^{(\omega)\ast}_{\mathfrak{gd}}\circ\mathrm{Uf}^{(\omega)}_{\Lambda}$.

**Formally weaker** than the informal statement. Informally, the two functors are equal; here the
carriers of transformed algebras are subtypes of cells, so the equality becomes a natural
isomorphism that is the identity on elements. -/
noncomputable def omegaUnificationFunctorChange (c : Derivor sig tau) :
    heterogeneousFunctor.{0, u, v, w} ℕ c ⋙ unificationFunctor sig ≅
      unificationFunctor tau ⋙ homogeneousOmegaFunctor c :=
  Functor.isoWhiskerRight (heterogeneousFunctorReductIso ℕ c) _ ≪≫
    eqToIso (unification_reduct c) ≪≫
    Functor.isoWhiskerLeft _ (homogeneousOmegaFunctorReductIso c).symm

/-! ## Transformations of indexed categories -/

/-- Graduation in dimension $\omega$ is a natural transformation between the split indexed
categories of homogeneous and heterogeneous $\omega$-categorial algebras. -/
noncomputable def omegaGraduationIndexed :
    homogeneousOmegaIndexed.{u, v, w} ⟶ heterogeneousIndexed.{0, u, v, w} ℕ where
  app sig := (graduationFunctor sig.unop.symbol).toCatHom
  naturality _ _ e := congrArg Functor.toCatHom (graduation_reduct e.unop)

/-- Unification in dimension $\omega$ is a natural transformation between the split indexed
categories of heterogeneous and homogeneous $\omega$-categorial algebras. -/
noncomputable def omegaUnificationIndexed :
    heterogeneousIndexed.{0, u, v, w} ℕ ⟶ homogeneousOmegaIndexed.{u, v, w} where
  app sig := (unificationFunctor sig.unop.symbol).toCatHom
  naturality _ _ e := congrArg Functor.toCatHom (unification_reduct e.unop)

/-- Graduation in dimension $\omega$ acts on algebras of different signatures: it extends to
a functor between the Grothendieck constructions that commutes with the projections to the
category of signatures. -/
noncomputable def omegaGraduationGrothendieck :
    SplitIndexedCategory.Grothendieck homogeneousOmegaIndexed.{u, v, w} ⥤
      SplitIndexedCategory.Grothendieck (heterogeneousIndexed.{0, u, v, w} ℕ) :=
  SplitIndexedCategory.map omegaGraduationIndexed

/-- Unification in dimension $\omega$ acts on algebras of different signatures: it extends
to a functor between the Grothendieck constructions that commutes with the projections to
the category of signatures. -/
noncomputable def omegaUnificationGrothendieck :
    SplitIndexedCategory.Grothendieck (heterogeneousIndexed.{0, u, v, w} ℕ) ⥤
      SplitIndexedCategory.Grothendieck homogeneousOmegaIndexed.{u, v, w} :=
  SplitIndexedCategory.map omegaUnificationIndexed

end CategorialAlgebras.ChangeOfSignature
