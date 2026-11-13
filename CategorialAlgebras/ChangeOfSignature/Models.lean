import CategorialAlgebras.ChangeOfSignature.Derivors
import CategorialAlgebras.ChangeOfSignature.Reducts
import CategorialAlgebras.Dimensions.Transport

/-!
# The functors of a change of signature

The functor induced by $\mathbf{c}^{(n)}$ on partial algebras sends models of the
homogeneous categorial specification of $\Lambda$ to models of that of $\Sigma$, and the
same holds for $\mathbf{c}^{\mathrm{htg}(n)}$ and the heterogeneous specifications. The
transformed algebra is the reduct of the categorial algebra along the derivor, up to the
insertion of the trivial cell proofs: its cells of sort $s$ are the elements of sort
$\varphi(s)$, every $\sigma$ acts as the term operation of $c(\sigma)$ (as that of
$c(\sigma)_k$ at $\sigma_k$), and the categorial structure is that of the sort $\varphi(s)$.
In particular the term operations of the terms of the base signature are total higher
functors, while arbitrary terms of the categorial signature may contain partial
compositions.

The induced functors on categorial algebras are naturally identified with the reduct
functors, and they preserve compositions and identities of derivors up to natural
isomorphisms that retain the underlying elements.
-/

universe i u v w

namespace CategorialAlgebras.ChangeOfSignature

open CategoryTheory Presentations Dimensions

variable {S T U : Type u} {sig : Signature.{u, v} S} {tau : Signature.{u, v} T}
  {ups : Signature.{u, v} U}

/-- Transport along an equality of types is heterogeneously equal to the original element. -/
theorem mpr_heq {α β : Sort _} (h : α = β) (y : β) : HEq (h.mpr y) y := by
  cases h
  rfl

/-- Transport along an equality of types is heterogeneously equal to the original element. -/
theorem mp_heq {α β : Sort _} (h : α = β) (y : α) : HEq (h.mp y) y := by
  cases h
  rfl

/-! ## The homogeneous presentation -/

section Homogeneous

variable {I : Type i} [LT I]

/-- In a homogeneous categorial algebra, the term $P$ of the base signature, regarded as a
term of the categorial signature, is defined everywhere, with the value of its term
functor. -/
theorem homogeneousTerm_mem (B : Homogeneous.CategorialAlgebra.{i, u, v, w} I tau)
    {R : Type u} (φ : R → T) (a : List R) {t} (P : Term tau (Word.MappedVariables φ a) t)
    (x : Word.Family (fun r => B.carrier (φ r)) a) :
    (B.termFunctor φ a P).toFun x ∈
      Term.partialEval (A := B.toPartialAlgebra) (Word.valuation x) (homogeneousTerm I P) := by
  induction P with
  | var y =>
    obtain ⟨j, h⟩ := y
    cases h
    exact Part.mem_some _
  | app τ t ih =>
    change _ ∈ Term.partialEval _ (Term.app (.base τ) (fun j => homogeneousTerm I (t j)))
    exact (Term.mem_partialEval_app _ _ _ _).mpr ⟨_, ih, Part.mem_some _⟩

/-- Insert the trivial cell proof of the homogeneous derivor of a change of signature. -/
def homogeneousCell (c : Derivor sig tau)
    (B : PartialAlgebra.{u, max i v u, w} (Homogeneous.Symbol I tau)) (s : S)
    (x : B.carrier (c.sortMap s)) : (homogeneous I c).Cell B s :=
  ⟨x, (homogeneous I c).isCell_of_empty (fun _ => rfl) B s x⟩

omit [LT I] in
/-- Inserting the trivial cell proofs is bijective. -/
theorem homogeneousCell_bijective (c : Derivor sig tau)
    (B : PartialAlgebra.{u, max i v u, w} (Homogeneous.Symbol I tau)) (s : S) :
    Function.Bijective (homogeneousCell c B s) :=
  ⟨fun _ _ he => congrArg Subtype.val he, fun x => ⟨x.val, Subtype.ext rfl⟩⟩

/-- The operations of the reduct have the values of the interpreting terms. -/
theorem homogeneousReduct_imageValue (c : Derivor sig tau)
    (B : Homogeneous.CategorialAlgebra.{i, u, v, w} I tau)
    {a s} (σ : Homogeneous.Symbol I sig a s)
    (x : Word.Family (homogeneousReduct c B).carrier a) {q}
    (hq : q ∈ (homogeneousReduct c B).toPartialAlgebra.op σ x) :
    q ∈ (homogeneous I c).imageValue B.toPartialAlgebra σ
      (fun j => homogeneousCell c B.toPartialAlgebra _ (x j)) := by
  cases σ with
  | base σ =>
    obtain rfl := Part.mem_some_iff.mp hq
    exact homogeneousTerm_mem B c.sortMap _ (c.image σ) x
  | source k s =>
    obtain rfl := Part.mem_some_iff.mp hq
    change _ ∈ Term.partialEval _ (Homogeneous.unary _ _)
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
    exact Part.mem_some _
  | target k s =>
    obtain rfl := Part.mem_some_iff.mp hq
    change _ ∈ Term.partialEval _ (Homogeneous.unary _ _)
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
    exact Part.mem_some _
  | comp k s =>
    change _ ∈ Term.partialEval _ (Homogeneous.binary _ _ _)
    erw [Homogeneous.partialEval_binary, Term.partialEval_var, Part.bind_some,
      Term.partialEval_var, Part.bind_some]
    exact hq

/-- The reduct realizes the transformation along the homogeneous derivor of a change of
signature, by inserting only the trivial cell proofs.

**Formally weaker** than the informal statement. Informally, the two algebras are equal; here the
carrier of a transformed algebra is a subtype of cells, so the equality becomes an isomorphism that
is the identity on elements. -/
noncomputable def homogeneousRealization (c : Derivor sig tau)
    (B : Homogeneous.CategorialAlgebra.{i, u, v, w} I tau) :
    (homogeneousReduct c B).toPartialAlgebra ≅ (homogeneous I c).transformed B.toPartialAlgebra :=
  realizationIso (homogeneous I c) B.toPartialAlgebra (homogeneousReduct c B).toPartialAlgebra
    (Homogeneous.equations_isEPAlgebra (homogeneousReduct c B).satisfiesEquations)
    (homogeneousCell c B.toPartialAlgebra) (homogeneousCell_bijective c B.toPartialAlgebra)
    (homogeneousReduct_imageValue c B)

/-- The realization of the reduct retains each underlying element. -/
@[simp] theorem homogeneousRealization_hom_val (c : Derivor sig tau)
    (B : Homogeneous.CategorialAlgebra.{i, u, v, w} I tau) (s : S)
    (x : (homogeneousReduct c B).carrier s) :
    ((homogeneousRealization c B).hom.toMap s x).val = x := rfl

/-- The homogeneous derivor of a change of signature sends models of the categorial
specification of $\Lambda$ to models of that of $\Sigma$. -/
theorem homogeneous_isModel (c : Derivor sig tau)
    (B : PartialAlgebra.{u, max i v u, w} (Homogeneous.Symbol I tau))
    (hB : (Homogeneous.specification I tau).IsModel B) :
    (Homogeneous.specification I sig).IsModel ((homogeneous I c).transformed B) := by
  let C := Homogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)
  have hc : C.toPartialAlgebra = B := Homogeneous.toPartialAlgebra_ofEquations B _
  rw [← hc]
  exact model_of_iso _ (homogeneousRealization c C)
    ⟨Homogeneous.equations_isEPAlgebra (homogeneousReduct c C).satisfiesEquations,
      fun _ ⟨e, he⟩ => he ▸ (homogeneousReduct c C).satisfiesEquations e⟩

/-- The functor induced by the homogeneous derivor of a change of signature on models. -/
noncomputable def homogeneousModels (I : Type i) [LT I] (c : Derivor sig tau) :
    (Homogeneous.specification I tau).Models ⥤ (Homogeneous.specification I sig).Models :=
  inducedModelFunctor.{u, max i v u, w} (homogeneous I c) _ _ (homogeneous_isModel c)

/-- The functor $\mathbf{c}^{(n)\ast}_{\mathfrak{gd}}$ on homogeneous categorial algebras,
transported along the model isomorphisms. -/
noncomputable def homogeneousFunctor (I : Type i) [LT I] (c : Derivor sig tau) :
    Homogeneous.CategorialAlgebra.{i, u, v, w} I tau ⥤
      Homogeneous.CategorialAlgebra.{i, u, v, w} I sig :=
  Homogeneous.modelIsomorphism.functor ⋙ homogeneousModels I c ⋙
    Homogeneous.modelIsomorphism.inverse

/-- On model homomorphisms, the functor of a change of signature restricts the original
map, reindexed along the sort map. -/
@[simp] theorem homogeneousModels_map_val (c : Derivor sig tau)
    {B C : (Homogeneous.specification I tau).Models} (f : B ⟶ C) (s : S) (x) :
    (((homogeneousModels.{i, u, v, w} I c).map f).hom.hom.toMap s x).val =
      f.hom.hom.toMap (c.sortMap s) x.val := rfl

/-- The reduct and the induced model functor agree after expansion to models. -/
noncomputable def homogeneousModelsReductIso (I : Type i) [LT I] (c : Derivor sig tau) :
    homogeneousReductFunctor.{i, u, u, v, v, w} I c ⋙ Homogeneous.modelIsomorphism.functor ≅
      Homogeneous.modelIsomorphism.functor ⋙ homogeneousModels I c :=
  NatIso.ofComponents (fun B => modelIso _ _ (homogeneousRealization c B)) (by
    intro B C f
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply PartialAlgebra.Hom.ext
    funext s x
    rfl)

/-- The functor of a change of signature on homogeneous categorial algebras is the reduct
functor, up to a natural isomorphism that retains the underlying elements. -/
noncomputable def homogeneousFunctorReductIso (I : Type i) [LT I] (c : Derivor sig tau) :
    homogeneousFunctor.{i, u, v, w} I c ≅ homogeneousReductFunctor I c :=
  Functor.isoWhiskerRight (homogeneousModelsReductIso I c).symm
      Homogeneous.modelIsomorphism.inverse ≪≫
    eqToIso (by
      change homogeneousReductFunctor I c ⋙
        (Homogeneous.modelIsomorphism.functor ⋙ Homogeneous.modelIsomorphism.inverse) = _
      rw [← Homogeneous.modelIsomorphism.unit_eq]
      rfl)

/-- The functor of a composite derivor is the composite of the functors, up to a natural
isomorphism that retains the underlying elements. -/
noncomputable def homogeneousModelsComp (I : Type i) [LT I] (c : Derivor sig tau)
    (d : Derivor tau ups) :
    homogeneousModels.{i, u, v, w} I d ⋙ homogeneousModels I c ≅
      homogeneousModels I (c.comp d) :=
  inducedCompositeModelsNatIsoOfEq (homogeneous I c) (homogeneous I d)
    (homogeneous I (c.comp d)) _ _ _ _ _ _
    (fun B _ => (homogeneous I c).comparison_surjective_of_empty _ B (fun _ => rfl))
    (homogeneous_comp I c d)

/-- The functor of an identity derivor is the identity, up to a natural isomorphism that
forgets only the cell proofs. -/
noncomputable def homogeneousModelsIdentity (I : Type i) [LT I] (sig : Signature.{u, v} S) :
    homogeneousModels.{i, u, v, w} I (Derivor.identity sig) ≅ 𝟭 _ :=
  inducedIdentityModelsIsoOfEq (homogeneous_identity I sig) _ _

/-- On categorial algebras, the functor of a composite derivor is the composite of the
functors, up to a natural isomorphism.

**Formally weaker** than the informal statement. Informally, the two functors are equal; here the
carriers of transformed algebras are subtypes of cells, so the equality becomes a natural
isomorphism that is the identity on elements. -/
noncomputable def homogeneousFunctorComp (I : Type i) [LT I] (c : Derivor sig tau)
    (d : Derivor tau ups) :
    homogeneousFunctor.{i, u, v, w} I d ⋙ homogeneousFunctor I c ≅
      homogeneousFunctor I (c.comp d) :=
  conjugateCompositeIso Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism
    Homogeneous.modelIsomorphism (homogeneousModelsComp I c d)

/-- On categorial algebras, the functor of an identity derivor is the identity, up to a
natural isomorphism.

**Formally weaker** than the informal statement. Informally, the two functors are equal; here the
carriers of transformed algebras are subtypes of cells, so the equality becomes a natural
isomorphism that is the identity on elements. -/
noncomputable def homogeneousFunctorIdentity (I : Type i) [LT I] (sig : Signature.{u, v} S) :
    homogeneousFunctor.{i, u, v, w} I (Derivor.identity sig) ≅ 𝟭 _ :=
  conjugateIdentityIso Homogeneous.modelIsomorphism (homogeneousModelsIdentity I sig)

end Homogeneous

/-! ## The heterogeneous presentation -/

section Heterogeneous

variable {I : Type i} [Preorder I]

/-- The term $P_k$ is the copy in dimension $k$ of the operation at the root of $P$, applied
to the copies of its arguments. -/
theorem heterogeneousTerm_app (k : I) {R : Type u} {φ : R → T} {a : List R} {b : List T}
    {t} (τ : tau b t) (ts : Word.Family (Term tau (Word.MappedVariables φ a)) b) :
    heterogeneousTerm I k (Term.app τ ts) =
      Heterogeneous.base k τ (fun j => heterogeneousTerm I k (ts j)) := by
  change Term.app (Heterogeneous.Symbol.base k τ) _ =
    Term.app (Heterogeneous.Symbol.base k τ) _
  congr 1
  funext q
  apply eq_of_heq
  simp only [Heterogeneous.dimensionFamily, Equiv.coe_fn_symm_mk]
  refine HEq.trans ?_ (mpr_heq _ _).symm
  exact valuation_heq _ _

/-- In a heterogeneous categorial algebra, the term $P_k$ is defined everywhere, with the
value of the term functor of $P$ in dimension $k$. -/
theorem heterogeneousTerm_mem (B : Heterogeneous.CategorialAlgebra.{i, u, v, w} I tau)
    {R : Type u} (φ : R → T) (k : I) (a : List R) {t}
    (P : Term tau (Word.MappedVariables φ a) t)
    (z : Word.Family (fun p : I × R => B.carrier (p.1, φ p.2))
      (Heterogeneous.dimensionWord k a)) :
    (B.termFunctor φ a P).toFun k (Heterogeneous.dimensionFamily k a z) ∈
      Term.partialEval (A := B.toPartialAlgebra)
        (Word.valuation (φ := fun p : I × R => (p.1, φ p.2)) z) (heterogeneousTerm I k P) := by
  induction P with
  | var y =>
    obtain ⟨j, h⟩ := y
    cases h
    apply Part.mem_some_iff.mpr
    change Heterogeneous.dimensionFamily k a z j = _
    apply eq_of_heq
    simp only [Heterogeneous.dimensionFamily, Equiv.coe_fn_mk, id]
    refine (mp_heq _ _).trans ?_
    exact (valuation_heq z (dimensionPosition k φ a _ ⟨j, rfl⟩)).symm
  | app τ t ih =>
    rw [heterogeneousTerm_app, Heterogeneous.partialEval_base]
    refine Part.mem_bind_iff.mpr ⟨_, (mem_partFamily _ _).mpr ih, ?_⟩
    refine Part.mem_some_iff.mpr ?_
    change _ = (B.op τ).toFun k (Heterogeneous.dimensionFamily (A := B.carrier) k _
      ((Heterogeneous.dimensionFamily (A := B.carrier) k _).symm _))
    rw [Equiv.apply_symm_apply]
    rfl

/-- Insert the trivial cell proof of the heterogeneous derivor of a change of signature. -/
def heterogeneousCell (c : Derivor sig tau)
    (B : PartialAlgebra.{max i u, max i v u, w} (Heterogeneous.Symbol I tau)) (p : I × S)
    (x : B.carrier (heterogeneousSortMap c p)) : (heterogeneous I c).Cell B p :=
  ⟨x, (heterogeneous I c).isCell_of_empty (fun _ => rfl) B p x⟩

omit [Preorder I] in
/-- Inserting the trivial cell proofs is bijective. -/
theorem heterogeneousCell_bijective [Preorder I] (c : Derivor sig tau)
    (B : PartialAlgebra.{max i u, max i v u, w} (Heterogeneous.Symbol I tau)) (p : I × S) :
    Function.Bijective (heterogeneousCell c B p) :=
  ⟨fun _ _ he => congrArg Subtype.val he, fun x => ⟨x.val, Subtype.ext rfl⟩⟩

/-- The operations of the reduct have the values of the interpreting terms. -/
theorem heterogeneousReduct_imageValue (c : Derivor sig tau)
    (B : Heterogeneous.CategorialAlgebra.{i, u, v, w} I tau)
    {a s} (σ : Heterogeneous.Symbol I sig a s)
    (x : Word.Family (heterogeneousReduct c B).carrier a) {q}
    (hq : q ∈ (heterogeneousReduct c B).toPartialAlgebra.op σ x) :
    q ∈ (heterogeneous I c).imageValue B.toPartialAlgebra σ
      (fun j => heterogeneousCell c B.toPartialAlgebra _ (x j)) := by
  cases σ with
  | base k σ =>
    obtain rfl := Part.mem_some_iff.mp hq
    exact heterogeneousTerm_mem B c.sortMap k _ (c.image σ) x
  | source h s =>
    obtain rfl := Part.mem_some_iff.mp hq
    change _ ∈ Term.partialEval _ (Heterogeneous.unary _ _)
    erw [Heterogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
    exact Part.mem_some _
  | target h s =>
    obtain rfl := Part.mem_some_iff.mp hq
    change _ ∈ Term.partialEval _ (Heterogeneous.unary _ _)
    erw [Heterogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
    exact Part.mem_some _
  | identity h s =>
    obtain rfl := Part.mem_some_iff.mp hq
    change _ ∈ Term.partialEval _ (Heterogeneous.unary _ _)
    erw [Heterogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
    exact Part.mem_some _
  | comp h s =>
    change _ ∈ Term.partialEval _ (Heterogeneous.binary _ _ _)
    erw [Heterogeneous.partialEval_binary, Term.partialEval_var, Part.bind_some,
      Term.partialEval_var, Part.bind_some]
    exact hq

/-- The reduct realizes the transformation along the heterogeneous derivor of a change of
signature, by inserting only the trivial cell proofs.

**Formally weaker** than the informal statement. Informally, the two algebras are equal; here the
carrier of a transformed algebra is a subtype of cells, so the equality becomes an isomorphism that
is the identity on elements. -/
noncomputable def heterogeneousRealization (c : Derivor sig tau)
    (B : Heterogeneous.CategorialAlgebra.{i, u, v, w} I tau) :
    (heterogeneousReduct c B).toPartialAlgebra ≅
      (heterogeneous I c).transformed B.toPartialAlgebra :=
  realizationIso (heterogeneous I c) B.toPartialAlgebra
    (heterogeneousReduct c B).toPartialAlgebra
    (Heterogeneous.equations_isEPAlgebra (heterogeneousReduct c B).satisfiesEquations)
    (heterogeneousCell c B.toPartialAlgebra) (heterogeneousCell_bijective c B.toPartialAlgebra)
    (heterogeneousReduct_imageValue c B)

/-- The realization of the reduct retains each underlying element. -/
@[simp] theorem heterogeneousRealization_hom_val (c : Derivor sig tau)
    (B : Heterogeneous.CategorialAlgebra.{i, u, v, w} I tau) (p : I × S)
    (x : (heterogeneousReduct c B).carrier p) :
    ((heterogeneousRealization c B).hom.toMap p x).val = x := rfl

/-- The heterogeneous derivor of a change of signature sends models of the heterogeneous
categorial specification of $\Lambda$ to models of that of $\Sigma$. -/
theorem heterogeneous_isModel (c : Derivor sig tau)
    (B : PartialAlgebra.{max i u, max i v u, w} (Heterogeneous.Symbol I tau))
    (hB : (Heterogeneous.specification I tau).IsModel B) :
    (Heterogeneous.specification I sig).IsModel ((heterogeneous I c).transformed B) := by
  let C := Heterogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)
  have hc : C.toPartialAlgebra = B := Heterogeneous.toPartialAlgebra_ofEquations B _
  rw [← hc]
  exact model_of_iso _ (heterogeneousRealization c C)
    ⟨Heterogeneous.equations_isEPAlgebra (heterogeneousReduct c C).satisfiesEquations,
      fun _ ⟨e, he⟩ => he ▸ (heterogeneousReduct c C).satisfiesEquations e⟩

/-- The functor induced by the heterogeneous derivor of a change of signature on models. -/
noncomputable def heterogeneousModels (I : Type i) [Preorder I] (c : Derivor sig tau) :
    (Heterogeneous.specification I tau).Models ⥤ (Heterogeneous.specification I sig).Models :=
  inducedModelFunctor.{max i u, max i v u, w} (heterogeneous I c) _ _ (heterogeneous_isModel c)

/-- The functor $\mathbf{c}^{\mathrm{htg}(n)\ast}_{\mathfrak{gd}}$ on heterogeneous
categorial algebras, transported along the model isomorphisms. -/
noncomputable def heterogeneousFunctor (I : Type i) [Preorder I] (c : Derivor sig tau) :
    Heterogeneous.CategorialAlgebra.{i, u, v, w} I tau ⥤
      Heterogeneous.CategorialAlgebra.{i, u, v, w} I sig :=
  Heterogeneous.modelIsomorphism.functor ⋙ heterogeneousModels I c ⋙
    Heterogeneous.modelIsomorphism.inverse

/-- On model homomorphisms, the functor of a change of signature restricts the original
map, reindexed along the sort map. -/
@[simp] theorem heterogeneousModels_map_val (c : Derivor sig tau)
    {B C : (Heterogeneous.specification I tau).Models} (f : B ⟶ C) (p : I × S) (x) :
    (((heterogeneousModels.{i, u, v, w} I c).map f).hom.hom.toMap p x).val =
      f.hom.hom.toMap (heterogeneousSortMap c p) x.val := rfl

/-- The reduct and the induced model functor agree after expansion to models. -/
noncomputable def heterogeneousModelsReductIso (I : Type i) [Preorder I] (c : Derivor sig tau) :
    heterogeneousReductFunctor.{i, u, u, v, v, w} I c ⋙ Heterogeneous.modelIsomorphism.functor ≅
      Heterogeneous.modelIsomorphism.functor ⋙ heterogeneousModels I c :=
  NatIso.ofComponents (fun B => modelIso _ _ (heterogeneousRealization c B)) (by
    intro B C f
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply PartialAlgebra.Hom.ext
    funext p x
    rfl)

/-- The functor of a change of signature on heterogeneous categorial algebras is the reduct
functor, up to a natural isomorphism that retains the underlying elements. -/
noncomputable def heterogeneousFunctorReductIso (I : Type i) [Preorder I] (c : Derivor sig tau) :
    heterogeneousFunctor.{i, u, v, w} I c ≅ heterogeneousReductFunctor I c :=
  Functor.isoWhiskerRight (heterogeneousModelsReductIso I c).symm
      Heterogeneous.modelIsomorphism.inverse ≪≫
    eqToIso (by
      change heterogeneousReductFunctor I c ⋙
        (Heterogeneous.modelIsomorphism.functor ⋙ Heterogeneous.modelIsomorphism.inverse) = _
      rw [← Heterogeneous.modelIsomorphism.unit_eq]
      rfl)

/-- The functor of a composite derivor is the composite of the functors, up to a natural
isomorphism that retains the underlying elements. -/
noncomputable def heterogeneousModelsComp (I : Type i) [Preorder I] (c : Derivor sig tau)
    (d : Derivor tau ups) :
    heterogeneousModels.{i, u, v, w} I d ⋙ heterogeneousModels I c ≅
      heterogeneousModels I (c.comp d) :=
  inducedCompositeModelsNatIsoOfEq (heterogeneous I c) (heterogeneous I d)
    (heterogeneous I (c.comp d)) _ _ _ _ _ _
    (fun B _ => (heterogeneous I c).comparison_surjective_of_empty _ B (fun _ => rfl))
    (heterogeneous_comp I c d)

/-- The functor of an identity derivor is the identity, up to a natural isomorphism that
forgets only the cell proofs. -/
noncomputable def heterogeneousModelsIdentity (I : Type i) [Preorder I]
    (sig : Signature.{u, v} S) :
    heterogeneousModels.{i, u, v, w} I (Derivor.identity sig) ≅ 𝟭 _ :=
  inducedIdentityModelsIsoOfEq (heterogeneous_identity I sig) _ _

/-- On categorial algebras, the functor of a composite derivor is the composite of the
functors, up to a natural isomorphism.

**Formally weaker** than the informal statement. Informally, the two functors are equal; here the
carriers of transformed algebras are subtypes of cells, so the equality becomes a natural
isomorphism that is the identity on elements. -/
noncomputable def heterogeneousFunctorComp (I : Type i) [Preorder I] (c : Derivor sig tau)
    (d : Derivor tau ups) :
    heterogeneousFunctor.{i, u, v, w} I d ⋙ heterogeneousFunctor I c ≅
      heterogeneousFunctor I (c.comp d) :=
  conjugateCompositeIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism (heterogeneousModelsComp I c d)

/-- On categorial algebras, the functor of an identity derivor is the identity, up to a
natural isomorphism.

**Formally weaker** than the informal statement. Informally, the two functors are equal; here the
carriers of transformed algebras are subtypes of cells, so the equality becomes a natural
isomorphism that is the identity on elements. -/
noncomputable def heterogeneousFunctorIdentity (I : Type i) [Preorder I]
    (sig : Signature.{u, v} S) :
    heterogeneousFunctor.{i, u, v, w} I (Derivor.identity sig) ≅ 𝟭 _ :=
  conjugateIdentityIso Heterogeneous.modelIsomorphism (heterogeneousModelsIdentity I sig)

end Heterogeneous

end CategorialAlgebras.ChangeOfSignature
