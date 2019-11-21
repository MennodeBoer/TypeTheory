Require Export UniMath.Foundations.Propositions.
Require Export UniMath.Foundations.Sets.

Require Export UniMath.MoreFoundations.Notations.

Require Export UniMath.CategoryTheory.Core.Categories.
Require Export UniMath.CategoryTheory.Core.Isos.
Require Export UniMath.CategoryTheory.limits.terminal.
Require Export UniMath.CategoryTheory.limits.binproducts.
Require Export UniMath.CategoryTheory.limits.pullbacks.

Local Open Scope cat.

Section Sections.
  Context {C : precategory}.

  Definition is_section {A B : C} (f : A --> B) (s : B --> A) :=
    s · f = identity B.

  Hypothesis H : has_homsets C.

  Lemma isaprop_is_section {A B : C} (f : A --> B) (s : B --> A) :
    isaprop (is_section f s).
  Proof.
    apply H.
  Qed.

End Sections.
 
Section BinProducts_Pullbacks.

  Coercion BinProductObject : BinProduct >-> ob.
  
  Definition pullback_of_product_gives_product {C : category} {X Y Z : C} (prod : BinProduct C Y Z) (f : X --> Y) (P : Pullback f (BinProductPr1 C prod)) : BinProduct C X Z.
  Proof.
    use make_BinProduct.
    - exact P.
    - apply PullbackPr1.
    - exact (BinProductPr2 C prod ∘ PullbackPr2 P).
    - unfold isBinProduct.
      intros D h g.
      use tpair.
      + exists (PullbackArrow P D h (BinProductArrow C prod (f ∘ h) g) (! (BinProductPr1Commutes _ _ _ _ _ _ _))).
        split.
        * apply PullbackArrow_PullbackPr1.
        * rewrite assoc.
          rewrite (PullbackArrow_PullbackPr2 _ _ _ _).
          apply BinProductPr2Commutes.
      + simpl.
        intros.
        destruct t as [t [eq1 eq2]].
        use total2_paths_f.
        * simpl.
          use PullbackArrowUnique.
          -- exact eq1.
          -- use BinProductArrowUnique.
             ++ destruct P as [P [H unique]].
                rewrite (! (assoc _ _ _)).
                unfold PullbackPr2.
                simpl.
                etrans.
                use (maponpaths (λ x , x ∘ t) (! H)).
                rewrite assoc.
                apply (maponpaths (λ x , f ∘ x) eq1).
            ++ rewrite assoc in eq2.
               exact eq2.
        * apply proofirrelevance.
          simpl.
          apply isofhleveldirprod.
          apply (homset_property C).
          apply (homset_property C).
  Defined.
  
  Definition binproduct_from_pullback_over_terminal {C : precategory} {T : Terminal C} {A B : C} (P : Pullback (TerminalArrow T A) (TerminalArrow T B)) : BinProduct C A B.
  Proof.
    use make_BinProduct.
    - exact P.
    - exact (PullbackPr1 P).
    - exact (PullbackPr2 P).
    - unfold isBinProduct.
      intros.
      apply P.
      rewrite TerminalArrowUnique.
      apply TerminalArrowUnique.
  Defined.

End BinProducts_Pullbacks.

Section Diagonal.
  Context  {C : precategory}.

  
  Definition diagonal {C : precategory} {A : C} (P : BinProduct C A A) : A --> P := BinProductArrow C P (identity A) (identity A).
  
End Diagonal.