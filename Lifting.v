Require Import UniMath.Foundations.Sets.


(* Functions f : a -> b and g : c -> d are weakly orthogonal if for
   any commutative square there is a diagonal h : b -> c making the
   diagram commute:

        i
     a  →  c
        h
   f ↓  ↗  ↓ g

     b  →  d
        j

   It is said that f has the left lifting property with respect to g,
   and g has the right lifting property with respect to f. *)

Definition weakly_orthogonal {a b c d : UU} (f : a -> b) (g : c -> d) : UU :=
  ∏ (i : a -> c) (j : b -> d), g ∘ i = j ∘ f -> ∃ h : b -> c, h ∘ f = i × g ∘ h = j.

Notation "f ⧄ g" := (weakly_orthogonal f g) (at level 90).


(* A function is surjective iff it has the right lifting property with
   respect to the simplest non-surjective function ∅ -> unit. *)

Lemma issurjective_weakly_orthogonal {c d : UU} (g : c -> d) :
  issurjective g -> @fromempty unit ⧄ g.
Proof.
  intros Hg i j H.
  use (hinhfun _ (Hg (j tt))); intro x. induction x as [x Hx].
  exists (λ _, x). apply make_dirprod; apply funextsec.
  - intro n. apply (fromempty n).
  - intro t. apply (pathscomp0 Hx). induction t. apply idpath.
Defined.

Lemma weakly_orthogonal_issurjective {c d : UU} (g : c -> d) :
  @fromempty unit ⧄ g -> issurjective g.
Proof.
  intros Hg y.
  use (hinhfun _ (Hg fromempty (λ _, y) _)).
  - intro h. induction h as [h Hh].
    exists (h tt). apply (eqtohomot (pr2 Hh)).
  - apply funextsec. intro n. apply (fromempty n).
Defined.


(* A function is an inclusion (function of h-level 1) iff it has the
   right lifting property with respect to the simplest non-inclusion
   bool -> unit. *)

Lemma isincl_weakly_orthogonal {c d : UU} (g : c -> d) :
  isincl g -> @tounit bool ⧄ g.
Proof.
  intros Hg i j H.
  induction (Hg (j tt)
                (i true  ,, eqtohomot H true)
                (i false ,, eqtohomot H false)) as [H0 _].
  apply hinhpr. exists (λ _, i true). use make_dirprod; apply funextsec.
  - intro b. induction b.
    + apply idpath.
    + exact (maponpaths pr1 H0).
  - intro t. apply (pathscomp0 (eqtohomot H true)).
    induction t. apply idpath.
Defined.

Lemma weakly_orthogonal_isincl {c d : hSet} (g : c -> d) :
  @tounit bool ⧄ g -> isincl g.
Proof.
  intros H y x x'.
  use (factor_through_squash (isapropiscontr (x = x')) _
                             (H (bool_ind _ (pr1 x) (pr1 x')) (λ _, y) _)).
  - intro h. induction h as [h [H0 H1]]. use make_iscontr.
    + use hfibertriangle2.
      * exact (! eqtohomot H0 true @ eqtohomot H0 false).
      * apply setproperty.
    + intro p. apply proofirrelevance.
      apply isaset_hfiber; apply setproperty.
  - apply funextsec. intro b. induction b.
    + exact (pr2 x).
    + exact (pr2 x').
Defined.
