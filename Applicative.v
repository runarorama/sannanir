Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Relation_Definitions.
Require Import Coq.Setoids.Setoid.

Set Implicit Arguments.

Implicit Type a b c d : Set.

Class Applicative(f: Set -> Set): Type := {
  carrier := f;

  pure: forall {a}, a -> f a;
  ap: forall {a b}, f (a -> b) -> f a -> f b;

  identity: forall a (v: f a), ap (pure id) v = v;
  composition: forall {a b c} (u: f (b -> c)) (v: f (a -> b)) (w: f a),
                     ap (ap (ap (pure compose) u) v) w = ap u (ap v w);
  homomorphism: forall {a b} (f : a -> b) (x: a), ap (pure f) (pure x) = pure (f x);
  interchange: forall {a b} (u: f (a -> b)) (v: a),
                  ap u (pure v) = ap (pure (fun (x: a -> b) => x v)) u
}.

Definition map {f: Set -> Set} {a b} {P: Applicative f} (g: a -> b) (z: f a): f b :=
  ap (pure g) z.

Definition map2 {f: Set -> Set} {a b c} (P: Applicative f) (g: a -> b -> c) (x: f a) (y: f b): f c :=
  ap (map g x) y.

Lemma hom_map: forall {f: Set -> Set} {a b: Set} (x: a) (g: a -> b) (P: Applicative f),
  map g (pure x) = pure (g x).
Proof.
  intros.
  apply homomorphism.
Qed.

Lemma interchange': forall {f: Set -> Set} {a b} {P: Applicative f} (v: a),
  ap (pure (fun (x: a -> b) => x v)) = (fun u => ap u (pure v)).
Proof.
  intros.
  change (ap (pure (fun x: a -> b => x v))) with (fun u => (ap (pure (fun x: a -> b => x v))) u).
  extensionality H.
  rewrite <- interchange.
  split.
Qed.

Lemma identity': forall {f: Set -> Set} {a} {P: Applicative f},
  ap (pure (@id a)) = @id (f a).
Proof.
  intros.
  extensionality H.
  apply identity.
Qed.

Lemma composition': forall {f: Set -> Set} {a b c} {P: Applicative f} (u: f (b -> c)) (v: f (a -> b)),
  ap (ap (ap (pure compose) u) v) = fun (w: f a) => ap u (ap v w).
intros.
  extensionality H.
  apply composition.
Qed.

Instance composeAp {f g: Set -> Set} {P: Applicative f} {Q: Applicative g}: Applicative (compose f g) := {
  pure := fun _ x => pure (pure x);
  ap   := fun _ _ ff fx => map2 P ap ff fx 
}.
Proof.
  (*identity*)
    unfold map2. unfold map. intros.
    rewrite homomorphism.
    rewrite identity'.
    rewrite identity.
  split.
  (*composition*)
    unfold map2; unfold map. intros.
    repeat (rewrite homomorphism || rewrite <- composition).
    rewrite interchange.
    rewrite <- composition.
    rewrite homomorphism.
    unfold compose.
    fold (@compose a b c).
    replace (fun (x : g (b -> c)) (x0 : g (a -> b)) => ap (ap (ap (pure compose) x) x0))
       with (fun (x : g (b -> c)) (x0 : g (a -> b)) x1 => ap x (ap x0 x1)).
    rewrite homomorphism.
    split.
    extensionality H. extensionality I. extensionality J.
    rewrite composition.
  split.
  (*homomorphism*)
    intros. unfold map2. unfold map.
    repeat rewrite homomorphism.
  split.
  (*interchange*)
    intros. unfold map2. unfold map.
    rewrite homomorphism.
    rewrite interchange'.
    rewrite interchange.
    rewrite <- composition.
    rewrite homomorphism.
    rewrite interchange.
    rewrite homomorphism.
    assert ((compose (fun x : g a -> g b => x (pure v)) ap) = ((fun u0 : g (a -> b) => ap u0 (pure v)))).
    unfold compose.
    extensionality H.
    split.
    elim H.
  split.
Qed.
