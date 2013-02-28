Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Relation_Definitions.
Require Import Coq.Setoids.Setoid

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

Definition map2 {f: Set -> Set} {a b c} (P: Applicative f)
  (g: a -> b -> c) (x: f a) (y: f b): f c :=
    ap (map g x) y.

Lemma hom_map: forall {f: Set -> Set} {a b: Set} (x: a) (g: a -> b) (P: Applicative f), map g (pure x) = pure (g x).
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

Lemma identity': forall {f: Set -> Set} {a} {P: Applicative f}, ap (pure (@id a)) = @id (f a).
Proof.
intros.
extensionality H.
apply identity.
Qed.

Instance composeAp {f g: Set -> Set} {P: Applicative f} {Q: Applicative g}: Applicative (compose f g) := {
  pure := fun _ x => pure (pure x);
  ap   := fun _ _ ff fx => map2 P ap ff fx 
}.
Proof.
unfold map2.
unfold map.
intros.
rewrite homomorphism.
rewrite identity'.
rewrite identity.
split.
unfold map2; unfold map.
intros.
rewrite homomorphism.
Focus 2.
intros. unfold map2. unfold map.
repeat rewrite homomorphism.
split.
Focus 2.
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
rewrite <- composition at 3.
